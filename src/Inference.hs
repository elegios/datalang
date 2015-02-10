{-# LANGUAGE TupleSections, TypeSynonymInstances, FlexibleInstances, TemplateHaskell, MultiParamTypeClasses #-}

module Inference (fullInfer, infer) where

import Ast hiding (Type(..), Restriction, FuncDef, Expression, Statement)
import Data.Functor ((<$>))
import Data.STRef
import Data.Tuple (swap)
import Data.Char (isLower, isUpper)
import Data.Generics.Uniplate.Direct
import Control.Applicative ((<*>), (<*), getZipList, ZipList(..))
import Control.Monad.ST
import Control.Monad.State
import Control.Lens hiding (op, universe, plate)
import qualified Ast
import qualified Data.Map as M
import qualified Data.Set as S

-- TODO: deal with named types, they are currently not correct

type UnifyError = String
type UnifyErrorFunction = UnifyError -> ErrorMessage

data Changeable = Changeable | Unchangeable String deriving (Eq, Show)
data TypeVarTarget = Environment | Unbounds deriving Eq

data ErrorMessage = ErrorString String deriving Show
data InferrerState s = InferrerState
  { _errors :: [ErrorMessage]
  , _variables :: M.Map String (Inferred s)
  , _typeVariables :: M.Map String (Inferred s)
  , _functions :: M.Map String Ast.FuncDef
  }

-- TODO: support for typeclasses and similar stuff
data Inferred s = IntT TSize
                | UIntT TSize
                | FloatT TSize
                | BoolT
                | NamedT String [Inferred s]
                | PointerT (Inferred s)
                | MemorychunkT (Inferred s) Bool (Inferred s)
                | StructT [(String, Inferred s)]
                | FunctionT [Inferred s] [Inferred s]
                | Ref (TVarRef s)
                deriving (Eq, Show)
data TVar s = Unbound (Restriction s) Changeable | Link (Inferred s) deriving (Eq, Show)
type TVarRef s = STRef s (TVar s)
instance Show (TVarRef s) where
  show _ = "tref"

instance Uniplate (Inferred s) where
  uniplate (IntT s) = plate IntT |- s
  uniplate (UIntT s) = plate UIntT |- s
  uniplate (FloatT s) = plate FloatT |- s
  uniplate BoolT = plate BoolT
  uniplate (NamedT n ts) = plate NamedT |- n ||* ts
  uniplate (PointerT t) = plate PointerT |* t
  uniplate (MemorychunkT it cap t) = plate MemorychunkT |* it |- cap |* t
  uniplate s@(StructT props) = plateProject fromStruct toStruct s
    where
      fromStruct _ = snd <$> props
      toStruct = StructT . zip (fst <$> props)
  uniplate (FunctionT its ots) = plate FunctionT ||* its ||* ots
  uniplate (Ref r) = plate Ref |- r
instance Biplate [Inferred s] (Inferred s) where
  biplate (x:xs) = plate (:) |* x ||* xs
  biplate x = plate x

type Restriction s = RestrictionT (Inferred s)

type Inferrer s a = StateT (InferrerState s) (ST s) a

makeLenses ''InferrerState

fullInfer :: Source -> ([ErrorMessage], Source)
fullInfer source = (reverse errs, newSource)
  where
    funcs = functionDefinitions source
    (errs, newFuncDefs) = M.mapAccum (infer funcs) [] funcs
    newSource = source { functionDefinitions = newFuncDefs }

infer :: M.Map String Ast.FuncDef -> [ErrorMessage] -> Ast.FuncDef -> ([ErrorMessage], Ast.FuncDef)
infer funcs errs def = runST $ convertOutput <$> runStateT inference initState
  where
    initState = InferrerState errs M.empty M.empty funcs
    inference = enterInfer def >>= exitInfer
    convertOutput = (_1 %~ view errors) . swap

enterInfer :: FuncDefT Ast.Type -> Inferrer s (FuncDefT (Inferred s))
enterInfer inDef = do
  FunctionT inTs' outTs' <- convertFuncSig restrs inTs outTs Environment
  zipWithM_ defineLocal (ins ++ outs) (inTs' ++ outTs')
  body' <- enterStatement body
  return $ Ast.FuncDef inTs' outTs' restrs ins outs body' sr
  where
    Ast.FuncDef inTs outTs restrs ins outs body sr = inDef
    defineLocal n t = variables . at n ?= t

enterStatement :: StatementT Ast.Type -> Inferrer s (StatementT (Inferred s))
enterStatement (FuncCall fName inexprs outexprs sr) = do
  (inexprs', inTs) <- unzip <$> mapM enterExpression inexprs
  (outexprs', outTs) <- unzip <$> mapM enterExpression outexprs
  unifyExternalFunction fName inTs outTs sr
  return $ FuncCall fName inexprs' outexprs' sr

enterStatement (Defer stmnt sr) = Defer <$> enterStatement stmnt <*> return sr

enterStatement (ShallowCopy assignee value sr) = do
  (assignee', assigneeT) <- enterExpression assignee
  (value', valueT) <- enterExpression value
  unify err assigneeT valueT
  return $ ShallowCopy assignee' value' sr
  where err unifyError = ErrorString $ "Type mismatch in assignment at " ++ show sr ++ ", the type of the left and right hand side expressions cannot be unified: " ++ unifyError

enterStatement (If condition thenStmnt mElseStmnt sr) = do
  (condition', condT) <- enterExpression condition
  makeBool err condT
  If condition' <$> enterStatement thenStmnt <*> elseStmnt' <*> return sr
  where
    elseStmnt' = maybe (return Nothing) (fmap Just . enterStatement) mElseStmnt
    err unifyError = ErrorString $ "Type mismatch in if statement at " ++ show sr ++ ", condition must have type Bool: " ++ unifyError

enterStatement (While condition stmnt sr) = do
  (condition', condT) <- enterExpression condition
  makeBool err condT
  While condition' <$> enterStatement stmnt <*> return sr
  where err unifyError = ErrorString $ "Type mismatch in while statement at " ++ show sr ++ ", condition must have type Bool: " ++ unifyError

enterStatement (Scope stmnts sr) = do
  prevVariables <- use variables
  stmnts' <- mapM enterStatement stmnts
  variables .= prevVariables
  return $ Scope stmnts' sr

enterStatement (Terminator terminator sr) = return $ Terminator terminator sr

-- TODO: deal with mutability, ensure nothing strange happens
enterStatement (VarInit mutable vName t expr sr) = do
  convertedT <- convert t
  (expr', exprT) <- enterExpression expr
  unify err convertedT exprT
  variables . at vName ?= convertedT
  return $ VarInit mutable vName convertedT expr' sr
  where err unifyError = ErrorString $ "Type mismatch in variable declaration at " ++ show sr ++ ": " ++ unifyError

enterExpression :: ExpressionT Ast.Type -> Inferrer s (ExpressionT (Inferred s), Inferred s)
enterExpression (Bin op expr1 expr2 sr) = do
  (expr1', tref1) <- enterExpression expr1
  (expr2', tref2) <- enterExpression expr2
  unify unifyErr tref1 tref2
  (Bin op expr1' expr2' sr,) <$> case () of
    _ | op == Remainder -> restrict intErr (NumR IntSpec) tref1
    _ | op `elem` [Equal, NotEqual] -> return BoolT
    _ | op `elem` [Plus, Minus, Times, Divide] -> restrict numErr (NumR NoSpec) tref1
    _ | op `elem` [BinAnd, BinOr, LShift, LogRShift, AriRShift, Xor] -> restrict uintErr UIntR tref1
    _ | op `elem` [Lesser, Greater, LE, GE] -> restrict numErr (NumR NoSpec) tref1 >> return BoolT
  where
    unifyErr m = ErrorString $ "Could not unify expression types around " ++ show op ++ " at " ++ show sr ++ ". " ++ show m
    numErr m = ErrorString $ "Expressions at " ++ show sr ++ " must have a numerical type. " ++ show m
    uintErr m = ErrorString $ "Expressions at " ++ show sr ++ " must have a uint type. " ++ show m
    intErr m = ErrorString $ "Expressions at " ++ show sr ++ " must have an int type. " ++ show m

enterExpression (Un Deref expr sr) = do
  (expr', tref) <- enterExpression expr
  innerTref <- makePointer errF tref
  return . (, innerTref) $ Un Deref expr' sr
  where errF m = ErrorString $ "Expression at " ++ show sr ++ " must be a pointer. " ++ show m

enterExpression (Un AddressOf expr sr) = do
  (expr', t) <- enterExpression expr
  return (Un AddressOf expr' sr, PointerT t)

enterExpression (Un AriNegate expr sr) = do
  (expr', tref) <- enterExpression expr
  restrict errF UIntR tref
  return . (, tref) $ Un AriNegate expr' sr
  where errF m = ErrorString $ "Expression at " ++ show sr ++ " must be a uint type. " ++ show m

enterExpression (Un BinNegate expr sr) = do
  (expr', tref) <- enterExpression expr
  restrict errF UIntR tref
  return . (, tref) $ Un BinNegate expr' sr
  where errF m = ErrorString $ "Expression at " ++ show sr ++ " must be a uint type. " ++ show m

enterExpression (Un Not expr sr) = do
  (expr', tref) <- enterExpression expr
  makeBool errF tref
  return . (, tref) $ Un Not expr' sr
  where errF m = ErrorString $ "Expression at " ++ show sr ++ " must be of type bool. " ++ show m

enterExpression (MemberAccess expr member sr) = do
  (expr', tref) <- enterExpression expr
  memberTref <- accessProperty errF member tref
  return . (, memberTref) $ MemberAccess expr' member sr
  where errF m = ErrorString $ "Expression at " ++ show sr ++ " has no property " ++ member ++ ". " ++ show m

enterExpression Subscript{} = undefined -- TODO: subscript restriction

enterExpression (Variable vName sr) =
  use (variables . at vName) >>= (fmap (Variable vName sr, ) . maybe notFound return)
  where notFound = do
          addError . ErrorString $ vName ++ " is not in scope at " ++ show sr
          newUnbound NoRestriction

enterExpression (ExprFunc fName inExprs t sr) = do
  (inExprs', inTs) <- unzip <$> mapM enterExpression inExprs
  convertedT <- convert t
  unifyExternalFunction fName inTs [convertedT] sr
  return (ExprFunc fName inExprs' convertedT sr, convertedT)

enterExpression (ExprLit lit sr) = (_1 %~ (`ExprLit` sr)) <$> enterLiteral lit

enterExpression (Zero t) = buildReturn (Zero, id) <$> convert t

enterLiteral :: LiteralT Ast.Type -> Inferrer s (LiteralT (Inferred s), Inferred s)
enterLiteral (ILit n t sr) = buildReturn (\tref -> ILit n tref sr, id) <$> (convert t >>= restrict errF (NumR NoSpec))
  where errF m = ErrorString $ "How did you even get this error (int)? " ++ show sr ++ " -- "++ show m

enterLiteral (FLit n t sr) = buildReturn (\tref -> FLit n tref sr, id) <$> (convert t >>= restrict errF (NumR FloatSpec))
  where errF m = ErrorString $ "How did you even get this error (float)? " ++ show sr ++ " -- " ++ show m

enterLiteral (BLit v sr) = return (BLit v sr, BoolT)

enterLiteral (Null Ast.UnknownT sr) =
  buildReturn ((`Null` sr), id) . PointerT <$> newUnbound NoRestriction

buildReturn :: (t -> a, t -> b) -> t -> (a, b)
buildReturn (a, b) t = (a t, b t)

exitInfer :: FuncDefT (Inferred s) -> Inferrer s (FuncDefT Ast.Type)
exitInfer outDef = do
  inTs' <- mapM (convertBack $ exitError sr) inTs
  outTs' <- mapM (convertBack $ exitError sr) outTs
  body' <- exitStatement body
  return $ Ast.FuncDef inTs' outTs' restrs ins outs body' sr
  where
    Ast.FuncDef inTs outTs restrs ins outs body sr = outDef

exitStatement :: StatementT (Inferred s) -> Inferrer s (StatementT Ast.Type)
exitStatement (FuncCall s ins outs sr) =
  FuncCall s <$> mapM exitExpression ins <*> mapM exitExpression outs <*> return sr
exitStatement (Defer stmnt sr) =
  flip Defer sr <$> exitStatement stmnt
exitStatement (ShallowCopy exp1 exp2 sr) =
  ShallowCopy <$> exitExpression exp1 <*> exitExpression exp2 <*> return sr
exitStatement (If cond thenStmnt mElseStmnt sr) =
  If <$> exitExpression cond <*> exitStatement thenStmnt <*> elseStmnt' <*> return sr
  where elseStmnt' = maybe (return Nothing) (fmap Just . exitStatement) mElseStmnt
exitStatement (While cond stmnt sr) =
  While <$> exitExpression cond <*> exitStatement stmnt <*> return sr
exitStatement (Scope stmnts sr) =
  flip Scope sr <$> mapM exitStatement stmnts
exitStatement (Terminator t sr) = return $ Terminator t sr
exitStatement (VarInit m n t expr sr) =
  VarInit m n <$> convertBack (exitError sr) t <*> exitExpression expr <*> return sr

exitExpression :: ExpressionT (Inferred s) -> Inferrer s (ExpressionT Ast.Type)
exitExpression (Bin op exp1 exp2 sr) =
  Bin op <$> exitExpression exp1 <*> exitExpression exp2 <*> return sr
exitExpression (Un op expr sr) =
  Un op <$> exitExpression expr <*> return sr
exitExpression (MemberAccess expr prop sr) =
  MemberAccess <$> exitExpression expr <*> return prop <*> return sr
exitExpression (Subscript exp1 exp2 sr) =
  Subscript <$> exitExpression exp1 <*> exitExpression exp2 <*> return sr
exitExpression (Variable n sr) = return $ Variable n sr
exitExpression (ExprFunc n ins t sr) =
  ExprFunc n <$> mapM exitExpression ins <*> convertBack (exitError sr) t <*> return sr
exitExpression (ExprLit lit sr) =
  flip ExprLit sr <$> exitLiteral lit
exitExpression (Zero t) =
  Zero <$> convertBack errF t
  where errF m = ErrorString $ "Could not deduce type of zero initialization: " ++ show m

exitLiteral :: LiteralT (Inferred s) -> Inferrer s (LiteralT Ast.Type)
exitLiteral (ILit i t sr) =
  ILit i <$> convertBack (exitError sr) t <*> return sr
exitLiteral (FLit f t sr) =
  FLit f <$> convertBack (exitError sr) t <*> return sr
exitLiteral (BLit b sr) = return $ BLit b sr
exitLiteral (Null t sr) =
  Null <$> convertBack (exitError sr) t <*> return sr
exitLiteral (Undef t sr) =
  Undef <$> convertBack (exitError sr) t <*> return sr

exitError :: SourceRange -> UnifyErrorFunction
exitError sr m = ErrorString $ "Error at " ++ show sr ++ " when finishing type inference: " ++ show m

convertBack :: UnifyErrorFunction -> Inferred s -> Inferrer s Ast.Type
convertBack errF inferred = case inferred of
  Ref r -> readRef r >>= \tvar -> case tvar of
    b@(Unbound _ Changeable) -> do
      addError . errF $ "A changeable unbound type variable cannot remain after typechecking: " ++ show b
      return Ast.UnknownT
    Unbound _ (Unchangeable n) -> return $ Ast.NamedT n []
    Link inf -> convertBack errF inf
  NamedT n its -> Ast.NamedT n <$> mapM (convertBack errF) its
  PointerT it -> Ast.PointerT <$> convertBack errF it
  MemorychunkT it1 cap it2 -> Ast.Memorychunk <$> convertBack errF it1 <*> return cap <*> convertBack errF it2
  StructT ps -> Ast.StructT <$> mapM propConvert ps
    where propConvert (n, it) = (n, ) <$> convertBack errF it
  -- (FunctionT its ots, _) -> Ast.Function <$> mapM (convertBack errF) its <*> mapM (convertBack errF) its -- TODO: re-add when adding function types
  _ -> return $ case inferred of
    BoolT -> Ast.BoolT
    IntT s -> Ast.IntT s; UIntT s -> Ast.UIntT s; FloatT s -> Ast.FloatT s

unifyExternalFunction :: String -> [Inferred s] -> [Inferred s] -> SourceRange -> Inferrer s ()
unifyExternalFunction fName inTs outTs sr = do
  mFunc <- use $ functions . at fName
  case mFunc of
    Nothing -> addError . ErrorString $ "Unknown function " ++ fName ++ " at " ++ show sr
    Just (Ast.FuncDef funcInTs funcOutTs restrs _ _ _ _) -> do
      FunctionT funcInTs' funcOutTs' <- convertFuncSig restrs funcInTs funcOutTs Unbounds
      when (length funcInTs /= length inTs) . addError . ErrorString $ "Wrong number of in arguments at " ++ show sr
      when (length funcOutTs /= length outTs) . addError . ErrorString $ "Wrong number of out arguments at " ++ show sr
      unifyArguments "in" funcInTs' inTs
      unifyArguments "out" funcOutTs' outTs
  where
    errF inOut num m = ErrorString $ "Type mismatch in function " ++ inOut ++ " argument number " ++ show num ++  " at " ++ show sr ++ ": " ++ show m
    unifyArguments inOut ts' ts = sequence_ . getZipList $ unify <$> ZipList (errF inOut <$> [(1 :: Int)..]) <*> ZipList ts' <*> ZipList ts

-- FIXME: Beginning of code to check for impact of NamedT (The functions herein need to read through the name) {

unify :: UnifyErrorFunction -> Inferred s -> Inferred s -> Inferrer s (Inferred s)
unify errF t1 t2 = return t1 <* case (t1, t2) of
  _ | t1 == t2 -> return ()
  (Ref uncompressedR1, Ref uncompressedR2) -> do
    r1 <- readRef uncompressedR1 >>= linkCompression uncompressedR1
    r2 <- readRef uncompressedR2 >>= linkCompression uncompressedR2
    unless (r1 == r2) $ do
      pair <- (,) <$> readRef r1 <*> readRef r2
      case pair of
        (Unbound _ (Unchangeable n1), Unbound _ (Unchangeable n2)) -> addError . errF $ "Cannot unify differing typevariables " ++ n1 ++ " and " ++ n2
        (Unbound restr Changeable, Unbound _ _) -> applyRestriction errF (Ref r2) restr >> writeRef r1 (Link $ Ref r2)
        (Unbound _ _, Unbound restr Changeable) -> applyRestriction errF (Ref r1) restr >> writeRef r2 (Link $ Ref r1)
        (_, Link t) -> unifyRef t r1
        (Link t, _) -> unifyRef t r2
  (Ref r, t) -> readRef r >>= linkCompression r >>= unifyRef t
  (t, Ref r) -> readRef r >>= linkCompression r >>= unifyRef t
  (NamedT n1 t1s, NamedT n2 t2s) | n1 == n2 -> zipWithM_ (unify errF) t1s t2s
  -- (NamedT n ts, _) -> -- TODO: some form of instantiation of the NamedT and attempt to unify t2 with it. otherwise we can never write a literal of a named type
  -- (_, NamedT n ts) -> -- TODO: here as well
  (PointerT i1, PointerT i2) -> void $ unify errF i1 i2
  (MemorychunkT r11 c1 r12, MemorychunkT r21 c2 r22) | c1 == c2 -> do
    unify errF r11 r21
    void $ unify errF r12 r22
  (StructT p1, StructT p2) | p1names == p2names -> zipWithM_ (unify errF) p1types p2types
    where
      (p1names, p1types) = unzip p1
      (p2names, p2types) = unzip p2
  (FunctionT i1 o1, FunctionT i2 o2) | length i1 == length i2 && length o1 == length o2 -> do
    zipWithM_ (unify errF) i1 i2
    zipWithM_ (unify errF) o1 o2
  _ -> addError . errF $ "Incompatible types (" ++ show t1 ++ " != " ++ show t2 ++ ")"
  where
    linkCompression :: TVarRef s -> TVar s -> Inferrer s (TVarRef s)
    linkCompression uncompressedR (Link (Ref nextR)) = do
      r <- readRef nextR >>= linkCompression nextR
      writeRef uncompressedR . Link $ Ref r
      return r
    linkCompression r _ = return r
    unifyRef t r = readRef r >>= \tvar -> case tvar of
      Unbound _ (Unchangeable name) -> addError . errF $ "Unable to unify typevariable " ++ name ++ " with concrete type " ++ show t
      Unbound restr Changeable -> do
        applyRestriction errF t restr
        writeRef r $ Link t
      Link t' -> void $ unify errF t t'

restrict :: UnifyErrorFunction -> Restriction s -> Inferred s -> Inferrer s (Inferred s)
restrict errF restr inferred = return inferred <* applyRestriction errF inferred restr

applyRestriction :: UnifyErrorFunction -> Inferred s -> Restriction s -> Inferrer s ()
applyRestriction _ _ NoRestriction = return ()

applyRestriction errF t@(Ref r) restr = readRef r >>= \tvar -> case tvar of
  Link inf -> applyRestriction errF inf restr
  Unbound NoRestriction Changeable -> writeRef r $ Unbound restr Changeable
  Unbound restr' (Unchangeable _) | restr == restr' -> return ()
  u@(Unbound (NumR spec) changeable) -> case restr of
    NumR NoSpec -> return ()
    NumR spec' | spec == spec' -> return ()
    NumR spec' | spec == NoSpec -> if changeable == Changeable
      then writeRef r $ Unbound (NumR spec') Changeable
      else addError . errF $ "Could not apply restriction " ++ show restr ++ " on type " ++ show t ++ " (" ++ show u ++ ")"
    _ -> addError . errF $ "Could not apply restriction " ++ show restr ++ " on type " ++ show t ++ " (" ++ show u ++ ")"
  u@(Unbound (PropertiesR origPs) changeable) -> case restr of
    PropertiesR restrPs -> recurse origPs restrPs >>= when (changeable == Changeable) . writeRef r . (\ps -> Unbound (PropertiesR ps) changeable)
    _ -> addError . errF $ "Could not apply restriction " ++ show restr ++ " on type " ++ show t ++ " (" ++ show u ++ ")"
    where
      recurse allOrigs@(op@(opName, opR) : origTail) allRestrs@(rp@(rpName, rpR) : restrTail) -- NOTE: essentially a merge sort
        | opName == rpName = (:) <$> ((opName,) <$> unify errF opR rpR) <*> recurse origTail restrTail
        | opName < rpName = (op :) <$> recurse origTail allRestrs
        | opName > rpName = do
            unless (changeable == Changeable) . addError . errF $ "Cannot change unchangeable type value, we require " ++ show u ++ " to have a property " ++ rpName ++ " but it does not"
            (rp :) <$> recurse allOrigs restrTail
  u -> addError . errF $ "Could not apply restriction " ++ show restr ++ " on type " ++ show t ++ " (" ++ show u ++ ")"

applyRestriction _ (UIntT _) UIntR = return ()

applyRestriction _ (IntT _) (NumR spec)
  | spec == NoSpec = return ()
  | spec == IntSpec = return ()
applyRestriction _ (FloatT _) (NumR spec)
  | spec == NoSpec = return ()
  | spec == FloatSpec = return ()

applyRestriction errF t@(StructT origPs) (PropertiesR restrPs) = recurse origPs restrPs
  where
    recurse allOrigs@((opName, opR) : origTail) allRestrs@((rpName, rpR) : restrTail)
      | opName == rpName = unify errF opR rpR >> recurse origPs restrPs
      | opName < rpName = recurse origTail allRestrs
      | opName > rpName = do
          addError . errF $ "Unsatisfied property requirement: " ++ show t ++ " lacks property " ++ rpName
          recurse allOrigs restrTail

applyRestriction errF t restr = addError . errF $ "Could not apply restriction " ++ show restr ++ " on type " ++ show t

accessProperty :: UnifyErrorFunction -> String -> Inferred s -> Inferrer s (Inferred s)
accessProperty errF member inferred = case inferred of
  PointerT inf -> accessProperty errF member inf
  StructT ps -> case lookup member ps of
    Just prop -> return prop
    Nothing -> do
      addError . errF $ "Struct lacks a property with the name " ++ member
      newUnbound NoRestriction
  Ref r -> readRef r >>= \tvar -> case tvar of
    Link inf -> accessProperty errF member inf
    Unbound NoRestriction Changeable -> do
      innerInferred <- newUnbound NoRestriction
      writeRef r $ Unbound (PropertiesR [(member, innerInferred)]) Changeable
      return innerInferred
    Unbound (PropertiesR ps) _ -> case lookup member ps of
      Just prop -> return prop
      Nothing -> do
        innerInferred <- newUnbound NoRestriction
        applyRestriction errF inferred $ PropertiesR [(member, innerInferred)]
        return innerInferred
    u -> do
      addError . errF $ show u ++ " cannot have a property " ++ member
      newUnbound NoRestriction
  t -> do
    addError . errF $ "Type " ++ show t ++ " cannot have a property"
    newUnbound NoRestriction

makePointer :: UnifyErrorFunction -> Inferred s -> Inferrer s (Inferred s)
makePointer errF inferred = case inferred of
  PointerT innerTref -> return innerTref
  Ref r -> readRef r >>= \tvar -> case tvar of
    Link inf -> makePointer errF inf
    Unbound NoRestriction Changeable -> do
      innerInferred <- newUnbound NoRestriction
      writeRef r . Link $ PointerT innerInferred
      return innerInferred
    Unbound restr@(PropertiesR _) Changeable -> do
      innerInferred <- newUnbound restr
      writeRef r . Link $ PointerT innerInferred
      return innerInferred
    u -> do
      addError . errF $ show u ++ " cannot be a pointer"
      newUnbound NoRestriction
  t -> do
    addError . errF $ "Type " ++ show t ++ " does not unify with a pointer"
    newUnbound NoRestriction

makeBool :: UnifyErrorFunction -> Inferred s -> Inferrer s ()
makeBool errF inferred = case inferred of
  BoolT -> return ()
  Ref r -> readRef r >>= \tvar -> case tvar of
    Link inf -> makeBool errF inf
    Unbound NoRestriction Changeable -> void . writeRef r $ Link BoolT
    u -> addError . errF $ show u ++ " cannot be a bool"
  t -> addError . errF $ "Type " ++ show t ++ " does not unify with a bool"

-- FIXME: End of code to check for impact of NamedT }

convert :: Ast.Type -> Inferrer s (Inferred s)
convert t = case t of
  Ast.NamedT n@(c:_) [] | isLower c -> use (typeVariables . at n) >>= \mT -> case mT of
    Just tref -> return tref
    Nothing -> do
      addError . ErrorString $ "Unknown typevariable '" ++ n ++ "'" -- FIXME: This error will also occur in functions calling incorrectly specified functions, not very helpful
      newUnbound NoRestriction
  _ -> case t of
    Ast.NamedT n@(c:_) its | isUpper c -> NamedT n <$> mapM convert its -- FIXME: Check for correct number of its according to the typedef
    Ast.PointerT it -> PointerT <$> convert it
    Ast.Memorychunk indexT hasCap it -> MemorychunkT <$> convert indexT <*> return hasCap <*> convert it
    Ast.StructT props -> StructT <$> mapM propConvert props
    Ast.UnknownT -> newUnbound NoRestriction
    _ -> simpleConvert
  where
    propConvert (n, it) = (n, ) <$> convert it
    simpleConvert = return $ case t of
      Ast.IntT s -> IntT s
      Ast.UIntT s -> UIntT s
      Ast.FloatT s -> FloatT s
      Ast.BoolT -> BoolT

convertFuncSig :: [(String, Ast.Restriction)] -> [Ast.Type] -> [Ast.Type] -> TypeVarTarget -> Inferrer s (Inferred s)
convertFuncSig restrs inTs outTs target = do
  prevTypeVars <- typeVariables <<.= M.empty
  defineTypeVars
  inTs' <- mapM convert inTs
  outTs' <- mapM convert outTs

  forM_ restrs $ \(n, restr) -> use (typeVariables . at n) >>= \mT -> case mT of
    Nothing -> addError . ErrorString $ "(Incorrect funcsig) Restriction " ++ show restr ++ " applied on unknown type variable " ++ n
    Just tref -> convertRestriction restr >>= \restr' -> forceRestrict errF restr' tref
      where errF m = ErrorString $ "(Incorrect funcsig) Could not apply restriction " ++ show restr ++ " to type variable " ++ n ++ ". " ++ show m

  case target of
    Environment -> typeVariables %= M.union prevTypeVars
    Unbounds -> typeVariables .= prevTypeVars

  return $ FunctionT inTs' outTs'
  where
    forceRestrict errF restr inferred@(Ref r) = do
      oldChangeable <- setChangeable r Changeable
      applyRestriction errF inferred restr
      void $ setChangeable r oldChangeable
    setChangeable r c = do
      Unbound restr c' <- readRef r
      writeRef r $ Unbound restr c
      return c'
    defineTypeVars = mapM_ defineTypeVar typeVarNames
    defineTypeVar n = newTypeVar n target >>= (typeVariables . at n ?=)
    typeVarNames = S.toList . S.fromList $ [n | Ast.NamedT n@(c:_) [] <- inTs ++ outTs >>= universe, isLower c] ++ map fst restrs

convertRestriction :: Ast.Restriction -> Inferrer s (Restriction s)
convertRestriction NoRestriction = return NoRestriction
convertRestriction UIntR = return UIntR
convertRestriction (NumR s) = return $ NumR s
convertRestriction (PropertiesR ps) = PropertiesR <$> mapM propConvert ps
  where propConvert (n, p) = (n, ) <$> convert p

newUnbound :: Restriction s -> Inferrer s (Inferred s)
newUnbound restr = lift . fmap Ref . newSTRef $ Unbound restr Changeable

newTypeVar :: String -> TypeVarTarget -> Inferrer s (Inferred s)
newTypeVar n Environment = lift . fmap Ref . newSTRef $ Unbound NoRestriction (Unchangeable n)
newTypeVar _ Unbounds = lift . fmap Ref . newSTRef $ Unbound NoRestriction Changeable

writeRef :: TVarRef s -> TVar s -> Inferrer s ()
writeRef r = lift . writeSTRef r

readRef :: TVarRef s -> Inferrer s (TVar s)
readRef = lift . readSTRef

addError :: ErrorMessage -> Inferrer s ()
addError err = errors %= (err :)
