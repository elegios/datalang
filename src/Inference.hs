{-# LANGUAGE TupleSections, TypeSynonymInstances, FlexibleInstances #-}

module Inference (fullInfer, infer) where

import Ast hiding (Type(..), Restriction, FuncDef, Expression, Statement)
import Data.Functor ((<$>))
import Data.STRef
import Data.Tuple (swap)
import Data.Char (isLower, isUpper)
import Data.Generics.Uniplate.Data
import Control.Applicative ((<*>))
import Control.Monad.ST
import Control.Monad.State
import Control.Lens hiding (op, universe)
import qualified Ast
import qualified Data.Map as M
import qualified Data.Set as S

-- TODO: deal with named types, they are currently not correct

type UnifyError = String
type UnifyErrorFunction = UnifyError -> ErrorMessage

data Changeable = Changeable | Unchangeable String deriving Eq
data TypeVarTarget = Environment | Unbounds deriving Eq

data ErrorMessage = ErrorString String deriving Show
data InferrerState s = InferrerState
  { _errors :: [ErrorMessage]
  , _variables :: M.Map String (TypeRef s)
  , _typeVariables :: M.Map String (TypeRef s)
  , _functions :: M.Map String Ast.FuncDef
  }

-- TODO: support for typeclasses and similar stuff
data Inferred s = IntT TSize
                | UIntT TSize
                | FloatT TSize
                | BoolT
                | NamedT String [TypeRef s]
                | PointerT (TypeRef s)
                | MemorychunkT (TypeRef s) Bool (TypeRef s)
                | StructT [(String, TypeRef s)]
                | Unbound (Restriction s)
                | Link (TypeRef s)
                | FunctionT [TypeRef s] [TypeRef s]
                deriving (Eq, Show)
instance Show (TypeRef s) where
  show _ = "tref"

type Restriction s = RestrictionT (TypeRef s)

type Inferrer s a = StateT (InferrerState s) (ST s) a
type TypeRef s = STRef s (Inferred s, Changeable)

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

enterInfer :: FuncDefT Ast.Type -> Inferrer s (FuncDefT (TypeRef s))
enterInfer inDef = do
  ftref <- convertFuncSig restrs inTs outTs Environment
  FunctionT inTs' outTs' <- recursiveMakeUnchangeable ftref >>= readTypeRef
  zipWithM_ defineLocal (ins ++ outs) (inTs' ++ outTs')
  body' <- enterStatement body
  return $ Ast.FuncDef inTs' outTs' restrs ins outs body' sr
  where
    Ast.FuncDef inTs outTs restrs ins outs body sr = inDef
    defineLocal n t = variables . at n ?= t

enterStatement :: StatementT Ast.Type -> Inferrer s (StatementT (TypeRef s))
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

enterExpression :: ExpressionT Ast.Type -> Inferrer s (ExpressionT (TypeRef s), TypeRef s)
enterExpression (Bin op expr1 expr2 sr) = do
  (expr1', tref1) <- enterExpression expr1
  (expr2', tref2) <- enterExpression expr2
  unify unifyErr tref1 tref2
  (Bin op expr1' expr2' sr,) <$> case () of
    _ | op == Remainder -> restrict intErr (NumR IntSpec) tref1
    _ | op `elem` [Equal, NotEqual] -> newTypeRef BoolT
    _ | op `elem` [Plus, Minus, Times, Divide] -> restrict numErr (NumR NoSpec) tref1
    _ | op `elem` [BinAnd, BinOr, LShift, LogRShift, AriRShift, Xor] -> restrict uintErr UIntR tref1
    _ | op `elem` [Lesser, Greater, LE, GE] -> do
      restrict numErr (NumR NoSpec) tref1
      newTypeRef BoolT
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
  (expr', innerTref) <- enterExpression expr
  tref <- newTypeRef $ PointerT innerTref
  return . (, tref) $ Un AddressOf expr' sr

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
          newTypeRef (Unbound NoRestriction)

enterExpression (ExprFunc fName inExprs t sr) = do
  (inExprs', inTs) <- unzip <$> mapM enterExpression inExprs
  convertedT <- convert t
  unifyExternalFunction fName inTs [convertedT] sr
  return (ExprFunc fName inExprs' convertedT sr, convertedT)

enterExpression (ExprLit lit sr) = (_1 %~ flip ExprLit sr) <$> enterLiteral lit

enterExpression (Zero t) = buildReturn (Zero, id) <$> convert t

enterLiteral :: LiteralT Ast.Type -> Inferrer s (LiteralT (TypeRef s), TypeRef s)
enterLiteral (ILit n t sr) = buildReturn (\tref -> ILit n tref sr, id) <$> (convert t >>= restrict errF (NumR NoSpec))
  where errF m = ErrorString $ "How did you even get this error (int)? " ++ show sr ++ " -- "++ show m

enterLiteral (FLit n t sr) = buildReturn (\tref -> FLit n tref sr, id) <$> (convert t >>= restrict errF (NumR FloatSpec))
  where errF m = ErrorString $ "How did you even get this error (float)? " ++ show sr ++ " -- " ++ show m

enterLiteral (BLit v sr) = (BLit v sr, ) <$> newTypeRef BoolT

enterLiteral (Null Ast.UnknownT sr) = buildReturn (flip Null sr, id) <$> (newTypeRef (Unbound NoRestriction) >>= newTypeRef . PointerT)

exitInfer :: FuncDefT (TypeRef s) -> Inferrer s (FuncDefT Ast.Type)
exitInfer outDef = do
  inTs' <- mapM (convertBack $ exitError sr) inTs
  outTs' <- mapM (convertBack $ exitError sr) outTs
  body' <- exitStatement body
  return $ Ast.FuncDef inTs' outTs' restrs ins outs body' sr
  where
    Ast.FuncDef inTs outTs restrs ins outs body sr = outDef

exitStatement :: StatementT (TypeRef s) -> Inferrer s (StatementT Ast.Type)
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

exitExpression :: ExpressionT (TypeRef s) -> Inferrer s (ExpressionT Ast.Type)
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

exitLiteral :: LiteralT (TypeRef s) -> Inferrer s (LiteralT Ast.Type)
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

convertBack :: UnifyErrorFunction -> TypeRef s -> Inferrer s Ast.Type
convertBack errF tref = fullReadType tref >>= \t -> case t of
  (b@(Unbound _), Changeable) -> do
    addError . errF $ "A changeable unbound type variable cannot remain after typechecking: " ++ show b
    return Ast.UnknownT
  (Unbound _, Unchangeable n) -> return $ Ast.NamedT n []
  (NamedT n its, _) -> Ast.NamedT n <$> mapM (convertBack errF) its
  (PointerT it, _) -> Ast.PointerT <$> convertBack errF it
  (MemorychunkT it1 cap it2, _) -> Ast.Memorychunk <$> convertBack errF it1 <*> return cap <*> convertBack errF it2
  (StructT ps, _) -> Ast.StructT <$> mapM propConvert ps
    where propConvert (n, it) = (n, ) <$> convertBack errF it
  -- (FunctionT its ots, _) -> Ast.Function <$> mapM (convertBack errF) its <*> mapM (convertBack errF) its -- TODO: re-add when adding function types
  (it, _) -> return $ case it of
    BoolT -> Ast.BoolT
    IntT s -> Ast.IntT s; UIntT s -> Ast.UIntT s; FloatT s -> Ast.FloatT s

unifyExternalFunction :: String -> [TypeRef s] -> [TypeRef s] -> SourceRange -> Inferrer s ()
unifyExternalFunction fName inTs outTs sr = do
  mFunc <- use $ functions . at fName
  case mFunc of
    Nothing -> addError . ErrorString $ "Unknown function " ++ fName ++ " at " ++ show sr
    Just (Ast.FuncDef funcInTs funcOutTs restrs _ _ _ _) -> do
      FunctionT funcInTs' funcOutTs' <- convertFuncSig restrs funcInTs funcOutTs Unbounds >>= readTypeRef
      when (length funcInTs /= length inTs) . addError . ErrorString $ "Wrong number of in arguments at " ++ show sr
      when (length funcOutTs /= length outTs) . addError . ErrorString $ "Wrong number of out arguments at " ++ show sr
      zipWithM_ (unify errF) funcInTs' inTs
      zipWithM_ (unify errF) funcOutTs' outTs
  where
    errF m = ErrorString $ "Type mismatch in function argument at " ++ show sr ++ ": " ++ show m -- TODO: report which argument

unify :: UnifyErrorFunction -> TypeRef s -> TypeRef s -> Inferrer s (TypeRef s)
unify errF ref1 ref2 = do
  r1 <- bottomRef ref1
  r2 <- bottomRef ref2
  if r1 == r2 then return r1 else do
    (t1, r1c) <- fullReadType r1
    (t2, r2c) <- fullReadType r2
    case (r1c, r2c) of
      (Unchangeable _, Unchangeable _) | t1 /= t2 -> -- NOTE: Unchangeable types are constructed in such a way that equivalent types have the same references, thus this works
        addError . errF $ "Attempt to unify two unchangeable type values (" ++ show t1 ++ " and " ++ show t2 ++ ")"
      (Unchangeable _, Unchangeable _) -> return ()
      (u@(Unchangeable _), _) -> forceUnify errF u (r1, t1) (r2, t2)
      (_, u@(Unchangeable _)) -> forceUnify errF u (r2, t2) (r1, t1)
      _ -> forceUnify errF Changeable (r1, t1) (r2, t2)
    return r1

-- FIXME: Beginning of code to check for impact of NamedT (The functions herein need to read through the name) {

forceUnify :: UnifyErrorFunction -> Changeable -> (TypeRef s, Inferred s) -> (TypeRef s, Inferred s) -> Inferrer s ()
forceUnify errF firstChangeable (r1, t1) (r2, t2) =
  case (t1, t2) of
    (_, Unbound restr) -> do
      applyRestriction errF firstChangeable (r1, t1) restr
      writeTypeRef r2 (Link r1)
    (Unbound NoRestriction, t) | firstChangeable == Changeable -> writeTypeRef r1 t -- TODO: might need to throw error about unchangeable thing here
    (a, b) | a == b -> return ()
    (NamedT n1 t1s, NamedT n2 t2s) | n1 == n2 -> zipWithM_ (unify errF) t1s t2s
    -- (NamedT n ts, _) -> -- TODO: some form of instantiation of the NamedT and attempt to unify t2 with it. otherwise we can never write a literal of a named type
    -- (_, NamedT n ts) -> -- TODO: here as well
    (PointerT i1, PointerT i2) -> void $ unify errF i1 i2
    (MemorychunkT r11 c1 r12, MemorychunkT r21 c2 r22) | c1 == c2 -> do
      unify errF r11 r21
      void $ unify errF r12 r22
    (StructT p1, StructT p2) | p1names == p2names -> zipWithM_ (unify errF) p1types p2types
      where
        p1names = map fst p1
        p2names = map fst p2
        p1types = map snd p1
        p2types = map snd p2
    (FunctionT i1 o1, FunctionT i2 o2) | length i1 == length i2 && length o1 == length o2 -> do
      zipWithM_ (unify errF) i1 i2
      zipWithM_ (unify errF) o1 o2
    _ -> addError . errF $ "Incompatible types (" ++ show t1 ++ " != " ++ show t2 ++ ")"

restrict :: UnifyErrorFunction -> Restriction s -> TypeRef s -> Inferrer s (TypeRef s)
restrict errF restr ref = do
  (t, changeable) <- fullReadType ref
  applyRestriction errF changeable (ref, t) restr
  return ref

applyRestriction :: UnifyErrorFunction -> Changeable -> (TypeRef s, Inferred s) -> Restriction s -> Inferrer s ()
applyRestriction _ _ _ NoRestriction = return ()

applyRestriction errF changeable (r, Unbound NoRestriction) restr = if changeable == Changeable
  then writeTypeRef r $ Unbound restr
  else addError . errF $ "Cannot change unchangeable type value"

applyRestriction _ _ (_, UIntT _) UIntR = return ()

applyRestriction _ _ (_, IntT _) (NumR spec)
  | spec == NoSpec = return ()
  | spec == IntSpec = return ()
applyRestriction _ _ (_, FloatT _) (NumR spec)
  | spec == NoSpec = return ()
  | spec == FloatSpec = return ()
applyRestriction errF changeable (r, Unbound (NumR spec1)) (NumR spec2)
  | spec1 == spec2 = return ()
  | spec2 == NoSpec = return ()
  | spec1 == NoSpec = if changeable == Changeable
    then writeTypeRef r (Unbound (NumR spec2))
    else addError . errF $ "Cannot change unchangeable type value"

applyRestriction errF _ (_, t@(StructT origPs)) (PropertiesR restrPs) = recurse origPs restrPs
  where
    recurse allOrigs@((opName, opR) : origTail) allRestrs@((rpName, rpR) : restrTail)
      | opName == rpName = unify errF opR rpR >> recurse origPs restrPs
      | opName < rpName = recurse origTail allRestrs
      | opName > rpName = do
          addError . errF $ "Unsatisfied property requirement: " ++ show t ++ " lacks property " ++ rpName
          recurse allOrigs restrTail
applyRestriction errF changeable (r, Unbound (PropertiesR origPs)) (PropertiesR restrPs) =
  recurse origPs restrPs >>= when (changeable == Changeable) . writeTypeRef r . Unbound . PropertiesR
  where
    recurse allOrigs@(op@(opName, opR) : origTail) allRestrs@(rp@(rpName, rpR) : restrTail)
      | opName == rpName = (:) <$> ((opName,) <$> unify errF opR rpR) <*> recurse origPs restrPs
      | opName < rpName = (op :) <$> recurse origTail allRestrs
      | opName > rpName = do
          unless (changeable == Changeable) . addError . errF $ "Cannot change unchangeable type value"
          (rp :) <$> recurse allOrigs restrTail

applyRestriction errF _ (_, t) restr = addError . errF $ "Could not apply restriction " ++ show restr ++ " on type " ++ show t

accessProperty :: UnifyErrorFunction -> String -> TypeRef s -> Inferrer s (TypeRef s)
accessProperty errF member r = do
  res <- fullReadType r
  case res of
    (StructT ps, _) -> case lookup member ps of
      Just tref -> return tref
      Nothing -> do
        addError . errF $ "Struct lacks a property with the name " ++ member
        newTypeRef $ Unbound NoRestriction
    (_, Unchangeable _) -> do
      addError . errF $ "Attempt to access a property on an unchangeable non-property type"
      newTypeRef $ Unbound NoRestriction
    (Unbound NoRestriction, _) -> do
      innerTref <- newTypeRef $ Unbound NoRestriction
      writeTypeRef r (Unbound (PropertiesR [(member, innerTref)]))
      return innerTref
    (t, _) -> do
      addError . errF $ "Type " ++ show t ++ " cannot have a property"
      newTypeRef $ Unbound NoRestriction

makePointer :: UnifyErrorFunction -> TypeRef s -> Inferrer s (TypeRef s)
makePointer errF r = do
  res <- fullReadType r
  case res of
    (PointerT innerTref, _) -> return innerTref
    (_, Unchangeable _) -> do
      addError . errF $ "Attempt to make an unchangeable non-pointer type value into a pointer"
      newTypeRef (Unbound NoRestriction)
    (Unbound NoRestriction, _) -> do
      innerTref <- newTypeRef $ Unbound NoRestriction
      writeTypeRef r $ PointerT innerTref
      return innerTref
    (t, _) -> do
      addError . errF $ "Type " ++ show t ++ " does not unify with a pointer"
      newTypeRef $ Unbound NoRestriction

makeBool :: UnifyErrorFunction -> TypeRef s -> Inferrer s ()
makeBool errF r = do
  res <- fullReadType r
  case res of
    (BoolT, _) -> return ()
    (_, Unchangeable _) -> addError . errF $ "Attempt to make an unchangeable non-bool type value into a bool"
    (Unbound NoRestriction, _) -> writeTypeRef r BoolT
    (t, _) -> addError . errF $ "Type " ++ show t ++ " does not unify with a bool"

-- FIXME: End of code to check for impact of NamedT }

convert :: Ast.Type -> Inferrer s (TypeRef s)
convert t = case t of
  Ast.NamedT n@(c:_) [] | isLower c -> use (typeVariables . at n) >>= \mT -> case mT of
    Just tref -> return tref
    Nothing -> do
      addError . ErrorString $ "Unknown typevariable '" ++ n ++ "'" -- FIXME: This error will also occur in functions calling incorrectly specified functions, not very helpful
      newTypeRef $ Unbound NoRestriction
  _ -> newTypeRef =<< case t of
    Ast.NamedT n@(c:_) its | isUpper c -> NamedT n <$> mapM convert its -- FIXME: Check for correct number of its according to the typedef
    Ast.PointerT it -> PointerT <$> convert it
    Ast.Memorychunk indexT hasCap it -> MemorychunkT <$> convert indexT <*> return hasCap <*> convert it
    Ast.StructT props -> StructT <$> mapM propConvert props
    _ -> simpleConvert
  where
    propConvert (n, it) = (n, ) <$> convert it
    simpleConvert = return $ case t of
      Ast.IntT s -> IntT s
      Ast.UIntT s -> UIntT s
      Ast.FloatT s -> FloatT s
      Ast.BoolT -> BoolT
      Ast.UnknownT -> Unbound NoRestriction

convertFuncSig :: [(String, Ast.Restriction)] -> [Ast.Type] -> [Ast.Type] -> TypeVarTarget -> Inferrer s (TypeRef s)
convertFuncSig restrs inTs outTs target = do
  prevTypeVars <- typeVariables <<.= M.empty
  defineTypeVars
  inTs' <- mapM convert inTs
  outTs' <- mapM convert outTs

  forM_ restrs $ \(n, restr) -> use (typeVariables . at n) >>= \mT -> case mT of
    Nothing -> addError . ErrorString $ "(Incorrect funcsig) Restriction " ++ show restr ++ " applied on unknown type variable " ++ n
    Just tref -> void $ convertRestriction restr >>= \restr' -> forceRestrict errF restr' tref
      where errF m = ErrorString $ "(Incorrect funcsig) Could not apply restriction " ++ show restr ++ " to type variable " ++ n ++ ". " ++ show m

  case target of
    Environment -> typeVariables %= M.union prevTypeVars
    Unbounds -> typeVariables .= prevTypeVars

  newTypeRef (FunctionT inTs' outTs')
  where
    forceRestrict errF restr tref = do
      (t, _) <- fullReadType tref
      applyRestriction errF Changeable (tref, t) restr
      return tref
    defineTypeVars = mapM_ defineTypeVar typeVarNames
    defineTypeVar n = newTypeVar n target >>= (typeVariables . at n ?=)
    typeVarNames = S.toList . S.fromList $ [n | Ast.NamedT n@(c:_) [] <- inTs ++ outTs >>= universe, isLower c] ++ map fst restrs

convertRestriction :: Ast.Restriction -> Inferrer s (Restriction s)
convertRestriction NoRestriction = return NoRestriction
convertRestriction UIntR = return UIntR
convertRestriction (NumR s) = return $ NumR s
convertRestriction (PropertiesR ps) = PropertiesR <$> mapM propConvert ps
  where propConvert (n, p) = (n, ) <$> convert p

newTypeRef :: Inferred s -> Inferrer s (TypeRef s)
newTypeRef = lift . newSTRef . (, Changeable)

newTypeVar :: String -> TypeVarTarget -> Inferrer s (TypeRef s)
newTypeVar n Environment = lift . newSTRef $ (Unbound NoRestriction, Unchangeable n)
newTypeVar _ Unbounds = lift . newSTRef $ (Unbound NoRestriction, Changeable)

writeTypeRef :: TypeRef s -> Inferred s -> Inferrer s ()
writeTypeRef r t = lift $ modifySTRef r (_1 .~ t)

readTypeRef :: TypeRef s -> Inferrer s (Inferred s)
readTypeRef = fmap fst . fullReadType

fullReadType :: TypeRef s -> Inferrer s (Inferred s, Changeable)
fullReadType r = liftM snd $ lift (readSTRef r) >>= recurse [] r
  where
    recurse path ref (Link t, Changeable)
      | t `elem` path = do
          addError . ErrorString $ "Got a recursive type path, ouch: " ++ show path
          return (undefined, (Unbound NoRestriction, Changeable))
      | otherwise = do
          res@(newRef, _) <- lift (readSTRef t) >>= recurse (t : path) t
          lift $ writeSTRef ref (Link newRef, Changeable)
          return res
    recurse _ _ (Link _, Unchangeable _) = error "Should be impossible, an unchangeable type with a link"
    recurse _ ref res = return (ref, res)

bottomRef :: TypeRef s -> Inferrer s (TypeRef s)
bottomRef ref = lift (readSTRef ref) >>= recurse ref
  where
    recurse _ (Link r, Changeable) = lift (readSTRef r) >>= recurse r
    recurse r _ = return r

recursiveMakeUnchangeable :: TypeRef s -> Inferrer s (TypeRef s)
recursiveMakeUnchangeable ref = inner ref >> return ref
  where
    inner r = setUnchangeable r >> readTypeRef r >>= recurse
    setUnchangeable r = lift $ modifySTRef r change
    change t@(_, Unchangeable _) = t
    change (t, Changeable) = (t, Unchangeable "unnamed")
    recurse t = case t of
      NamedT _ rs -> mapM_ inner rs
      PointerT r -> inner r
      MemorychunkT ir _ cr -> inner ir >> inner cr
      StructT ps -> mapM_ (inner . snd) ps
      Unbound (PropertiesR ps) -> mapM_ (inner . snd) ps
      FunctionT inRs outRs -> mapM_ inner inRs >> mapM_ inner outRs
      _ -> return ()

addError :: ErrorMessage -> Inferrer s ()
addError err = errors %= (err :)

buildReturn :: (t -> a, t -> b) -> t -> (a, b)
buildReturn (a, b) t = (a t, b t)

-- Lenses

errors :: Functor f => ([ErrorMessage] -> f [ErrorMessage]) -> InferrerState s -> f (InferrerState s)
errors inj g = (\errs -> g { _errors = errs }) <$> inj (_errors g)
{-# INLINE errors #-}

variables :: Functor f => (M.Map String (TypeRef s) -> f (M.Map String (TypeRef s))) -> InferrerState s -> f (InferrerState s)
variables inj g = (\vars -> g { _variables = vars }) <$> inj (_variables g)
{-# INLINE variables #-}

typeVariables :: Functor f => (M.Map String (TypeRef s) -> f (M.Map String (TypeRef s))) -> InferrerState s -> f (InferrerState s)
typeVariables inj g = (\vars -> g { _typeVariables = vars }) <$> inj (_typeVariables g)
{-# INLINE typeVariables #-}

functions :: Functor f => (M.Map String Ast.FuncDef -> f (M.Map String Ast.FuncDef)) -> InferrerState s -> f (InferrerState s)
functions inj g = (\vars -> g { _functions = vars }) <$> inj (_functions g)
{-# INLINE functions #-}
