{-# LANGUAGE TupleSections, TypeSynonymInstances, FlexibleInstances, TemplateHaskell, MultiParamTypeClasses, FunctionalDependencies, LambdaCase, MultiWayIf #-}

module Inference (infer) where

import Ast (SourceRange(..), TSize(..), BinOp(..), UnOp(..), TerminatorType(..), NumSpec(..), location, Source)
import NameResolution (Resolved(..), ResolvedSource(..))
import Parser (HiddenIdentifiers)
import Data.Maybe (fromJust, isJust)
import Data.Functor ((<$>))
import Data.STRef
import Data.Generics.Uniplate.Direct
import Control.Applicative ((<*>), Applicative, (<*))
import Control.Monad.ST
import Control.Monad.State
import Control.Monad.Except (ExceptT, runExceptT, throwError, MonadError)
import Control.Lens hiding (op, universe, plate, index)
import qualified Parser as P
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.List as List
import qualified Data.Traversable as T

import Debug.Trace

-- AST types

type ICallableDef s = CallableDefT (Inferred s) (ICompoundAccess s)
type CallableDef = CallableDefT TypeKey CompoundAccess
data CallableDefT t a = FuncDef
                        { callableName :: String
                        , intypes :: [t]
                        , outtype :: t
                        , inargs :: [Resolved]
                        , outarg :: Resolved
                        , callableBody :: StatementT t a
                        , callableRange :: SourceRange
                        }
                      | ProcDef
                        { callableName :: String
                        , intypes :: [t]
                        , outtypes :: [t]
                        , inargs :: [Resolved]
                        , outargs :: [Resolved]
                        , callableBody :: StatementT t a
                        , callableRange :: SourceRange
                        }

type IStatement s = StatementT (Inferred s) (ICompoundAccess s)
type Statement = StatementT TypeKey CompoundAccess
data StatementT t a = ProcCall (ExpressionT t a) [ExpressionT t a] [ExpressionT t a] SourceRange
                    | Defer (StatementT t a) SourceRange
                    | ShallowCopy (ExpressionT t a) (ExpressionT t a) SourceRange
                    | If (ExpressionT t a) (StatementT t a) (Maybe (StatementT t a)) SourceRange
                    | While (ExpressionT t a) (StatementT t a) SourceRange
                    | Scope [StatementT t a] SourceRange
                    | Terminator TerminatorType SourceRange
                    | VarInit Bool Resolved t (ExpressionT t a) SourceRange

type IExpression s = ExpressionT (Inferred s) (ICompoundAccess s)
type Expression = ExpressionT TypeKey CompoundAccess
data ExpressionT t a = Bin BinOp (ExpressionT t a) (ExpressionT t a) SourceRange
                     | Un UnOp (ExpressionT t a) SourceRange
                     | CompoundAccess (ExpressionT t a) a SourceRange
                     | Variable Resolved t SourceRange
                     | FuncCall (ExpressionT t a) [ExpressionT t a] t SourceRange
                     | ExprLit (LiteralT t)
                     deriving Show

type IRepMap s = M.Map Resolved (IExpression s, Inferred s)
data IAccess s = IMember String | IBracket [Either String (IExpression s, Inferred s)] deriving Show

type ICompoundAccess s = STRef s (MaybeExpanded s)
data MaybeExpanded s = IUnExpanded (Inferred s) (IAccess s) (Inferred s)
                     | IExpanded (IRepMap s) (Maybe (IExpression s)) (IExpression s)
                     | IExpandedMember String
                     | IExpandedSubscript (IExpression s)
                     deriving Show

type RepMap = M.Map Resolved Expression
data CompoundAccess = Expanded RepMap (Maybe Expression) Expression
                    | ExpandedMember String
                    | ExpandedSubscript Expression

type ILiteral s = LiteralT (Inferred s)
type Literal = LiteralT TypeKey
data LiteralT t = ILit Integer t SourceRange
                | FLit Double t SourceRange
                | BLit Bool SourceRange
                | Null t SourceRange
                | Undef t SourceRange
                | Zero t SourceRange
                deriving Show

data IRestriction s = NoRestriction
                    | PropertiesR [ICompoundAccess s]
                    | UIntR
                    | NumR NumSpec
                    deriving (Show, Eq)

newtype TypeKey = TypeKey { representation :: Int } deriving (Eq, Ord, Show)

data FlatType = IntT TSize
              | UIntT TSize
              | FloatT TSize
              | BoolT
              | NamedT String [TypeKey]
              | TypeVar String
              | PointerT TypeKey
              | StructT [(String, TypeKey)]
              | FuncT [TypeKey] TypeKey
              | ProcT [TypeKey] [TypeKey]
              deriving (Show, Eq, Ord)

data Replacements s = Replacements
                     HiddenIdentifiers
                     (M.Map String (P.Replacement Resolved))
                     [([P.BracketTokenT Resolved], P.Replacement Resolved)]
data Inferred s = IInt TSize
                | IUInt TSize
                | IFloat TSize
                | IBool
                | INewType String [Inferred s] (Inferred s) (Replacements s)
                | IPointer (Inferred s)
                | IStruct [(String, Inferred s)]
                | IFunc [Inferred s] (Inferred s)
                | IProc [Inferred s] [Inferred s]
                | IRef (TVarRef s)
                deriving (Show, Eq, Ord)
data TVar s = Unbound (IRestriction s) | Link (Inferred s) deriving (Eq, Show)
data TVarRefT s a = TVarRef Int (STRef s a) deriving Eq
type TVarRef s = TVarRefT s (TVar s)

-- Inference types

data ErrorMessage = ErrorString String deriving Show

type ErrF = String -> ErrorMessage

class Enterable a s b | a s -> b where
  enter :: a -> Inferrer s b
class EnterableWithType a s b | a s -> b where
  enterT :: a -> Inferrer s (b, Inferred s)
class Finalizable a s b | a s -> b where
  exit :: a -> Finalizer s b

type Inferrer s a = StateT (InferrerState s) (ExceptT ErrorMessage (ST s)) a
type Finalizer s a = StateT (FinalizerState s) (ExceptT ErrorMessage (ST s)) a
type Super s a = StateT (SuperState s) (ST s) a

data InferrerState s = InferrerState
                       { _typeDefs :: M.Map String (P.TypeDefT Resolved)
                       , _callableDefs :: M.Map String (P.CallableDefT Resolved)
                       , _typeVars :: M.Map String (Inferred s)
                       , _locals :: M.Map Resolved (Inferred s)
                       , _enteredNames :: M.Map P.Type (Inferred s)
                       , _replacementContext :: Inferred s
                       , _requestedGlobals :: [(Resolved, Inferred s)]
                       , _refId :: Int
                       , _defineTypeVars :: Bool
                       , _toInferredMap :: M.Map TypeKey (Inferred s)
                       }
data FinalizerState s = FinalizerState
                        { _flatTypes :: M.Map TypeKey FlatType
                        , _typeKeys :: M.Map FlatType TypeKey
                        , _newTypes :: M.Map (String, [TypeKey]) TypeKey
                        , _nextTypeKey :: TypeKey
                        , _toInferred :: M.Map TypeKey (Inferred s)
                        }
data SuperState s = SuperState
                    { _done :: S.Set (IRequest s)
                    }

type IRequest s = RequestT TypeKey
type Request = RequestT P.Type
type RequestT t = (Resolved, t)

-- Basic instances

instance Source (CallableDefT t a) where
  location = callableRange

instance Show (ICompoundAccess s) where
  show _ = "compoundaccess"

instance Eq (Replacements s) where
  _ == _ = True
instance Ord (Replacements s) where
  compare _ _ = EQ

instance Show (TVarRefT s a) where
  show (TVarRef i _) = "tvarref" ++ show i
instance Ord (TVarRefT s a) where
  TVarRef i1 _ `compare` TVarRef i2 _ = i1 `compare` i2

instance Show (Replacements s) where
  show (Replacements hi ai ps) = "Replacements " ++ show hi ++ " " ++ show (M.keys ai) ++ " " ++ show (fst <$> ps)

makeLenses ''InferrerState
makeLenses ''FinalizerState
makeLenses ''SuperState

-- Big fat runner function

infer :: ResolvedSource -> [Request] -> [Either ErrorMessage (CallableDef, M.Map TypeKey FlatType)]
infer (ResolvedSource tDefs cDefs) requests = runST $ flip evalStateT initSuperState $
  runInferrer 0 M.empty (mapM convReq requests) >>= \case
    Left e -> return [Left e]
    Right (rs, st) -> runFinalizer initFinalizerState (mapM convReq' rs) >>= \case
      Left e -> return [Left e]
      Right (rs', finSt) -> inferRequest (_refId st) finSt ((:[]) <$> mapWith id rs')
  where
    convReq (n, t) = (n,) <$> enter t
    convReq' (n, t) = (n,) <$> convertType fullyReifiedError t
    fullyReifiedError m = ErrorString $ "All requested types must be fully reified: " ++ m
    initSuperState = SuperState
      { _done = S.empty
      }
    initFinalizerState = FinalizerState
      { _flatTypes = M.empty
      , _typeKeys = M.empty
      , _newTypes = M.empty
      , _nextTypeKey = TypeKey 0
      , _toInferred = M.empty
      }
    basicInferrerState = InferrerState
      { _typeDefs = tDefs
      , _callableDefs = cDefs
      , _typeVars = M.empty
      , _locals = M.empty
      , _enteredNames = M.empty
      , _replacementContext = error "Compiler error: not in a replacement context, yet tried to use one"
      , _requestedGlobals = []
      , _refId = 0
      , _defineTypeVars = False
      , _toInferredMap = M.empty
      }
    runInferrer rid infmap = lift . runExceptT . flip runStateT (basicInferrerState {_refId = rid, _toInferredMap = infmap})
    runFinalizer st = lift . runExceptT . flip runStateT st
    inferRequest :: Int -> FinalizerState s -> M.Map (IRequest s) [IRequest s] -> Super s [Either ErrorMessage (CallableDef, M.Map TypeKey FlatType)]
    inferRequest _ _ todo | M.null todo = return []
    inferRequest rid finSt todo = (done %= S.insert req) >> case trace ("requested " ++ show req) $ M.lookup fn cDefs of
      Nothing -> error $ "Compiler error: could not find callable " ++ fn
      Just def -> runInferrer rid infmap (enter t >>= enterDef def) >>= \case
        Left e -> (Left e:) <$> inferRequest rid finSt rest
        Right (def', st) -> runFinalizer finSt exiter >>= \case
          Left e -> (Left e:) <$> inferRequest rid finSt rest
          Right ((def'', reqs), finSt') -> do
            removeDone <- flip S.difference <$> use done
            let next = rest `M.union` ((:path) <$> mapWith id (S.toList nextList))
                nextList = removeDone $ S.fromList reqs
                rid' = _refId st
            (Right (def'', _flatTypes finSt'):) <$> inferRequest rid' finSt' next
          where
            exiter = (,) <$> exit def' <*> mapM (return `pairA` convertType undefined) (_requestedGlobals st)
      where
        ((req@(Global fn, t), path), rest) = M.deleteFindMin todo
        infmap = _toInferred finSt

-- Enter phase

enterDef :: P.CallableDefT Resolved -> Inferred s -> Inferrer s (ICallableDef s)
enterDef d@P.FuncDef{} t = withCallableType d $ do
  defineTypeVars .= True
  is <- mapM enter $ P.intypes d
  o <- enter $ P.outtype d
  defineTypeVars .= False
  unify errF t $ IFunc is o
  locals .= M.fromList (zip (P.outarg d : P.inargs d) (o : is))
  FuncDef (P.callableName d) is o
    <$> return (P.inargs d)
    <*> return (P.outarg d)
    <*> enter (P.callableBody d)
    <*> return (P.callableRange d)
  where errF m = ErrorString $ "Function at " ++ show (location d) ++ " called with the wrong type: " ++ m
enterDef d@P.ProcDef{} t = withCallableType d $ do
  defineTypeVars .= True
  is <- mapM enter $ P.intypes d
  os <- mapM enter $ P.outtypes d
  defineTypeVars .= False
  unify errF t $ IProc is os
  locals .= M.fromList (zip (P.inargs d ++ P.outargs d) (is ++ os))
  ProcDef (P.callableName d) is os
    <$> return (P.inargs d)
    <*> return (P.outargs d)
    <*> enter (P.callableBody d)
    <*> return (P.callableRange d)
  where errF m = ErrorString $ "Procedure at " ++ show (location d) ++ " called with the wrong type: " ++ m

instance Enterable TypeKey s (Inferred s) where
  enter tk = use (toInferredMap . at tk) >>= justErr err
    where err = ErrorString $ "Compiler error: could not find typekey " ++ show tk

instance Enterable P.Type s (Inferred s) where
  enter (P.IntT s _) = return $ IInt s
  enter (P.UIntT s _) = return $ IUInt s
  enter (P.FloatT s _) = return $ IFloat s
  enter (P.BoolT _) = return IBool
  enter nt@(P.NamedT n _ sr) = use (enteredNames . at nt) >>= maybe construct return
    where
      construct = do
        IRef r <- newUnbound NoRestriction
        enteredNames . at nt ?= IRef r
        t <- use (typeDefs . at n) >>= \case -- TODO: move unknown to nameresolution
          Nothing -> throwError . ErrorString $ "Unknown type name " ++ n ++ " at " ++ show sr
          Just P.Alias{ P.typeParams = ps
                      , P.wrappedType = w } ->
            snd <$> withTypeVars nt ps (enter w)
          Just P.NewType{ P.typeParams = ps
                        , P.hiddenIdentifiers = hi
                        , P.introducedIdentifiers = ai
                        , P.bracketPatterns = bp
                        , P.wrappedType = w } -> do
            (ts', w') <- withTypeVars nt ps $ enter w
            return . INewType n ts' w' $ Replacements hi (M.fromList ai) bp
        writeRef r $ Link t
        return t
  enter (P.TypeVar n r) = use (typeVars . at n) >>= \case
    Just t -> return t
    Nothing -> use defineTypeVars >>= \case
      True -> newUnbound NoRestriction >>= (typeVars . at n <?=)
      False -> throwError . ErrorString $ "Unknown type variable " ++ n ++ " at " ++ show r
  enter (P.PointerT t _) = IPointer <$> enter t
  enter (P.StructT ps _) = IStruct <$> mapM (return `pairA` enter) ps
  enter (P.ProcT is os _) = IProc <$> mapM enter is <*> mapM enter os
  enter (P.FuncT is o _) = IFunc <$> mapM enter is <*> enter o

instance Enterable (P.StatementT Resolved) s (IStatement s) where
  enter (P.ProcCall p is os r) = do
    (p', t) <- enterT p
    (is', its) <- unzip <$> mapM enterT is
    (os', ots) <- unzip <$> mapM enterT os
    unify errF t $ IProc its ots
    return $ ProcCall p' is' os' r
    where errF m = ErrorString $ show r ++ ": " ++ m
  enter (P.Defer s r) = Defer <$> enter s <*> return r
  enter (P.ShallowCopy var e r) = do
    (var', varT) <- enterT var
    (e', et) <- enterT e
    unify errF varT et
    return $ ShallowCopy var' e' r
    where errF m = ErrorString $ "Assignment at " ++ show r ++ ": " ++ m
  enter (P.If c t me r) = do
    (c', ct) <- enterT c
    unify errF ct IBool
    If c' <$> enter t <*> T.mapM enter me <*> return r
    where errF m = ErrorString $ "Condition in if at " ++ show r ++ " must be bool: " ++ m
  enter (P.While c s r) = do
    (c', ct) <- enterT c
    unify errF ct IBool
    While c' <$> enter s <*> return r
    where errF m = ErrorString $ "Condition in while at " ++ show r ++ " must be bool: " ++ m
  enter (P.Scope s r) = do
    prevLocals <- use locals
    Scope <$> mapM enter s <*> return r <* (locals .= prevLocals)
  enter (P.Terminator t r) = return $ Terminator t r
  enter (P.VarInit mut n mt me r) = do -- TODO: deal with mutability at type level?
    (e', t') <- T.mapM enterT me >>= \case
      Just (e, et) -> T.mapM (enter >=> unify errF et) mt >> return (e, et)
      Nothing -> do
        u <- newUnbound NoRestriction
        t' <- justErr internal mt >>= enter
        unify errF u t'
        return (ExprLit $ Zero u r, t')
    locals . at n ?= t'
    return $ VarInit mut n t' e' r
    where
      errF m = ErrorString $ "Type mismatch in let at " ++ show r ++ ": " ++ m
      internal = ErrorString $ "Compiler error: neither type nor expr at " ++ show r

instance Enterable (P.ExpressionT Resolved) s (IExpression s) where
  enter = fmap fst . enterT
instance EnterableWithType (P.ExpressionT Resolved) s (IExpression s) where
  enterT (P.Bin o e1 e2 r) = do
    (e1', e1t) <- enterT e1
    (e2', e2t) <- enterT e2
    unify unifyErr e1t e2t
    (Bin o e1' e2' r,) <$>
      if | o == Remainder -> restrict intErr e1t $ NumR IntSpec
         | o `elem` [Equal, NotEqual] -> return IBool
         | o `elem` [Plus, Minus, Times, Divide] -> restrict numErr e1t $ NumR NoSpec
         | o `elem` [BinAnd, BinOr, LShift, LogRShift, AriRShift, Xor] -> restrict uintErr e1t UIntR
         | o `elem` [Lesser, Greater, LE, GE] -> restrict numErr e1t (NumR NoSpec) >> return IBool
    where
      unifyErr m = ErrorString $ "Could not unify expression types around " ++ show o ++ " at " ++ show r ++ ". " ++ m
      numErr m = ErrorString $ "Expressions at " ++ show r ++ " must have a numerical type. " ++ m
      uintErr m = ErrorString $ "Expressions at " ++ show r ++ " must have a uint type. " ++ m
      intErr m = ErrorString $ "Expressions at " ++ show r ++ " must have an int type. " ++ m
  enterT (P.Un o e r) = do
    (e', t) <- enterT e
    (Un o e' r,) <$> case o of
      Deref -> derefPtr ptrErr t
      AddressOf -> return $ IPointer t
      AriNegate -> restrict numErr t $ NumR NoSpec
      BinNegate -> restrict uintErr t UIntR
      Not -> unify boolErr t IBool >> return IBool
    where
      ptrErr = mustBeA "pointer"
      numErr = mustBeA "number"
      uintErr = mustBeA "uint"
      boolErr = mustBeA "bool"
      mustBeA t m = ErrorString $ "Expression at " ++ show (location e) ++ " must be a " ++ t ++ ": " ++ m
  enterT (P.MemberAccess e prop r) = do
    (e', t) <- enterT e
    (a, it) <- newICompound errF t $ IMember prop
    return (CompoundAccess e' a r, it)
    where errF m = ErrorString $ "Expression at " ++ show (location e) ++ " must have a property " ++ prop ++ ": " ++ m
  enterT (P.Subscript e bp r) = do
    (e', t) <- enterT e
    (a, it) <- mapM (T.mapM enterT) bp >>= newICompound errF t . IBracket
    return (CompoundAccess e' a r, it)
    where errF m = ErrorString $ "Expression at " ++ show (location e) ++ " does not support the []-expression at " ++ show r ++ ": " ++ m
  enterT (P.Variable n r) = case n of
    Self -> use replacementContext >>= \t -> return (Variable n t r, t)
    ReplacementLocal True prop -> do
      t <- use replacementContext
      (a, it) <- newICompound locErr t $ IMember prop
      return (CompoundAccess (Variable Self t r) a r, it)
    Global g -> use (callableDefs . at g) >>= \case
      Nothing -> throwError . ErrorString $ "Compiler error: unknown global " ++ g ++ " at " ++ show r
      Just def -> do
        t <- createCallableType def
        requestedGlobals %= ((n,t):)
        return (Variable n t r, t)
    _ -> use (locals . at n) >>= justErr resErr >>= \t -> return (Variable n t r, t)
    where
      locErr m = ErrorString $ "Compiler error: unsupported replacementlocal: " ++ m
      resErr = ErrorString $ "Compiler error: var " ++ show n ++ " at " ++ show r ++ " not found"
  enterT (P.FuncCall f is r) = do
    (f', t) <- enterT f
    (is', its) <- unzip <$> mapM enterT is
    ret <- getFuncReturn errF t its
    return (FuncCall f' is' ret r, ret)
    where errF m = ErrorString $ "Expression at " ++ show (location f) ++ " must be a func: " ++ m
  enterT (P.ExprLit l) = (_1 %~ ExprLit) <$> enterT l
  enterT (P.TypeAssertion e t r) = do
    (e', et) <- enterT e
    enter t >>= unify errF et
    return (e', et)
    where errF m = ErrorString $ "Failed type assertion at " ++ show r ++ ": " ++ m

instance EnterableWithType P.Literal s (ILiteral s) where
  enterT (P.ILit i r) = litF (ILit i) r $ NumR NoSpec -- BUG: no uint literals
  enterT (P.FLit f r) = litF (FLit f) r $ NumR FloatSpec
  enterT (P.BLit b r) = return (BLit b r, IBool)
  enterT (P.Null r) = do
    u <- newUnbound NoRestriction
    return (Null (IPointer u) r, IPointer u)
  enterT (P.Undef r) = litF Undef r NoRestriction

litF :: (Inferred s -> SourceRange -> ILiteral s) -> SourceRange -> IRestriction s -> Inferrer s (ILiteral s, Inferred s)
litF constr r restr = newUnbound restr >>= (\t -> return (constr t r, t))

-- Enter library functions

newICompound :: ErrF -> Inferred s -> IAccess s -> Inferrer s (ICompoundAccess s, Inferred s)
newICompound errF t a = do
  u <- newUnbound NoRestriction
  ca <- lift . lift $ newSTRef (IUnExpanded t a u)
  restrict errF t $ PropertiesR [ca]
  return (ca, u)

createCallableType :: P.CallableDefT v -> Inferrer s (Inferred s)
createCallableType d@P.FuncDef{P.intypes = its, P.outtype = ot} =
  withCallableType d $ IFunc <$> mapM enter its <*> enter ot

createCallableType d@P.ProcDef{P.intypes = its, P.outtypes = ots} =
  withCallableType d $ IProc <$> mapM enter its <*> mapM enter ots

withCallableType :: P.CallableDefT v -> Inferrer s a -> Inferrer s a
withCallableType d m = do
  newTypeVars <- M.fromList <$> mapM makeVar typevars
  prevTypeVars <- typeVars <<%= M.union newTypeVars
  m <* (typeVars .= prevTypeVars)
  where
    makeVar n = (n,) <$> newUnbound NoRestriction
    typevars = [n | P.TypeVar n _ <- universeBi ts]
    ts = case d of
      P.FuncDef{P.intypes = its, P.outtype = ot} -> ot : its
      P.ProcDef{P.intypes = its, P.outtypes = ots} -> its ++ ots

withTypeVars :: P.Type -> [String] -> Inferrer s a -> Inferrer s ([Inferred s], a)
withTypeVars (P.NamedT n ts r) ps i = do
  when (length ps /= length ts) $ do
    let errS = "Incorrect usage of named type " ++ n ++ " at " ++ show r ++ ": " ++
               "wrong number of type arguments, got " ++ show (length ts) ++ ", wanted"
               ++ show (length ps)
    throwError $ ErrorString errS
  ts' <- mapM enter ts
  prevTypeVars <- typeVars <<%= M.union (M.fromList $ zip ps ts')
  a <- i
  typeVars .= prevTypeVars
  return (ts', a)
withTypeVars t _ _ = error $ "(Compiler error): Incorrect usage of withTypeVars, " ++ show t ++ " should be a NamedT"

newUnbound :: IRestriction s -> Inferrer s (Inferred s)
newUnbound restr =
  IRef <$> (TVarRef <$> (refId <<+= 1) <*> (lift . lift . newSTRef $ Unbound restr))

getFuncReturn :: ErrF -> Inferred s -> [Inferred s] -> Inferrer s (Inferred s)
getFuncReturn errF (IFunc is ret) newIs
  | length is == length newIs = zipWithM_ (unify errF) is newIs >> return ret
  | otherwise = throwError . errF $ "Got an incorrect number of arguments, got " ++
                show (length newIs) ++ ", wanted " ++ show (length is)
getFuncReturn errF (IRef r) is = readRef r >>= \case
  Unbound NoRestriction -> do
    u <- newUnbound NoRestriction
    writeRef r . Link $ IFunc is u
    return u
  Link t -> getFuncReturn errF t is
  u -> throwError . errF $ "Cannot change " ++ show u ++ " into a func"
getFuncReturn errF u _ = throwError . errF $ show u ++ " cannot be a func"

derefPtr :: ErrF -> Inferred s -> Inferrer s (Inferred s)
derefPtr _ (IPointer t) = return t
derefPtr errF (IRef r) = readRef r >>= \case
  Unbound NoRestriction -> do
    u <- newUnbound NoRestriction
    writeRef r . Link $ IPointer u
    return u
  Link t -> derefPtr errF t
  u -> throwError . errF $ show u ++ " cannot be a pointer"

unify :: ErrF -> Inferred s -> Inferred s -> Inferrer s ()
unify errF t1 t2 = unless (t1 == t2) $ case (t1, t2) of
  (IRef uncompressedR1, IRef uncompressedR2) -> do
    r1 <- readRef uncompressedR1 >>= linkCompression uncompressedR1
    r2 <- readRef uncompressedR2 >>= linkCompression uncompressedR2
    unless (r1 == r2) $ (,) <$> readRef r1 <*> readRef r2 >>= \case
      (Unbound restr, Unbound _) ->
        writeRef r1 (Link $ IRef r2) >> applyRestriction errF (IRef r2) restr
      (_, Link t) -> unifyRef t r1
      (Link t, _) -> unifyRef t r2
  (IRef r, t) -> readRef r >>= linkCompression r >>= unifyRef t
  (t, IRef r) -> readRef r >>= linkCompression r >>= unifyRef t
  (INewType n1 t1s _ _, INewType n2 t2s _ _) | n1 == n2 -> zipWithM_ uni t1s t2s
  (IPointer i1, IPointer i2) -> uni i1 i2
  (IStruct p1, IStruct p2) | p1names == p2names -> zipWithM_ uni p1ts p2ts
    where
      (p1names, p1ts) = unzip p1
      (p2names, p2ts) = unzip p2
  (IProc i1 o1, IProc i2 o2) | length i1 == length i2 && length o1 == length o2 -> do
    zipWithM_ uni i1 i2
    zipWithM_ uni o1 o2
  (IFunc i1 o1, IFunc i2 o2) | length i1 == length i2 -> do
    zipWithM_ uni i1 i2
    uni o1 o2
  _ -> throwError . errF $ "Incompatible types (" ++ show t1 ++ " != " ++ show t2 ++ ")"
  where
    uni = unify errF
    linkCompression :: TVarRef s -> TVar s -> Inferrer s (TVarRef s)
    linkCompression uncompressedR (Link (IRef nextR)) = do
      r <- readRef nextR >>= linkCompression nextR
      writeRef uncompressedR . Link $ IRef r
      return r
    linkCompression r _ = return r
    unifyRef t r = readRef r >>= \case
      Unbound restr -> writeRef r (Link t) >> applyRestriction errF t restr
      Link t' -> uni t t'

restrict :: ErrF -> Inferred s -> IRestriction s -> Inferrer s (Inferred s)
restrict errF t restr = applyRestriction errF t restr >> return t

applyRestriction :: ErrF -> Inferred s -> IRestriction s -> Inferrer s ()

applyRestriction _ _ NoRestriction = return ()

applyRestriction errF INewType{} (PropertiesR expands) =
  mapM_ (attemptCompoundExpand errF) expands

applyRestriction errF t@(IRef r) restr = readRef r >>= \case
  Link i -> applyRestriction errF i restr
  Unbound restr' | restr == restr' -> return ()
  Unbound NoRestriction -> writeRef r $ Unbound restr
  u@(Unbound (NumR spec)) -> case restr of
    NumR NoSpec -> return ()
    NumR spec' | spec == spec' -> return ()
    NumR _ | spec == NoSpec -> writeRef r $ Unbound restr
    _ -> throwError . errF $ "Could not apply restriction " ++ show restr ++ " on type " ++ show t ++ " (" ++ show u ++ ")"
  u@(Unbound (PropertiesR origExpands)) -> case restr of
    PropertiesR restrExpands ->
      writeRef r . Unbound . PropertiesR . List.nub $ origExpands ++ restrExpands
    _ -> throwError . errF $ "Could not apply restriction " ++ show restr ++ " on type " ++ show t ++ " (" ++ show u ++ ")"
  u -> throwError . errF $ "Could not apply restriction " ++ show restr ++ " on type " ++ show t ++ " (" ++ show u ++ ")"

applyRestriction _ IUInt{} UIntR = return ()

applyRestriction _ IInt{} (NumR spec)
  | spec `elem` [NoSpec, IntSpec] = return ()
applyRestriction _ IFloat{} (NumR spec)
  | spec `elem` [NoSpec, FloatSpec] = return ()

applyRestriction errF IPointer{} (PropertiesR expands) =
  mapM_ (attemptCompoundExpand errF) expands

applyRestriction errF IStruct{} (PropertiesR expands) =
  mapM_ (attemptCompoundExpand errF) expands

applyRestriction errF t restr = throwError . errF $ "Could not apply restriction " ++ show restr ++ " on type " ++ show t

attemptCompoundExpand :: ErrF -> ICompoundAccess s -> Inferrer s ()
attemptCompoundExpand errF r = readRef r >>= \case
  IUnExpanded t (IMember m) retty -> memberAccess t
    where
      memberAccess = readTillNonPointer >=> \case
        Nothing -> return ()
        Just (IStruct ps) | isJust mT -> do
          unify errF retty $ fromJust mT
          writeRef r $ IExpandedMember m
          where mT = List.lookup m ps
        Just u@(INewType _ _ w (Replacements hi ai _)) -> case M.lookup m ai of
          Nothing -> case hi of
            P.HideSome hidden | m `notElem` hidden -> memberAccess w
            _ -> throwError . errF $ show u ++ " has no member " ++ m
          Just rep -> do
            prevReplacementContext <- replacementContext <<.= w
            expand retty rep M.empty
            replacementContext .= prevReplacementContext
        Just u -> throwError . errF $ show u ++ " has no member " ++ m
  IUnExpanded t (IBracket bp) retty ->
    readTillType t >>= \case
      Nothing -> return ()
      Just (IPointer it) -> case bp of
        [Right (e, intT)] -> do
          restrict errF intT (NumR IntSpec)
          unify errF retty it
          writeRef r $ IExpandedSubscript e
        _ -> throwError . errF $ "A pointer only supports [int]"
      Just u@(INewType _ _ w (Replacements _ _ ntbp)) -> do
        useMatch <- justErr err . msum $ match <$> ntbp
        prevReplacementContext <- replacementContext <<.= w
        useMatch
        replacementContext .= prevReplacementContext
        where
          match (pattern, rep) = (>>= expand retty rep) <$> inner pattern bp
          inner [] [] = Just $ return M.empty
          inner (P.BrId n _ : pTail) (Right rep : bpTail) =
            (M.insert n rep <$>) <$> inner pTail bpTail
          inner (P.BrId n (Just rep) : pTail) bpTail =
            (M.insert n <$> enterT rep <*>) <$> inner pTail bpTail
          inner (P.BrOp o : pTail) (Left o' : bpTail)
            | o == o' = inner pTail bpTail
          inner _ _ = Nothing
          err = errF $ show u ++ " has no []-expression matching " ++ show bp
      Just u -> throwError . ErrorString $ show u ++ " has no []-expression matching " ++ show bp
  u -> trace ("double expand of " ++ show u) $ return () -- NOTE: already expanded
  where
    expand retty (me, e) irepmap = do
      prevLocals <- locals <<%= M.union (snd <$> irepmap)
      me' <- T.mapM (enterT >=> \(e', et) -> unify errF IBool et >> return e') me
      (e', t) <- enterT e
      unify errF retty t
      writeRef r $ IExpanded irepmap me' e'
      locals .= prevLocals
    readTillType (IRef tref) = readRef tref >>= \case
      Link t -> readTillType t
      _ -> return Nothing
    readTillType t = return $ Just t
    readTillNonPointer (IRef tref) = readRef tref >>= \case
      Link t -> readTillNonPointer t
      _ -> return Nothing
    readTillNonPointer (IPointer t) = readTillNonPointer t
    readTillNonPointer t = return $ Just t

-- Finalizer phase

convertType :: ErrF -> Inferred s -> Finalizer s TypeKey
convertType errF = inner
  where
    create inf ft = use (typeKeys . at ft) >>= \case
      Just tk -> return tk
      Nothing -> do
        tk <- newTypeKey
        toInferred . at tk ?= inf
        flatTypes . at tk ?= ft
        typeKeys . at ft <?= tk
    inner :: Inferred s -> Finalizer s TypeKey
    inner i@(IInt s) = create i $ IntT s
    inner i@(IUInt s) = create i $ UIntT s
    inner i@(IFloat s) = create i $ FloatT s
    inner i@IBool = create i BoolT
    inner (INewType n ts w _) = do
      ntKey <- (n,) <$> mapM inner ts
      use (newTypes . at ntKey) >>= \case
        Just tk -> return tk
        Nothing -> do
          tk <- newTypeKey >>= (newTypes . at ntKey <?=)
          wtk <- inner w
          ft <- fromJust <$> use (flatTypes . at wtk)
          flatTypes . at tk ?= ft
          return tk
    inner i@(IPointer it) = inner it >>= create i . PointerT
    inner i@(IStruct ps) = mapM (return `pairA` inner) ps >>= create i . StructT
    inner i@(IFunc is o) = (FuncT <$> mapM inner is <*> inner o) >>= create i
    inner i@(IProc is os) = (ProcT <$> mapM inner is <*> mapM inner os) >>= create i
    inner (IRef r) = readBottom r >>= \case
      Unbound{} -> throwError . errF $ "Found an unbound type"
      Link it -> inner it
      where
        readBottom ref = readRef ref >>= \case
          Link (IRef ref') -> readBottom ref'
          b -> return b

newTypeKey :: Finalizer s TypeKey
newTypeKey = nextTypeKey <<%= TypeKey . (+1) . representation

instance Finalizable (ICallableDef s) s CallableDef where
  exit d@FuncDef{} = FuncDef (callableName d)
                 <$> mapM (convertType . exErr $ location d) (intypes d)
                 <*> convertType (exErr $ location d) (outtype d)
                 <*> return (inargs d)
                 <*> return (outarg d)
                 <*> exit (callableBody d)
                 <*> return (location d)
  exit d@ProcDef{} = ProcDef (callableName d)
                 <$> mapM (convertType . exErr $ location d) (intypes d)
                 <*> mapM (convertType . exErr $ location d) (outtypes d)
                 <*> return (inargs d)
                 <*> return (outargs d)
                 <*> exit (callableBody d)
                 <*> return (location d)

instance Finalizable (IStatement s) s Statement where
  exit (ProcCall p is os r) =
    ProcCall <$> exit p <*> mapM exit is <*> mapM exit os <*> return r
  exit (Defer s r) = Defer <$> exit s <*> return r
  exit (ShallowCopy a e r) = ShallowCopy <$> exit a <*> exit e <*> return r
  exit (If c t me r) = If <$> exit c <*> exit t <*> T.mapM exit me <*> return r
  exit (While c s r) = While <$> exit c <*> exit s <*> return r
  exit (Scope stmnts r) = Scope <$> mapM exit stmnts <*> return r
  exit (Terminator t r) = return $ Terminator t r
  exit (VarInit mut n t e r) =
    VarInit mut n <$> convertType (exErr r) t <*> exit e <*> return r

instance Finalizable (IExpression s) s Expression where
  exit (Bin o e1 e2 r) = Bin o <$> exit e1 <*> exit e2 <*> return r
  exit (Un o e r) = Un o <$> exit e <*> return r
  exit (CompoundAccess e a r) =
    CompoundAccess <$> exit e <*> (readRef a >>= access) <*> return r
    where
      access = \case
        IUnExpanded{} -> throwError . ErrorString $ "Compiler error: unexpanded compound at " ++ show r
        IExpanded repmap cond rep ->
          Expanded <$> T.mapM (exit . fst) repmap <*> T.mapM exit cond <*> exit rep
        IExpandedMember m -> return $ ExpandedMember m
        IExpandedSubscript index -> ExpandedSubscript <$> exit index
  exit (Variable n t r) = Variable n <$> convertType (exErr r) t <*> return r
  exit (FuncCall f as ret r) =
    FuncCall <$> exit f <*> mapM exit as <*> convertType (exErr r) ret <*> return r
  exit (ExprLit l) = ExprLit <$> exit l

instance Finalizable (ILiteral s) s Literal where
  exit (ILit i t r) = ILit i <$> convertType (exErr r) t <*> return r
  exit (FLit d t r) = FLit d <$> convertType (exErr r) t <*> return r
  exit (BLit b r) = return $ BLit b r
  exit (Null t r) = Null <$> convertType (exErr r) t <*> return r
  exit (Undef t r) = Undef <$> convertType (exErr r) t <*> return r
  exit (Zero t r) = Zero <$> convertType (exErr r) t <*> return r

exErr :: SourceRange -> ErrF
exErr r m = ErrorString $ "Error at " ++ show r ++ ": " ++ m

-- Somewhat general functions

pairA :: Applicative f => (a -> f c) -> (b -> f d) -> (a, b) -> f (c, d)
pairA af bf (a, b) = (,) <$> af a <*> bf b

justErr :: MonadError e m => e -> Maybe a -> m a
justErr _ (Just a) = return a
justErr err Nothing = throwError err

mapWith :: Ord k => (a -> k) -> [a] -> M.Map k a
mapWith f = M.fromList . map (\a -> (f a, a))

class Ref r where
  readRef :: (MonadTrans m1, Monad (m1 (ST s)), MonadTrans m2) => r s a -> m2 (m1 (ST s)) a
  writeRef :: (MonadTrans m1, Monad (m1 (ST s)), MonadTrans m2) => r s a -> a -> m2 (m1 (ST s)) ()

instance Ref TVarRefT where
  readRef (TVarRef _ r) = lift . lift $ readSTRef r
  writeRef (TVarRef _ r) = lift . lift . writeSTRef r
instance Ref STRef where
  readRef = lift . lift . readSTRef
  writeRef r = lift . lift . writeSTRef r

{-
Three stage inference:
1. enter: convert to Inferred, ICompoundAccess and InferredSource, store unexpanded newtype replacements
2. expand: try to iteratively expand all unexpanded newtype replacements until fixpoint. If fixpoint has remaining unexpanded things, error out.
3. exit: convert to FlatType and CompoundAccess, generate new types (TypeKey) basically everywhere to keep all types non-cyclic (use a M.Map FlatType TypeKey inside a new monad with state and except)
-}
