{-# LANGUAGE TupleSections, TemplateHaskell, LambdaCase, TypeSynonymInstances, FlexibleInstances, OverloadedStrings #-}

module CodeGen (generate) where

import GlobalAst (Inline(..), getSizeFromTSize, nowhere, TerminatorType(..))
import NameResolution.Ast (Resolved(..))
import Inference.Ast (TypeKey, FlatType(..), CallableDef, CallableDefT(..), Statement, StatementT(..), Expression, ExpressionT(..), Literal(..))
import Control.Applicative ((<*>), Applicative)
import Control.Lens hiding (op)
import Control.Monad.State
import Control.Monad.Except (ExceptT, runExceptT, MonadError, throwError)
import Data.Either (partitionEithers)
import Data.Functor ((<$>))
import Data.Word (Word32, Word)
import Data.String (IsString, fromString)
import LLVM.General.AST (Name(..), Type(..), BasicBlock(..), Named(..))
import qualified Data.Map as M
import qualified LLVM.General.AST as AST
import qualified LLVM.General.AST.Global as G
import qualified LLVM.General.AST.Attribute as A
import qualified LLVM.General.AST.Type as T
import qualified LLVM.General.AST.Instruction as I
import qualified LLVM.General.AST.CallingConvention as CC
import qualified LLVM.General.AST.Constant as C
import qualified LLVM.General.AST.Linkage as Linkage
import qualified LLVM.General.AST.Visibility as Visibility

data ErrorMessage = ErrorString String deriving Show

type CodeGen a = StateT CodeGenState (ExceptT ErrorMessage Identity) a
type Super a = StateT SuperState Identity a

data CodeGenState = CodeGenState
                    { _super :: SuperState
                    , _fresh :: Word
                    , _locals :: M.Map Resolved Operand
                    , _entryBlock :: BasicBlock
                    , _currentBlock :: BasicBlock
                    , _finalizedBlocks :: [BasicBlock]
                    , _retInstr :: Named I.Terminator
                    , _defers :: Defers
                    , _breakTarget :: Maybe Name
                    , _continueTarget :: Maybe Name
                    }
data Defers = Defers
              { _defersAll :: [Statement]
              , _defersLoop :: [Statement]
              , _defersScope :: [Statement]
              }

data SuperState = SuperState
                  { _callableNames :: M.Map (Resolved, TypeKey, Inline) Name
                  , _namedTypes :: M.Map TypeKey Type
                  , _types :: M.Map TypeKey FlatType
                  , _structCounter :: Int
                  }

data Operand = Operand TypeKey Bool AST.Operand

class Generateable a where
  gen :: a -> CodeGen ()

class GenerateableWithOperand a where
  genO :: a -> CodeGen Operand

makeLenses ''CodeGenState
makeLenses ''SuperState
makeLenses ''Defers

generate :: [(CallableDef, M.Map TypeKey FlatType)] -> Either [ErrorMessage] AST.Module
generate inferred = runSuper $ do
  (errs, generated) <- partitionEithers <$> mapM genCallable inferred
  if null errs
    then Right <$> finishGeneration (makeDefMap generated)
    else return $ Left errs
  where
    runSuper = runIdentity . flip evalStateT initState
    initState = SuperState
                { _callableNames = M.empty
                , _namedTypes = M.empty
                , _types = M.empty
                , _structCounter = 0
                }
    getSig d = (Global $ callableName d, finalType d)
    makeDefMap = M.fromList . zip (getSig . fst <$> inferred)

finishGeneration :: M.Map (Resolved, TypeKey) AST.Global -> Super AST.Module
finishGeneration fdefs = do
  functionDefs <- map makeF . M.toList <$> use callableNames
  (nts, fts) <- unzip . M.elems
                <$> (M.intersectionWith (,) <$> use namedTypes <*> use types)
  llvmts <- mapM fToLLVMType fts
  let typeDefs = zipWith makeT nts llvmts
      makeT (NamedTypeReference n) t = AST.TypeDefinition n $ Just t
  return $ AST.defaultModule { AST.moduleDefinitions = functionDefs ++ typeDefs }
  where
    makeF ((r, t, i), n) = case M.lookup (r, t) fdefs of
      Nothing -> error $ "Compiler error, couldn't find function " ++ show (r, t)
      Just f@G.Function{G.functionAttributes = attrs} -> AST.GlobalDefinition $ case i of
        NeverInline -> f { G.name = n, G.functionAttributes = A.NoInline : attrs }
        UnspecifiedInline -> f { G.name = n }
        AlwaysInline -> f { G.name = n, G.functionAttributes = A.AlwaysInline : attrs }

-- ###Callable generation starters

genCallable :: (CallableDef, M.Map TypeKey FlatType) -> Super (Either ErrorMessage AST.Global)
genCallable (d, ts) = do
  prevTypes <- types <<.= ts
  let newToName = M.keys . M.filter isStruct $ M.difference ts prevTypes
  firstN <- structCounter <<+= length newToName
  let newNamed = M.fromAscList $ zip newToName newNames
      newNames = NamedTypeReference . Name . ("struct" ++) . show <$> [firstN..]
  namedTypes %= (`M.union` newNamed)
  get >>= runCodeGen (codegenCallable d)
  where
    isStruct StructT{} = True
    isStruct _ = False
    runCodeGen m su = case run of
      Right (ret, CodeGenState{_super = st}) -> put st >> return (Right ret)
      Left e -> return $ Left e
      where
        run = runIdentity . runExceptT . runStateT m $ CodeGenState
              { _super = su
              , _fresh = 0
              , _entryBlock = BasicBlock "entry" [] (Do $ I.Br "first" [])
              , _currentBlock = BasicBlock "first" [] (Do $ I.Ret Nothing [])
              , _finalizedBlocks = []
              , _locals = M.empty
              , _retInstr = Do $ I.Ret Nothing []
              , _defers = Defers [] [] []
              , _breakTarget = Nothing
              , _continueTarget = Nothing
              }

codegenCallable :: CallableDef -> CodeGen AST.Global
codegenCallable d@FuncDef{} = do
  (ins, inps) <- fmap unzip . mapM (makeParamOp False) $ intypes d
  (out, _) <- makeParamOp True $ outtype d
  locals .= M.fromList (zip (outarg d : inargs d) (out : ins))

  retInstr .= (Do $ I.Br "return" [])
  currentBlock . blockTerminator .= (Do $ I.Br "return" [])
  gen initRet

  firstBlock <- currentBlock <<.= BasicBlock "return" [] undefined
  Operand _ _ op <- genO readRet >>= unPoint
  currentBlock . blockTerminator .= (Do $ I.Ret (Just op) [])
  finalizeAndReplaceWith firstBlock

  blocks <- codegenBody d
  retty <- toLLVMType False $ outtype d
  return $ defaultFunction
    { G.basicBlocks = blocks
    , G.parameters = (inps, False)
    , G.returnType = retty
    }
  where
    initRet :: Statement
    initRet = VarInit True (outarg d) (ExprLit (Zero (outtype d) nowhere)) nowhere
    readRet :: Expression
    readRet = Variable (outarg d) (outtype d) nowhere

codegenCallable d@ProcDef{} = do
  (ins, inps) <- fmap unzip . mapM (makeParamOp False) $ intypes d
  (outs, outps) <- fmap unzip . mapM (makeParamOp True) $ outtypes d
  locals .= M.fromList (zip (inargs d ++ outargs d) (ins ++ outs))

  blocks <- codegenBody d
  return $ defaultFunction
    { G.basicBlocks = blocks
    , G.parameters = (inps ++ outps, False)
    }

makeParamOp :: Bool -> TypeKey -> CodeGen (Operand, AST.Parameter)
makeParamOp pointable t = do
  n <- newName
  llvmt <- toLLVMType pointable t
  return ( Operand t pointable $ AST.LocalReference llvmt n
         , AST.Parameter llvmt n [])

codegenBody :: CallableDef -> CodeGen [BasicBlock]
codegenBody d = do
  gen $ callableBody d
  use currentBlock >>= finalizeBlock
  use entryBlock >>= finalizeBlock
  use finalizedBlocks

-- ###Regular code generation

instance Generateable Statement where
  gen (ProcCall inl (Variable n pt _) is os _) = do
    pop <- requestCallable (n, pt, inl)
    iOps <- mapM (genO >=> unPoint) is
    oOps <- mapM genO os
    uinstr $ I.Call False CC.Fast [] pop ((,[]) . getOp <$> (iOps ++ oOps)) [] []
  gen (Defer stmnt _) = do
    defers . defersAll %= (stmnt :)
    defers . defersLoop %= (stmnt :)
    defers . defersScope %= (stmnt :)
  gen (ShallowCopy a e _) = do
    Operand _ True aOp <- genO a -- TODO: throw error before codegen if fail
    Operand _ False eOp <- genO e >>= unPoint
    uinstr $ I.Store False aOp eOp Nothing 0 []
  gen (If cond stmnt mElseStmnt _) = do
    Operand _ _ condOp <- genO cond >>= unPoint
    (thenName, elseName, nextName) <- (,,) <$> newName <*> newName <*> newName
    prevTerminator <- currentBlock . blockTerminator <<.=
                      (Do $ I.CondBr condOp thenName elseName [])

    finalizeAndReplaceWith $ BasicBlock thenName [] (Do $ I.Br nextName [])
    gen stmnt

    finalizeAndReplaceWith $ BasicBlock elseName [] (Do $ I.Br nextName [])
    maybe (return ()) gen mElseStmnt

    finalizeAndReplaceWith $ BasicBlock nextName [] prevTerminator
  gen (While cond stmnt _) = do
    (condName, bodyName, nextName) <- (,,) <$> newName <*> newName <*> newName
    prevTerminator <- currentBlock . blockTerminator <<.= (Do $ I.Br condName [])

    finalizeAndReplaceWith $ BasicBlock condName [] undefined
    Operand _ False condOp <- genO cond >>= unPoint
    currentBlock . blockTerminator .= (Do $ I.CondBr condOp bodyName nextName [])

    finalizeAndReplaceWith $ BasicBlock bodyName [] (Do $ I.Br condName [])
    prevBreak <- breakTarget <<.= Just nextName
    prevContinue <- continueTarget <<.= Just condName
    gen stmnt
    breakTarget .= prevBreak
    continueTarget .= prevContinue

    finalizeAndReplaceWith $ BasicBlock nextName [] prevTerminator
  gen (Scope stmnts _) = do
    prevLocals <- use locals
    prevDefers <- use defers
    defers . defersScope .= []

    mapM_ gen stmnts

    use (defers . defersScope) >>= mapM_ gen
    defers .= prevDefers
    locals .= prevLocals
  gen (Terminator tt r) = do
    (term, deferred) <- case tt of
      Return -> (,) <$> use retInstr <*> use (defers . defersAll)
      _ -> do
        target <- use (boolean breakTarget continueTarget $ tt == Break) >>=
          justErr (ErrorString $ "Cannot break or continue at " ++ show r ++ ", no loop.")
        (Do $ I.Br target [], ) <$> use (defers . defersLoop)
    mapM_ gen deferred
    currentBlock . blockTerminator .= term
  gen (VarInit False n e _) = genO e >>= unPoint >>= (locals . at n ?=)
  gen (VarInit True n e _) = do
    Operand t False eOp <- genO e >>= unPoint
    allocaName <- newName
    allocaType <- toLLVMType False t
    let varOp = AST.LocalReference (T.ptr allocaType) allocaName
        alloca = I.Alloca allocaType Nothing 0 []
    entryBlock . blockInstrs %= (allocaName := alloca :)
    locals . at n ?= Operand t True varOp
    uinstr $ I.Store False varOp eOp Nothing 0 []

instance GenerateableWithOperand Expression where
  genO = undefined -- TODO

-- ###Codegen helpers

uinstr :: I.Instruction -> CodeGen ()
uinstr instruction = currentBlock . blockInstrs %= (Do instruction :)

instr :: TypeKey -> Bool -> I.Instruction -> CodeGen Operand
instr tk pointable instruction = do
  n <- newName
  t <- toLLVMType pointable tk
  currentBlock . blockInstrs %= (n := instruction :)
  return . Operand tk pointable $ AST.LocalReference t n

requestCallable :: (Resolved, TypeKey, Inline) -> CodeGen AST.CallableOperand
requestCallable sig@(Global n, tk, inl) =
  use (super . callableNames . at sig) >>= \case
    Just n' -> do
      t <- toLLVMType False tk
      return . Right . AST.ConstantOperand $ C.GlobalReference t n'
    Nothing -> do
      t <- toLLVMType False tk
      n' <- makeName
      return . Right . AST.ConstantOperand $ C.GlobalReference t n'
  where
    makeName = super . callableNames . at sig <?= Name (n ++ "#" ++ show tk ++ "#" ++ show inl)

unPoint :: Operand -> CodeGen Operand
unPoint o@(Operand _ False _) = return o
unPoint (Operand t True prev) = instr t False $ I.Load False prev Nothing 0 []

getOp :: Operand -> AST.Operand
getOp (Operand _ _ o) = o

defaultFunction :: G.Global
defaultFunction = G.Function
  { G.linkage = Linkage.Internal
  , G.visibility = Visibility.Default
  , G.callingConvention = CC.Fast
  , G.returnAttributes = []
  , G.returnType = T.void
  , G.name = error "Compiler error: This function does not yet have a name set"
  , G.parameters = ([], False)
  , G.functionAttributes = []
  , G.section = Nothing
  , G.alignment = 0
  , G.garbageCollectorName = Nothing
  , G.basicBlocks = []
  }

finalizeAndReplaceWith :: BasicBlock -> CodeGen ()
finalizeAndReplaceWith b = (currentBlock <<.= b) >>= finalizeBlock

finalizeBlock :: BasicBlock -> CodeGen ()
finalizeBlock (BasicBlock n is t) = finalizedBlocks %= (BasicBlock n (reverse is) t :)

newName :: CodeGen Name
newName = UnName <$> (fresh <<+= 1)

-- ###Type conversion helpers

class (Applicative m, Monad m) => TypeConverter m where
  getFT :: TypeKey -> m FlatType
  getLLVMType :: TypeKey -> m (Maybe Type)

instance TypeConverter (StateT SuperState Identity) where
  getFT tk = use (types . at tk) >>= \case
    Nothing -> error $ "Compiler error: could not find typekey: " ++ show tk
    Just t -> return t
  getLLVMType tk = use (namedTypes . at tk)

instance TypeConverter (StateT CodeGenState (ExceptT ErrorMessage Identity)) where
  getFT tk = use (super . types . at tk) >>= \case
    Nothing -> error $ "Compiler error: could not find typekey: " ++ show tk
    Just t -> return t
  getLLVMType tk = use (super . namedTypes . at tk)

fToLLVMType :: TypeConverter m => FlatType -> m Type
fToLLVMType BoolT = return T.i1
fToLLVMType (PointerT tk) = T.ptr <$> toLLVMType False tk
fToLLVMType (StructT ps) = T.StructureType False <$> mapM (toLLVMType False . snd) ps
fToLLVMType (FuncT is o) = -- TODO: should this actually be a pointer to function?
  T.FunctionType <$> toLLVMType False o <*> mapM (toLLVMType False) is <*> return False
fToLLVMType (ProcT is os) =
  T.FunctionType T.void <$> sequence (is' ++ os') <*> return False
  where
    is' = toLLVMType False <$> is
    os' = fmap T.ptr . toLLVMType True <$> os
fToLLVMType t = return $ case t of
  FloatT{} -> T.FloatingPointType (getSize t) T.IEEE
  _ -> T.IntegerType (getSize t)

toLLVMType :: TypeConverter m => Bool -> TypeKey -> m Type
toLLVMType False tk = getLLVMType tk >>= maybe (getFT tk >>= fToLLVMType) return
toLLVMType True tk = T.ptr <$> (getLLVMType tk >>= maybe (getFT tk >>= fToLLVMType) return)

getSize :: FlatType -> Word32
getSize (IntT s) = getSizeFromTSize s
getSize (UIntT s) = getSizeFromTSize s
getSize (FloatT s) = getSizeFromTSize s

-- ###Helpers:

boolean :: a -> a -> Bool -> a
boolean a b c = if c then a else b

justErr :: MonadError e m => e -> Maybe a -> m a
justErr _ (Just a) = return a
justErr err Nothing = throwError err

mapWith :: Ord k => (a -> k) -> [a] -> M.Map k a
mapWith f as = M.fromList $ zip (f <$> as) as

instance IsString Name where
  fromString = Name

-- ###Manual lenses:

blockInstrs :: Functor f => ([AST.Named AST.Instruction] -> f [AST.Named AST.Instruction]) -> AST.BasicBlock -> f AST.BasicBlock
blockInstrs inj (AST.BasicBlock n i t) = (\is -> AST.BasicBlock n is t) <$> inj i
{-# INLINE blockInstrs #-}

blockTerminator :: Functor f => (AST.Named AST.Terminator -> f (AST.Named AST.Terminator)) -> AST.BasicBlock -> f AST.BasicBlock
blockTerminator inj (AST.BasicBlock n i t) = AST.BasicBlock n i <$> inj t
{-# INLINE blockTerminator #-}

blockName :: Functor f => (AST.Name -> f AST.Name) -> AST.BasicBlock -> f AST.BasicBlock
blockName inj (AST.BasicBlock n i t) = (\n' -> AST.BasicBlock n' i t) <$> inj n
{-# INLINE blockName #-}
