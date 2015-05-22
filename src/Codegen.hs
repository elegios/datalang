{-# LANGUAGE TupleSections, TemplateHaskell, LambdaCase, TypeSynonymInstances, FlexibleInstances, OverloadedStrings #-}

module CodeGen (generate) where

import GlobalAst (Inline(..), getSizeFromTSize)
import NameResolution.Ast (Resolved(..))
import Inference.Ast (TypeKey, FlatType(..), CallableDef, CallableDefT(..), Statement, StatementT(..), Expression, ExpressionT(..))
import Control.Applicative ((<*>), Applicative)
import Control.Lens
import Control.Monad.State
import Control.Monad.Except (ExceptT, runExceptT)
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
              }

codegenCallable :: CallableDef -> CodeGen AST.Global
codegenCallable FuncDef{} = undefined -- TODO
codegenCallable d@ProcDef{} = do
  (ins, inps) <- fmap unzip . mapM (makeOp False) $ intypes d
  (outs, outps) <- fmap unzip . mapM (makeOp True) $ outtypes d
  locals .= M.fromList (zip (inargs d ++ outargs d) (ins ++ outs))
  gen $ callableBody d
  use entryBlock >>= finalizeBlock
  blocks <- use finalizedBlocks
  return $ defaultFunction
    { G.basicBlocks = blocks
    , G.parameters = (inps ++ outps, False)
    }
  where
    makeOp pointable t = do
      n <- newName
      llvmt <- toLLVMType pointable t
      return ( Operand t pointable $ AST.LocalReference llvmt n
             , AST.Parameter llvmt n [])
-- ###Regular code generation

instance Generateable Statement where
  gen (ProcCall inl (Variable n pt _) is os _) = do
    pop <- requestCallable (n, pt, inl)
    iOps <- mapM (genO >=> unPoint) is
    oOps <- mapM genO os
    uinstr $ I.Call False CC.Fast [] pop ((,[]) . getOp <$> (iOps ++ oOps)) [] []

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
