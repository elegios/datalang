{-# LANGUAGE TupleSections #-}

module CodeGen.FuncGen where

import Ast
import CodeGen.Basics
import Data.Maybe
import Data.Functor ((<$>))
import Data.List
import Data.Word
import Data.Generics.Uniplate.Data
import Control.Lens hiding (op, index, parts, transform)
import Control.Monad.State (runStateT, StateT, gets)
import Control.Monad.Except
import LLVM.General.AST.Operand
import LLVM.General.AST.Name
import LLVM.General.AST.Global
import LLVM.General.AST.Instruction as I hiding (condition, index)
import qualified LLVM.General.AST.Type as T
import qualified LLVM.General.AST.Constant as C
import qualified LLVM.General.AST as AST
import qualified Data.Map as M

data FuncState = FuncState
  { _genState :: GenState
  , _breakTarget :: Maybe Name
  , _continueTarget :: Maybe Name
  , _retTerminator :: Terminator
  , _locals :: M.Map String FuncGenOperand
  , _nextFresh :: Word
  , _finalizedBlocks :: [BasicBlock]
  , _currentBlock :: BasicBlock
  }

type FuncGen a = StateT FuncState (ExceptT ErrorMessage Identity) a

type FuncGenOperand = (Operand, Type, Bool)

runFuncGen :: FuncState -> FuncGen a -> Either ErrorMessage (a, FuncState)
runFuncGen initState = runIdentity . runExceptT .  flip runStateT initState

finalizeBlock :: BasicBlock -> FuncGen ()
finalizeBlock b = finalizedBlocks %= ((b & blockInstrs %~ reverse) :)

finalizeAndReplaceWith :: BasicBlock -> FuncGen ()
finalizeAndReplaceWith b = (currentBlock <<.= b) >>= finalizeBlock

instr :: (Instruction, T.Type) -> FuncGen Operand
instr (instruction, t) = do
  unname <- fresh
  currentBlock . blockInstrs %= (unname := instruction :)
  return $ LocalReference t unname

uinstr :: Instruction -> FuncGen ()
uinstr instruction = currentBlock . blockInstrs %= (Do instruction :)

newBlock :: FuncGen BasicBlock
newBlock = do
  unname <- fresh
  return $ BasicBlock unname [] (Do $ Ret Nothing [])

fresh :: FuncGen Name
fresh = liftM UnName $ nextFresh <<+= 1

requestFunction :: FuncSig -> FuncGen CallableOperand
requestFunction func = do
  mo <- gets $ getFunctionOperand func . _genState
  maybe newRequest return mo
  where
    getNextName :: FuncGen Int
    getNextName = fromJust <$> (genState . nextNameNumber . at fname <%= (Just . maybe 0 succ))
    requestWithOperand :: CallableOperand -> FuncGen CallableOperand
    requestWithOperand op = genState . requested . at func <?= op
    newRequest = do
      num <- getNextName
      llvmt <- toFunctionType inTs outTs retty
      requestWithOperand . Right . ConstantOperand . C.GlobalReference llvmt . Name $ fname ++ show num
    (fname, inTs, outTs, retty) = case func of
      NormalSig n its ots -> (n, its, ots, Nothing)
      ExprSig n its ot -> (n, its, [], Just ot)

getFunctionOperand :: FuncSig -> GenState -> Maybe CallableOperand
getFunctionOperand sig state = case M.lookup sig $ _generated state of
  Just o -> Just o
  Nothing -> M.lookup sig $ _requested state

toFunctionType :: [Type] -> [Type] -> Maybe Type -> FuncGen T.Type
toFunctionType inTs outTs retty = do
  llvmretty <- maybe (return T.void) (toLLVMType False) retty
  ts <- toFunctionParams inTs outTs
  return $ T.FunctionType llvmretty ts False

toFunctionParams :: [Type] -> [Type] -> FuncGen [T.Type]
toFunctionParams inTs outTs = mapM (uncurry toLLVMType) $ ins ++ outs
  where
    ins = zip (repeat False) inTs
    outs = zip (repeat True) outTs

ensureTopNotNamed :: Type -> FuncGen Type
ensureTopNotNamed (NamedT tName ts) = do
  mType <- uses (genState . source) $ M.lookup tName . typeDefinitions
  case mType of
    Nothing -> throwError . ErrorString $ "Unknown type " ++ tName
    Just (TypeDef it tNames _) -> return $ transform replaceParamTypes it
      where
        translation = M.fromList $ zip tNames ts
        replaceParamTypes x@(NamedT innerTName []) = fromMaybe x $ M.lookup innerTName translation
        replaceParamTypes x = x
ensureTopNotNamed x = return x

toLLVMType :: Bool -> Type -> FuncGen T.Type
toLLVMType mutable nt = ensureTopNotNamed nt >>= \t -> case t of
  StructT props -> do
    mType <- use $ genState . structTypes . at (snd <$> props)
    case mType of
      Just (_, ret) -> return ret
      Nothing -> do
        n <- use $ genState . structTypes . to M.size
        let llvmname = Name $ "struct" ++ show n
            llvmtype = T.NamedTypeReference llvmname
        genState . structTypes . at (snd <$> props) ?= (undefined, llvmtype)
        -- This enables recursion. Since the actual llvm top-level definition
        -- won't be used until the entire call to toLLVMType is done it is okay
        -- to have an undefined there as it won't actually be accessed.
        inners <- mapM (toLLVMType False . snd) props
        let struct = AST.TypeDefinition llvmname . Just $ T.StructureType False inners
        genState . structTypes . at (snd <$> props) ?= (struct, llvmtype)
        return . boolean T.ptr id mutable $ llvmtype
  PointerT inner -> boolean T.ptr id mutable . T.ptr <$> toLLVMType False inner
  _ -> boolean T.ptr id mutable <$> case M.lookup t typeMap of
    Just llvmtype -> return llvmtype
    Nothing -> throwError . ErrorString $ "Missed a case in the compiler, there is a type that cannot be converted to an LLVM type: " ++ show t

findMemberIndex :: String -> Type -> SourceRange -> FuncGen (Integer, Type)
findMemberIndex mName (StructT fields) sr = case find (\(_, (n, _)) -> n == mName) $ zip [0..] fields of
  Just (i, (_, t)) -> return (i, t)
  Nothing -> throwError . ErrorString $ "Unknown member field " ++ mName ++ " in struct at " ++ show sr
-- TODO: ugly death in findMemberIndex on strange memorychunks
findMemberIndex mName (Memorychunk iType _ _) _ = return . (, iType) $ case mName of
  "len" -> 0
  "cap" -> 1
findMemberIndex _ _ sr = throwError . ErrorString $ "Attempt to access member field of non-struct type at " ++ show sr

opOp :: FuncGenOperand -> Operand
opOp (a, _, _) = a
opType :: FuncGenOperand -> Type
opType (_, a, _) = a
opMutable :: FuncGenOperand -> Bool
opMutable (_, _, a) = a

-- Lenses

breakTarget :: Functor f => (Maybe Name -> f (Maybe Name)) -> FuncState -> f FuncState
breakTarget inj g = (\bt -> g { _breakTarget = bt }) <$> inj (_breakTarget g)
{-# INLINE breakTarget #-}

continueTarget :: Functor f => (Maybe Name -> f (Maybe Name)) -> FuncState -> f FuncState
continueTarget inj g = (\ct -> g { _continueTarget = ct }) <$> inj (_continueTarget g)
{-# INLINE continueTarget #-}

locals :: Functor f => (M.Map String FuncGenOperand -> f (M.Map String FuncGenOperand)) -> FuncState -> f FuncState
locals inj g = (\locs -> g { _locals = locs }) <$> inj (_locals g)
{-# INLINE locals #-}

retTerminator :: Functor f => (Terminator -> f Terminator) -> FuncState -> f FuncState
retTerminator inj g = (\locs -> g { _retTerminator = locs }) <$> inj (_retTerminator g)
{-# INLINE retTerminator #-}

genState :: Functor f => (GenState -> f GenState) -> FuncState -> f FuncState
genState inj g = (\bt -> g { _genState = bt }) <$> inj (_genState g)
{-# INLINE genState #-}

finalizedBlocks :: Functor f => ([BasicBlock] -> f [BasicBlock]) -> FuncState -> f FuncState
finalizedBlocks inj g = (\fbs -> g { _finalizedBlocks = fbs }) <$> inj (_finalizedBlocks g)
{-# INLINE finalizedBlocks #-}

currentBlock :: Functor f => (BasicBlock -> f BasicBlock) -> FuncState -> f FuncState
currentBlock inj g = (\cb -> g { _currentBlock = cb }) <$> inj (_currentBlock g)
{-# INLINE currentBlock #-}

nextFresh :: Functor f => (Word -> f Word) -> FuncState -> f FuncState
nextFresh inj g = (\nf -> g { _nextFresh = nf }) <$> inj (_nextFresh g)
{-# INLINE nextFresh #-}
