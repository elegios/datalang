{-# LANGUAGE OverloadedStrings #-}

module CodeGen where

{- TODO:
 - Save a "stack trace" of requested functions, to make it easier to figure out
   why a specific function was requested.
 - Deal with default sizes of i, u and f
 - Ensure that operations involving u types are actually unsigned, it's not
   carried in the type
 -}

import Ast
import Data.Maybe
import Data.Functor ((<$>))
import Data.String (IsString, fromString)
import Data.List
import Data.Word
import Control.Lens
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Identity
import LLVM.General.AST.Operand
import LLVM.General.AST.Constant
import LLVM.General.AST.Name
import LLVM.General.AST.Global
import LLVM.General.AST.Instruction
import qualified LLVM.General.AST.Type as T
import qualified LLVM.General.AST.CallingConvention as CC
import qualified LLVM.General.AST as AST
import qualified Data.Map as M

type GenFuncs = M.Map (String, [Type], [Type]) CallableOperand
data GenState = GenState
  { _generated :: GenFuncs
  , _requested :: GenFuncs
  , _nextName :: M.Map String Int
  , _errors :: [ErrorMessage]
  , _source :: Source
  }

data FuncState = FuncState
  { _genState :: GenState
  , _breakTarget :: Maybe Name
  , _continueTarget :: Maybe Name
  , _locals :: M.Map String (Operand, Type)
  , _nextFresh :: Word
  , _finalizedBlocks :: [BasicBlock]
  , _currentBlock :: BasicBlock
  }

emptyState :: GenFuncs -> Source -> GenState
emptyState reqs = GenState M.empty reqs M.empty []

data ErrorMessage = ErrorString String

type CodeGen a = StateT GenState Identity a
type FuncGen a = StateT FuncState (ExceptT ErrorMessage Identity) a

generate :: Source -> GenFuncs -> Either [ErrorMessage] AST.Module
generate source requests = case errs of
  [] -> Right $ AST.defaultModule { AST.moduleDefinitions = defs }
  _ -> Left errs
  where
    (defs, resState) = runIdentity . runStateT generator $ emptyState requests source
    errs = _errors resState
    generator :: CodeGen [AST.Definition]
    generator = do
      mreq <- use $ requested . to M.minViewWithKey
      maybe (return []) runGenerateFunction mreq
    runGenerateFunction ((func, _), _) = do
      res <- generateFunction func
      op <- requested . at func <<.= Nothing
      generated . at func .= op
      case res of
        Left err -> (errors %= (err:)) >> generator
        Right res -> (res:) <$> generator

generateFunction :: (String, [Type], [Type]) -> CodeGen (Either ErrorMessage AST.Definition)
generateFunction (name, inTs, outTs) = do
  mFunc <- uses source $ find (\(s, _, _) -> s == name) . functionDefinitions
  case mFunc of
    Nothing -> return . Left . ErrorString $ "Function " ++ name ++ " not found"
    Just (_, FuncDef innames outnames stmnts, _) -> do
      currGenState <- get
      let initState = FuncState currGenState Nothing Nothing locals 0 [] entryBlock
          entryBlock = BasicBlock "entry" [] . Do $ Ret Nothing []
      return . runIdentity . runExceptT . flip evalStateT initState $ do
        generateFunctionBody stmnts
        use currentBlock >>= finalizeBlock
        blocks <- use finalizedBlocks
        return . AST.GlobalDefinition $ functionDefaults
          { name = fromString name
          , parameters = (params, False)
          , basicBlocks = reverse blocks
          , returnType = T.void
          }
      where
        locals = M.fromList . zip (innames ++ outnames) . zip paramLocals $ inTs ++ outTs
        paramLocals = zipWith LocalReference (toFunctionParams inTs outTs) names
        params = map (\f -> f []) withNames
        withNames = zipWith Parameter (toFunctionParams inTs outTs) names
        names = fromString <$> (innames ++ outnames)

generateFunctionBody :: [Statement] -> FuncGen ()
generateFunctionBody [] = return ()
generateFunctionBody (VarInit name t _ : stmnts) = do
  op <- instr (Alloca llvmType Nothing 0 [], llvmType)
  locals . at name ?= (op, t)
  generateFunctionBody stmnts
  where
    llvmType = toLLVMType t
generateFunctionBody (Terminator t sr : stmnts)
  | not $ null stmnts = throwError . ErrorString $ "There are statements after the terminator at " ++ show sr
  | otherwise = do
    term <- case t of
      Return -> return $ Ret Nothing []
      _ -> do
        target <- use (boolean breakTarget continueTarget $ t == Break)
        case target of
          Nothing -> throwError . ErrorString $ "Cannot break or continue at " ++ show sr ++ ", no loop."
          Just name -> return $ Br name []
    currentBlock . blockTerminator .= Do term
generateFunctionBody (Scope inner _ : outer) = do
  prevLocals <- use locals
  generateFunctionBody inner
  locals .= prevLocals
  generateFunctionBody outer
generateFunctionBody (ShallowCopy assignee expression sr : stmnts) = do
  assOp <- generateAssignableExpression assignee
  expOp <- generateExpression expression
  uinstr $ Store False assOp expOp Nothing 0 []
  generateFunctionBody stmnts
generateFunctionBody (FuncCall name inargs outargs sr : stmnts) = do
  funcOp <- requestFunction (name, snd <$> inargs, snd <$> outargs)
  inOps <- sequence $ generateAssignableExpression <$> (fst <$> inargs) -- TODO: generate scalars when inargs are scalars instead
  outOps <- sequence $ generateAssignableExpression <$> (fst <$> outargs)
  uinstr $ Call False CC.C [] funcOp (zip (inOps ++ outOps) $ repeat []) [] []
  generateFunctionBody stmnts

generateAssignableExpression :: Expression -> FuncGen Operand
generateAssignableExpression = undefined

generateExpression :: Expression -> FuncGen Operand
generateExpression = undefined

finalizeBlock :: BasicBlock -> FuncGen ()
finalizeBlock b = finalizedBlocks %= ((b & blockInstrs %~ reverse) :)

fresh :: FuncGen Name
fresh = liftM UnName $ nextFresh <<+= 1

freshName :: String -> FuncGen Name
freshName name = liftM (Name . (name ++) . show) $ nextFresh <<+= 1

instr :: (Instruction, T.Type) -> FuncGen Operand
instr (instruction, t) = do
  name <- fresh
  currentBlock . blockInstrs %= (name := instruction :)
  return $ LocalReference t name

uinstr :: Instruction -> FuncGen ()
uinstr instruction = currentBlock . blockInstrs %= (Do instruction :)

newBlock :: FuncGen BasicBlock
newBlock = do
  name <- fresh
  return $ BasicBlock name [] (Do $ Ret Nothing [])

requestFunction :: (String, [Type], [Type]) -> FuncGen CallableOperand
requestFunction func@(name, inTs, outTs) = do
  mo <- gets $ getFunctionOperand func . _genState
  maybe newRequest return mo
  where
    getNextName :: FuncGen Int
    getNextName = fromJust <$> (genState . nextName . at name <%= (Just . maybe 0 succ))
    requestWithOperand :: CallableOperand -> FuncGen CallableOperand
    requestWithOperand op = genState . requested . at func <?= op
    newRequest = do
      num <- getNextName
      requestWithOperand . Right . ConstantOperand . GlobalReference (toFunctionType inTs outTs) . fromString $ name ++ show num

getFunctionOperand :: (String, [Type], [Type]) -> GenState -> Maybe CallableOperand
getFunctionOperand sig state = case M.lookup sig $ _generated state of
  Just o -> Just o
  Nothing -> M.lookup sig $ _requested state

toFunctionType :: [Type] -> [Type] -> T.Type
toFunctionType inTs outTs = (\ts -> T.FunctionType T.void ts False) $ toFunctionParams inTs outTs

toFunctionParams :: [Type] -> [Type] -> [T.Type]
{-toFunctionParams inTs outTs = (toScalarType <$> inTs) ++ (T.ptr . toScalarType <$> outTs)-} --TODO: handle this instead in codegen for function
toFunctionParams inTs outTs = toLLVMType <$> (inTs ++ outTs)

toLLVMType :: Type -> T.Type
toLLVMType t = fromMaybe composite $ M.lookup t typeMap
  where
    composite = case t of
      StructT parts -> T.StructureType False $ toLLVMType . snd <$> parts
      FuncT ins outs -> toFunctionType ins outs

typeMap :: M.Map Type T.Type
typeMap = M.fromList
  [ (I8, T.i8)
  , (I16, T.i16)
  , (I32, T.i32)
  , (I64, T.i64)

  , (U8, T.i8)
  , (U16, T.i16)
  , (U32, T.i32)
  , (U64, T.i64)

  , (F32, T.float)
  , (F64, T.double)

  , (BoolT, T.i1)
  ]

-- These lenses could be generated if TemplateHaskell didn't
-- require things to be linked dynamically which conflicts
-- with my llvm bindings atm

generated :: Functor f => (GenFuncs -> f GenFuncs) -> GenState -> f GenState
generated inj state = (\gen -> state { _generated = gen }) <$> inj (_generated state)
{-# INLINE generated #-}

requested :: Functor f => (GenFuncs -> f GenFuncs) -> GenState -> f GenState
requested inj state = (\req -> state { _requested = req }) <$> inj (_requested state)
{-# INLINE requested #-}

nextName :: Functor f => (M.Map String Int -> f (M.Map String Int)) -> GenState -> f GenState
nextName inj state = (\nn -> state { _nextName = nn }) <$> inj (_nextName state)
{-# INLINE nextName #-}

source :: Functor f => (Source -> f Source) -> GenState -> f GenState
source inj g = (\s -> g { _source = s }) <$> inj (_source g)
{-# INLINE source #-}

errors :: Functor f => ([ErrorMessage] -> f [ErrorMessage]) -> GenState -> f GenState
errors inj g = (\errs -> g { _errors = errs }) <$> inj (_errors g)
{-# INLINE errors #-}

breakTarget :: Functor f => (Maybe Name -> f (Maybe Name)) -> FuncState -> f FuncState
breakTarget inj g = (\bt -> g { _breakTarget = bt }) <$> inj (_breakTarget g)
{-# INLINE breakTarget #-}

continueTarget :: Functor f => (Maybe Name -> f (Maybe Name)) -> FuncState -> f FuncState
continueTarget inj g = (\ct -> g { _continueTarget = ct }) <$> inj (_continueTarget g)
{-# INLINE continueTarget #-}

locals :: Functor f => (M.Map String (Operand, Type) -> f (M.Map String (Operand, Type))) -> FuncState -> f FuncState
locals inj g = (\locs -> g { _locals = locs }) <$> inj (_locals g)
{-# INLINE locals #-}

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

blockInstrs :: Functor f => ([Named Instruction] -> f [Named Instruction]) -> BasicBlock -> f BasicBlock
blockInstrs inj (BasicBlock n i t) = (\is -> BasicBlock n is t) <$> inj i
{-# INLINE blockInstrs #-}

blockTerminator :: Functor f => (Named Terminator -> f (Named Terminator)) -> BasicBlock -> f BasicBlock
blockTerminator inj (BasicBlock n i t) = BasicBlock n i <$> inj t
{-# INLINE blockTerminator #-}

instance IsString Name where
  fromString = Name

boolean :: a -> a -> Bool -> a
boolean a _ True = a
boolean _ a False = a
