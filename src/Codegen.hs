{-# LANGUAGE TupleSections #-}

module CodeGen where

-- TODO: Save a "stack trace" of requested functions, to make it easier to figure out why a specific function was requested.

import Ast
import Data.Maybe
import Data.Functor ((<$>))
import Data.List
import Data.Word
import Control.Lens hiding (op, index, parts)
import Control.Monad.State (runStateT, StateT, get, put, gets)
import Control.Monad.Except
import LLVM.General.AST.Operand
import LLVM.General.AST.Name
import LLVM.General.AST.Global
import LLVM.General.AST.IntegerPredicate as IP
import LLVM.General.AST.Instruction as I hiding (condition, index)
import qualified LLVM.General.AST.FloatingPointPredicate as FP
import qualified LLVM.General.AST.Type as T
import qualified LLVM.General.AST.CallingConvention as CC
import qualified LLVM.General.AST.Constant as C
import qualified LLVM.General.AST as AST
import qualified LLVM.General.AST.Float as F
import qualified Data.Map as M

data FuncSig = NormalSig String [Type] [Type]
             | ExprSig String [Type] Type deriving (Eq, Ord)
type GenFuncs = M.Map FuncSig CallableOperand
data GenState = GenState
  { _generated :: GenFuncs
  , _requested :: GenFuncs
  , _nextNameNumber :: M.Map String Int
  , _errors :: [ErrorMessage]
  , _source :: Source
  }

data FuncState = FuncState
  { _genState :: GenState
  , _breakTarget :: Maybe Name
  , _continueTarget :: Maybe Name
  , _retTerminator :: Terminator
  , _locals :: M.Map String (Operand, Type)
  , _nextFresh :: Word
  , _finalizedBlocks :: [BasicBlock]
  , _currentBlock :: BasicBlock
  }

emptyState :: GenFuncs -> Source -> GenState
emptyState reqs = GenState M.empty reqs M.empty []

data ErrorMessage = ErrorString String deriving Show

type CodeGen a = StateT GenState Identity a
type FuncGen a = StateT FuncState (ExceptT ErrorMessage Identity) a

generate :: Source -> GenFuncs -> Either [ErrorMessage] AST.Module
generate sourceToGen requests = case errs of
  [] -> Right $ AST.defaultModule { AST.moduleDefinitions = defs }
  _ -> Left errs
  where
    (defs, resState) = runIdentity . runStateT generator $ emptyState requests sourceToGen
    errs = _errors resState
    generator :: CodeGen [AST.Definition]
    generator = do
      mreq <- use $ requested . to M.minViewWithKey
      maybe (return []) runGenerateFunction mreq
    runGenerateFunction ((func, _), _) = do
      eRes <- generateFunction func
      op <- requested . at func <<.= Nothing
      generated . at func .= op
      case eRes of
        Left err -> (errors %= (err:)) >> generator
        Right res -> (res:) <$> generator

generateFunction :: FuncSig -> CodeGen (Either ErrorMessage AST.Definition)
generateFunction sig@(NormalSig fName inTs outTs) = do
  mFunc <- uses source $ find (\(s, _, _) -> s == fName) . functionDefinitions
  case mFunc of
    Nothing -> return . Left . ErrorString $ "Function " ++ fName ++ " not found"
    Just (_, FuncDef innames outnames stmnts, _) -> do
      currGenState <- get
      let initState = FuncState currGenState Nothing Nothing (Ret Nothing []) initialLocals 0 [] entryBlock
          entryBlock = BasicBlock (Name "entry") [] . Do $ Ret Nothing []
      let eit = runIdentity . runExceptT . flip runStateT initState $ do
            generateFunctionBody stmnts
            constructFunctionDeclaration sig params T.void
      case eit of
        Left e -> return $ Left e
        Right (res, st) -> put (_genState st) >> return (Right res)
      where
        initialLocals = M.fromList . zip (innames ++ outnames) . zip paramLocals $ inTs ++ outTs
        paramLocals = zipWith LocalReference (toFunctionParams inTs outTs) names
        params = map (\f -> f []) withNames
        withNames = zipWith Parameter (toFunctionParams inTs outTs) names
        names = Name <$> (innames ++ outnames)

generateFunction sig@(ExprSig fName inTs outT) = do
  currGenState <- get
  let initState = FuncState currGenState Nothing Nothing (Br (Name "returnBlock") []) M.empty 0 [] entryBlock
      entryBlock = BasicBlock (Name "entry") [] . Do $ Br (Name "returnBlock") []
      retBlock = BasicBlock (Name "returnBlock") [] . Do $ Ret Nothing []
  let eit = runIdentity . runExceptT . flip runStateT initState $ do
        mFunc <- uses (genState . source . to functionDefinitions) $ find (\(s, _, _) -> s == fName)
        (_, FuncDef innames [outname] stmnts, _) <- justErr (ErrorString $ "Function " ++ fName ++ " not found") mFunc -- TODO: ugly death on incorrect number of outarguments

        let initLocals = M.fromList . zip innames . zip paramLocals $ inTs
            paramLocals = zipWith LocalReference (toFunctionParams inTs []) names
            params = map (\f -> f []) withNames
            withNames = zipWith Parameter (toFunctionParams inTs []) names
            names = Name <$> innames

        locals .= initLocals
        generateFunctionBody $ VarInit outname outT undefined : stmnts

        finalizeAndReplaceWith retBlock
        (retOp, _) <- generateExpression (Variable outname undefined)
        currentBlock . blockTerminator .= (Do $ Ret (Just retOp) [])

        constructFunctionDeclaration sig params $ toLLVMType outT
  case eit of
    Left e -> return $ Left e
    Right (res, st) -> put (_genState st) >> return (Right res)

constructFunctionDeclaration :: FuncSig -> [Parameter] -> T.Type -> FuncGen AST.Definition
constructFunctionDeclaration sig params retty = do
  use currentBlock >>= finalizeBlock
  blocks <- use finalizedBlocks
  mOpName <- uses (genState . requested . at sig) $ fmap extractNameFromCallableOperand
  return . AST.GlobalDefinition $ functionDefaults
    { name = fromJust mOpName
    , parameters = (params, False)
    , basicBlocks = reverse blocks
    , returnType = retty
    }

generateFunctionBody :: [Statement] -> FuncGen ()
generateFunctionBody [] = return ()

generateFunctionBody (VarInit vName t _ : stmnts) = do
  op <- instr (Alloca llvmType Nothing 0 [], llvmType)
  locals . at vName ?= (op, t)
  generateFunctionBody stmnts
  where
    llvmType = toLLVMType t

generateFunctionBody (Terminator t sr : stmnts)
  | not $ null stmnts = throwError . ErrorString $ "There are statements after the terminator at " ++ show sr
  | otherwise = do
    term <- case t of
      Return -> use retTerminator
      _ -> do
        target <- use (boolean breakTarget continueTarget $ t == Break)
        case target of
          Nothing -> throwError . ErrorString $ "Cannot break or continue at " ++ show sr ++ ", no loop."
          Just bName -> return $ Br bName []
    currentBlock . blockTerminator .= Do term

generateFunctionBody (Scope inner _ : outer) = do
  prevLocals <- use locals
  generateFunctionBody inner
  locals .= prevLocals
  generateFunctionBody outer

generateFunctionBody (ShallowCopy assignee expression sr : stmnts) = do
  (assOp, _) <- generateAssignableExpression assignee
  (expOp, _) <- generateExpression expression
  uinstr $ Store False assOp expOp Nothing 0 []
  generateFunctionBody stmnts

generateFunctionBody (FuncCall fName ins outs sr : stmnts) = do
  inOps <- sequence $ generateAssignableExpression <$> ins -- TODO: generate scalars when ins are scalars instead
  outOps <- sequence $ generateAssignableExpression <$> outs
  funcOp <- requestFunction $ NormalSig fName (snd <$> inOps) (snd <$> outOps)
  uinstr $ Call False CC.C [] funcOp (zip (map fst $ inOps ++ outOps) $ repeat []) [] []
  generateFunctionBody stmnts

generateFunctionBody (While condition stmnt sr : stmnts) = do
  condBlock <- newBlock
  bodyBlock <- newBlock
  nextBlock <- newBlock
  let nextName = nextBlock ^. blockName
      condName = condBlock ^. blockName
      bodyName = bodyBlock ^. blockName

  prevBreakTarget <- breakTarget <<.= Just nextName
  prevContinueTarget <- continueTarget <<.= Just condName
  prevTerminator <- currentBlock . blockTerminator <<.= (Do $ Br condName [])

  finalizeAndReplaceWith condBlock
  (condOp, _) <- generateExpression condition
  currentBlock . blockTerminator .= (Do $ CondBr condOp bodyName nextName [])

  finalizeAndReplaceWith $ bodyBlock & blockTerminator .~ (Do $ Br condName [])
  generateFunctionBody [stmnt]

  finalizeAndReplaceWith $ nextBlock & blockTerminator .~ prevTerminator
  breakTarget .= prevBreakTarget
  continueTarget .= prevContinueTarget
  generateFunctionBody stmnts

generateFunctionBody (If condition thenStmnt mElseStmnt sr : stmnts) = do
  thenBlock <- newBlock
  elseBlock <- newBlock
  nextBlock <- newBlock
  let nextName = nextBlock ^. blockName
      thenName = thenBlock ^. blockName
      elseName = elseBlock ^. blockName

  (condOp, _) <- generateExpression condition
  prevTerminator <- currentBlock . blockTerminator <<.= (Do $ CondBr condOp thenName elseName [])

  finalizeAndReplaceWith $ thenBlock & blockTerminator .~ (Do $ Br nextName [])
  generateFunctionBody [thenStmnt]

  finalizeAndReplaceWith $ elseBlock & blockTerminator .~ (Do $ Br nextName [])
  generateFunctionBody $ maybeToList mElseStmnt

  finalizeAndReplaceWith $ nextBlock & blockTerminator .~ prevTerminator
  generateFunctionBody stmnts

generateAssignableExpression :: Expression -> FuncGen (Operand, Type)
generateAssignableExpression (Variable vName sr) = do
  mOp <- use $ locals . at vName
  case mOp of
    Nothing -> throwError . ErrorString $ "Unknown variable " ++ vName ++ " at " ++ show sr
    Just op -> return op
generateAssignableExpression (MemberAccess expression mName sr) = do
  (bigOp, bigT) <- generateAssignableExpression expression
  (index, t) <- findNameIndexInStruct mName bigT sr
  op <- instr (I.GetElementPtr False bigOp [constInt 0, constInt index] [], toLLVMType t)
  return (op, t)
  where
    constInt = ConstantOperand . C.Int 32

generateExpression :: Expression -> FuncGen (Operand, Type)
generateExpression (ExprLit lit sr) = return $ case lit of
  ILit val t -> (ConstantOperand $ C.Int size val, t)
    where size = fromJust $ M.lookup t typeSizeMap
  FLit val t -> (ConstantOperand . C.Float $ F.Double val, t)
  BLit val -> (ConstantOperand . C.Int 1 $ boolean 1 0 val, BoolT)

generateExpression (Variable vName sr) = do
  mVal <- use $ locals . at vName
  case mVal of
    Nothing -> throwError . ErrorString $ "Unknown variable " ++ vName ++ " at " ++ show sr
    Just (op, t) -> liftM (, t) . instr $ (Load False op Nothing 0 [], toLLVMType t)

generateExpression (MemberAccess expression mName sr) = do
  (bigOp, bigT) <- generateExpression expression
  (index, t) <- findNameIndexInStruct mName bigT sr
  ptrOp <- instr (GetElementPtr False bigOp [constInt 0, constInt index] [], toLLVMType t)
  liftM (, t) . instr $ (Load False ptrOp Nothing 0 [], toLLVMType t)
  where
    constInt = ConstantOperand . C.Int 32

generateExpression (ExprFunc fName expressions t sr) = do
  ops <- sequence $ generateExpression <$> expressions
  funcOp <- requestFunction $ ExprSig fName (snd <$> ops) t
  retOp <- instr (Call False CC.C [] funcOp (zip (fst <$> ops) $ repeat []) [] [], toLLVMType t)
  return (retOp, t)

{-generateExpression (Un operator expression sr) = do-} -- TODO: Unary operators
  {-(expOp, t) <- generateExpression expression-}
  {-case operator of-}
    {-AriNegate -> -}

generateExpression (Bin operator exp1 exp2 sr) = do
  res1@(_, t1) <- generateExpression exp1
  res2@(_, t2) <- generateExpression exp2
  when (t1 /= t2) . throwError . ErrorString $ "The expressions around " ++ show operator ++ " at " ++ show sr ++ " have different types (" ++ show t1 ++ " != " ++ show t2 ++ ")"
  llvmOperator <- if isNum t1
    then case operator of
      Plus -> return $ if isFloat t1 then FAdd NoFastMathFlags else Add False False
      Minus -> return $ if isFloat t1 then FSub NoFastMathFlags else Sub False False
      Times -> return $ if isFloat t1 then FMul NoFastMathFlags else Mul False False
      Divide -> return $ if isFloat t1
        then FDiv NoFastMathFlags else if isUnsigned t1
          then UDiv False
          else SDiv False
      Remainder -> return $ if isFloat t1
        then FRem NoFastMathFlags else if isUnsigned t1
          then URem
          else SRem
      Lesser -> return $ if isFloat t1
        then FCmp FP.OLT
        else ICmp $ if isUnsigned t1 then ULT else SLT
      Greater -> return $ if isFloat t1
        then FCmp FP.OGT
        else ICmp $ if isUnsigned t1 then UGT else SGT
      LE -> return $ if isFloat t1
        then FCmp FP.OLE
        else ICmp $ if isUnsigned t1 then ULE else SLE
      GE -> return $ if isFloat t1
        then FCmp FP.OGE
        else ICmp $ if isUnsigned t1 then UGE else SGE
      Equal -> return $ if isFloat t1
        then FCmp FP.OEQ
        else ICmp IP.EQ
      NotEqual -> return $ if isFloat t1
        then FCmp FP.ONE
        else ICmp NE
      BinAnd -> if isFloat t1
        then throwError . ErrorString $ "BinAnd is not applicable to floats: " ++ show sr
        else return AST.And
      BinOr -> if isFloat t1
        then throwError . ErrorString $ "BinOr is not applicable to floats: " ++ show sr
        else return AST.Or
      Ast.Xor -> if isFloat t1
        then throwError . ErrorString $ "Xor is not applicable to floats: " ++ show sr
        else return AST.Xor
      LShift -> if isFloat t1
        then throwError . ErrorString $ "LShift is not applicable to floats: " ++ show sr
        else return $ Shl False False
      LogRShift -> if isFloat t1
        then throwError . ErrorString $ "LogRShift is not applicable to floats: " ++ show sr
        else return $ LShr False
      AriRShift -> if isFloat t1
        then throwError . ErrorString $ "LogRShift is not applicable to floats: " ++ show sr
        else return $ AShr False
      _ -> throwError . ErrorString $ show operator ++ " not supported for expressions of type " ++ show t1 ++ " at " ++ show sr

    else case t1 of -- Non-numerical case
      BoolT -> return . ICmp $ case operator of -- TODO: shortcutting &&/||
        Equal -> IP.EQ
        NotEqual -> IP.NE
      -- TODO: struct binary operators
  binOp llvmOperator res1 res2

binOp :: (Operand -> Operand -> InstructionMetadata -> Instruction) -> (Operand, Type) -> (Operand, Type) -> FuncGen (Operand, Type)
binOp operator (op1, t1) (op2, _) = do
  res <- instr (operator op1 op2 [], toLLVMType t1)
  return (res, t1)

findNameIndexInStruct :: String -> Type -> SourceRange -> FuncGen (Integer, Type)
findNameIndexInStruct mName (StructT fields) sr = case find (\(_, (n, _)) -> n == mName) $ zip [0..] fields of
  Just (i, (_, t)) -> return (i, t)
  Nothing -> throwError . ErrorString $ "Unknown member field " ++ mName ++ " in struct at " ++ show sr
findNameIndexInStruct _ _ sr = throwError . ErrorString $ "Attempt to access member field of non-struct type at " ++ show sr

finalizeBlock :: BasicBlock -> FuncGen ()
finalizeBlock b = finalizedBlocks %= ((b & blockInstrs %~ reverse) :)

finalizeAndReplaceWith :: BasicBlock -> FuncGen ()
finalizeAndReplaceWith b = (currentBlock <<.= b) >>= finalizeBlock

fresh :: FuncGen Name
fresh = liftM UnName $ nextFresh <<+= 1

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

isFloat :: Type -> Bool
isFloat F32 = True
isFloat F64 = True
isFloat _ = False

isUnsigned :: Type -> Bool
isUnsigned U8 = True
isUnsigned U16 = True
isUnsigned U32 = True
isUnsigned U64 = True
isUnsigned _ = False

isNum :: Type -> Bool
isNum I8 = True
isNum I16 = True
isNum I32 = True
isNum I64 = True
isNum n = isFloat n || isUnsigned n

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
      requestWithOperand . Right . ConstantOperand . C.GlobalReference (toFunctionType inTs outTs retty) . Name $ fname ++ show num
    (fname, inTs, outTs, retty) = case func of
      NormalSig n its ots -> (n, its, ots, T.void)
      ExprSig n its ot -> (n, its, [], toLLVMType ot)

extractNameFromCallableOperand :: CallableOperand -> Name
extractNameFromCallableOperand (Right (ConstantOperand (C.GlobalReference _ n))) = n

getFunctionOperand :: FuncSig -> GenState -> Maybe CallableOperand
getFunctionOperand sig state = case M.lookup sig $ _generated state of
  Just o -> Just o
  Nothing -> M.lookup sig $ _requested state

toFunctionType :: [Type] -> [Type] -> T.Type -> T.Type
toFunctionType inTs outTs retty = (\ts -> T.FunctionType retty ts False) $ toFunctionParams inTs outTs

toFunctionParams :: [Type] -> [Type] -> [T.Type]
{-toFunctionParams inTs outTs = (toScalarType <$> inTs) ++ (T.ptr . toScalarType <$> outTs)-} --TODO: handle this instead in codegen for function
toFunctionParams inTs outTs = T.ptr . toLLVMType <$> (inTs ++ outTs)

toLLVMType :: Type -> T.Type
toLLVMType t = fromMaybe composite $ M.lookup t typeMap
  where
    composite = case t of
      StructT parts -> T.StructureType False $ toLLVMType . snd <$> parts

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

typeSizeMap :: M.Map Type Word32
typeSizeMap = M.fromList
  [ (I8, 8)
  , (I16, 16)
  , (I32, 32)
  , (I64, 64)

  , (U8, 8)
  , (U16, 16)
  , (U32, 32)
  , (U64, 64)

  , (F32, 32)
  , (F64, 64)
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

nextNameNumber :: Functor f => (M.Map String Int -> f (M.Map String Int)) -> GenState -> f GenState
nextNameNumber inj state = (\nn -> state { _nextNameNumber = nn }) <$> inj (_nextNameNumber state)
{-# INLINE nextNameNumber #-}

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

blockInstrs :: Functor f => ([Named Instruction] -> f [Named Instruction]) -> BasicBlock -> f BasicBlock
blockInstrs inj (BasicBlock n i t) = (\is -> BasicBlock n is t) <$> inj i
{-# INLINE blockInstrs #-}

blockTerminator :: Functor f => (Named Terminator -> f (Named Terminator)) -> BasicBlock -> f BasicBlock
blockTerminator inj (BasicBlock n i t) = BasicBlock n i <$> inj t
{-# INLINE blockTerminator #-}

blockName :: Functor f => (Name-> f Name) -> BasicBlock -> f BasicBlock
blockName inj (BasicBlock n i t) = (\n' -> BasicBlock n' i t) <$> inj n
{-# INLINE blockName #-}

boolean :: a -> a -> Bool -> a
boolean a _ True = a
boolean _ a False = a

justErr :: MonadError e m => e -> Maybe a -> m a
justErr _ (Just a) = return a
justErr err Nothing = throwError err
