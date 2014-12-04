{-# LANGUAGE TupleSections #-}

module CodeGen where

-- TODO: Save a "stack trace" of requested functions, to make it easier to figure out why a specific function was requested.

import Ast
import Data.Maybe
import Data.Functor ((<$>))
import Data.List
import Data.Word
import Data.Generics.Uniplate.Data
import Control.Lens hiding (op, index, parts, transform)
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

type GenFuncs = M.Map FuncSig CallableOperand
data GenState = GenState
  { _generated :: GenFuncs
  , _requested :: GenFuncs
  , _nextNameNumber :: M.Map String Int
  , _structTypes :: M.Map [Type] (AST.Definition, T.Type)
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
emptyState reqs = GenState M.empty reqs M.empty M.empty []

data ErrorMessage = ErrorString String deriving Show

type CodeGen a = StateT GenState Identity a
type FuncGen a = StateT FuncState (ExceptT ErrorMessage Identity) a

runFuncGen :: FuncState -> FuncGen a -> Either ErrorMessage (a, FuncState)
runFuncGen initState = runIdentity . runExceptT .  flip runStateT initState

runCodeGen :: GenState -> CodeGen a -> (a, GenState)
runCodeGen initState = runIdentity . flip runStateT initState

generate :: Source -> GenFuncs -> Either [ErrorMessage] AST.Module
generate sourceToGen requests = case errs of
  [] -> Right $ AST.defaultModule { AST.moduleDefinitions = structDefs ++ defs }
  _ -> Left errs
  where
    (defs, resState) = runCodeGen (emptyState requests sourceToGen) generateFunctions 
    errs = _errors resState
    structDefs = map fst . M.elems $ _structTypes resState
    generateFunctions = do
      mreq <- use $ requested . to M.minViewWithKey
      maybe (return []) runGenerateFunction mreq
    runGenerateFunction ((func, _), _) = do
      eRes <- generateFunction func
      op <- requested . at func <<.= Nothing
      generated . at func .= op
      case eRes of
        Left err -> (errors %= (err:)) >> generateFunctions
        Right res -> (res:) <$> generateFunctions

initialFuncState :: GenState -> FuncState
initialFuncState currGenState = FuncState currGenState Nothing Nothing (Ret Nothing []) M.empty 0 [] entryBlock
  where entryBlock = BasicBlock (Name "entry") [] . Do $ Ret Nothing []

generateFunction :: FuncSig -> CodeGen (Either ErrorMessage AST.Definition)
generateFunction sig@(NormalSig fName inTs outTs) = do
  currGenState <- get
  let eit = runFuncGen (initialFuncState currGenState) $ do
        mFunc <- uses (genState. source . to functionDefinitions) $ M.lookup fName
        (FuncDef innames outnames stmnts _) <- justErr (ErrorString $ "Function " ++ fName ++ " not found") mFunc

        (initLocals, params) <- generateInitialFunctionLocals innames inTs outnames outTs
        locals .= initLocals

        generateFunctionBody stmnts
        constructFunctionDeclaration sig params T.void
  case eit of
    Left e -> return $ Left e
    Right (res, st) -> put (_genState st) >> return (Right res)

generateFunction sig@(ExprSig fName inTs outT) = do
  currGenState <- get
  let initState = FuncState currGenState Nothing Nothing (Br (Name "returnBlock") []) M.empty 0 [] entryBlock
      entryBlock = BasicBlock (Name "entry") [] . Do $ Br (Name "returnBlock") []
      retBlock = BasicBlock (Name "returnBlock") [] . Do $ Ret Nothing []
  let eit = runFuncGen initState $ do
        mFunc <- uses (genState . source . to functionDefinitions) $ M.lookup fName
        (FuncDef innames [outname] stmnts _) <- justErr (ErrorString $ "Function " ++ fName ++ " not found") mFunc -- TODO: ugly death on incorrect number of outarguments

        (initLocals, params) <- generateInitialFunctionLocals innames inTs [] []
        locals .= initLocals

        generateFunctionBody $ VarInit outname outT undefined : stmnts

        finalizeAndReplaceWith retBlock
        (retOp, _) <- generateExpression (Variable outname undefined)
        currentBlock . blockTerminator .= (Do $ Ret (Just retOp) [])

        toLLVMType outT >>= constructFunctionDeclaration sig params
  case eit of
    Left e -> return $ Left e
    Right (res, st) -> put (_genState st) >> return (Right res)

generateInitialFunctionLocals :: [String] -> [Type] -> [String] -> [Type] -> FuncGen (M.Map String (Operand, Type), [Parameter])
generateInitialFunctionLocals innames inTs outnames outTs = do
  llvmparams <- toFunctionParams inTs outTs
  let names = innames ++ outnames
      types = inTs ++ outTs
      llvmnames = Name <$> names

      params = zipWith3 Parameter llvmparams llvmnames (repeat [])

      paramLocals = zipWith LocalReference llvmparams llvmnames
      initialLocals = M.fromList . zip (innames ++ outnames) . zip paramLocals $ types
  return (initialLocals, params)

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
  realT <- ensureTopNotNamed t
  llvmtype <- toLLVMType realT
  op <- instr (Alloca llvmtype Nothing 0 [], T.ptr llvmtype)
  locals . at vName ?= (op, realT)
  generateFunctionBody stmnts

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
  inOps <- mapM generateAssignableExpression ins -- TODO: generate scalars when ins are scalars instead
  outOps <- mapM generateAssignableExpression outs
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

generateAssignableExpression (MemberAccess expression mName sr) =
  generateAssignableExpression expression >>= derefPointer >>= bottomGeneration
  where
    derefPointer (op, t) = do
      realT <- ensureTopNotNamed t
      case realT of
        PointerT innerT -> do
          llvmtype <- T.ptr <$> toLLVMType innerT
          innerOp <- instr (Load False op Nothing 0 [], llvmtype)
          derefPointer (innerOp, innerT)
        _ -> return (op, realT)
    bottomGeneration (bottomOp, bottomType) = do
      (index, t) <- findNameIndexInStruct mName bottomType sr
      realT <- ensureTopNotNamed t
      llvmtype <- T.ptr <$> toLLVMType realT
      op <- instr (I.GetElementPtr False bottomOp [constInt 0, constInt index] [], llvmtype)
      return (op, realT)
    constInt = ConstantOperand . C.Int 32

generateAssignableExpression (Un Deref expression sr) = do
  (expOp, PointerT t) <- generateExpression expression
  realT <- ensureTopNotNamed t
  return (expOp, realT)

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
    Just (op, t) -> do
      llvmtype <- toLLVMType t
      i <-  instr (Load False op Nothing 0 [], llvmtype)
      return (i, t)

generateExpression (MemberAccess expression mName sr) =
  generateExpression expression >>= derefPointer >>= bottomGeneration
  where
    derefPointer (op, t) = do
      realT <- ensureTopNotNamed t
      case realT of
        PointerT innerT -> do
          llvmtype <- toLLVMType innerT
          innerOp <- instr (Load False op Nothing 0 [], llvmtype)
          derefPointer (innerOp, innerT)
        _ -> return (op, realT)
    bottomGeneration (bottomOp, bottomType) = do
      (index, t) <- findNameIndexInStruct mName bottomType sr
      realT <- ensureTopNotNamed t
      llvmtype <- toLLVMType realT
      ptrOp <- instr (ExtractValue bottomOp [fromInteger index] [], llvmtype)
      return (ptrOp, realT)

generateExpression (ExprFunc fName expressions t sr) = do
  ops <- mapM generateExpression expressions
  funcOp <- requestFunction $ ExprSig fName (snd <$> ops) t
  llvmtype <- toLLVMType t
  retOp <- instr (Call False CC.C [] funcOp (zip (fst <$> ops) $ repeat []) [] [], llvmtype)
  return (retOp, t)

-- TODO: ugly deaths in generateExpression for UnOps
generateExpression (Un Deref expression sr) = do
  (expOp, PointerT t) <- generateExpression expression
  realT <- ensureTopNotNamed t
  llvmtype <- toLLVMType realT
  res <- instr (Load False expOp Nothing 0 [], llvmtype)
  return (res, realT)
generateExpression (Un AddressOf expression sr) =
  (_2 %~ PointerT) <$> generateAssignableExpression expression
generateExpression (Un operator expression sr) = do
  (expOp, t) <- generateExpression expression
  llvmtype <- toLLVMType t
  res <- instr . (, llvmtype) $ case operator of
    AriNegate -> if isFloat t
      then FSub NoFastMathFlags (zero t) expOp []
      else Sub False False (zero t) expOp []
    Not -> AST.Xor (one t) expOp []
    BinNegate -> AST.Xor (one t) expOp []
  return (res, t)
  where
    zero t = if isFloat t
      then ConstantOperand . C.Float $ F.Double 0
      else ConstantOperand $ C.Int size 0
      where size = fromJust $ M.lookup t typeSizeMap
    one t = ConstantOperand $ C.Int size 0
      where size = fromJust $ M.lookup t typeSizeMap

generateExpression (Bin operator exp1 exp2 sr) = do
  res1@(_, t1) <- generateExpression exp1
  case (t1, operator) of
    (StructT props, _) -> do
      res2 <- generateExpression exp2
      structBins res1 res2 props operator sr
    (_, ShortAnd) -> shortcuts res1 exp2 ShortAnd sr
    (_, ShortOr) -> shortcuts res1 exp2 ShortOr sr
    _ -> do
      res2@(_, t2) <- generateExpression exp2
      when (t1 /= t2) . throwError . ErrorString $ "The expressions around " ++ show operator ++ " at " ++ show sr ++ " have different types (" ++ show t1 ++ " != " ++ show t2 ++ ")"
      simpleBins res1 res2 t1 operator sr

simpleBins :: (Operand, Type) -> (Operand, Type) -> Type -> BinOp -> SourceRange -> FuncGen (Operand, Type)
simpleBins res1 res2 t operator sr = do
  llvmOperator <- if isNum t
    then case operator of
      Plus -> return $ if isFloat t then FAdd NoFastMathFlags else Add False False
      Minus -> return $ if isFloat t then FSub NoFastMathFlags else Sub False False
      Times -> return $ if isFloat t then FMul NoFastMathFlags else Mul False False
      Divide -> return $ if isFloat t
        then FDiv NoFastMathFlags else if isUnsigned t
          then UDiv False
          else SDiv False
      Remainder -> return $ if isFloat t
        then FRem NoFastMathFlags else if isUnsigned t
          then URem
          else SRem
      Lesser -> return $ if isFloat t
        then FCmp FP.OLT
        else ICmp $ if isUnsigned t then ULT else SLT
      Greater -> return $ if isFloat t
        then FCmp FP.OGT
        else ICmp $ if isUnsigned t then UGT else SGT
      LE -> return $ if isFloat t
        then FCmp FP.OLE
        else ICmp $ if isUnsigned t then ULE else SLE
      GE -> return $ if isFloat t
        then FCmp FP.OGE
        else ICmp $ if isUnsigned t then UGE else SGE
      Equal -> return $ if isFloat t
        then FCmp FP.OEQ
        else ICmp IP.EQ
      NotEqual -> return $ if isFloat t
        then FCmp FP.ONE
        else ICmp NE
      BinAnd -> if isFloat t
        then throwError . ErrorString $ "BinAnd is not applicable to floats: " ++ show sr
        else return AST.And
      BinOr -> if isFloat t
        then throwError . ErrorString $ "BinOr is not applicable to floats: " ++ show sr
        else return AST.Or
      Ast.Xor -> if isFloat t
        then throwError . ErrorString $ "Xor is not applicable to floats: " ++ show sr
        else return AST.Xor
      LShift -> if isFloat t
        then throwError . ErrorString $ "LShift is not applicable to floats: " ++ show sr
        else return $ Shl False False
      LogRShift -> if isFloat t
        then throwError . ErrorString $ "LogRShift is not applicable to floats: " ++ show sr
        else return $ LShr False
      AriRShift -> if isFloat t
        then throwError . ErrorString $ "AriRShift is not applicable to floats: " ++ show sr
        else return $ AShr False
      _ -> throwError . ErrorString $ show operator ++ " not supported for expressions of type " ++ show t ++ " at " ++ show sr

    else case t of -- Non-numerical case
      BoolT -> return $ case operator of
        Equal -> ICmp IP.EQ
        NotEqual -> ICmp IP.NE
        LongAnd -> AST.And
        LongOr -> AST.Or
      PointerT _ -> return $ case operator of
        Equal -> ICmp IP.EQ
        NotEqual -> ICmp IP.NE
  binOp llvmOperator res1 res2

shortcuts :: (Operand, Type) -> Expression -> BinOp -> SourceRange -> FuncGen (Operand, Type)
shortcuts (op1, _) exp2 operator sr = do
  block2 <- newBlock
  contBlock <- newBlock
  prevName <- use $ currentBlock . blockName
  let name2 = block2 ^. blockName
      contName = contBlock ^. blockName
      (trueName, falseName, shortResult) = case operator of
        ShortAnd -> (name2, contName, 0)
        ShortOr -> (contName, name2, 1)

  prevTerminator <- use $ currentBlock . blockTerminator
  currentBlock . blockTerminator .= (Do $ CondBr op1 trueName falseName [])

  finalizeAndReplaceWith block2
  (op2, _) <- generateExpression exp2
  currentBlock . blockTerminator .= (Do $ Br contName [])

  finalizeAndReplaceWith $ block2 & blockTerminator .~ prevTerminator
  op <- instr (Phi T.i1 [(ConstantOperand $ C.Int 1 shortResult, prevName), (op2, name2)] [], T.i1)
  return (op, BoolT)

structBins :: (Operand, Type) -> (Operand, Type) -> [(String, Type)] -> BinOp -> SourceRange -> FuncGen (Operand, Type)
-- TODO: ugly death upon operator that is not Equal or NotEqual for structs
structBins res1 res2 props operator sr = do
  first : bools <- mapM (loadProp res1 res2) . zip [0..] $ snd <$> props
  foldM (binOp andOr) first bools
  where
    andOr = case operator of
      Equal -> AST.And
      NotEqual -> AST.Or
    loadProp (op1, _) (op2, _) (index, t) = do
      realT <- ensureTopNotNamed t
      llvmtype <- toLLVMType realT
      comp1 <- (, realT) <$> instr (ExtractValue op1 [index] [], llvmtype)
      comp2 <- (, realT) <$> instr (ExtractValue op2 [index] [], llvmtype)
      case realT of
        StructT innerProps -> structBins comp1 comp2 innerProps operator sr
        _ -> simpleBins comp1 comp2 realT operator sr

binOp :: (Operand -> Operand -> InstructionMetadata -> Instruction) -> (Operand, Type) -> (Operand, Type) -> FuncGen (Operand, Type)
binOp operator (op1, t1) (op2, _) = do
  llvmt <- toLLVMType t1
  res <- instr (operator op1 op2 [], llvmt)
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
      llvmt <- toFunctionType inTs outTs retty
      requestWithOperand . Right . ConstantOperand . C.GlobalReference llvmt . Name $ fname ++ show num
    (fname, inTs, outTs, retty) = case func of
      NormalSig n its ots -> (n, its, ots, Nothing)
      ExprSig n its ot -> (n, its, [], Just ot)

extractNameFromCallableOperand :: CallableOperand -> Name
extractNameFromCallableOperand (Right (ConstantOperand (C.GlobalReference _ n))) = n

getFunctionOperand :: FuncSig -> GenState -> Maybe CallableOperand
getFunctionOperand sig state = case M.lookup sig $ _generated state of
  Just o -> Just o
  Nothing -> M.lookup sig $ _requested state

toFunctionType :: [Type] -> [Type] -> Maybe Type -> FuncGen T.Type
toFunctionType inTs outTs retty = do
  llvmretty <- maybe (return T.void) toLLVMType retty
  ts <- toFunctionParams inTs outTs
  return $ T.FunctionType llvmretty ts False

toFunctionParams :: [Type] -> [Type] -> FuncGen [T.Type]
-- toFunctionParams inTs outTs = do --TODO: deal with this instead when inargs are properly marked as immutable
--   its <- mapM toLLVMType inTs
--   ots <- mapM toLLVMType outTs
--   return $ its ++ (T.ptr <$> ots)
toFunctionParams inTs outTs = (map T.ptr <$>) . mapM toLLVMType $ inTs ++ outTs

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

toLLVMType :: Type -> FuncGen T.Type
toLLVMType nt = ensureTopNotNamed nt >>= \t -> case t of
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
        inners <- mapM (toLLVMType . snd) props
        let struct = AST.TypeDefinition llvmname . Just $ T.StructureType False inners
        genState . structTypes . at (snd <$> props) ?= (struct, llvmtype)
        return llvmtype
  PointerT inner -> T.ptr <$> toLLVMType inner
  _ -> case M.lookup t typeMap of
    Just llvmtype -> return llvmtype
    Nothing -> throwError . ErrorString $ "Missed a case in the compiler, there is a type that cannot be converted to an LLVM type: " ++ show t

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

structTypes :: Functor f => (M.Map [Type] (AST.Definition, T.Type) -> f (M.Map [Type] (AST.Definition, T.Type))) -> GenState -> f GenState
structTypes inj state = (\st -> state { _structTypes = st }) <$> inj (_structTypes state)
{-# INLINE structTypes #-}

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
