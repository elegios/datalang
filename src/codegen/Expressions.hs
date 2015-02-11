{-# LANGUAGE TupleSections #-}

module CodeGen.Expressions (generateExpression, toImmutable) where

import Ast
import CodeGen.FuncGen
import CodeGen.Basics
import Data.Functor ((<$>))
import Data.Word (Word32)
import Control.Lens hiding (op, index, parts, transform)
import Control.Monad.Except
import LLVM.General.AST.Operand
import LLVM.General.AST.IntegerPredicate as IP
import LLVM.General.AST.Instruction as I hiding (condition, index)
import qualified LLVM.General.AST.FloatingPointPredicate as FP
import qualified LLVM.General.AST.Type as T
import qualified LLVM.General.AST.CallingConvention as CC
import qualified LLVM.General.AST.Constant as C
import qualified LLVM.General.AST as AST
import qualified LLVM.General.AST.Float as F

type LLVMOperator = Operand -> Operand -> InstructionMetadata -> Instruction

generateExpression :: Expression -> FuncGen FuncGenOperand
generateExpression (Variable vName sr) =
  use (locals . at vName) >>= justErr (ErrorString $ "Compiler error: Unknown variable " ++ vName ++ " at " ++ show sr)

generateExpression (MemberAccess expression mName sr) =
  generateExpression expression >>= derefPointer >>= bottomGeneration
  where
    derefPointer (op, t, mutable) = do
      realT <- ensureTopNotNamed t
      case realT of
        PointerT innerT -> do
          llvmtype <- toLLVMType mutable innerT
          innerOp <- instr (Load False op Nothing 0 [], llvmtype)
          derefPointer (innerOp, innerT, mutable)
        _ -> return (op, realT, mutable)
    bottomGeneration (bottomOp, bottomType, mutable) = do
      (index, t) <- findMemberIndex mName bottomType sr
      realT <- ensureTopNotNamed t
      llvmtype <- toLLVMType mutable realT
      op <- instr (accessOp bottomOp index mutable, llvmtype)
      return (op, realT, mutable)
    accessOp bottomOp index mutable = if mutable
      then I.GetElementPtr False bottomOp [constInt 0, constInt index] []
      else ExtractValue bottomOp [fromInteger index] []
    constInt = ConstantOperand . C.Int 32

generateExpression (Subscript chunk index _) = do
  c@(_, Memorychunk _ hasCap innerT, mutable) <- generateExpression chunk
  (chunkOp, _, _) <- toImmutable c
  llvmtype <- toLLVMType True innerT
  ptrOp <- instr (ExtractValue chunkOp [boolean 2 1 hasCap] [], llvmtype)
  (indexOp, _, _) <- generateExpression index >>= toImmutable
  elementOp <- instr (I.GetElementPtr False ptrOp [indexOp] [], llvmtype)
  boolean return toImmutable mutable (elementOp, innerT, True)

generateExpression (ExprLit lit _) = case lit of
  ILit val t _ -> do
    t' <- ensureTopNotNamed t
    return (ConstantOperand $ C.Int (getSize t') val, t', False)
  FLit val t _ -> do
    t' <- ensureTopNotNamed t
    return (ConstantOperand . C.Float $ F.Double val, t', False)
  BLit val _ -> return (ConstantOperand . C.Int 1 $ boolean 1 0 val, BoolT, False)
  Null t _ -> do
    llvmt <- toLLVMType False t
    t' <- ensureTopNotNamed t
    return (ConstantOperand $ C.Null llvmt, t', False)
  Undef t _ -> do
    llvmt <- toLLVMType False t
    t' <- ensureTopNotNamed t
    return (ConstantOperand $ C.Undef llvmt, t', False)

generateExpression (FuncCall fName expressions t _) = do
  ops <- mapM (generateExpression >=> toImmutable) expressions
  retty <- ensureTopNotNamed t
  funcOp <- requestFunction $ FuncSig fName (opType <$> ops) retty
  llvmtype <- toLLVMType False t
  retOp <- instr (Call False CC.C [] funcOp (zip (opOp <$> ops) $ repeat []) [] [], llvmtype)
  return (retOp, retty, False)

generateExpression (Un Deref expression _) = do
  (expOp, PointerT t, mutable) <- generateExpression expression
  realT <- ensureTopNotNamed t
  llvmtype <- toLLVMType mutable realT
  op <- instr (Load False expOp Nothing 0 [], llvmtype)
  return (op, realT, mutable)

generateExpression (Un AddressOf expression _) = do
  (op, t, True) <- generateExpression expression -- TODO: ugly death on expression not being mutable
  return (op, PointerT t, False)

generateExpression (Un operator expression _) = do
  (expOp, t, _) <- generateExpression expression >>= toImmutable
  llvmtype <- toLLVMType False t
  res <- instr . (, llvmtype) . (\f -> f expOp []) $ case operator of
    AriNegate -> if isFloat t
      then FSub NoFastMathFlags (zero t)
      else Sub False False (zero t)
    Not -> AST.Xor (ones t)
    BinNegate -> AST.Xor (ones t)
  return (res, t, False)
  where
    zero t = if isFloat t
      then ConstantOperand . C.Float $ F.Double 0
      else ConstantOperand $ C.Int (getSize t) 0
    ones t = ConstantOperand $ C.Int (getSize t) (-1) -- FIXME: examine the correctness of this

generateExpression (Bin operator exp1 exp2 sr) = do
  res1@(_, t1, _) <- generateExpression exp1 >>= toImmutable
  case (t1, operator) of
    (StructT props, _) -> do
      res2 <- generateExpression exp2 >>= toImmutable
      structBins res1 res2 props operator sr
    (_, ShortAnd) -> shortcuts res1 exp2 ShortAnd sr
    (_, ShortOr) -> shortcuts res1 exp2 ShortOr sr
    _ -> do
      res2@(_, t2, _) <- generateExpression exp2 >>= toImmutable
      when (t1 /= t2) . throwError . ErrorString $ "Compiler error: The expressions around " ++ show operator ++ " at " ++ show sr ++ " have different types (" ++ show t1 ++ " != " ++ show t2 ++ ")"
      simpleBins res1 res2 t1 operator sr

-- NOTE: the initial toLLVMType call ensures that any contained structtype exists as a definition
generateExpression (Zero t) = toLLVMType False t >> (, t, False) . ConstantOperand <$> generateZero t
  where
    generateZero :: Type -> FuncGen C.Constant
    generateZero named@NamedT{} = ensureTopNotNamed named >>= generateZero
    generateZero (StructT ps) = do
      Just (AST.TypeDefinition n _, _) <- use (genState . structTypes . at (snd <$> ps))
      C.Struct (Just n) False <$> mapM (generateZero . snd) ps
    generateZero (PointerT it) = C.Null <$> toLLVMType False it
    generateZero BoolT = return $ C.Int 1 0
    generateZero (FloatT S32) = return . C.Float $ F.Single 0
    generateZero (FloatT S64) = return . C.Float $ F.Double 0
    generateZero nt = return $ C.Int (getSize nt) 0

simpleBins :: FuncGenOperand -> FuncGenOperand -> Type -> BinOp -> SourceRange -> FuncGen FuncGenOperand
simpleBins res1 res2 t operator sr =
  makeOp res1 res2 =<< if isNum t
    then twoway $ case operator of
      Equal     -> (FCmp FP.OEQ, ICmp IP.EQ)
      NotEqual  -> (FCmp FP.ONE, ICmp IP.NE)
      Plus      -> (FAdd NoFastMathFlags, Add False False)
      Minus     -> (FSub NoFastMathFlags, Sub False False)
      Times     -> (FMul NoFastMathFlags, Mul False False)
      Divide    -> (FDiv NoFastMathFlags, SDiv False)
      Remainder -> (FRem NoFastMathFlags, SRem)
      Lesser    -> (FCmp FP.OLT, ICmp SLT)
      Greater   -> (FCmp FP.OGT, ICmp SGT)
      LE        -> (FCmp FP.OLE, ICmp SLE)
      GE        -> (FCmp FP.OGE, ICmp SGE)
      _         -> err

    else case t of -- Non-numerical case
      UIntT _ -> return $ case operator of
        Equal     -> ICmp IP.EQ
        NotEqual  -> ICmp IP.NE
        BinAnd    -> AST.And
        BinOr     -> AST.Or
        Ast.Xor   -> AST.Xor
        LShift    -> Shl False False
        LogRShift -> LShr False
        AriRShift -> AShr False
        _         -> err
      BoolT -> return $ case operator of
        Equal    -> ICmp IP.EQ
        NotEqual -> ICmp IP.NE
        LongAnd  -> AST.And
        LongOr   -> AST.Or
        _        -> err
      PointerT _ -> return $ case operator of
        Equal    -> ICmp IP.EQ
        NotEqual -> ICmp IP.NE
        _        -> err
  where
    err = error $ "Compiler error: operator " ++ show operator ++ " is not valid for type " ++ show t ++ " (at " ++ show sr ++ ")"
    twoway = return . boolean fst snd (isFloat t)
    makeOp o1 o2 op = binOp op o1 o2

shortcuts :: FuncGenOperand -> Expression -> BinOp -> SourceRange -> FuncGen FuncGenOperand
shortcuts (op1, _, _) exp2 operator _ = do
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
  (op2, _, _) <- generateExpression exp2 >>= toImmutable
  currentBlock . blockTerminator .= (Do $ Br contName [])

  finalizeAndReplaceWith $ block2 & blockTerminator .~ prevTerminator
  op <- instr (Phi T.i1 [(ConstantOperand $ C.Int 1 shortResult, prevName), (op2, name2)] [], T.i1)
  return (op, BoolT, False)

structBins :: FuncGenOperand -> FuncGenOperand -> [(String, Type)] -> BinOp -> SourceRange -> FuncGen FuncGenOperand
structBins res1 res2 props operator sr = do
  first : bools <- mapM (loadProp res1 res2) . zip [0..] $ snd <$> props
  foldM (binOp andOr) first bools
  where
    andOr = case operator of
      Equal -> AST.And
      NotEqual -> AST.Or
    loadProp (op1, _, _) (op2, _, _) (index, t) = do
      realT <- ensureTopNotNamed t
      llvmtype <- toLLVMType False realT
      comp1 <- (, realT, False) <$> instr (ExtractValue op1 [index] [], llvmtype)
      comp2 <- (, realT, False) <$> instr (ExtractValue op2 [index] [], llvmtype)
      case realT of
        StructT innerProps -> structBins comp1 comp2 innerProps operator sr
        _ -> simpleBins comp1 comp2 realT operator sr

binOp :: LLVMOperator -> FuncGenOperand -> FuncGenOperand -> FuncGen FuncGenOperand
binOp operator (op1, t1, _) (op2, _, _) = do
  llvmt <- toLLVMType False t1
  res <- instr (operator op1 op2 [], llvmt)
  return (res, t1, False)

toImmutable :: FuncGenOperand -> FuncGen FuncGenOperand
toImmutable res@(_, _, False) = return res
toImmutable (op, t, True) = do
  llvmtype <- toLLVMType False t
  (, t, False) <$> instr (Load False op Nothing 0 [], llvmtype)

isFloat :: Type -> Bool
isFloat (FloatT _) = True
isFloat _ = False

isNum :: Type -> Bool
isNum (IntT _) = True
isNum n = isFloat n

getSize :: Type -> Word32
getSize (IntT s) = sizeToWord32 s
getSize (UIntT s) = sizeToWord32 s
getSize (FloatT s) = sizeToWord32 s
