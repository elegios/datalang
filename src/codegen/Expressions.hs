{-# LANGUAGE TupleSections #-}

module CodeGen.Expressions where

import Ast
import CodeGen.FuncGen
import CodeGen.Basics
import Data.Maybe
import Data.Functor ((<$>))
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
import qualified Data.Map as M

generateAssignableExpression :: Expression -> FuncGen (Operand, Type)
generateAssignableExpression (Variable vName sr) =
  use (locals . at vName) >>= justErr (ErrorString $ "Unknown variable " ++ vName ++ " at " ++ show sr)

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
  (op, t) <- use (locals . at vName) >>= justErr (ErrorString $ "Unknown variable " ++ vName ++ " at " ++ show sr)
  llvmtype <- toLLVMType t
  i <- instr (Load False op Nothing 0 [], llvmtype)
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
      Equal     -> twoway t (FCmp FP.OEQ) (ICmp IP.EQ)
      NotEqual  -> twoway t (FCmp FP.ONE) (ICmp NE)
      Plus      -> twoway t (FAdd NoFastMathFlags) (Add False False)
      Minus     -> twoway t (FSub NoFastMathFlags) (Sub False False)
      Times     -> twoway t (FMul NoFastMathFlags) (Mul False False)
      Divide    -> threeway t (FDiv NoFastMathFlags) (UDiv False) (SDiv False)
      Remainder -> threeway t (FRem NoFastMathFlags) URem SRem
      Lesser    -> threeway t (FCmp FP.OLT) (ICmp ULT) (ICmp SLT)
      Greater   -> threeway t (FCmp FP.OGT) (ICmp UGT) (ICmp SGT)
      LE        -> threeway t (FCmp FP.OLE) (ICmp ULE) (ICmp SLE)
      GE        -> threeway t (FCmp FP.OGE) (ICmp UGE) (ICmp SGE)
      BinAnd    -> nonfloat BinAnd t AST.And
      BinOr     -> nonfloat BinOr t AST.Or
      Ast.Xor   -> nonfloat Ast.Xor t AST.Xor
      LShift    -> nonfloat LShift t $ Shl False False
      LogRShift -> nonfloat LogRShift t $ LShr False
      AriRShift -> nonfloat AriRShift t $ AShr False
      _ -> throwError . ErrorString $ show operator ++ " not supported for expressions of type " ++ show t ++ " at " ++ show sr

    else case t of -- Non-numerical case
      BoolT -> return $ case operator of
        Equal    -> ICmp IP.EQ
        NotEqual -> ICmp IP.NE
        LongAnd  -> AST.And
        LongOr   -> AST.Or
      PointerT _ -> return $ case operator of
        Equal    -> ICmp IP.EQ
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

binOp :: LLVMOperator -> (Operand, Type) -> (Operand, Type) -> FuncGen (Operand, Type)
binOp operator (op1, t1) (op2, _) = do
  llvmt <- toLLVMType t1
  res <- instr (operator op1 op2 [], llvmt)
  return (res, t1)

type LLVMOperator = Operand -> Operand -> InstructionMetadata -> Instruction

twoway :: Type -> LLVMOperator -> LLVMOperator -> FuncGen LLVMOperator
twoway t f i = return $ if isFloat t then f else i

threeway :: Type -> LLVMOperator -> LLVMOperator -> LLVMOperator -> FuncGen LLVMOperator
threeway t f u i = return $ if isFloat t then f else if isUnsigned t then u else i

nonfloat :: BinOp -> Type -> LLVMOperator -> FuncGen LLVMOperator
nonfloat op t i = if isFloat t
  then throwError . ErrorString $ show op ++ " is not applicable to floats "
  else return i
