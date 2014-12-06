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

generateExpression :: Expression -> FuncGen FuncGenOperand
generateExpression (Variable vName sr) =
  use (locals . at vName) >>= justErr (ErrorString $ "Unknown variable " ++ vName ++ " at " ++ show sr)

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
      (index, t) <- findNameIndexInStruct mName bottomType sr
      realT <- ensureTopNotNamed t
      llvmtype <- toLLVMType mutable realT
      op <- instr (accessOp bottomOp index mutable, llvmtype)
      return (op, realT, mutable)
    accessOp bottomOp index mutable = if mutable
      then I.GetElementPtr False bottomOp [constInt 0, constInt index] []
      else ExtractValue bottomOp [fromInteger index] []
    constInt = ConstantOperand . C.Int 32

generateExpression (Un Deref expression sr) = do
  (expOp, PointerT t, mutable) <- generateExpression expression
  realT <- ensureTopNotNamed t
  llvmtype <- toLLVMType mutable realT
  op <- instr (Load False expOp Nothing 0 [], llvmtype)
  return (op, realT, mutable)

generateExpression (ExprLit lit sr) = return $ case lit of
  ILit val t -> (ConstantOperand $ C.Int size val, t, False)
    where size = fromJust $ M.lookup t typeSizeMap
  FLit val t -> (ConstantOperand . C.Float $ F.Double val, t, False)
  BLit val -> (ConstantOperand . C.Int 1 $ boolean 1 0 val, BoolT, False)

generateExpression (ExprFunc fName expressions t sr) = do
  ops <- mapM (generateExpression >=> toImmutable) expressions
  retty <- ensureTopNotNamed t
  funcOp <- requestFunction $ ExprSig fName (opType <$> ops) retty
  llvmtype <- toLLVMType False t
  retOp <- instr (Call False CC.C [] funcOp (zip (opOp <$> ops) $ repeat []) [] [], llvmtype)
  return (retOp, t, False)

generateExpression (Un AddressOf expression sr) = do
  (op, t, True) <- generateExpression expression -- TODO: ugly death on expression not being mutable
  return (op, PointerT t, False)

generateExpression (Un operator expression sr) = do
  (expOp, t, _) <- generateExpression expression >>= toImmutable
  llvmtype <- toLLVMType False t
  res <- instr . (, llvmtype) . (\f -> f expOp []) $ case operator of
    AriNegate -> if isFloat t
      then FSub NoFastMathFlags (zero t)
      else Sub False False (zero t)
    Not -> AST.Xor (one t)
    BinNegate -> AST.Xor (one t)
  return (res, t, False)
  where
    zero t = if isFloat t
      then ConstantOperand . C.Float $ F.Double 0
      else ConstantOperand $ C.Int size 0
      where size = fromJust $ M.lookup t typeSizeMap
    one t = ConstantOperand $ C.Int size 0
      where size = fromJust $ M.lookup t typeSizeMap

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
      when (t1 /= t2) . throwError . ErrorString $ "The expressions around " ++ show operator ++ " at " ++ show sr ++ " have different types (" ++ show t1 ++ " != " ++ show t2 ++ ")"
      simpleBins res1 res2 t1 operator sr

simpleBins :: FuncGenOperand -> FuncGenOperand -> Type -> BinOp -> SourceRange -> FuncGen FuncGenOperand
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

shortcuts :: FuncGenOperand -> Expression -> BinOp -> SourceRange -> FuncGen FuncGenOperand
shortcuts (op1, _, _) exp2 operator sr = do
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
-- TODO: ugly death upon operator that is not Equal or NotEqual for structs
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

type LLVMOperator = Operand -> Operand -> InstructionMetadata -> Instruction

twoway :: Type -> a -> a -> FuncGen a
twoway t f i = return $ if isFloat t then f else i

threeway :: Type -> a -> a -> a -> FuncGen a
threeway t f u i = return $ if isFloat t then f else if isUnsigned t then u else i

nonfloat :: BinOp -> Type -> a -> FuncGen a
nonfloat op t i = if isFloat t
  then throwError . ErrorString $ show op ++ " is not applicable to floats "
  else return i

toImmutable :: FuncGenOperand -> FuncGen FuncGenOperand
toImmutable res@(_, _, False) = return res
toImmutable (op, t, True) = do
  llvmtype <- toLLVMType False t
  (, t, False) <$> instr (Load False op Nothing 0 [], llvmtype)
