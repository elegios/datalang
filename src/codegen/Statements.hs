module CodeGen.Statements where

import Ast
import CodeGen.Basics
import CodeGen.FuncGen
import CodeGen.Expressions
import Data.Maybe
import Data.Functor ((<$>))
import Control.Lens hiding (op, index, parts, transform)
import Control.Monad.Except
import LLVM.General.AST.Instruction as I hiding (condition, index)
import qualified LLVM.General.AST.Type as T
import qualified LLVM.General.AST.CallingConvention as CC

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
