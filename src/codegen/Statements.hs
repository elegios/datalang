{-# LANGUAGE TupleSections #-}

module CodeGen.Statements where

import Ast
import CodeGen.Basics
import CodeGen.FuncGen
import CodeGen.Expressions
import Data.Functor ((<$>))
import Control.Applicative ((<*>))
import Control.Lens hiding (op, index, parts, transform)
import Control.Monad
import LLVM.General.AST.Instruction as I hiding (condition, index)
import qualified LLVM.General.AST.Type as T
import qualified LLVM.General.AST.CallingConvention as CC

generateStatement :: Statement -> FuncGen ()
generateStatement (VarInit vName t True _) = do
  realT <- ensureTopNotNamed t
  llvmtypeToAllocate <- toLLVMType False realT
  op <- instr (Alloca llvmtypeToAllocate Nothing 0 [], T.ptr llvmtypeToAllocate)
  locals . at vName ?= (op, realT, True)

generateStatement (Defer stmnt _) = do
  defers . defersAll %= (stmnt :)
  defers . defersLoop %= (stmnt :)
  defers . defersScope %= (stmnt :)

generateStatement (Terminator t sr) = do
  (term, deferred) <- case t of
    Return -> (,) <$> use retTerminator <*> use (defers . defersAll)
    _ -> do
      target <- use (boolean breakTarget continueTarget $ t == Break) >>= justErr (ErrorString $ "Cannot break or continue at " ++ show sr ++ ", no loop.")
      (Br target [], ) <$> use (defers . defersLoop)
  mapM_ generateStatement deferred
  currentBlock . blockTerminator .= Do term

generateStatement (Scope inner _) = do
  prevLocals <- use locals
  prevDefers <- use defers
  defers . defersScope .= []

  mapM_ generateStatement inner

  use (defers . defersScope) >>= mapM_ generateStatement
  defers .= prevDefers
  locals .= prevLocals

generateStatement (ShallowCopy assignee expression _) = do
  (assOp, _, True) <- generateExpression assignee
  (expOp, _, _) <- generateExpression expression >>= toImmutable
  uinstr $ Store False assOp expOp Nothing 0 []

generateStatement (FuncCall fName ins outs _) = do
  inOps <- mapM (generateExpression >=> toImmutable) ins
  outOps <- mapM generateExpression outs -- TODO: death in llvm if not all outops are mutable
  funcOp <- requestFunction $ NormalSig fName (opType <$> inOps) (opType <$> outOps)
  uinstr $ Call False CC.C [] funcOp (zip (map opOp $ inOps ++ outOps) $ repeat []) [] []

generateStatement (While condition stmnt _) = do
  prevDefers <- use defers
  defers . defersLoop .= []

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
  (condOp, _, _) <- generateExpression condition >>= toImmutable
  currentBlock . blockTerminator .= (Do $ CondBr condOp bodyName nextName [])

  finalizeAndReplaceWith $ bodyBlock & blockTerminator .~ (Do $ Br condName [])
  generateStatement stmnt

  finalizeAndReplaceWith $ nextBlock & blockTerminator .~ prevTerminator
  breakTarget .= prevBreakTarget
  continueTarget .= prevContinueTarget

  use (defers . defersLoop) >>= mapM_ generateStatement
  defers .= prevDefers

generateStatement (If condition thenStmnt mElseStmnt _) = do
  thenBlock <- newBlock
  elseBlock <- newBlock
  nextBlock <- newBlock
  let nextName = nextBlock ^. blockName
      thenName = thenBlock ^. blockName
      elseName = elseBlock ^. blockName

  (condOp, _, _) <- generateExpression condition >>= toImmutable
  prevTerminator <- currentBlock . blockTerminator <<.= (Do $ CondBr condOp thenName elseName [])

  finalizeAndReplaceWith $ thenBlock & blockTerminator .~ (Do $ Br nextName [])
  generateStatement thenStmnt

  finalizeAndReplaceWith $ elseBlock & blockTerminator .~ (Do $ Br nextName [])
  maybe (return ()) generateStatement mElseStmnt

  finalizeAndReplaceWith $ nextBlock & blockTerminator .~ prevTerminator
