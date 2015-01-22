{-# LANGUAGE TupleSections #-}

module CodeGen.Functions (generateFunction) where

import Ast
import CodeGen.Basics
import CodeGen.FuncGen
import CodeGen.Statements
import CodeGen.Expressions
import Data.Char (isLower)
import Data.Maybe
import Data.Functor ((<$>))
import Control.Lens hiding (op, index, parts, transform)
import Control.Monad.State (get, put)
import Control.Monad
import Control.Monad.Except (throwError)
import LLVM.General.AST.Operand
import LLVM.General.AST.Name
import LLVM.General.AST.Global
import LLVM.General.AST.Instruction as I hiding (condition, index)
import qualified LLVM.General.AST.Type as T
import qualified LLVM.General.AST.Constant as C
import qualified LLVM.General.AST as AST
import qualified Data.Map as M

initialFuncState :: GenState -> FuncState
initialFuncState currGenState = FuncState currGenState Nothing Nothing (Ret Nothing []) M.empty M.empty 0 [] entryBlock (Defers [] [] [])
  where entryBlock = BasicBlock (Name "entry") [] . Do $ Ret Nothing []

generateFunction :: FuncSig -> CodeGen (Either ErrorMessage AST.Definition)
generateFunction sig@(NormalSig fName inTs outTs) = do
  currGenState <- get
  let generateBody = do
        (FuncDef inTSpec outTSpec _ innames outnames stmnt _) <-
          use (genState . source . to functionDefinitions . at fName) >>=
          justErr (ErrorString $ "Compiler error: Function " ++ fName ++ " not found")

        zipWithM_ defineTypeVariable inTs inTSpec
        zipWithM_ defineTypeVariable outTs outTSpec

        (initLocals, params) <- generateInitialFunctionLocals innames inTs outnames outTs
        locals .= initLocals

        generateStatement stmnt
        constructFunctionDeclaration sig params T.void
  case runFuncGen (initialFuncState currGenState) generateBody of
    Left e -> return $ Left e
    Right (res, st) -> put (_genState st) >> return (Right res)

generateFunction sig@(ExprSig fName inTs outT) = do
  currGenState <- get
  let initState = FuncState currGenState Nothing Nothing (Br (Name "returnBlock") []) M.empty M.empty 0 [] entryBlock (Defers [] [] [])
      entryBlock = BasicBlock (Name "entry") [] . Do $ Br (Name "returnBlock") []
      retBlock = BasicBlock (Name "returnBlock") [] . Do $ Ret Nothing []
      generateBody = do
        (FuncDef inTSpec [outTSpec] _ innames [outname] stmnt sr) <-
          use (genState . source . to functionDefinitions . at fName)
          >>= justErr (ErrorString $ "Compiler error: Function " ++ fName ++ " not found")

        zipWithM_ defineTypeVariable inTs inTSpec
        defineTypeVariable outT outTSpec

        (initLocals, params) <- generateInitialFunctionLocals innames inTs [] []
        locals .= initLocals

        generateStatement $ VarInit True outname outT (Zero outT) sr
        generateStatement stmnt

        finalizeAndReplaceWith retBlock
        (retOp, _, _) <- generateExpression (Variable outname undefined) >>= toImmutable
        currentBlock . blockTerminator .= (Do $ Ret (Just retOp) [])

        toLLVMType False outT >>= constructFunctionDeclaration sig params
  case runFuncGen initState generateBody of
    Left e -> return $ Left e
    Right (res, st) -> put (_genState st) >> return (Right res)

generateInitialFunctionLocals :: [String] -> [Type] -> [String] -> [Type] -> FuncGen (M.Map String FuncGenOperand, [Parameter])
generateInitialFunctionLocals innames inTs outnames outTs = do
  llvmparams <- toFunctionParams inTs outTs
  let names = innames ++ outnames
      types = map (\t -> (, t, False)) inTs ++ map (\t -> (, t, True)) outTs
      llvmnames = Name <$> names

      params = zipWith3 Parameter llvmparams llvmnames (repeat [])

      paramLocals = zipWith LocalReference llvmparams llvmnames
      initialLocals = M.fromList . zip (innames ++ outnames) . zipWith ($) types $ paramLocals
  return (initialLocals, params)

constructFunctionDeclaration :: FuncSig -> [Parameter] -> T.Type -> FuncGen AST.Definition
constructFunctionDeclaration sig params retty = do
  use currentBlock >>= finalizeBlock
  blocks <- use finalizedBlocks
  mOpName <- uses (genState . requested . at sig) $ fmap extractName
  return . AST.GlobalDefinition $ functionDefaults
    { name = fromJust mOpName
    , parameters = (params, False)
    , basicBlocks = reverse blocks
    , returnType = retty
    }
  where extractName (Right (ConstantOperand (C.GlobalReference _ n))) = n

defineTypeVariable :: Type -> Type -> FuncGen ()
defineTypeVariable t (NamedT n@(c:_) []) | isLower c = typeVariables . at n ?= t
defineTypeVariable (StructT ps1) (StructT ps2)
  | ps1names == ps2names = zipWithM_ defineTypeVariable ps1ts ps2ts
  where
    ps1names = map fst ps1
    ps2names = map fst ps2
    ps1ts = map snd ps1
    ps2ts = map snd ps2
defineTypeVariable (PointerT t1) (PointerT t2) = defineTypeVariable t1 t2
defineTypeVariable (NamedT n1 ts1) (NamedT n2 ts2)
  | n1 == n2 = zipWithM_ defineTypeVariable ts1 ts2
defineTypeVariable t1 t2
  | t1 == t2 = return ()
  | otherwise = throwError . ErrorString $ "Compiler error: Could not define all typevariables, " ++ show t1 ++ " and " ++ show t2 ++ " should have been equal"
