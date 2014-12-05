module CodeGen.Functions where

import Ast
import CodeGen.Basics
import CodeGen.FuncGen
import CodeGen.Statements
import CodeGen.Expressions
import Data.Maybe
import Data.Functor ((<$>))
import Control.Lens hiding (op, index, parts, transform)
import Control.Monad.State (get, put)
import LLVM.General.AST.Operand
import LLVM.General.AST.Name
import LLVM.General.AST.Global
import LLVM.General.AST.Instruction as I hiding (condition, index)
import qualified LLVM.General.AST.Type as T
import qualified LLVM.General.AST as AST
import qualified Data.Map as M

initialFuncState :: GenState -> FuncState
initialFuncState currGenState = FuncState currGenState Nothing Nothing (Ret Nothing []) M.empty 0 [] entryBlock
  where entryBlock = BasicBlock (Name "entry") [] . Do $ Ret Nothing []

generateFunction :: FuncSig -> CodeGen (Either ErrorMessage AST.Definition)
generateFunction sig@(NormalSig fName inTs outTs) = do
  currGenState <- get
  let generateBody = do
        mFunc <- uses (genState. source . to functionDefinitions) $ M.lookup fName
        (FuncDef innames outnames stmnt _) <- justErr (ErrorString $ "Function " ++ fName ++ " not found") mFunc

        (initLocals, params) <- generateInitialFunctionLocals innames inTs outnames outTs
        locals .= initLocals

        generateStatement stmnt
        constructFunctionDeclaration sig params T.void
  case runFuncGen (initialFuncState currGenState) generateBody of
    Left e -> return $ Left e
    Right (res, st) -> put (_genState st) >> return (Right res)

generateFunction sig@(ExprSig fName inTs outT) = do
  currGenState <- get
  let initState = FuncState currGenState Nothing Nothing (Br (Name "returnBlock") []) M.empty 0 [] entryBlock
      entryBlock = BasicBlock (Name "entry") [] . Do $ Br (Name "returnBlock") []
      retBlock = BasicBlock (Name "returnBlock") [] . Do $ Ret Nothing []
      generateBody = do
        (FuncDef innames [outname] stmnt sr) <- use (genState . source . to functionDefinitions . at fName) -- TODO: ugly death on incorrect number of outarguments
                                                >>= justErr (ErrorString $ "Function " ++ fName ++ " not found")

        (initLocals, params) <- generateInitialFunctionLocals innames inTs [] []
        locals .= initLocals

        generateStatement $ VarInit outname outT sr
        generateStatement stmnt

        finalizeAndReplaceWith retBlock
        (retOp, _) <- generateExpression (Variable outname undefined)
        currentBlock . blockTerminator .= (Do $ Ret (Just retOp) [])

        toLLVMType outT >>= constructFunctionDeclaration sig params
  case runFuncGen initState generateBody of
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

