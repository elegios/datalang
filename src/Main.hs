{-# LANGUAGE OverloadedStrings #-}

module Main where

import Data.String (IsString, fromString)
import qualified LLVM.General.AST as AST
import qualified LLVM.General.AST.Global as G
import qualified LLVM.General.AST.Type as T
import qualified LLVM.General.AST.Name as Name
import qualified LLVM.General.AST.Instruction as I
import qualified LLVM.General.AST.Operand as O
import qualified LLVM.General.AST.CallingConvention as CC
import qualified LLVM.General.AST.Constant as C
import qualified LLVM.General.Module as M
import LLVM.General.Context
import LLVM.General.Target
import Control.Monad.Except (runExceptT, ExceptT(..))

main = runJIT example

example = AST.defaultModule
  { AST.moduleName = "exampleModule"
  , AST.moduleDefinitions = [
      putDef,
      exampleDef
    ]
  }

exampleDef = AST.GlobalDefinition $ G.functionDefaults
  { G.returnType = T.VoidType
  , G.name = "main"
  , G.basicBlocks = [ exampleBlock ]
  }

exampleBlock = AST.BasicBlock "entryBlock" [putlnCall] (I.Do $ I.Ret Nothing [])

putDef = AST.GlobalDefinition $ G.functionDefaults
  { G.name = "putchar"
  , G.parameters = ([G.Parameter (T.IntegerType 32) "c" []], False)
  , G.returnType = T.IntegerType 32
  }

putln = O.ConstantOperand $ C.GlobalReference (T.FunctionType (T.IntegerType 32) [T.IntegerType 32] False) "putchar"

putlnCall = I.Do $ I.Call False CC.C [] (Right putln) [(O.ConstantOperand $ C.Int 32 65,[])] [] []


instance IsString Name.Name where
  fromString = Name.Name

runJIT :: AST.Module -> IO (Either String ())
runJIT mod = withContext $ \context ->
    runExceptT $ M.withModuleFromAST context mod $ \m ->
      failIO . withDefaultTargetMachine $ \mac -> failIO $ M.writeObjectToFile mac (M.File "test.o") m

failIO :: ExceptT String IO a -> IO a
failIO e = runExceptT e >>= \r -> case r of
  Left err -> fail err
  Right a -> return a

