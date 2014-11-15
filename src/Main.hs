{-# LANGUAGE OverloadedStrings #-}

module Main where

import CodeGen
import Ast
import Data.String (IsString, fromString)
import qualified Data.Map as Map
import qualified LLVM.General.AST as AST
import qualified LLVM.General.AST.Global as G
import qualified LLVM.General.AST.Type as T
import qualified LLVM.General.AST.Name as Name
import qualified LLVM.General.AST.Instruction as I
import qualified LLVM.General.AST.Operand as O
import qualified LLVM.General.AST.CallingConvention as CC
import qualified LLVM.General.AST.Constant as C
import qualified LLVM.General.Module as M
import LLVM.General.PrettyPrint
import LLVM.General.Context
import LLVM.General.Target
import Control.Monad.Except (runExceptT, ExceptT(..))

main = case generate ast (Map.fromList [(requestedSig, Right . O.ConstantOperand . C.GlobalReference (toFunctionType [] [] $ toLLVMType I32) $ "main")]) of
  Left errs -> putStrLn "errors: " >> print errs
  Right mod -> putStrLn (showPretty mod) >> writeObjectFile mod >> putStrLn "result: " >> printModule mod
  where
    {-(requestedSig, ast) = (NormalSig "main" [] [], testAst)-}
    (requestedSig, ast) = (ExprSig "main" [] I32, exprAst)

testAst :: Source
testAst = Source
  { functionDefinitions =
    [ ("main", FuncDef [] []
      [ VarInit "a" U64 sr
      , ShallowCopy (Variable "a" sr) (Bin Plus (Variable "a" sr) (ExprLit (ILit 4 U64) sr) sr) sr
      , While (Bin Lesser (Variable "a" sr) (ExprLit (ILit 10 U64) sr) sr) (Scope
        [ ShallowCopy (Variable "a" sr) (Bin Times (Variable "a" sr) (ExprLit (ILit 2 U64) sr) sr) sr
        ] sr) sr
      , While (Bin Lesser (Variable "a" sr) (ExprLit (ILit 1000000000 U64) sr) sr) (Scope
        [ ShallowCopy (Variable "a" sr) (Bin Plus (Variable "a" sr) (ExprLit (ILit 1 U64) sr) sr) sr
        ] sr) sr
      ], sr)
    ]
  , typeDefinitions = []
  , constantDefinitions = []
  }

exprAst :: Source
exprAst = Source
  { functionDefinitions =
    [ ("main", FuncDef [] ["a"]
      [ ShallowCopy (Variable "a" sr) (ExprFunc "other" [] I32 sr) sr
      , If (ExprLit (BLit True) sr) (Scope
        [ FuncCall "other" [] [Variable "a" sr] sr
        , Terminator Return sr
        ] sr) Nothing sr
      ], sr)
    , ("other", FuncDef [] ["a"]
      [ ShallowCopy (Variable "a" sr) (Bin Plus (Variable "a" sr) (ExprLit (ILit 2 I32) sr) sr) sr
      ], sr)
    ]
  , typeDefinitions = []
  , constantDefinitions = []
  }


sr = SourceRange SourceLoc SourceLoc
writeObjectFile :: AST.Module -> IO (Either String ())
writeObjectFile mod = withContext $ \context ->
    runExceptT $ M.withModuleFromAST context mod $ \m ->
      failIO . withDefaultTargetMachine $ \mac -> failIO $ M.writeObjectToFile mac (M.File "test.o") m

printModule :: AST.Module -> IO ()
printModule mod =
  withContext $ \context -> do
    runExceptT $ M.withModuleFromAST context mod $ \m -> do
      s <- M.moduleLLVMAssembly m
      putStrLn s
    return ()

failIO :: ExceptT String IO a -> IO a
failIO e = runExceptT e >>= \r -> case r of
  Left err -> fail err
  Right a -> return a

