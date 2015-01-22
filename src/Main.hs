module Main where

import CodeGen
import Ast
import Parser
import Inference
import System.FilePath
import System.Environment (getArgs)
import System.Exit (exitFailure)
import qualified Data.Map as Map
import qualified LLVM.General.AST as AST
import qualified LLVM.General.AST.Type as T
import qualified LLVM.General.AST.Name as Name
import qualified LLVM.General.AST.Operand as O
import qualified LLVM.General.AST.Constant as C
import qualified LLVM.General.Module as M
import LLVM.General.Context
import LLVM.General.Target
import LLVM.General.Analysis
import Control.Monad.Except (runExceptT, ExceptT(..))
import Control.Monad (unless)

main :: IO ()
main = do
  sourceFile : _ <- getArgs
  source <- parseFile sourceFile >>= either (fail . show) return
  let (inferenceErrors, inferredSource) = fullInfer source
  unless (null inferenceErrors) $ do
    putStrLn "inference errors:"
    mapM_ print inferenceErrors
    exitFailure
  writeSourceToObjectFile inferredSource requested $ replaceExtension sourceFile "o"
  where requested = Map.fromList [(ExprSig "main" [] (IntT S32), Right . O.ConstantOperand . C.GlobalReference (T.FunctionType T.i32 [] False) $ Name.Name "main")]

writeSourceToObjectFile :: Source -> GenFuncs -> FilePath -> IO ()
writeSourceToObjectFile source requested oPath = case generate source requested of
  Left errs -> putStrLn "codegen errors: " >> print errs
  Right mod -> asGeneralModule mod (\m -> do
    verifyResult <- runExceptT $ verify m
    case verifyResult of
      Left mess -> putStrLn $ "Verify error: " ++ mess
      Right _ -> do
        putStrLn "result: "
        writeObjectFile oPath m
        printModule m
    )

{-
testAst :: Source
testAst = Source
  { functionDefinitions = Map.fromList
    [ ("main", FuncDef [] [] (Scope
      [ VarInit "a" U64 True sr
      , ShallowCopy (Variable "a" sr) (Bin Plus (Variable "a" sr) (ExprLit (ILit 4 U64) sr) sr) sr
      , VarInit "bo" BoolT True sr
      , ShallowCopy (Variable "bo" sr) (ExprLit (BLit True) sr) sr
      , ShallowCopy (Variable "bo" sr) (ExprLit (BLit False) sr) sr
      , While (Bin Lesser (Variable "a" sr) (ExprLit (ILit 10 U64) sr) sr) (Scope
        [ ShallowCopy (Variable "a" sr) (Bin Times (Variable "a" sr) (ExprLit (ILit 2 U64) sr) sr) sr
        ] sr) sr
      , While (Bin Lesser (Variable "a" sr) (ExprLit (ILit 1000000000 U64) sr) sr) (Scope
        [ ShallowCopy (Variable "a" sr) (Bin Plus (Variable "a" sr) (ExprLit (ILit 1 U64) sr) sr) sr
        ] sr) sr
      ] sr) sr)
    ]
  , typeDefinitions = Map.empty
  } -- Does not return anything, so probably 0

nonRunnablePointers :: Source
nonRunnablePointers = Source
  { functionDefinitions = Map.fromList
    [ ("main", FuncDef [] ["ret"] (Scope
      [ VarInit "p" (PointerT U32) True sr
      , ShallowCopy (Un Deref (Variable "p" sr) sr) (ExprLit (ILit 4 U32) sr) sr
      , ShallowCopy (Variable "ret" sr) (Un Deref (Variable "p" sr) sr) sr
      ] sr) sr)
    ]
  , typeDefinitions = Map.empty
  } -- Seg fault
-}

writeObjectFile :: FilePath -> M.Module -> IO ()
writeObjectFile path mod = failIO . withDefaultTargetMachine $ \mac -> failIO $ M.writeObjectToFile mac (M.File path) mod

printModule :: M.Module -> IO ()
printModule mod = M.moduleLLVMAssembly mod >>= putStrLn

failIO :: ExceptT String IO a -> IO a
failIO e = runExceptT e >>= \r -> case r of
  Left err -> fail err
  Right a -> return a

asGeneralModule :: AST.Module -> (M.Module -> IO a) -> IO a
asGeneralModule mod monad = do
  res <- withContext $ \context ->
    runExceptT . M.withModuleFromAST context mod $ monad
  case res of
    Left mess -> fail mess
    Right res -> return res
