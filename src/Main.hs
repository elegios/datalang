module Main where

import GlobalAst (TSize(S32), nowhere)
import Parser (parseFile)
import Parser.Ast (Type(FuncT, IntT))
import NameResolution (resolveNames)
import NameResolution.Ast (Resolved(Global))
import Inference (infer)
import Data.Functor ((<$>))
import System.Environment (getArgs)
import qualified LLVM.General.AST as AST
import qualified LLVM.General.Module as M
import LLVM.General.Context
import LLVM.General.Target
import Control.Monad.Except (runExceptT, ExceptT(..))

-- main :: IO ()
main = do
  sourceFile : _ <- getArgs
  source <- parseFile sourceFile >>= either (fail . show) return
  putStrLn "Parse done"
  resolved <- either (fail . show) return $ resolveNames source
  putStrLn "Name resolution done"
  let inferred = infer resolved [(Global "main", FuncT [] (IntT S32 nowhere) nowhere)]
  print $ fmap (const True) <$> inferred
  putStrLn "Inference done"
  return inferred
-- main = do
--   sourceFile : _ <- getArgs
--   source <- parseFile sourceFile >>= either (fail . show) return
--   putStrLn "Parse done"
--   let (inferenceErrors, inferredSource) = fullInfer source
--   unless (null inferenceErrors) $ do
--     putStrLn "inference errors:"
--     mapM_ print inferenceErrors
--     exitFailure
--   putStrLn "Inference done"
--   writeSourceToObjectFile inferredSource requested $ replaceExtension sourceFile "o"
--   putStrLn "Codegen done"
--   where requested = Map.fromList [(FuncSig "main" [] (IntT S32), Right . O.ConstantOperand . C.GlobalReference (T.FunctionType T.i32 [] False) $ Name.Name "main")]

-- writeSourceToObjectFile :: Source -> GenFuncs -> FilePath -> IO ()
-- writeSourceToObjectFile source requested oPath = case generate source requested of
--   Left errs -> putStrLn "codegen errors: " >> print errs
--   Right mod -> asGeneralModule mod (\m -> do
--     verifyResult <- runExceptT $ verify m
--     case verifyResult of
--       Left mess -> putStrLn $ "Verify error: " ++ mess
--       Right _ -> do
--         putStrLn "result: "
--         writeObjectFile oPath m
--         printModule m
--     )

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

isRight :: Either a b -> Bool
isRight Right{} = True
isRight _ = False
