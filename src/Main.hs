{-# LANGUAGE LambdaCase #-}

module Main where

import GlobalAst (TSize(S32), nowhere)
import Parser (parseFile)
import Parser.Ast (Type(FuncT, IntT), cImportDefinitions)
import NameResolution (resolveNames)
import NameResolution.Ast (Resolved(Global))
import Inference (infer)
import CodeGen (generate)
import Data.Functor ((<$>))
import Data.List (intercalate)
import Control.Monad (unless)
import Data.Either (partitionEithers)
import System.Environment (getArgs)
import System.FilePath (replaceExtension)
import qualified LLVM.General.AST as AST
import qualified LLVM.General.Module as M
import LLVM.General.PrettyPrint
import LLVM.General.Context
import LLVM.General.Target
import LLVM.General.Analysis (verify)
import Control.Monad.Except (runExceptT, ExceptT(..))
import qualified Data.Map as Map

-- TODO: Some form of namespaces
-- TODO: Constant support
-- TODO: Function overloading and selection

-- TODO: More fancy pointers
-- TODO: Find and prevent infinite recursive structures
-- TODO: Strings
-- TODO: Algebraic types (as tagged unions?)

-- TODO: For, possibly for-each
-- TODO: Switch, match or pattern match
-- TODO: Delete/Heap/Stack?

-- TODO: Bitcast, conversion.
-- TODO: Allow calling of functionpointers

-- main :: IO ()
main = do
  sourceFile : _ <- getArgs
  source <- parseFile sourceFile >>= either (fail . show) return
  putStrLn "Parse done"
  resolved <- either (fail . show) return $ resolveNames source
  putStrLn "Name resolution done"
  let inferred = infer resolved
  case inferred of
    Left errs -> fail $ show errs
    Right success@(_, _, _, ts) -> do
      mapM_ print $ Map.toList ts
      triple <- getDefaultTargetTriple
      case generate triple success of
        Left errors -> fail $ show errors
        Right m -> (writeModuleToObjectFile m $ replaceExtension sourceFile "o")
  return inferred

testLLVMstuff = do
  initializeAllTargets
  failIO $ withDefaultTargetMachine getTargetMachineDataLayout
  getDefaultTargetTriple

writeModuleToObjectFile :: AST.Module -> FilePath -> IO ()
writeModuleToObjectFile m p = asGeneralModule m $ \mod ->
  -- printModule mod >>
  -- failIO (M.writeLLVMAssemblyToFile (M.File $ p ++ ".ll") mod) >>
  runExceptT (verify mod) >>= \case
    Left mess -> putStrLn $ "Verify error: " ++ mess
    Right _ -> do
      putStrLn "Codegen done"
      writeObjectFile p mod
      -- printModule mod

writeObjectFile :: FilePath -> M.Module -> IO ()
writeObjectFile path mod = failIO . withDefaultTargetMachine $ \mac ->
  failIO $ M.writeObjectToFile mac (M.File path) mod

printModule :: M.Module -> IO ()
printModule mod = M.moduleLLVMAssembly mod >>= putStrLn

failIO :: ExceptT String IO a -> IO a
failIO e = runExceptT e >>= \r -> case r of
  Left err -> fail err
  Right a -> return a

asGeneralModule :: AST.Module -> (M.Module -> IO a) -> IO a
asGeneralModule mod monad = withContext $ \context ->
  failIO . M.withModuleFromAST context mod $ monad

isRight :: Either a b -> Bool
isRight Right{} = True
isRight _ = False
