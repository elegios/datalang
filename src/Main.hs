module Main where

import CodeGen
import Ast
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
import LLVM.General.Analysis
import System.Exit
import Control.Monad.Except (runExceptT, ExceptT(..))

main = case generate ast requested of
  Left errs -> putStrLn "errors: " >> print errs
  Right mod -> putStrLn (showPretty mod) >> asGeneralModule mod (\m -> do
    verifyResult <- runExceptT $ verify m
    case verifyResult of
      Left mess -> putStrLn $ "Verify error: " ++ mess
      Right _ -> do
        writeObjectFile m
        putStrLn "result: "
        printModule m)
  where
    -- (requestedSig, ast, normal) = (NormalSig "main" [] [], testAst, False)
    -- (requestedSig, ast, normal) = (ExprSig "main" [] I32, exprAst, True)
    (requestedSig, ast, normal) = (ExprSig "main" [] I32, fancyTypes, True)
    requested = Map.fromList [(requestedSig, Right . O.ConstantOperand . C.GlobalReference llvmt $ Name.Name "main")]
    llvmt = if normal
      then T.FunctionType T.i32 [] False
      else T.FunctionType T.void [] False

testAst :: Source
testAst = Source
  { functionDefinitions = Map.fromList
    [ ("main", FuncDef [] []
      [ VarInit "a" U64 sr
      , ShallowCopy (Variable "a" sr) (Bin Plus (Variable "a" sr) (ExprLit (ILit 4 U64) sr) sr) sr
      , VarInit "bo" BoolT sr
      , ShallowCopy (Variable "bo" sr) (ExprLit (BLit True) sr) sr
      , ShallowCopy (Variable "bo" sr) (ExprLit (BLit False) sr) sr
      , While (Bin Lesser (Variable "a" sr) (ExprLit (ILit 10 U64) sr) sr) (Scope
        [ ShallowCopy (Variable "a" sr) (Bin Times (Variable "a" sr) (ExprLit (ILit 2 U64) sr) sr) sr
        ] sr) sr
      , While (Bin Lesser (Variable "a" sr) (ExprLit (ILit 1000000000 U64) sr) sr) (Scope
        [ ShallowCopy (Variable "a" sr) (Bin Plus (Variable "a" sr) (ExprLit (ILit 1 U64) sr) sr) sr
        ] sr) sr
      ] sr)
    ]
  , typeDefinitions = Map.empty
  }

exprAst :: Source
exprAst = Source
  { functionDefinitions = Map.fromList
    [ ("main", FuncDef [] ["a"]
      [ ShallowCopy (Variable "a" sr) (ExprFunc "other" [] I32 sr) sr
      , If (ExprLit (BLit True) sr) (Scope
        [ FuncCall "other" [] [Variable "a" sr] sr
        , Terminator Return sr
        ] sr) Nothing sr
      ] sr)
    , ("other", FuncDef [] ["a"]
      [ ShallowCopy (Variable "a" sr) (Bin Plus (Variable "a" sr) (ExprLit (ILit 2 I32) sr) sr) sr
      ] sr)
    ]
  , typeDefinitions = Map.empty
  }

fancyTypes :: Source
fancyTypes = Source
  { functionDefinitions = Map.fromList
    [ ("main", FuncDef [] ["ret"]
      [ VarInit "tup" (NamedT "Tuple" [U32, U32]) sr
      , ShallowCopy (MemberAccess (Variable "tup" sr) "a" sr) (ExprLit (ILit 2 U32) sr) sr
      , ShallowCopy (MemberAccess (Variable "tup" sr) "b" sr) (ExprLit (ILit 3 U32) sr) sr
      , ShallowCopy (Variable "ret" sr) (Bin Plus (MemberAccess (Variable "tup" sr) "a" sr) (Bin Times (ExprLit (ILit 10 U32) sr) (MemberAccess (Variable "tup" sr) "b" sr) sr) sr) sr
      ] sr)
    ]
  , typeDefinitions = Map.fromList
    [ ("Tuple", TypeDef (
      StructT [("a", NamedT "a" []), ("b", NamedT "b" [])]
      ) ["a", "b"] sr)]
  }

sr :: SourceRange
sr = SourceRange SourceLoc SourceLoc

writeObjectFile :: M.Module -> IO ()
writeObjectFile mod = failIO . withDefaultTargetMachine $ \mac -> failIO $ M.writeObjectToFile mac (M.File "test.o") mod

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
