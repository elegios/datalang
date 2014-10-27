{-# LANGUAGE OverloadedStrings #-}

module CodeGen where

{- TODO:
 - Save a "stack trace" of requested functions, to make it easier to figure out
   why a specific function was requested.
 - Deal with default sizes of i, u and f
 - Ensure that operations involving u types are actually unsigned, it's not
   carried in the type
 -}

import Ast
import Data.Maybe
import Data.Functor ((<$>))
import Data.String (IsString, fromString)
import Control.Lens
import Control.Monad.State
import Control.Monad.Except 
import Control.Monad.Identity
import LLVM.General.AST.Operand
import LLVM.General.AST.Constant
import LLVM.General.AST.Name
import qualified LLVM.General.AST.Type as T
import qualified LLVM.General.AST as AST
import qualified Data.Map as M

type GenFuncs = M.Map (String, [Type], [Type]) Operand
data GeneratedFunctions = GeneratedFunctions
  { _generated :: GenFuncs
  , _requested :: GenFuncs 
  , _nextName :: M.Map String Int
  }

data GenState = GenState
  { _generatedFuncs :: GeneratedFunctions
  , _breakTarget :: Maybe Name
  , _continueTarget :: Maybe Name
  , _locals :: M.Map String (Operand, Type)
  , _errors :: [ErrorMessage]
  }

emptyState :: GenState
emptyState = GenState (GeneratedFunctions M.empty M.empty M.empty) Nothing Nothing M.empty []

data ErrorMessage

type CodeGen a = ExceptT ErrorMessage (StateT GenState Identity) a

generate :: Source -> GenFuncs -> Either [ErrorMessage] AST.Module
generate source requests = case errs of
  [] -> Right $ AST.defaultModule { AST.moduleDefinitions = defs }
  _ -> Left errs
  where
    (defs, resState) = runIdentity . runStateT generator $ emptyState & generatedFuncs . requested .~ requests
    errs = _errors resState
    generator :: StateT GenState Identity [AST.Definition]
    generator = do
      mreq <- use $ generatedFuncs . requested . to M.minViewWithKey
      maybe (return []) runGenerateFunction mreq
    runGenerateFunction ((func, _), _) = do
      resetGeneratorState
      res <- runExceptT $ generateFunction func
      op <- generatedFuncs . requested . at func <<.= Nothing
      generatedFuncs . generated . at func .= op
      case res of
        Left err -> (errors %= (err:)) >> generator
        Right res -> (res:) <$> generator

resetGeneratorState :: StateT GenState Identity ()
resetGeneratorState = modify $ \s -> s
  { _breakTarget = Nothing
  , _continueTarget = Nothing
  , _locals = M.empty
  }

generateFunction :: (String, [Type], [Type]) -> CodeGen AST.Definition
generateFunction = undefined

requestFunction :: (String, [Type], [Type]) -> CodeGen Operand
requestFunction func@(name, inTs, outTs) = do
  mo <- gets $ getFunctionOperand func . _generatedFuncs
  maybe newRequest return mo
  where
    getNextName :: CodeGen Int
    getNextName = fromJust <$> ( generatedFuncs . nextName . at name <%= (Just . maybe 0 succ))
    requestWithOperand :: Operand -> CodeGen Operand
    requestWithOperand op = generatedFuncs . requested . at func <?= op
    newRequest = do
      num <- getNextName
      requestWithOperand . ConstantOperand . GlobalReference (toFunctionType inTs outTs) . fromString $ name ++ show num

getFunctionOperand :: (String, [Type], [Type]) -> GeneratedFunctions -> Maybe Operand
getFunctionOperand sig (GeneratedFunctions gen req _) = case M.lookup sig gen of
  Just o -> Just o
  Nothing -> M.lookup sig req 

toFunctionType :: [Type] -> [Type] -> T.Type
toFunctionType inTs outTs = (\ts -> T.FunctionType T.void ts False) $ (toScalarType <$> inTs) ++ (T.ptr . toScalarType <$> outTs)
  where
    toScalarType t = fromMaybe composite $ M.lookup t typeMap
      where
        composite = case t of
          StructT parts -> T.StructureType False $ toScalarType . snd <$> parts
          FuncT ins outs -> toFunctionType ins outs

typeMap :: M.Map Type T.Type
typeMap = M.fromList
  [ (I8, T.i8)
  , (I16, T.i16)
  , (I32, T.i32)
  , (I64, T.i64)

  , (U8, T.i8)
  , (U16, T.i16)
  , (U32, T.i32)
  , (U64, T.i64)

  , (F32, T.float)
  , (F64, T.double)

  , (BoolT, T.i1)
  ]
  
-- These lenses could be generated if TemplateHaskell didn't
-- require things to be linked dynamically which conflicts
-- with my llvm bindings atm

generated :: Functor f => (GenFuncs -> f GenFuncs) -> GeneratedFunctions -> f GeneratedFunctions 
generated inj (GeneratedFunctions gen req nex) = (\g -> GeneratedFunctions g req nex) <$> inj gen
{-# INLINE generated #-}

requested :: Functor f => (GenFuncs -> f GenFuncs) -> GeneratedFunctions -> f GeneratedFunctions 
requested inj (GeneratedFunctions gen req nex) = (\r -> GeneratedFunctions gen r nex) <$> inj req
{-# INLINE requested #-}

nextName :: Functor f => (M.Map String Int -> f (M.Map String Int)) -> GeneratedFunctions -> f GeneratedFunctions
nextName inj (GeneratedFunctions gen req nex) = GeneratedFunctions gen req <$> inj nex
{-# INLINE nextName #-}

generatedFuncs :: Functor f => (GeneratedFunctions -> f GeneratedFunctions) -> GenState -> f GenState
generatedFuncs inj (GenState gen errs) = (\g -> GenState g errs) <$> inj gen
{-# INLINE generatedFuncs #-}

errors :: Functor f => ([ErrorMessage] -> f [ErrorMessage]) -> GenState -> f GenState
errors inj (GenState gen errs) = GenState gen <$> inj errs
{-# INLINE errors #-}

instance IsString Name where
  fromString = Name
