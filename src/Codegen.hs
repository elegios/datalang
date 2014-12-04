{-# LANGUAGE TupleSections #-}

module CodeGen where

-- TODO: Save a "stack trace" of requested functions, to make it easier to figure out why a specific function was requested.

import Ast
import CodeGen.Functions
import CodeGen.Basics
import Data.Functor ((<$>))
import Control.Lens hiding (op, index, parts, transform)
import qualified LLVM.General.AST as AST
import qualified Data.Map as M

generate :: Source -> GenFuncs -> Either [ErrorMessage] AST.Module
generate sourceToGen requests = case errs of
  [] -> Right $ AST.defaultModule { AST.moduleDefinitions = structDefs ++ defs }
  _ -> Left errs
  where
    (defs, resState) = runCodeGen (emptyState requests sourceToGen) generateFunctions 
    errs = _errors resState
    structDefs = map fst . M.elems $ _structTypes resState
    generateFunctions = do
      mreq <- use $ requested . to M.minViewWithKey
      maybe (return []) runGenerateFunction mreq
    runGenerateFunction ((func, _), _) = do
      eRes <- generateFunction func
      op <- requested . at func <<.= Nothing
      generated . at func .= op
      case eRes of
        Left err -> (errors %= (err:)) >> generateFunctions
        Right res -> (res:) <$> generateFunctions
