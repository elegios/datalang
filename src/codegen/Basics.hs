{-# LANGUAGE TemplateHaskell #-}

module CodeGen.Basics where

import Ast
import Data.Functor ((<$>))
import Data.Word
import Control.Lens hiding (op, index, parts, transform)
import Control.Monad.State (runStateT, StateT)
import Control.Monad.Except
import LLVM.General.AST.Operand
import qualified LLVM.General.AST.Type as T
import qualified LLVM.General.AST.Constant as C
import qualified LLVM.General.AST as AST
import qualified Data.Map as M

type CodeGen a = StateT GenState Identity a

type GenFuncs = M.Map FuncSig CallableOperand

data ErrorMessage = ErrorString String deriving Show

data GenState = GenState
  { _generated :: GenFuncs
  , _requested :: GenFuncs
  , _nextNameNumber :: M.Map String Int
  , _structTypes :: M.Map [Type] (AST.Definition, T.Type)
  , _errors :: [ErrorMessage]
  , _source :: Source
  }

makeLenses ''GenState

runCodeGen :: GenState -> CodeGen a -> (a, GenState)
runCodeGen initState = runIdentity . flip runStateT initState

-- General helpers, should perhaps be moved (TODO)
boolean :: a -> a -> Bool -> a
boolean a _ True = a
boolean _ a False = a

justErr :: MonadError e m => e -> Maybe a -> m a
justErr _ (Just a) = return a
justErr err Nothing = throwError err

-- Helpers

sizeToWord32 :: TSize -> Word32
sizeToWord32 s = case s of
  S8 -> 8; S16 -> 16; S32 -> 32; S64 -> 64

-- manual lenses

blockInstrs :: Functor f => ([AST.Named AST.Instruction] -> f [AST.Named AST.Instruction]) -> AST.BasicBlock -> f AST.BasicBlock
blockInstrs inj (AST.BasicBlock n i t) = (\is -> AST.BasicBlock n is t) <$> inj i
{-# INLINE blockInstrs #-}

blockTerminator :: Functor f => (AST.Named AST.Terminator -> f (AST.Named AST.Terminator)) -> AST.BasicBlock -> f AST.BasicBlock
blockTerminator inj (AST.BasicBlock n i t) = AST.BasicBlock n i <$> inj t
{-# INLINE blockTerminator #-}

blockName :: Functor f => (AST.Name -> f AST.Name) -> AST.BasicBlock -> f AST.BasicBlock
blockName inj (AST.BasicBlock n i t) = (\n' -> AST.BasicBlock n' i t) <$> inj n
{-# INLINE blockName #-}
