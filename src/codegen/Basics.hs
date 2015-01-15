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

data GenState = GenState
  { _generated :: GenFuncs
  , _requested :: GenFuncs
  , _nextNameNumber :: M.Map String Int
  , _structTypes :: M.Map [Type] (AST.Definition, T.Type)
  , _errors :: [ErrorMessage]
  , _source :: Source
  }

data ErrorMessage = ErrorString String deriving Show

runCodeGen :: GenState -> CodeGen a -> (a, GenState)
runCodeGen initState = runIdentity . flip runStateT initState

emptyState :: GenFuncs -> Source -> GenState
emptyState reqs = GenState M.empty reqs M.empty M.empty []

-- General helpers, should perhaps be moved (TODO)
boolean :: a -> a -> Bool -> a
boolean a _ True = a
boolean _ a False = a

justErr :: MonadError e m => e -> Maybe a -> m a
justErr _ (Just a) = return a
justErr err Nothing = throwError err

-- Helpers

isFloat :: Type -> Bool
isFloat (FloatT _) = True
isFloat _ = False

isUnsigned :: Type -> Bool
isUnsigned (UIntT _) = True
isUnsigned _ = False

isNum :: Type -> Bool
isNum (IntT _) = True
isNum n = isFloat n || isUnsigned n

typeMap :: M.Map Type T.Type
typeMap = M.fromList
  [ (IntT S8, T.i8)
  , (IntT S16, T.i16)
  , (IntT S32, T.i32)
  , (IntT S64, T.i64)

  , (UIntT S8, T.i8)
  , (UIntT S16, T.i16)
  , (UIntT S32, T.i32)
  , (UIntT S64, T.i64)

  , (FloatT S32, T.float)
  , (FloatT S64, T.double)

  , (BoolT, T.i1)
  ]

getSize :: Type -> Word32
getSize (IntT s) = sizeToWord32 s
getSize (UIntT s) = sizeToWord32 s
getSize (FloatT s) = sizeToWord32 s

sizeToWord32 :: TSize -> Word32
sizeToWord32 S8 = 8
sizeToWord32 S16 = 16
sizeToWord32 S32 = 32
sizeToWord32 S64 = 64

extractNameFromCallableOperand :: CallableOperand -> AST.Name
extractNameFromCallableOperand (Right (ConstantOperand (C.GlobalReference _ n))) = n

-- Lenses
generated :: Functor f => (GenFuncs -> f GenFuncs) -> GenState -> f GenState
generated inj state = (\gen -> state { _generated = gen }) <$> inj (_generated state)
{-# INLINE generated #-}

requested :: Functor f => (GenFuncs -> f GenFuncs) -> GenState -> f GenState
requested inj state = (\req -> state { _requested = req }) <$> inj (_requested state)
{-# INLINE requested #-}

nextNameNumber :: Functor f => (M.Map String Int -> f (M.Map String Int)) -> GenState -> f GenState
nextNameNumber inj state = (\nn -> state { _nextNameNumber = nn }) <$> inj (_nextNameNumber state)
{-# INLINE nextNameNumber #-}

structTypes :: Functor f => (M.Map [Type] (AST.Definition, T.Type) -> f (M.Map [Type] (AST.Definition, T.Type))) -> GenState -> f GenState
structTypes inj state = (\st -> state { _structTypes = st }) <$> inj (_structTypes state)
{-# INLINE structTypes #-}

source :: Functor f => (Source -> f Source) -> GenState -> f GenState
source inj g = (\s -> g { _source = s }) <$> inj (_source g)
{-# INLINE source #-}

errors :: Functor f => ([ErrorMessage] -> f [ErrorMessage]) -> GenState -> f GenState
errors inj g = (\errs -> g { _errors = errs }) <$> inj (_errors g)
{-# INLINE errors #-}

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
