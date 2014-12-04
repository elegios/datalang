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
isFloat F32 = True
isFloat F64 = True
isFloat _ = False

isUnsigned :: Type -> Bool
isUnsigned U8 = True
isUnsigned U16 = True
isUnsigned U32 = True
isUnsigned U64 = True
isUnsigned _ = False

isNum :: Type -> Bool
isNum I8 = True
isNum I16 = True
isNum I32 = True
isNum I64 = True
isNum n = isFloat n || isUnsigned n

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

typeSizeMap :: M.Map Type Word32
typeSizeMap = M.fromList
  [ (I8, 8)
  , (I16, 16)
  , (I32, 32)
  , (I64, 64)

  , (U8, 8)
  , (U16, 16)
  , (U32, 32)
  , (U64, 64)

  , (F32, 32)
  , (F64, 64)
  ]

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

blockName :: Functor f => (AST.Name-> f AST.Name) -> AST.BasicBlock -> f AST.BasicBlock
blockName inj (AST.BasicBlock n i t) = (\n' -> AST.BasicBlock n' i t) <$> inj n
{-# INLINE blockName #-}
