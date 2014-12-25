{-# LANGUAGE DeriveDataTypeable #-}

module Ast where

import qualified Data.Map as M
import Data.Data

data SourceLoc = SourceLoc File Line Column deriving Show
type File = String
type Line = Int
type Column = Int
data SourceRange = SourceRange SourceLoc SourceLoc deriving Show

data FuncSig = NormalSig String [Type] [Type]
             | ExprSig String [Type] Type deriving (Eq, Ord)

type Source = SourceT Type
data SourceT t = Source
  { functionDefinitions :: M.Map String (FuncDefT t)
  , typeDefinitions :: M.Map String TypeDef
  } deriving Show
-- TODO: Some form of namespaces
-- TODO: Constant support
-- TODO: Function overloading and selection

data Type = I8 | I16 | I32 | I64
          | U8 | U16 | U32 | U64
          |            F32 | F64
          | NamedT String [Type]
          | BoolT
          | PointerT Type
          | Memorychunk Type Bool Type
          | StructT [(String, Type)]
          | UnknownT
          deriving (Show, Ord, Eq, Data, Typeable) -- TODO: Manual definition using uniplate.direct for speed
data TypeDef = TypeDef [String] Type SourceRange deriving Show
-- TODO: More fancy pointers
-- TODO: Find and prevent infinite recursive structures
-- TODO: Function types
-- TODO: Strings
-- TODO: Algebraic types (as tagged unions?)

type FuncDef = FuncDefT Type
data FuncDefT t = FuncDef
  { inargs :: [String]
  , outargs :: [String]
  , functionBody :: StatementT t
  , sourcerange :: SourceRange
  } deriving Show

type Statement = StatementT Type
data StatementT t = FuncCall String [ExpressionT t] [ExpressionT t] SourceRange
                  | Defer (StatementT t) SourceRange
                  | ShallowCopy (ExpressionT t) (ExpressionT t) SourceRange
                  | If (ExpressionT t) (StatementT t) (Maybe (StatementT t)) SourceRange
                  | While (ExpressionT t) (StatementT t) SourceRange
                  | Scope [StatementT t] SourceRange
                  | Terminator TerminatorType SourceRange
                  | VarInit Bool String t (ExpressionT t) SourceRange
                  deriving Show
-- TODO: For, possibly for-each
-- TODO: Switch, match or pattern match
-- TODO: Delete/Heap/Stack?

data TerminatorType = Return | Break | Continue deriving (Show, Eq)

type Expression = ExpressionT Type
data ExpressionT t = Bin BinOp (ExpressionT t) (ExpressionT t) SourceRange
                   | Un UnOp (ExpressionT t) SourceRange
                   | MemberAccess (ExpressionT t) String SourceRange
                   | Subscript (ExpressionT t) (ExpressionT t) SourceRange
                   | Variable String SourceRange
                   | ExprFunc String [ExpressionT t] t SourceRange
                   | ExprLit (LiteralT t) SourceRange
                   | Zero t
                   deriving Show
-- TODO: Bitcast, conversion.
-- TODO: Allow calling of functionpointers
-- TODO: Figure out what to do with zero, find the type and generate any possible value or expand to a large literal after inference?

-- Short/Long And/Or means shortcutting/not shortcutting
data BinOp = Plus | Minus | Times | Divide | Remainder
           | Lesser | Greater | LE | GE | Equal | NotEqual
           | ShortAnd | ShortOr | LongAnd | LongOr
           | BinAnd | BinOr | LShift | LogRShift | AriRShift | Xor
           deriving Show
data UnOp = Not | BinNegate | AriNegate | Deref | AddressOf deriving Show

type Literal = LiteralT Type
data LiteralT t = ILit Integer t
                | FLit Double t
                | BLit Bool
                | Null t
                | Undef t
                deriving Show
-- TODO: struct literals
-- TODO: memorychunk literals
