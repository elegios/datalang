{-# LANGUAGE DeriveDataTypeable #-}

module Ast where

import qualified Data.Map as M
import Data.Data

data SourceLoc = SourceLoc deriving Show
data SourceRange = SourceRange SourceLoc SourceLoc deriving Show

data FuncSig = NormalSig String [Type] [Type]
             | ExprSig String [Type] Type deriving (Eq, Ord)

data Source = Source
  { functionDefinitions :: M.Map String FuncDef
  , typeDefinitions :: M.Map String TypeDef
  }
-- TODO: Some form of namespaces
-- TODO: Constant support
-- TODO: Function overloading and selection

data Type = I8 | I16 | I32 | I64
          | U8 | U16 | U32 | U64
          |            F32 | F64
          | NamedT String [Type]
          | BoolT
          | PointerT Type
          | StructT [(String, Type)] deriving (Show, Ord, Eq, Data, Typeable) -- TODO: Manual definition using uniplate.direct for speed
data TypeDef = TypeDef Type [String] SourceRange deriving Show
-- TODO: More fancy pointers
-- TODO: Memorychunks
-- TODO: Find and prevent infinite recursive structures
-- TODO: Function types
-- TODO: Strings
-- TODO: Algebraic types (as tagged unions?)

data FuncDef = FuncDef
  { inargs :: [String]
  , outargs :: [String]
  , statement :: Statement
  , sourcerange :: SourceRange
  } deriving Show

data Statement = FuncCall String [Expression] [Expression] SourceRange
               | ShallowCopy Expression Expression SourceRange
               | If Expression Statement (Maybe Statement) SourceRange
               | While Expression Statement SourceRange
               | Scope [Statement] SourceRange
               | Terminator TerminatorType SourceRange
               | VarInit String Type Bool SourceRange deriving Show
-- TODO: For, possibly for-each
-- TODO: Switch, match or pattern match
-- TODO: Zero-initialization
-- TODO: Defer

data TerminatorType = Return | Break | Continue deriving (Show, Eq)

data Expression = Bin BinOp Expression Expression SourceRange
                | Un UnOp Expression SourceRange
                | MemberAccess Expression String SourceRange
                | Variable String SourceRange
                | ExprFunc String [Expression] Type SourceRange
                | ExprLit Literal SourceRange deriving Show
-- TODO: Bitcast, conversion.

-- Short/Long And/Or means shortcutting/not shortcutting
data BinOp = Plus | Minus | Times | Divide | Remainder
           | Lesser | Greater | LE | GE | Equal | NotEqual
           | ShortAnd | ShortOr | LongAnd | LongOr 
           | BinAnd | BinOr | LShift | LogRShift | AriRShift | Xor deriving Show
data UnOp = Not | BinNegate | AriNegate | Deref | AddressOf deriving Show

data Literal = ILit Integer Type
             | FLit Double Type
             | BLit Bool deriving Show
-- TODO: struct literals

{-
 - Several things that we want to represent cannot be using this ast.
 - We will later need to do various forms of checking on the code, to
 - find if a function is pure for example, which will require storage
 - of additional info related to each of these things. Should that be
 - added to the ast, or should it be a similar structure that only has
 - the info required for checking, and the work of doing this checking
 - simply involves building that structure?
 -
 - One thing I'll probably want is multiple implementations functions
 - with the same name, 'init' for example, which requires the compiler
 - to be able to choose, which means some way to prioritize, probably
 - with more info than just the number of arguments. This will require
 - a type signature for the function.
 -
 - Pointers are not yet here, and because of this it is not possible to
 - represent any kind of recursive datastructure (linked lists etc).
 - These will have to be able to refer to types by reference as opposed
 - to value, as that value would be infinitely large.
 -}
