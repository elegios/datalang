module Ast where

data SourceLoc = SourceLoc deriving Show
data SourceRange = SourceRange SourceLoc SourceLoc deriving Show

data Source = Source
  { functionDefinitions :: [Top FuncDef]
  , typeDefinitions :: [Top Type]
  , constantDefinitions :: [Top Literal]
  }

type Top a = (String, a, SourceRange)

data Type = Idefault | I8 | I16 | I32 | I64
          | Udefault | U8 | U16 | U32 | U64
          | Fdefault |            F32 | F64
          | BoolT
          | StructT [(String, Type)]
          | FuncT [Type] [Type] deriving (Show, Ord, Eq) -- TODO: Pointers and memorychunks
  -- TODO: custom instance for Eq

data FuncDef = FuncDef
  { inargs :: [String]
  , outargs :: [String]
  , stmnts :: [Statement]
  } deriving Show

data Statement = FuncCall String [(Expression, Type)] [(Expression, Type)] SourceRange
               | ShallowCopy Expression Expression SourceRange
               | If Expression Statement (Maybe Statement) SourceRange
               | While Expression Statement SourceRange
               | Scope [Statement] SourceRange
               | Terminator TerminatorType SourceRange
               | VarInit String Type SourceRange deriving Show

data TerminatorType = Return | Break | Continue deriving (Show, Eq)

data Expression = Bin BinOp Expression Expression SourceRange
                | Un UnOp Expression SourceRange
                | MemberAccess Expression String SourceRange
                | Variable String SourceRange
                | ExprLit Literal SourceRange deriving Show

data BinOp = Plus | Minus | Times | Divide | Remainder
           | Lesser | Greater | LE | GE | Equal | NotEqual
           | And | Or
           | BinAnd | BinOr | LShift | LogRShift | AriRShift | Xor deriving Show
data UnOp = Not | BinNegate | AriNegate deriving Show

data Literal = ILit Integer Type
             | FLit Double Type
             | BLit Bool deriving Show -- TODO: struct literals

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
