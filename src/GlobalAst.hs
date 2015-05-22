{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

-- TODO: split into Parser.Ast and Inference.Ast

module GlobalAst where

import qualified Data.Map as M
import Data.Functor ((<$>))
import Data.Generics.Uniplate.Direct

data SourceLoc = SourceLoc File Line Column deriving (Show, Eq, Ord)
type File = String
type Line = Int
type Column = Int
data SourceRange = SourceRange SourceLoc SourceLoc

instance Eq SourceRange where
  _ == _ = True
instance Ord SourceRange where
  compare _ _ = EQ

nowhere :: SourceRange
nowhere = SourceRange (SourceLoc "nowhere" 0 0) (SourceLoc "nowhere" 0 0)

instance Show SourceRange where
  show (SourceRange start@(SourceLoc f _ _) end) = f ++ "(" ++ pos start ++ " - " ++ pos end ++ ")"
    where pos (SourceLoc _ l c) = show l ++ ":" ++ show c

type Signature = SignatureT Type
data SignatureT t = ProcSig String [t] [t]
                  | FuncSig String [t] t deriving (Eq, Ord)

-- type Source = SourceT Type
data SourceT t = Source
  { functionDefinitions :: M.Map String (CallableDefT t)
  , typeDefinitions :: M.Map String TypeDef
  } deriving Show
-- TODO: Some form of namespaces
-- TODO: Constant support
-- TODO: Function overloading and selection

data Inline = NeverInline | UnspecifiedInline | AlwaysInline deriving (Show, Ord, Eq)

data TSize = S8 | S16 | S32 | S64 deriving (Show, Ord, Eq)
data Type = IntT TSize
          | UIntT TSize
          | FloatT TSize
          | BoolT
          | NamedT String [Type]
          | NewTypeT String Replacements Type
          | PointerT Type
          | StructT [(String, Type)]
          | UnknownT
          deriving (Show, Ord, Eq)

getSizeFromTSize :: Integral a => TSize -> a
getSizeFromTSize S8 = 8
getSizeFromTSize S16 = 16
getSizeFromTSize S32 = 32
getSizeFromTSize S64 = 64

data Replacements = Replacements
  { identifiers :: M.Map String (Maybe Expression, Expression)
  , patterns :: [([BracketToken], (Maybe Expression, Expression))]
  } deriving Show
instance Eq Replacements where
  _ == _ = True
instance Ord Replacements where
  compare _ _ = EQ
data BracketToken = BracketIdentifier String (Maybe Expression)
                  | BracketOperator String deriving Show
data TypeDef = NewType [String] Replacements Type SourceRange
             | Alias [String] Type SourceRange deriving Show

-- TODO: More fancy pointers
-- TODO: Find and prevent infinite recursive structures
-- TODO: Function types
-- TODO: Strings
-- TODO: Algebraic types (as tagged unions?)

instance Uniplate Type where
  uniplate (IntT s) = plate IntT |- s
  uniplate (UIntT s) = plate UIntT |- s
  uniplate (FloatT s) = plate FloatT |- s
  uniplate BoolT = plate BoolT
  uniplate (NamedT n ts) = plate NamedT |- n ||* ts
  uniplate (PointerT t) = plate PointerT |* t
  uniplate s@(StructT props) = plateProject from to s
    where
      from _ = snd <$> props
      to = StructT . zip (fst <$> props)
instance Biplate [Type] (Type) where
    biplate (x:xs) = plate (:) |* x ||* xs
    biplate x = plate x

type Restriction = RestrictionT Type
data RestrictionT t = NoRestriction
                    | PropertiesR [(String, t)] [([Either String t], t)]
                    | UIntR
                    | NumR NumSpec
                    deriving (Show, Eq)
data NumSpec = NoSpec | IntSpec | FloatSpec deriving (Show, Eq)

type CallableDef = CallableDefT Type
data CallableDefT t =
  ProcDef
  { intypes :: [t]
  , outTypes :: [t]
  , restrictions :: [(String, Restriction)]
  , inargs :: [String]
  , outargs :: [String]
  , functionBody :: StatementT t
  , sourcerange :: SourceRange
  } |
  FuncDef
  { intypes :: [t]
  , retType :: t
  , restrictions :: [(String, Restriction)]
  , inargs :: [String]
  , retarg :: String
  , functionBody :: StatementT t
  , sourcerange :: SourceRange
  }
  deriving Show

type Statement = StatementT Type
data StatementT t = ProcCall String [ExpressionT t] [ExpressionT t] SourceRange
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
-- TODO: Defer currently just moves the statement to all places it needs to be. Introducing a new shadowing local variable will break intent. This would need to be changed in both inferrer and generator, or by an extra pass beforehand

data TerminatorType = Return | Break | Continue deriving (Show, Eq)

type Expression = ExpressionT Type
data ExpressionT t = Bin BinOp (ExpressionT t) (ExpressionT t) SourceRange
                   | Un UnOp (ExpressionT t) SourceRange
                   | MemberAccess (ExpressionT t) String SourceRange
                   | Subscript (ExpressionT t) [BracketExprT t] SourceRange
                   | Variable String SourceRange
                   | FuncCall String [ExpressionT t] t SourceRange
                   | ExprLit (LiteralT t) SourceRange
                   | TypeAssertion Expression Type SourceRange
                   | Zero t
                   deriving Show
type BracketExpr = BracketExprT Type
data BracketExprT t = BracketExpr (ExpressionT t) SourceRange
                    | BracketExprOp String SourceRange
                    deriving Show
-- TODO: Bitcast, conversion.
-- TODO: Allow calling of functionpointers

-- NOTE: Short/Long And/Or means shortcutting/not shortcutting
data BinOp = Plus | Minus | Times | Divide | Remainder
           | Lesser | Greater | LE | GE | Equal | NotEqual
           | ShortAnd | ShortOr | LongAnd | LongOr
           | BinAnd | BinOr | LShift | LogRShift | AriRShift | Xor
           deriving (Show, Eq)
data UnOp = Not | BinNegate | AriNegate | Deref | AddressOf deriving Show

type Literal = LiteralT Type
data LiteralT t = ILit Integer t SourceRange
                | FLit Double t SourceRange
                | BLit Bool SourceRange
                | Null t SourceRange
                | Undef t SourceRange
                deriving Show
-- TODO: struct literals

class Source a where
  location :: a -> SourceRange
