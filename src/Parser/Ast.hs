{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module Parser.Ast where

import GlobalAst (SourceRange(..), TSize(..), BinOp(..), UnOp(..), TerminatorType(..), Source, location)
import Data.Generics.Uniplate.Direct

type SourceFile = SourceFileT String
data SourceFileT v = SourceFile
  { typeDefinitions :: [TypeDefT v]
  , callableDefinitions :: [CallableDefT v]
  }

data HiddenIdentifiers = HideAll | HideSome [String] deriving Show
type Replacement v = (Maybe (ExpressionT v), ExpressionT v)
type TypeDef = TypeDefT String
data TypeDefT v = NewType
                  { typeName :: String
                  , typeParams :: [String]
                  , hiddenIdentifiers :: HiddenIdentifiers
                  , introducedIdentifiers :: [(String, Replacement v)]
                  , bracketPatterns :: [([BracketTokenT v], Replacement v)]
                  , wrappedType :: Type
                  , typeRange :: SourceRange
                  }
                | Alias
                  { typeName :: String
                  , typeParams :: [String]
                  , wrappedType :: Type
                  , typeRange :: SourceRange
                  }
data BracketTokenT v = BrId v (Maybe (ExpressionT v))
                     | BrOp String
instance Show v => Show (BracketTokenT v) where
  show (BrId v me) = maybe "" (const "optional ") me ++ show v
  show (BrOp o) = show o

type CallableDef = CallableDefT String
data CallableDefT v = FuncDef
                      { callableName :: String
                      , intypes :: [Type]
                      , outtype :: Type
                      , inargs :: [v]
                      , outarg :: v
                      , callableBody :: StatementT v
                      , callableRange :: SourceRange
                      }
                    | ProcDef
                      { callableName :: String
                      , intypes :: [Type]
                      , outtypes :: [Type]
                      , inargs :: [v]
                      , outargs :: [v]
                      , callableBody :: StatementT v
                      , callableRange :: SourceRange
                      }

data Type = IntT TSize SourceRange
          | UIntT TSize SourceRange
          | FloatT TSize SourceRange
          | BoolT SourceRange
          | NamedT String [Type] SourceRange
          | TypeVar String SourceRange
          | PointerT Type SourceRange
          | StructT [(String, Type)] SourceRange
          | ProcT [Type] [Type] SourceRange
          | FuncT [Type] Type SourceRange
          | UnknownT SourceRange
          deriving (Show, Eq, Ord)

instance Uniplate Type where
  uniplate (IntT s r) = plate IntT |- s |- r
  uniplate (UIntT s r) = plate IntT |- s |- r
  uniplate (FloatT s r) = plate FloatT |- s |- r
  uniplate (BoolT r) = plate BoolT |- r
  uniplate (NamedT n ts r) = plate NamedT |- n ||* ts |- r
  uniplate (TypeVar n r) = plate TypeVar |- n |- r
  uniplate (PointerT t r) = plate PointerT |* t |- r
  uniplate (StructT ps r) = plate StructT ||+ ps |- r
  uniplate (ProcT is os r) = plate ProcT ||* is ||* os |- r
  uniplate (FuncT is o r) = plate FuncT ||* is |* o |- r

instance Biplate (String, Type) Type where
  biplate (s, t) = plate (,) |- s |* t
instance Biplate [Type] Type where
  biplate [] = plate []
  biplate (t:ts) = plate (:) |* t ||* ts

type Statement = StatementT String
data StatementT v = ProcCall (ExpressionT v) [ExpressionT v] [ExpressionT v] SourceRange
                  | Defer (StatementT v) SourceRange
                  | ShallowCopy (ExpressionT v) (ExpressionT v) SourceRange
                  | If (ExpressionT v) (StatementT v) (Maybe (StatementT v)) SourceRange
                  | While (ExpressionT v) (StatementT v) SourceRange
                  | Scope [StatementT v] SourceRange
                  | Terminator TerminatorType SourceRange
                  | VarInit Bool v (Maybe Type) (Maybe (ExpressionT v)) SourceRange

type Expression = ExpressionT String
data ExpressionT v = Bin BinOp (ExpressionT v) (ExpressionT v) SourceRange
                   | Un UnOp (ExpressionT v) SourceRange
                   | MemberAccess (ExpressionT v) String SourceRange
                   | Subscript (ExpressionT v) [Either String (ExpressionT v)] SourceRange
                   | Variable v SourceRange
                   | FuncCall (ExpressionT v) [ExpressionT v] SourceRange
                   | ExprLit (LiteralT v)
                   | TypeAssertion (ExpressionT v) Type SourceRange

type Literal = LiteralT String
data LiteralT v = ILit Integer SourceRange
                | FLit Double SourceRange
                | BLit Bool SourceRange
                | Null SourceRange
                | Undef SourceRange
                | StructLit [(String, ExpressionT v)] SourceRange
                | StructTupleLit [ExpressionT v] SourceRange

instance Source (TypeDefT v) where
  location = typeRange
instance Source (CallableDefT v) where
  location = callableRange
instance Source Type where
  location (IntT _ r) = r
  location (UIntT _ r) = r
  location (FloatT _ r) = r
  location (BoolT r) = r
  location (NamedT _ _ r) = r
  location (PointerT _ r) = r
  location (StructT _ r) = r
instance Source (StatementT v) where
  location (ProcCall _ _ _ r) = r
  location (Defer _ r) = r
  location (ShallowCopy _ _ r) = r
  location (If _ _ _ r) = r
  location (While _ _ r) = r
  location (Scope _ r) = r
  location (Terminator _ r) = r
  location (VarInit _ _ _ _ r) = r
instance Source (ExpressionT v) where
  location (Bin _ _ _ r) = r
  location (Un _ _ r) = r
  location (MemberAccess _ _ r) = r
  location (Subscript _ _ r) = r
  location (Variable _ r) = r
  location (FuncCall _ _ r) = r
  location (ExprLit l) = location l
  location (TypeAssertion _ _ r) = r
instance Source (LiteralT v) where
  location (ILit _ r) = r
  location (FLit _ r) = r
  location (BLit _ r) = r
  location (Null r) = r
  location (Undef r) = r
  location (StructTupleLit _ r) = r
  location (StructLit _ r) = r
