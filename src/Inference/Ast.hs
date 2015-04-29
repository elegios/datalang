module Inference.Ast where

import NameResolution.Ast
import GlobalAst (SourceRange(..), TSize(..), BinOp(..), UnOp(..), TerminatorType(..), location, Source)
import qualified Data.Map as M

type CallableDef = CallableDefT TypeKey CompoundAccess
data CallableDefT t a = FuncDef
                        { callableName :: String
                        , intypes :: [t]
                        , outtype :: t
                        , inargs :: [Resolved]
                        , outarg :: Resolved
                        , callableBody :: StatementT t a
                        , callableRange :: SourceRange
                        }
                      | ProcDef
                        { callableName :: String
                        , intypes :: [t]
                        , outtypes :: [t]
                        , inargs :: [Resolved]
                        , outargs :: [Resolved]
                        , callableBody :: StatementT t a
                        , callableRange :: SourceRange
                        }

type Statement = StatementT TypeKey CompoundAccess
data StatementT t a = ProcCall (ExpressionT t a) [ExpressionT t a] [ExpressionT t a] SourceRange
                    | Defer (StatementT t a) SourceRange
                    | ShallowCopy (ExpressionT t a) (ExpressionT t a) SourceRange
                    | If (ExpressionT t a) (StatementT t a) (Maybe (StatementT t a)) SourceRange
                    | While (ExpressionT t a) (StatementT t a) SourceRange
                    | Scope [StatementT t a] SourceRange
                    | Terminator TerminatorType SourceRange
                    | VarInit Bool Resolved t (ExpressionT t a) SourceRange

type Expression = ExpressionT TypeKey CompoundAccess
data ExpressionT t a = Bin BinOp (ExpressionT t a) (ExpressionT t a) SourceRange
                     | Un UnOp (ExpressionT t a) SourceRange
                     | CompoundAccess (ExpressionT t a) a SourceRange
                     | Variable Resolved t SourceRange
                     | FuncCall (ExpressionT t a) [ExpressionT t a] t SourceRange
                     | ExprLit (LiteralT t)
                     deriving Show

type RepMap = M.Map Resolved Expression
data CompoundAccess = Expanded RepMap (Maybe Expression) Expression
                    | ExpandedMember String
                    | ExpandedSubscript Expression

type Literal = LiteralT TypeKey
data LiteralT t = ILit Integer t SourceRange
                | FLit Double t SourceRange
                | BLit Bool SourceRange
                | Null t SourceRange
                | Undef t SourceRange
                | Zero t SourceRange
                deriving Show

newtype TypeKey = TypeKey { representation :: Int } deriving (Eq, Ord, Show)

data FlatType = IntT TSize
              | UIntT TSize
              | FloatT TSize
              | BoolT
              | NamedT String [TypeKey]
              | TypeVar String
              | PointerT TypeKey
              | StructT [(String, TypeKey)]
              | FuncT [TypeKey] TypeKey
              | ProcT [TypeKey] [TypeKey]
              deriving (Show, Eq, Ord)

instance Source (CallableDefT t a) where
  location = callableRange
