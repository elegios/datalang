module Inference.Ast where

import NameResolution.Ast
import GlobalAst (SourceRange(..), TSize(..), BinOp(..), UnOp(..), TerminatorType(..), location, Source)
import qualified Data.Map as M

type CallableDef = CallableDefT TypeKey CompoundAccess Literal
data CallableDefT t a l = FuncDef
                        { callableName :: String
                        , intypes :: [t]
                        , outtype :: t
                        , inargs :: [Resolved]
                        , outarg :: Resolved
                        , callableBody :: StatementT t a l
                        , callableRange :: SourceRange
                        }
                      | ProcDef
                        { callableName :: String
                        , intypes :: [t]
                        , outtypes :: [t]
                        , inargs :: [Resolved]
                        , outargs :: [Resolved]
                        , callableBody :: StatementT t a l
                        , callableRange :: SourceRange
                        }

type Statement = StatementT TypeKey CompoundAccess Literal
data StatementT t a l = ProcCall (ExpressionT t a l) [ExpressionT t a l] [ExpressionT t a l] SourceRange
                      | Defer (StatementT t a l) SourceRange
                      | ShallowCopy (ExpressionT t a l) (ExpressionT t a l) SourceRange
                      | If (ExpressionT t a l) (StatementT t a l) (Maybe (StatementT t a l)) SourceRange
                      | While (ExpressionT t a l) (StatementT t a l) SourceRange
                      | Scope [StatementT t a l] SourceRange
                      | Terminator TerminatorType SourceRange
                      | VarInit Bool Resolved t (ExpressionT t a l) SourceRange

type Expression = ExpressionT TypeKey CompoundAccess Literal
data ExpressionT t a l = Bin BinOp (ExpressionT t a l) (ExpressionT t a l) SourceRange
                     | Un UnOp (ExpressionT t a l) SourceRange
                     | CompoundAccess (ExpressionT t a l) a SourceRange
                     | Variable Resolved t SourceRange
                     | FuncCall (ExpressionT t a l) [ExpressionT t a l] t SourceRange
                     | ExprLit l
                     deriving Show

type RepMap = M.Map Resolved Expression
data CompoundAccess = Expanded RepMap (Maybe Expression) Expression
                    | ExpandedMember String
                    | ExpandedSubscript Expression

data Literal = ILit Integer TypeKey SourceRange
             | FLit Double TypeKey SourceRange
             | BLit Bool SourceRange
             | Null TypeKey SourceRange
             | Undef TypeKey SourceRange
             | Zero TypeKey SourceRange
             | StructLit [(String, Expression)] TypeKey SourceRange

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

instance Source (CallableDefT t a l) where
  location = callableRange
