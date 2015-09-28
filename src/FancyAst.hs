{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UndecidableInstances #-}

module FancyAst where
  
data SourceLoc = SourceLoc FilePath Line Column
type Line = Int
type Column = Int
data SourceRange = SourceRange SourceLoc SourceLoc
data Location = ExpandedLoc Location SourceRange | OriginalLoc SourceRange

nowhere :: Location
nowhere = OriginalLoc $ SourceRange (SourceLoc "nowhere" 0 0) (SourceLoc "nowhere" 0 0)

data Name -- TODO: a sum type of unresolved and the various kinds of resolved names

type LocStmtF expr stmnt = TagF (StmtF expr) Location
data StmtF expr stmnt = ProcCall Inline expr [expr] [expr]
                      | ShallowCopy expr expr
                      | If expr stmnt (Maybe stmnt)
                      | While expr stmnt
                      | Scope [stmnt]
                      | Terminator TerminatorType
                      | VarInit Bool Name expr deriving Functor

type LocExprF access expr = TagF (ExprF access) Location
data ExprF access expr = Bin BinOp expr expr
                       | Un UnOp expr
                       | CompoundAccess expr access
                       | Variable Name
                       | FuncCall Inline expr [expr]
                       | ExprLit (Literal expr) deriving Functor

data Literal expr = ILit Integer
                  | FLit Double
                  | BLit Bool
                  | Null
                  | Undef
                  | Zero
                  | TupLit [expr] deriving Functor

newtype TagF f a r = TagF (f r, a) deriving Functor

class UnTag f b | f -> b where
  untag :: f a -> b a

instance UnTag (StmtF stmnt) (StmtF stmnt) where
  untag = id
instance UnTag (ExprF access) (ExprF access) where
  untag = id

instance UnTag f inner => UnTag (TagF f a) inner where
  untag (TagF (on, _)) = untag on

class Tagged a tag where
  tagMap :: (tag -> tag) -> a -> a

instance Tagged (TagF f tag r) tag where
  tagMap f (TagF (r, a)) = TagF (r, f a)

instance Tagged (f r) iTag => Tagged (TagF f oTag r) iTag where
  tagMap f (TagF (r, a)) = TagF (tagMap f r, a)

data BinOp = Plus | Minus | Times | Divide | Remainder
           | Lesser | Greater | LE | GE | Equal | NotEqual
           | ShortAnd | ShortOr | LongAnd | LongOr
           | BinAnd | BinOr | LShift | LogRShift | AriRShift | Xor
           deriving (Show, Eq)
data UnOp = Not | BinNegate | AriNegate | Deref | AddressOf deriving Show

data TerminatorType = Return | Break | Continue deriving (Show, Eq)

data Inline = NeverInline | UnspecifiedInline | AlwaysInline deriving (Show, Ord, Eq)
