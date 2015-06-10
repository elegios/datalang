{-# LANGUAGE LambdaCase #-}

module GlobalAst
( SourceRange(..)
, SourceLoc(..)
, nowhere
, TSize(..)
, getSizeFromTSize
, BinOp(..)
, UnOp(..)
, TerminatorType(..)
, Inline(..)
, Source
, location
) where

-- ### Locations in source code
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

class Source a where
  location :: a -> SourceRange

-- ### Various 'enums' used throughout the compiler

-- NOTE: Short/Long And/Or means shortcutting/not shortcutting
data BinOp = Plus | Minus | Times | Divide | Remainder
           | Lesser | Greater | LE | GE | Equal | NotEqual
           | ShortAnd | ShortOr | LongAnd | LongOr
           | BinAnd | BinOr | LShift | LogRShift | AriRShift | Xor
           deriving (Show, Eq)
data UnOp = Not | BinNegate | AriNegate | Deref | AddressOf deriving Show

data TerminatorType = Return | Break | Continue deriving (Show, Eq)

data Inline = NeverInline | UnspecifiedInline | AlwaysInline deriving (Show, Ord, Eq)

data TSize = S8 | S16 | S32 | S64 deriving (Show, Ord, Eq)

getSizeFromTSize :: Integral a => TSize -> a
getSizeFromTSize = \case S8 -> 8; S16 -> 16; S32 -> 32; S64 -> 64
