{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Lispy.Parser.Data where

import Lispy.Ast (UnTag(untag), TagF(..), Location, nowhere)
import Data.Functor.Foldable (Fix(..), cata)
import qualified Text.PrettyPrint as P

type Token = Fix (TagF TokF Location)
type LocTokF tok = TagF TokF Location tok
data TokF tok = Identifier String
              | Symbol String
              | LiteralToken (Literal tok)
              | Statements [[tok]]
              | List [tok]
              | MemberAccess [tok] deriving (Show, Functor)
data Literal tok = IntLit Integer
                 | FloatLit Double
                 | BoolLit Bool
                 | StringLit String
                 | TupleLit [tok]
                 | UndefLit
                 | NullLit deriving (Show, Functor)

instance UnTag TokF TokF where
  untag = id

pretty :: [[Token]] -> String
pretty = P.render . cata alg . Fix . TagF . (, nowhere) . Statements
  where
    (<>) = (P.<>)
    ($+$) = (P.$+$)
    nest = P.nest
    vcat = P.vcat
    hsep = P.hsep
    text = P.text
    sep = P.sep
    u = untag
    alg :: LocTokF P.Doc -> P.Doc
    alg (u -> Statements stmnts) = text "{" $+$ nest 2 (vcat $ hsep <$> stmnts) $+$ text "}"
    alg (u -> Symbol s) = text "\'" <> text s
    alg (u -> Identifier s) = text s
    alg (u -> LiteralToken l) = case l of
      IntLit i -> text $ show i
      FloatLit f -> text $ show f
      BoolLit b -> if b then text "true" else text "false"
      StringLit s -> text "\"" <> text s <> text "\""
      TupleLit toks -> text "'(" <> sep toks <> text ")"
      UndefLit -> text "_"
      NullLit -> text "null"
    alg (u -> List toks) = text "(" <> sep toks <> text ")"
    alg (u -> MemberAccess toks) = text "[" <> sep toks <> text "]"
