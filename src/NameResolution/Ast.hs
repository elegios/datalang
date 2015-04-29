module NameResolution.Ast where

import Parser.Ast
import qualified Data.Map as M

data Resolved = Local
                { depth :: Int
                , name :: String
                }
              | Global
                { name :: String
                }
              | ReplacementLocal
                { member :: Bool
                , name :: String
                }
              | Self
              deriving (Eq, Ord, Show)

data ResolvedSource = ResolvedSource
  { types :: M.Map String (TypeDefT Resolved)
  , callables :: M.Map String (CallableDefT Resolved)
  }
