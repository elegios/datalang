module Main where

import Lispy.Parser (parseFile, pretty)

import System.Environment (getArgs)

main = do
  path : _ <- getArgs
  parseFile path >>= either print (putStrLn . pretty)
