{-# LANGUAGE OverloadedStrings, MultiParamTypeClasses #-}

module Main where

import System.Environment
import Text.PrettyPrint
import Language.Foveran.Parsing
import Language.Foveran.Typing

main :: IO ()
main = do
  filename:_ <- getArgs
  readResult <- readFoveranFile filename
  case readResult of 
    Left err ->
        putStrLn $ render (ppInputError err)
    Right decls ->
        checkDeclarations decls