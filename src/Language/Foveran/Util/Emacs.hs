module Language.Foveran.Util.Emacs where

import System.Exit
import Text.PrettyPrint (render)
import Data.SExpr (pprint)
import Language.Forvie.Editor.EmacsMode
import Language.Forvie.Lexing.Spec (compileLexicalSpecification)

import Language.Foveran.Parsing.Token ()
import Language.Foveran.Parsing.LexicalSpec (lexicalSpec)

genEmacsMode :: IO a
genEmacsMode = do
  putStrLn $ render $ pprint $ generateElisp $ compileLexicalSpecification $ lexicalSpec
  exitSuccess
