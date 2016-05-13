{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Editor.EmacsMode
    ( generateEmacsMode )
    where

import           Paths_Foveran
import           System.IO (stdout)
import           Data.SExpr (SExpr (..), pprint)
import           Text.PrettyPrint (render)
import           Data.FiniteStateMachine.Deterministic.Elisp (makeTransitionFunctionCharTables)
import           Language.Foveran.Lexing.Spec (CompiledLexSpec (..), Classification (..), SyntaxHighlight (..))
import           Language.Foveran.Util.Templater
import qualified Data.ByteString as B
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE

toFace :: Classification -> SExpr
toFace Comment     = Atom "'comment"
toFace Keyword     = Atom "'keyword"
toFace Identifier  = Atom "'identifier"
toFace Punctuation = Atom "'punctuation"
toFace Whitespace  = Atom "'whitespace"
toFace Constant    = Atom "'constant"
toFace Operator    = Atom "'operator"
toFace Constructor = Atom "'constructor"
toFace Type        = Atom "'type"

generateElisp :: SyntaxHighlight tok =>
                 String ->
                 CompiledLexSpec tok ->
                 [SExpr]
generateElisp name =
    makeTransitionFunctionCharTables name . fmap (toFace . lexicalClass) . lexSpecDFA

-- | Generate the Emacs lisp code for a simple emacs major mode based
-- on the provided lexical specification.
--
-- The Emacs lisp code is sent to `stdout`.
--
-- The generated major mode has the following features:
-- 
-- * Accurate syntax highlighting based on the lexical specification
generateEmacsMode :: SyntaxHighlight tok =>
                     CompiledLexSpec tok -- ^ Lexical specification to be used for syntax highlighting
                  -> T.Text              -- ^ The name for this mode, used to prefix all the generated elisp functions
                  -> T.Text              -- ^ An emacs-style regular expression for filenames where this mode should be used
                  -> IO ()               -- ^ `IO` action that emits Elisp code to `stdout`
generateEmacsMode lexSpec modename fileregexp =
    do mapM_ (putStrLn . render . pprint) (generateElisp (T.unpack modename) lexSpec)
       templateFilename <- getDataFileName "elisp/mode-template.el"
       template <- B.readFile templateFilename
       B.hPut stdout (applyVariableSubstitution subst template)
    where
      subst :: [(B.ByteString, B.ByteString)]
      subst = [ (TE.encodeUtf8 "modename",   TE.encodeUtf8 modename)
              , (TE.encodeUtf8 "fileregexp", TE.encodeUtf8 fileregexp)
              ]
