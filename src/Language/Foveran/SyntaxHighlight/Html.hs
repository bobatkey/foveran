{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module         :  Language.Foveran.SyntaxHighlight.Html
-- Copyright      :  Robert Atkey 2012
-- License        :  BSD3
--
-- Maintainer     :  bob.atkey@gmail.com
-- Stability      :  experimental
-- Portability    :  unknown
--
-- Functions for converting 'Lexeme's to HTML, classified according to
-- the 'SyntaxHighlight' class.

module Language.Foveran.SyntaxHighlight.Html
    ( generateHtml )
    where

import           Prelude hiding (foldl)
import           Text.Blaze.Html5 ((!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import           Data.MonadicStream (Reader, foldl)
import           Language.Foveran.Lexing.Spec
import           Text.Lexeme

highlightLexeme :: SyntaxHighlight tok => Lexeme tok -> H.Html
highlightLexeme (Lexeme tok _ txt) =
    classOf tok $ H.toHtml txt

classOf :: SyntaxHighlight tok => tok -> H.Html -> H.Html
classOf tok =
    case lexicalClass tok of
      Comment     -> H.span ! A.class_ "comment"
      Keyword     -> H.span ! A.class_ "keyword"
      Identifier  -> H.span ! A.class_ "identifier"
      Punctuation -> H.span ! A.class_ "punctuation"
      Operator    -> H.span ! A.class_ "operator"
      Constant    -> H.span ! A.class_ "constant"
      Constructor -> H.span ! A.class_ "constructor"
      Whitespace  -> \x -> x
      Type        -> H.span ! A.class_ "type"

-- | Convert a stream of 'Lexeme's tagged with 'SyntaxHighlight'able
-- tokens into a piece of @pre@formatted HTML. Each non-'WhiteSpace'
-- 'Lexeme' is wrapped in a @\<span class=\"XXX\"\>@ element, where the
-- class depends on the 'Classification' of the Lexeme:
--
--    ['Comment'] becomes @comment@.
--
--    ['Keyword'] becomes @keyword@.
--
--    ['Identifier'] becomes @identifier@.
--
--    ['Punctuation'] becomes @punctuation@.
--
--    ['Operator'] becomes @operator@.
--
--    ['Constant'] becomes @constant@.
-- 
--    ['Constructor'] becomes @constructor@.
--
--    ['Type'] becomes @type@.
--
-- The entire output is then wrapped in a @\<pre\>@ tag.
generateHtml :: (SyntaxHighlight tok, Monad m) =>
                Reader (Lexeme tok) m H.Html
generateHtml =
    H.pre <$> foldl (\doc lexeme -> doc `mappend` highlightLexeme lexeme) mempty
