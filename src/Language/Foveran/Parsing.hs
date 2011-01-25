{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses, OverloadedStrings #-}

-- | Implementation of the Foveran parsing process, from bytes on disk
-- up to abstract syntax trees in "Foveran.Syntax.Checked" form.

module Language.Foveran.Parsing
    ( readFoveranFile
    , ppInputError
    )
    where

import Control.Category ((>>>))
import Data.ByteString (ByteString)
import qualified Data.Text as T
import Text.PrettyPrint
import Text.PrettyPrint.IsString
import Text.Position
import Control.StreamProcessor
import Control.StreamProcessor.ByteString
import Control.StreamProcessor.UTF8
import Control.StreamProcessor.IO

import Text.ParserCombinators
import Language.Forvie.Lexing.Spec
import Language.Forvie.Lexing.Generator

import Language.Foveran.Util.PrettyPrinting

import Language.Foveran.Syntax.Display (Declaration)

import Language.Foveran.Parsing.Token
import Language.Foveran.Parsing.LexicalSpec
import Language.Foveran.Parsing.Parser

--------------------------------------------------------------------------------
data InputError
    = PE_UTF8DecodeError String
    | PE_LexingError     (Maybe (Char, Position))
    | PE_ParsingError    (Maybe (Lexeme Token)) [Maybe Token]

instance UTF8DecodeError InputError where
    utf8DecodeError = PE_UTF8DecodeError

instance LexingError InputError where
    lexingErrAtEOS       = PE_LexingError Nothing
    lexingErrOnInput c p = PE_LexingError (Just (c,p))
    
instance ParsingError Token InputError where
    parseError = PE_ParsingError

--------------------------------------------------------------------------------
ppToken Nothing  = "End of file"
ppToken (Just t) = text $ show t

ppExpecting [] =
    "Expecting nothing"
ppExpecting [x] =
    "Expecting" <+> ppToken x
ppExpecting l =
    "Expecting one of" $$ nest 4 (hsep (map ppToken l))

ppInputError :: InputError -> Doc
ppInputError (PE_UTF8DecodeError s) =
    "UTF-8 Decoding error" <> colon <+> text s
ppInputError (PE_LexingError Nothing) =
    "Lexing error at the end of the file, incomplete token"
ppInputError (PE_LexingError (Just (c, p))) =
    "Lexing error at" <+> ppPos p <+> "on input" <+> char c
ppInputError (PE_ParsingError Nothing expecting) =
    "Parsing error at end of the file" $$ ppExpecting expecting
ppInputError (PE_ParsingError (Just (Lexeme _ p s)) expecting) =
    "Parse error" <+> ppSpan p <+> "on input" <+> text (T.unpack s)
    $$ ppExpecting expecting

--------------------------------------------------------------------------------

parser :: SR InputError ByteString [Declaration]
parser =
    deChunk >>>
    decodeUTF8 >>>
    $(lexerSPStatic (compileLexicalSpecification lexicalSpec)) >>>
    exceptIgnorable >>|
    parse file

readFoveranFile :: FilePath -> IO (Either InputError [Declaration])
readFoveranFile filename = onFile filename 8192 parser
