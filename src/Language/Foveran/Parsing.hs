{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses, OverloadedStrings #-}

-- | Implementation of the Foveran parsing process, from bytes on disk
-- up to abstract syntax trees in "Foveran.Syntax.Display" form.

module Language.Foveran.Parsing
    ( parseFile
    , lexFile
    , ppInputError
    )
    where

import           Prelude hiding (map, lex, filter)
import           Control.Monad.Error (Error (..))
import           Data.Functor ((<$>))
import qualified Data.ByteString as B
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import           Data.MonadicStream
import           Text.PrettyPrint
import           Text.PrettyPrint.IsString
import           Text.Position

import           Text.ParserCombinators
import           Text.Lexeme (Lexeme (Lexeme))
import           Language.Forvie.Lexing.Spec
import           Language.Forvie.Lexing.Text
import           Language.Forvie.Layout

import           Language.Foveran.Util.PrettyPrinting

import           Language.Foveran.Syntax.Display (Declaration)

import           Language.Foveran.Parsing.Token
import           Language.Foveran.Parsing.LexicalSpec
import           Language.Foveran.Parsing.Parser

--------------------------------------------------------------------------------
data InputError
    = PE_LexingError     (Maybe (Char, Position))
    | PE_ParsingError    (Maybe (Lexeme Token)) [Maybe Token]
    | PE_LayoutError     Span

instance Error InputError where
    
  
instance ParsingError Token InputError where
    parseError = PE_ParsingError

instance LayoutError InputError where
    layoutError = PE_LayoutError

--------------------------------------------------------------------------------
ppToken :: Maybe Token -> Doc
ppToken Nothing  = "End of file"
ppToken (Just t) = text $ show t

ppExpecting :: [Maybe Token] -> Doc
ppExpecting [] =
    "Expecting nothing"
ppExpecting [x] =
    "Expecting" <+> ppToken x
ppExpecting l =
    "Expecting one of" $$ nest 4 (hsep (fmap ppToken l))

ppInputError :: InputError -> Doc
ppInputError (PE_LexingError Nothing) =
    "Lexing error at the end of the file, incomplete token"
ppInputError (PE_LexingError (Just (c, p))) =
    "Lexing error at" <+> ppPos p <+> "on input" <+> char c
ppInputError (PE_ParsingError Nothing expecting) =
    "Parsing error at end of the file" $$ ppExpecting expecting
ppInputError (PE_ParsingError (Just (Lexeme _ p s)) expecting) =
    "Parse error" <+> ppSpan p <+> "on input" <+> text (T.unpack s)
    $$ ppExpecting expecting
ppInputError (PE_LayoutError p) =
    "Layout error at" <+> ppSpan p

{------------------------------------------------------------------------------}
lexer :: T.Text
      -> Stream (Either InputError) (Lexeme (Action (NewlineOr Token)))
lexer text =
    lex lexicalSpec
        (OnError $ Left . PE_LexingError)
        text

exceptIgnorable :: Monad m => Processor (Lexeme (Action tok)) m (Lexeme tok)
exceptIgnorable = filter f
    where f (Lexeme (Ignore _) _ _) = Nothing
          f (Lexeme (Emit   t) p s) = Just (Lexeme t p s)

parser :: T.Text -> Either InputError [Declaration]
parser text = lexer text |>| (exceptIgnorable >>| (layout >>| parse file))

{------------------------------------------------------------------------------}
parseFile :: FilePath
          -> IO (Either InputError [Declaration])
parseFile filename = do
  text <- TE.decodeUtf8 <$> B.readFile filename
  return (parser text)

lexFile :: FilePath
        -> IO (Stream (Either InputError) (Lexeme (Action (NewlineOr Token))))
lexFile filename = do
  text <- TE.decodeUtf8 <$> B.readFile filename
  return (lexer text)
