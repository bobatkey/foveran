{-# LANGUAGE OverloadedStrings, MultiParamTypeClasses #-}

module Main where

import qualified Data.Text as T
import qualified Data.ByteString as B
import Data.Rec (AnnotRec)
import Control.Monad (unless)
import System.IO (stdin)
import Text.LexerGenerator (LexingError (..), Lexeme(..))
import Foveran.Parsing.Lexer (lexer)
import Foveran.Parsing.Parser (file)
import Text.ParserCombinators (parse, ParsingError (..))
import Control.StreamProcessor ((>>>))
import Control.StreamReader (SR, (>>|))
import Control.StreamReader.IO (onHandle)
import Control.StreamProcessor.DecodeUTF8 (decodeUTF8, UTF8DecodeError (..))
import Control.StreamProcessor.ByteString (deChunk)
import Foveran.Syntax.Display (Declaration (..), Definition (..), Datatype (..))
import Foveran.Syntax.LocallyNameless (toLocallyNameless)
import qualified Foveran.Syntax.Checked as CS
import Foveran.Parsing.PrettyPrinter
import Text.Position
import Text.PrettyPrint
import Text.PrettyPrint.IsString ()
import qualified Foveran.Parsing.Token as Tok
import Foveran.Typing.Conversion (Value)
import Foveran.Typing.Context
import Foveran.Typing.Checker
import Foveran.Typing.Errors
import Foveran.NameSupply (Ident)
import Foveran.Typing.DataDecl

ppPos p =
  text "line" <+> int (posLineNum p) <> comma <+> text "col" <+> int (posColumnNum p)

ppSpan (Span l r) =
  text "from" <+> ppPos l <+> text "to" <+> ppPos r

instance LexingError Doc where
    lexingErrAtEOS = text "Lexing error at End of File"
    lexingErrOnInput c p = text "Lexing error at" <+> ppPos p <+> text "on input" <+> char c

ppToken Nothing  = "End of file"
ppToken (Just t) = text $ show t

ppExpecting [] =
    "Expecting nothing"
ppExpecting [x] =
    "Expecting" <+> ppToken x
ppExpecting l =
    "Expecting one of" $$ nest 4 (hsep (map ppToken l))

instance ParsingError Tok.Token Doc where
    parseError Nothing               expecting =
        text "Parse error at End of File" 
        $$ ppExpecting expecting
    
    parseError (Just (Lexeme _ p s)) expecting =
        text "Parse error" <+> ppSpan p <+> text "on input" <+> text (show s)
        $$ ppExpecting expecting

instance UTF8DecodeError Doc where
    utf8DecodeError s = "UTF-8 Decoding error:" <+> text s

parseFile :: SR Doc B.ByteString [Declaration]
parseFile = deChunk >>> decodeUTF8 >>> lexer >>| parse file

data Error
    = TypeError     TypeError
    | RepeatedIdent Ident
    | MalformedDefn Ident Ident

newtype DeclCheckM p a = DM (Context -> IO (Either (p, Error) (a,Context)))

instance Monad (DeclCheckM p) where
  return x   = DM $ \ctxt -> return $ Right (x, ctxt)
  DM t >>= f = DM $ \ctxt -> do r <- t ctxt
                                case r of
                                  Left error      -> return $ Left error
                                  Right (a,ctxt') -> let DM t' = f a
                                                     in t' ctxt'

liftTyCheck :: (Context -> TypingMonad p a) -> DeclCheckM p a
liftTyCheck f = DM $ \ctxt -> case f ctxt of
                                Error p err -> return $ Left  (p, TypeError err)
                                Result a    -> return $ Right (a, ctxt)

extend :: p -> Ident -> Value -> Maybe Value -> DeclCheckM p ()
extend p nm ty def = DM $ \ctxt -> case ctxtExtend ctxt nm ty def of
                                     Nothing    -> return $ Left (p, RepeatedIdent nm)
                                     Just ctxt' -> return $ Right ((), ctxt')

evaluate :: CS.Term -> DeclCheckM p Value
evaluate t = DM $ \ctxt -> return $ Right (t `evalIn` ctxt, ctxt)

malformedDefinition :: p -> Ident -> Ident -> DeclCheckM p ()
malformedDefinition p nm1 nm2 = DM $ \_ -> return $ Left (p, MalformedDefn nm1 nm2)

liftIO :: IO a -> DeclCheckM p a
liftIO c = DM $ \ctxt -> do r <- c
                            return $ Right (r, ctxt)

checkDefinition :: Definition -> DeclCheckM Span ()
checkDefinition (Definition p nm extTy nm' extTm) =
    do unless (nm == nm') $ malformedDefinition p nm nm'
       liftIO $ do putStrLn ("Checking definition: " ++ T.unpack nm)
                   putStrLn $ render $ ("Type: " <+> ppAnnotTerm extTy
                                        $$ "Term: " <+> ppAnnotTerm extTm)
                   putStrLn ""
       let ty = toLocallyNameless extTy
           tm = toLocallyNameless extTm
       (_, cTy) <- liftTyCheck $ setCheck ty
       vTy <- evaluate cTy
       cTm <- liftTyCheck $ flip (tyCheck tm) vTy -- FIXME: get rid of this flip
       vTm <- evaluate cTm
       extend p nm vTy (Just vTm)

checkDatatype :: Datatype -> DeclCheckM Span ()
checkDatatype d =
    do checkDefinition (genDesc d)
       checkDefinition (genDatatypeCarrier d)
       mapM_ checkDefinition (genConstructors d)

checkDecl :: Declaration -> DeclCheckM Span ()
checkDecl (AssumptionDecl p nm extTm) =
  do let t = toLocallyNameless extTm
     (_, c) <- liftTyCheck $ setCheck t
     v <- evaluate c
     extend p nm v Nothing
checkDecl (DefinitionDecl d) = checkDefinition d
checkDecl (DatatypeDecl d)   = checkDatatype d

runDeclCheckM :: DeclCheckM Span () -> IO ()
runDeclCheckM (DM f) =
    do r <- f emptyContext
       case r of
         Right ((), _)   -> return ()
         Left (p, TypeError e) ->
             putStrLn $ render $ text "Type error in term" <+> ppSpan p
                                 $$ nest 2 (ppTypeError e)
         Left (p, RepeatedIdent nm) ->
             putStrLn $ render $ "Repeated binding" <+> "“" <> text (T.unpack nm) <> "”" <+> "at" <+> ppSpan p
         Left (p, MalformedDefn nm1 nm2) ->
             putStrLn $ "Malformed definition at " ++ show p

main :: IO ()
main = do
  result <- onHandle stdin 8192 parseFile
  case result of
    Left err ->
        putStrLn $ render err
    Right decls ->
        runDeclCheckM $ mapM_ checkDecl decls
{-      flip mapM_ decls
        $ \d -> do putStrLn $ render $ ppDecl d
                   putStrLn ""
-}
