{-# LANGUAGE OverloadedStrings, FlexibleInstances, GeneralizedNewtypeDeriving, TypeOperators #-}

module Language.Foveran.Typing.DeclCheckMonad
    ( DeclCheckM ()
    , extend -- FIXME: try to get rid of this
    , reportDataDeclError
    , reportMalformedDefinition
    , runTyping
    , runTypingNoHoles
    , evaluate
    , getContext -- FIXME: try to get rid of this
    , runDeclCheck
    , checkDefinition )
    where

import           Control.Applicative
import           Control.Monad (unless, ap)
import           Control.Monad.IO.Class (MonadIO (..))
import           Control.Monad.State (StateT, get, put, evalStateT)
import qualified Control.Monad.Error as E
import           Control.Monad.Error (ErrorT, runErrorT, throwError, MonadError)
import           Data.Rec (AnnotRec (Annot))
import           Data.Traversable (traverse)
import           Text.Position (Span)

import           Text.PrettyPrint (render, (<+>), ($$), nest, (<>), vcat, text)
import           Language.Foveran.Util.PrettyPrinting (ppSpan)
import           Language.Foveran.Parsing.PrettyPrinter (ppIdent, ppPlain)

import           Language.Foveran.Syntax.Identifier (Ident, runNameGeneration)
import           Language.Foveran.Syntax.LocallyNameless (TermPos)
import qualified Language.Foveran.Syntax.Checked as CS

import           Language.Foveran.Typing.Conversion (Value, evalIn)
import           Language.Foveran.Typing.DefinitionContext
import           Language.Foveran.Typing.Context
import           Language.Foveran.Typing.LocalContext
import           Language.Foveran.Typing.Hole
import           Language.Foveran.Typing.Checker
import           Language.Foveran.Typing.Errors

{------------------------------------------------------------------------------}
data Error
    = TypeError     (Context :>: LocalContext) TypeError
    | DataDeclError DataDeclError
    | RepeatedIdent Ident
    | MalformedDefn Ident Ident
    | IncompleteTyping

newtype DeclCheckM a = DM { runDM :: StateT Context (ErrorT (Span, Error) IO) a }
    deriving (Monad, Applicative, Functor, MonadIO, MonadError (Span,Error))

instance E.Error (Span, Error) where
    noMsg = error "noMsg: not supported for Error"
    strMsg = error "strMsg: not support for Error"

getContext :: DeclCheckM Context
getContext = DM $ get

reportDataDeclError :: Span -> DataDeclError -> DeclCheckM a
reportDataDeclError p err = throwError (p, DataDeclError err)

reportMalformedDefinition :: Span -> Ident -> Ident -> DeclCheckM ()
reportMalformedDefinition p nm1 nm2 =
    throwError (p, MalformedDefn nm1 nm2)

runTyping :: TypingMonad Context a -> DeclCheckM (a,Holes)
runTyping f = do
  ctxt <- DM get
  case runTypingMonad f ctxt noHoles emptyLocalContext of
    Left (p, holes, lctxt, err) ->
        do throwError (p, TypeError (ctxt :>: lctxt) err)
    Right (a, holes)  ->
        do return (a, holes)

runTypingNoHoles :: Span
                 -> TypingMonad Context a
                 -> DeclCheckM a
runTypingNoHoles p t = do
  (a, holes) <- runTyping t
  case getHoles holes of
    [] -> return a
    _  -> throwError (p, IncompleteTyping)

extend :: Span -> Ident -> Value -> Maybe Value -> DeclCheckM ()
extend p nm ty def = do
  ctxt <- DM $ get
  case extendContext ctxt nm ty def of
    Nothing    -> throwError (p, RepeatedIdent nm)
    Just ctxt' -> DM $ put ctxt'

evaluate :: CS.Term -> DeclCheckM Value
evaluate t = do
  ctxt <- DM $ get
  return (evalIn t ctxt noHoles)

positionOf :: TermPos -> Span
positionOf (Annot p _) = p

checkDefinition :: Span -> Ident -> TermPos -> Maybe TermPos -> DeclCheckM ()
checkDefinition p nm ty Nothing = do
  cTy <- runTypingNoHoles (positionOf ty) $ isType ty
  vTy <- evaluate cTy
  extend p nm vTy Nothing
checkDefinition p nm ty (Just tm) = do
  cTy <- runTypingNoHoles (positionOf ty) $ isType ty
  vTy <- evaluate cTy
  (cTm, holes) <- runTyping $ tm `hasType` vTy
  ctxt <- DM $ get
  case getHoles holes of
    [] -> do vTm <- evaluate cTm
             extend p nm vTy (Just vTm)
    h  -> do liftIO $ putStrLn $ render $    "Generated holes:" <+> text (show (length h))
                                          $$ nest 2 (vcat (map (uncurry (ppHole ctxt)) $ reverse h))
                                          -- $$ "Term:"
                                          -- $$ nest 2 (ppPlain $ runNameGeneration ctxt $ CS.toDisplaySyntax $ cTm)
             extend p nm vTy Nothing

runDeclCheck :: DeclCheckM () -> IO ()
runDeclCheck e = do
  r <- runErrorT $ evalStateT (runDM e) emptyContext
  case r of
    Right () -> return ()
    Left (p, TypeError ctxt e) ->
        putStrLn $ render $ "Type error in term" <+> ppSpan p
                            $$ nest 2 (ppTypeError ctxt e)
    Left (p, RepeatedIdent nm) ->
        putStrLn $ render $ "Repeated binding" <+> "“" <> ppIdent nm <> "”" <+> "at" <+> ppSpan p
    Left (p, MalformedDefn nm1 nm2) ->
        putStrLn $ "Malformed definition at " ++ show p
    Left (p, IncompleteTyping) ->
        putStrLn $ "Incomplete typing at " ++ show p
    Left (p, DataDeclError e) ->
        putStrLn $ render $ "Data Declaration error at" <+> ppSpan p <> ":" <+> ppDataDeclError e