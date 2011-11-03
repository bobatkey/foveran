{-# LANGUAGE OverloadedStrings, FlexibleInstances, GeneralizedNewtypeDeriving #-}

module Language.Foveran.Typing.DeclCheckMonad
    ( DeclCheckM ()
    , extend -- FIXME: try to get rid of this
    , reportError
    , malformedDefinition
    , liftTyCheck
    , evaluate
    , getContext -- FIXME: try to get rid of this
    , runDeclCheck
    , checkInternalDefinition
    )
    where

import           Control.Applicative
import           Control.Monad (unless, ap)
import           Control.Monad.IO.Class (MonadIO (..))
import           Control.Monad.State (StateT, get, put, evalStateT)
import qualified Control.Monad.Error as E
import           Control.Monad.Error (ErrorT, runErrorT, throwError, MonadError)
import           Data.Traversable (traverse)
import           Text.Position (Span)

import           Text.PrettyPrint (render, (<+>), ($$), nest, (<>))
import           Text.PrettyPrint.IsString ()
import           Language.Foveran.Util.PrettyPrinting (ppSpan)
import           Language.Foveran.Parsing.PrettyPrinter (ppIdent)

import           Language.Foveran.Syntax.Identifier (Ident)
import           Language.Foveran.Syntax.LocallyNameless (TermPos)
import qualified Language.Foveran.Syntax.Checked as CS

import           Language.Foveran.Typing.Conversion (Value)
import           Language.Foveran.Typing.Context
import           Language.Foveran.Typing.Checker
import           Language.Foveran.Typing.Errors

{------------------------------------------------------------------------------}
data Error
    = TypeError     TypeError
    | RepeatedIdent Ident
    | MalformedDefn Ident Ident

newtype DeclCheckM a = DM { runDM :: StateT Context (ErrorT (Span, Error) IO) a }
    deriving (Monad, Applicative, Functor, MonadIO, MonadError (Span,Error))

instance E.Error (Span, Error) where
    noMsg = error "noMsg: not supported for Error"
    strMsg = error "strMsg: not support for Error"

getContext :: DeclCheckM Context
getContext = DM $ get

-- FIXME: consider splitting out the IDataDecl errors from the type errors
reportError :: Span -> TypeError -> DeclCheckM a
reportError p err = throwError (p,TypeError err)

liftTyCheck :: (Context -> TypingMonad Span a) -> DeclCheckM a
liftTyCheck f = do
  ctxt <- DM get
  case runTypingMonad $ f ctxt of
    Left (p, err) -> throwError (p, TypeError err)
    Right (a,_)   -> return a

extend :: Span -> Ident -> Value -> Maybe Value -> DeclCheckM ()
extend p nm ty def = do
  do ctxt <- DM $ get
     case ctxtExtend ctxt nm ty def of
       Nothing    -> throwError (p, RepeatedIdent nm)
       Just ctxt' -> DM $ put ctxt'

evaluate :: CS.Term -> DeclCheckM Value
evaluate t = do ctxt <- DM $ get
                return (t `evalIn` ctxt)

malformedDefinition :: Span -> Ident -> Ident -> DeclCheckM ()
malformedDefinition p nm1 nm2 =
    throwError (p, MalformedDefn nm1 nm2)

checkInternalDefinition :: Span -> Ident -> TermPos -> Maybe TermPos -> DeclCheckM ()
checkInternalDefinition p nm ty tm = do
  -- FIXME: check for duplicate names before we bother type checking
  (_, cTy) <- liftTyCheck $ setCheck ty
  vTy      <- evaluate cTy
  cTm      <- traverse (\tm -> liftTyCheck $ flip (tyCheck tm) vTy) tm -- FIXME: get rid of this flip
  vTm      <- traverse evaluate cTm
  extend p nm vTy vTm

runDeclCheck :: DeclCheckM () -> IO ()
runDeclCheck e =
    do r <- runErrorT $ evalStateT (runDM e) emptyContext
       case r of
         Right () -> return ()
         Left (p, TypeError e) ->
             putStrLn $ render $ "Type error in term" <+> ppSpan p
                                 $$ nest 2 (ppTypeError e)
         Left (p, RepeatedIdent nm) ->
             putStrLn $ render $ "Repeated binding" <+> "“" <> ppIdent nm <> "”" <+> "at" <+> ppSpan p
         Left (p, MalformedDefn nm1 nm2) ->
             putStrLn $ "Malformed definition at " ++ show p
