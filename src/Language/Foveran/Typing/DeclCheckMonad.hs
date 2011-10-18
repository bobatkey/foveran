{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing.DeclCheckMonad
    ( DeclCheckM ()
    , extend
    , reportError
    , liftTyCheck
    , evaluate
    , getContext -- FIXME: try to get rid of this
    , runDeclCheckM
    , checkDefinition -- FIXME: move this
    , checkInternalDefinition
    )
    where

import Control.Applicative
import Control.Monad (unless, ap)
import Control.Monad.IO.Class (MonadIO (..))
import Data.Traversable (traverse)
import Data.Text as T (unpack)
import Text.Position

import Text.PrettyPrint
import Text.PrettyPrint.IsString ()
import Language.Foveran.Util.PrettyPrinting

import Language.Foveran.Syntax.Display (Declaration (..), Definition (..), Datatype (..))
import qualified Language.Foveran.Syntax.Display as DS
import Language.Foveran.Syntax.Identifier (Ident)
import Language.Foveran.Syntax.LocallyNameless (toLocallyNamelessClosed)
import qualified Language.Foveran.Syntax.LocallyNameless as LN
import qualified Language.Foveran.Syntax.Checked as CS
import Language.Foveran.Parsing.PrettyPrinter
import Language.Foveran.Typing.Conversion (Value)
import Language.Foveran.Typing.Context
import Language.Foveran.Typing.Checker
import Language.Foveran.Typing.Errors

{------------------------------------------------------------------------------}
data Error
    = TypeError     TypeError
    | RepeatedIdent Ident
    | MalformedDefn Ident Ident

newtype DeclCheckM a = DM (Context -> IO (Either (Span, Error) (a,Context)))

instance Monad DeclCheckM where
  return x   = DM $ \ctxt -> return $ Right (x, ctxt)
  DM t >>= f = DM $ \ctxt -> do r <- t ctxt
                                case r of
                                  Left error      -> return $ Left error
                                  Right (a,ctxt') -> let DM t' = f a
                                                     in t' ctxt'

instance Functor DeclCheckM where
    fmap = liftA

instance Applicative DeclCheckM where
    pure  = return
    (<*>) = ap

instance MonadIO DeclCheckM where
    liftIO c = DM $ \ctxt -> do r <- c
                                return $ Right (r, ctxt)

getContext :: DeclCheckM Context
getContext = DM $ \c -> return (Right (c,c))

-- FIXME: consider splitting out the IDataDecl errors from the type errors
reportError :: Span -> TypeError -> DeclCheckM a
reportError p err = DM $ \ctxt -> return (Left (p,TypeError err))

liftTyCheck :: (Context -> TypingMonad Span a) -> DeclCheckM a
liftTyCheck f = DM $ \ctxt -> case f ctxt of
                                Error p err -> return $ Left  (p, TypeError err)
                                Result a    -> return $ Right (a, ctxt)

extend :: Span -> Ident -> Value -> Maybe Value -> DeclCheckM ()
extend p nm ty def =
    DM $ \ctxt ->
        case ctxtExtend ctxt nm ty def of
          Nothing    -> return $ Left (p, RepeatedIdent nm)
          Just ctxt' -> return $ Right ((), ctxt')

evaluate :: CS.Term -> DeclCheckM Value
evaluate t = DM $ \ctxt -> return $ Right (t `evalIn` ctxt, ctxt)

malformedDefinition :: Span -> Ident -> Ident -> DeclCheckM ()
malformedDefinition p nm1 nm2 = DM $ \_ -> return $ Left (p, MalformedDefn nm1 nm2)

checkDefinition :: Definition -> DeclCheckM ()
checkDefinition (Definition p nm extTy nm' extTm) =
    do unless (nm == nm') $ malformedDefinition p nm nm'
       liftIO $ do putStrLn ("Checking definition: " ++ T.unpack nm)
                   putStrLn $ render $ (   "Type: " <+> ppAnnotTerm extTy
                                        $$ "Term: " <+> ppAnnotTerm extTm)
                   putStrLn ""
       let ty = toLocallyNamelessClosed extTy
           tm = toLocallyNamelessClosed extTm
       checkInternalDefinition p nm ty (Just tm)

checkInternalDefinition :: Span -> Ident -> LN.TermPos -> Maybe LN.TermPos -> DeclCheckM ()
checkInternalDefinition p nm ty tm = do
  (_, cTy) <- liftTyCheck $ setCheck ty
  vTy      <- evaluate cTy
  cTm      <- traverse (\tm -> liftTyCheck $ flip (tyCheck tm) vTy) tm -- FIXME: get rid of this flip
  vTm      <- traverse evaluate cTm
  extend p nm vTy vTm
  

runDeclCheckM :: DeclCheckM () -> IO ()
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
