{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing.DeclCheckMonad
    ( DeclCheckM ()
    , checkDecl
    , extend
    , runDeclCheckM
    )
    where

import Control.Monad (unless)

import Data.Text as T (unpack)
import Text.Position

import Text.PrettyPrint
import Text.PrettyPrint.IsString ()
import Language.Foveran.Util.PrettyPrinting

import Language.Foveran.Syntax.Display (Declaration (..), Definition (..), Datatype (..))
import qualified Language.Foveran.Syntax.Display as DS
import Language.Foveran.Syntax.LocallyNameless (Ident, toLocallyNameless)
import qualified Language.Foveran.Syntax.Checked as CS
import Language.Foveran.Parsing.PrettyPrinter
import Language.Foveran.Typing.Conversion (Value)
import Language.Foveran.Typing.Context
import Language.Foveran.Typing.Checker
import Language.Foveran.Typing.Errors
import Language.Foveran.Typing.DataDecl

{------------------------------------------------------------------------------}
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

getContext :: DeclCheckM p Context
getContext = DM $ \c -> return (Right (c,c))

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

doNormalise :: DS.TermPos -> DeclCheckM Span ()
doNormalise tmDS = do
  let tm = toLocallyNameless tmDS
  (ty,c) <- liftTyCheck $ tySynth tm
  v <- evaluate c
  ctxt <- getContext
  let d  = ppTerm ctxt v ty
      d0 = ppPlain $ contextNameSupply ctxt $ CS.toDisplaySyntax c
  liftIO $ putStrLn $ render $ ("normalised: "
                                $$ nest 4 d0
                                $$ "to"
                                $$ nest 4 d
                                $$ "")
  return ()

checkDecl :: Declaration -> DeclCheckM Span ()
checkDecl (AssumptionDecl p nm extTm) =
  do let t = toLocallyNameless extTm
     (_, c) <- liftTyCheck $ setCheck t
     v <- evaluate c
     extend p nm v Nothing
checkDecl (DefinitionDecl d) = checkDefinition d
checkDecl (DatatypeDecl d)   = checkDatatype d
checkDecl (Normalise tm)     = doNormalise tm

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
