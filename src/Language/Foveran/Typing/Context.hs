{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing.Context
    ( Context
    , emptyContext
    , ctxtExtend
    , ctxtExtendFreshen
    , evalIn
    , evalInWithArg
    , lookupType
    , lookupDef
    , contextNameSupply
    )
    where

import           Data.Functor
import           Data.Monoid
import qualified Data.Text as T
import qualified Data.Map as M
import           Data.Rec (AnnotRec)
import           Language.Foveran.Syntax.Checked (Term)
import           Language.Foveran.Typing.Conversion
import           Language.Foveran.NameSupply

-- FIXME: Make this abstract
type Context = M.Map Ident (Value, Maybe Value)

emptyContext :: Context
emptyContext = M.empty

ctxtExtend :: Context -> Ident -> Value -> Maybe Value -> Maybe Context
ctxtExtend ctxt nm ty defn
    = case M.lookup nm ctxt of
        Nothing -> Just $ M.insert nm (ty, defn) ctxt
        Just _  -> Nothing

-- FIXME: try to find better ways of freshening names
ctxtExtendFreshen :: Context -> Ident -> Value -> Maybe Value -> (Ident, Context)
ctxtExtendFreshen ctxt nm ty defn
    = case M.lookup nm ctxt of
        Nothing -> (nm, M.insert nm (ty, defn) ctxt)
        Just _  -> ctxtExtendFreshen ctxt (nm `mappend` "'") ty defn

evalIn :: Term -> Context -> Value
evalIn t ctxt = evaluate t [] (lookupDef ctxt)

evalInWithArg :: Term -> Context -> Value -> Value
evalInWithArg t ctxt v = evaluate t [v] (lookupDef ctxt)

lookupType :: Ident -> Context -> Maybe Value
lookupType nm ctxt = fst <$> M.lookup nm ctxt

lookupDef :: Context -> Ident -> (Value, Maybe Value)
lookupDef ctxt nm = case M.lookup nm ctxt of
                      Nothing        -> error $ "lookupDef: definition not found: " ++ T.unpack nm
                      Just (ty, def) -> (ty, def)

-- FIXME: this is a little confused, probably a better way exists
contextNameSupply :: Context -> NS a -> a
contextNameSupply ctxt (NS f) = f (M.keysSet ctxt, [])
