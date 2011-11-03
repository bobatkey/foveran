{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing.Context
    ( Context ()
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
import qualified Data.Set as S
import           Data.Rec (AnnotRec)
import           Language.Foveran.Syntax.Checked (Term)
import           Language.Foveran.Syntax.Identifier
import           Language.Foveran.Typing.Conversion

-- FIXME: keep track of the order?
data Context
    = Context { ctxtGlobal :: M.Map Ident (Value, Maybe Value) }

namesOf :: Context -> S.Set Ident
namesOf ctxt = M.keysSet (ctxtGlobal ctxt)

emptyContext :: Context
emptyContext = Context M.empty

ctxtExtend :: Context -> Ident -> Value -> Maybe Value -> Maybe Context
ctxtExtend ctxt nm ty defn
    = case M.lookup nm (ctxtGlobal ctxt) of
        Nothing -> Just $ ctxt { ctxtGlobal = M.insert nm (ty, defn) (ctxtGlobal ctxt) }
        Just _  -> Nothing

ctxtExtendFreshen :: Context -> Ident -> Value -> Maybe Value -> (Ident, Context)
ctxtExtendFreshen ctxt nm ty defn =
    ( freshNm
    , ctxt { ctxtGlobal = M.insert freshNm (ty, defn) (ctxtGlobal ctxt) } )
    where
      (_, freshNm) = freshen (namesOf ctxt) nm

evalIn :: Term -> Context -> Value
evalIn t ctxt = evaluate t [] (lookupDef ctxt)

evalInWithArg :: Term -> Context -> Value -> Value
evalInWithArg t ctxt v = evaluate t [v] (lookupDef ctxt)

lookupType :: Ident -> Context -> Maybe Value
lookupType nm ctxt = fst <$> M.lookup nm (ctxtGlobal ctxt)

lookupDef :: Context -> Ident -> (Value, Maybe Value)
lookupDef ctxt nm = case M.lookup nm (ctxtGlobal ctxt) of
                      Nothing        -> error $ "lookupDef: definition not found: " ++ T.unpack nm
                      Just (ty, def) -> (ty, def)

-- FIXME: this is a little confused, probably a better way exists
contextNameSupply :: Context -> NameSupply a -> a
contextNameSupply ctxt f = runNameSupply f (namesOf ctxt)
