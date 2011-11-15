{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing.Conversion
       ( Value (..)
       , DefinitionContext (..)
       , lookupType
       , evalInWith
       , evalIn
       , reifyType0
       , reify
       , ($$)
       , (.->.)
       , forall
       , reflect
       , vsem
       , vsemI
       , vfst
       , vlift
       , vliftI
       , vmuI
       )
       where

import Language.Foveran.Typing.Conversion.Value
import Language.Foveran.Typing.Conversion.Evaluation

-- working from “Normalisation by Evaluation for Martin-Löf Type
-- Theory with One Universe” by Abel, Aehlig and Dybjer.
