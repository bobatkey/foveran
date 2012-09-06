{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing.Conversion
       ( Value (..)
       , evalInWith
       , evalIn
       , reifyType0
       , reify
       , ($$)
       , (.->.)
       , forall
       , reflect
       , vsemI
       , vfst
       , vliftI
       , vmuI
       )
       where

import Language.Foveran.Typing.Conversion.Value
import Language.Foveran.Typing.Conversion.Evaluation

-- working from “Normalisation by Evaluation for Martin-Löf Type
-- Theory with One Universe” by Abel, Aehlig and Dybjer.
