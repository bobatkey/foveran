{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing.Conversion
       ( Value (..)
       , evaluate
       , reifyType0
       , ($$)
       , (.->.)
       , forall
       , reflect
       , vsemTy
       , vsem
       , vsemI
       , vfst
       , vlift
       , vmuI
       )
       where

import Language.Foveran.Typing.Conversion.Value
import Language.Foveran.Typing.Conversion.Evaluation

-- working from “Normalisation by Evaluation for Martin-Löf Type
-- Theory with One Universe” by Abel, Aehlig and Dybjer.
