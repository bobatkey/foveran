{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing.Conversion
       ( Value (..)
       , evaluate
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
       , vmuI
       , tmFree -- FIXME: replace this with reflectFree

       , vTy
       , vCtxt
       , vtysem
       , vtypred
       , vctxtsem
       , vctxtpred
       )
       where

import Language.Foveran.Typing.Conversion.Value
import Language.Foveran.Typing.Conversion.Evaluation

-- working from “Normalisation by Evaluation for Martin-Löf Type
-- Theory with One Universe” by Abel, Aehlig and Dybjer.
