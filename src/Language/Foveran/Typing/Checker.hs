{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing.Checker
    ( TypingMonad (..)
    , tyCheck
    , setCheck
    , tySynth
    )
    where

import           Control.Monad (unless)
import           Data.Maybe (fromMaybe)
import           Data.Rec (AnnotRec (Annot), Rec (In))
import           Language.Foveran.Syntax.LocallyNameless
import qualified Language.Foveran.Syntax.Checked as CS
import           Language.Foveran.Typing.Conversion
import           Language.Foveran.Typing.Context
import           Language.Foveran.Typing.Errors

{------------------------------------------------------------------------------}
-- This is a bit small at the moment, but it might get bigger
data TypingMonad p a
    = Error  p TypeError
    | Result a

instance Monad (TypingMonad p) where
    return x = Result x
    Error p e >>= _ = Error p e
    Result x  >>= f = f x

{------------------------------------------------------------------------------}
compareTypes :: p -> Context -> Value -> Value -> TypingMonad p ()
compareTypes p ctxt (VSet i) (VSet j) =
  unless (j <= i) $ Error p (LevelProblem j i)
compareTypes p ctxt v1       v2 =
  unless (tm1 == tm2) $ Error p (TypesNotEqual ctxt v1 v2)
      where
        tm1 = reifyType0 v1
        tm2 = reifyType0 v2

-- should probably extend the cummulativity checking to include Pi and
-- Sigma types (i.e. with cummulativity in the codomain of Pi). See
-- e.g. “The View from the Left” or Norell's thesis.

{------------------------------------------------------------------------------}
-- Type checking
tyCheck :: AnnotRec p TermCon -> Context -> Value -> TypingMonad p CS.Term

tyCheck (Annot p (Lam x t)) ctxt (VPi _ tA tB) =
  do let (x',ctxt') = ctxtExtendFreshen ctxt x tA Nothing
     tm <- tyCheck (close x' t) ctxt' (tB $ reflect tA (CS.tmFree x'))
     return (In $ CS.Lam x (CS.bindFree x' tm))

tyCheck (Annot p (Lam x t)) ctxt v =
    Error p (ExpectingPiTypeForLambda ctxt v)

tyCheck (Annot p (Pair t1 t2)) ctxt (VSigma _ tA tB) =
    do tm1 <- tyCheck t1 ctxt tA
       tm2 <- tyCheck t2 ctxt (tB $ tm1 `evalIn` ctxt)
       return (In $ CS.Pair tm1 tm2)

tyCheck (Annot p (Pair _ _)) ctxt v =
    Error p (ExpectingSigmaTypeForPair ctxt v)

tyCheck (Annot p (Inl t)) ctxt (VSum tA _) =
    do tm <- tyCheck t ctxt tA
       return (In $ CS.Inl tm)

tyCheck (Annot p (Inl t)) ctxt v =
    Error p (ExpectingSumTypeForInl ctxt v)

tyCheck (Annot p (Inr t)) ctxt (VSum _ tB) =
    do tm <- tyCheck t ctxt tB
       return (In $ CS.Inr tm)

tyCheck (Annot p (Inr t)) ctxt v =
    Error p (ExpectingSumTypeForInr ctxt v)

tyCheck (Annot p UnitI) ctxt VUnit =
    do return (In $ CS.UnitI)

tyCheck (Annot p UnitI) ctxt v =
    Error p (ExpectingUnitTypeForUnit ctxt v)

tyCheck (Annot p (Desc_K t)) ctxt VDesc =
    do tm <- tyCheck t ctxt (VSet 0)
       return (In $ CS.Desc_K tm)

tyCheck (Annot p (Desc_K t)) ctxt (VIDesc v) =
    do tm <- tyCheck t ctxt (VSet 0)
       return (In $ CS.IDesc_K tm)

tyCheck (Annot p (Desc_K t)) ctxt v =
    Error p (ExpectingDescTypeForDesc ctxt v)

tyCheck (Annot p Desc_Id) ctxt VDesc =
    do return (In $ CS.Desc_Id)

tyCheck (Annot p Desc_Id) ctxt v =
    Error p (ExpectingDescTypeForDesc ctxt v)

tyCheck (Annot p (Desc_Prod t1 t2)) ctxt VDesc =
    do tm1 <- tyCheck t1 ctxt VDesc
       tm2 <- tyCheck t2 ctxt VDesc
       return (In $ CS.Desc_Prod tm1 tm2)

tyCheck (Annot p (Desc_Prod t1 t2)) ctxt (VIDesc v) =
    do tm1 <- tyCheck t1 ctxt (VIDesc v)
       tm2 <- tyCheck t2 ctxt (VIDesc v)
       return (In $ CS.IDesc_Pair tm1 tm2)

tyCheck (Annot p (Desc_Prod t1 t2)) ctxt v =
    Error p (ExpectingDescTypeForDesc ctxt v)

tyCheck (Annot p (Desc_Sum t1 t2)) ctxt VDesc =
    do tm1 <- tyCheck t1 ctxt VDesc
       tm2 <- tyCheck t2 ctxt VDesc
       return (In $ CS.Desc_Sum tm1 tm2)

tyCheck (Annot p (Desc_Sum t1 t2)) ctxt v =
    Error p (ExpectingDescTypeForDesc ctxt v)

tyCheck (Annot p (Construct t)) ctxt (VMu f) =
    do tm <- tyCheck t ctxt (vsem f $$ VMu f)
       return ( In $ CS.Construct tm )

tyCheck (Annot p (Construct t)) ctxt (VMuI a d i) =
    do tm <- tyCheck t ctxt (vsemI $$ a $$ (d $$ i) $$ vmuI a d)
       return ( In $ CS.Construct tm )

tyCheck (Annot p (Construct t)) ctxt v =
    Error p (ExpectingMuTypeForConstruct ctxt v)

tyCheck (Annot p (IDesc_Id t)) ctxt (VIDesc v) =
    do tm <- tyCheck t ctxt v
       return ( In $ CS.IDesc_Id tm )

tyCheck (Annot p (IDesc_Id t)) ctxt v =
    Error p (ExpectingDescTypeForDesc ctxt v)

tyCheck (Annot p (IDesc_Sg t1 t2)) ctxt (VIDesc v) =
    do tm1 <- tyCheck t1 ctxt (VSet 0)
       tm2 <- tyCheck t2 ctxt (tm1 `evalIn` ctxt .->. VIDesc v)
       return (In $ CS.IDesc_Sg tm1 tm2)

tyCheck (Annot p (IDesc_Sg t1 t2)) ctxt v =
    Error p (ExpectingDescTypeForDesc ctxt v)

tyCheck (Annot p (IDesc_Pi t1 t2)) ctxt (VIDesc v) =
    do tm1 <- tyCheck t1 ctxt (VSet 0)
       tm2 <- tyCheck t2 ctxt (tm1 `evalIn` ctxt .->. VIDesc v)
       return (In $ CS.IDesc_Pi tm1 tm2)

tyCheck (Annot p (IDesc_Pi t1 t2)) ctxt v =
    Error p (ExpectingDescTypeForDesc ctxt v)

tyCheck (Annot p t) ctxt v =
    do (v',tm) <- tySynth (Annot p t) ctxt
       compareTypes p ctxt v v'
       return tm


setCheck :: AnnotRec p TermCon -> Context -> TypingMonad p (Int, CS.Term)
setCheck t@(Annot p _) ctxt =
    do (tA,tm) <- tySynth t ctxt
       case tA of
         VSet j -> return (j, tm)
         _      -> Error p ExpectingSet



tySynth :: AnnotRec p TermCon -> Context -> TypingMonad p (Value, CS.Term)
tySynth (Annot p (Bound _)) ctxt =
    error "internal: 'bound' variable discovered during type synthesis"
tySynth (Annot p (Free nm)) ctxt =
    case lookupType nm ctxt of
      Nothing -> Error p (UnknownIdentifier nm)
      Just tA -> return (tA, In $ CS.Free nm)
tySynth (Annot p (App t t')) ctxt =
    do (tF, tm) <- tySynth t ctxt
       case tF of
         VPi _ tA tB -> do tm' <- tyCheck t' ctxt tA
                           return (tB $ tm' `evalIn` ctxt, In $ CS.App tm tm')
         ty          -> Error p (ApplicationOfNonFunction ctxt ty)
tySynth (Annot p (Set l)) ctxt =
    return (VSet (l + 1), In $ CS.Set l)
tySynth (Annot p (Pi x t1 t2)) ctxt =
    do (j,tm1) <- setCheck t1 ctxt
       let v          = tm1 `evalIn` ctxt
           (x',ctxt') = ctxtExtendFreshen ctxt (fromMaybe "x" x) v Nothing
       (k,tm2) <- setCheck (close x' t2) ctxt'
       return (VSet $ max j k, In $ CS.Pi x tm1 (CS.bindFree x' tm2))
tySynth (Annot p (Sigma x t1 t2)) ctxt =
    do (j,tm1) <- setCheck t1 ctxt
       let v          = tm1 `evalIn` ctxt
           (x',ctxt') = ctxtExtendFreshen ctxt (fromMaybe "x" x) v Nothing
       (k,tm2) <- setCheck (close x' t2) ctxt'
       return (VSet $ max j k, In $ CS.Sigma x tm1 (CS.bindFree x' tm2))
tySynth (Annot p (Sum t1 t2)) ctxt =
    do (i,tm1) <- setCheck t1 ctxt
       (j,tm2) <- setCheck t2 ctxt
       return (VSet (max i j), In $ CS.Sum tm1 tm2)
tySynth (Annot p (Case t x tP y tL z tR)) ctxt =
    do (tS,tmS) <- tySynth t ctxt
       case tS of
         VSum tA tB ->
             do let (x', ctxt1) = ctxtExtendFreshen ctxt x tS Nothing
                (i,tmP0) <- setCheck (close x' tP) ctxt1
                let tmP         = CS.bindFree x' tmP0
                    (y', ctxt2) = ctxtExtendFreshen ctxt y tA Nothing
                    vtP1        = (tmP `evalInWithArg` ctxt2) (VInl (reflect tA (CS.tmFree y')))
                tmL <- tyCheck (close y' tL) ctxt2 vtP1
                let (z', ctxt3) = ctxtExtendFreshen ctxt z tB Nothing
                    vtP2        = (tmP `evalInWithArg` ctxt3) (VInr (reflect tB (CS.tmFree z')))
                tmR <- tyCheck (close z' tR) ctxt3 vtP2
                let tmA = reifyType0 tA
                    tmB = reifyType0 tB
                return ( (tmP `evalInWithArg` ctxt) (tmS `evalIn` ctxt)
                       , In $ CS.Case tmS tmA tmB x tmP
                                                  y (CS.bindFree y' tmL)
                                                  z (CS.bindFree z' tmR))
         v ->
             Error p (CaseOnNonSum ctxt v)
tySynth (Annot p Unit) ctxt =
    return (VSet 0, In $ CS.Unit)
tySynth (Annot p UnitI) ctxt =
    return (VUnit, In $ CS.UnitI)

tySynth (Annot p Empty) ctxt =
    return (VSet 0, In $ CS.Empty)
tySynth (Annot p ElimEmpty) ctxt =
    -- FIXME: make this have a mandatory argument so we can use an arbitrary level
    return ( forall "A" (VSet 10) $ \a -> VEmpty .->. a
           , In $ CS.ElimEmpty)

tySynth (Annot p Desc) ctxt =
    return (VSet 1, In $ CS.Desc)
tySynth (Annot p Desc_Elim) ctxt =
    return ( forall "P" (VDesc .->. VSet 10) $ \vP ->
             (forall "A" (VSet 0) $ \x -> vP $$ VDesc_K x) .->.
             (vP $$ VDesc_Id) .->.
             (forall "d1" VDesc $ \d1 ->
              forall "d2" VDesc $ \d2 ->
              (vP $$ d1) .->. (vP $$ d2) .->. (vP $$ (VDesc_Prod d1 d2))) .->.
             (forall "d1" VDesc $ \d1 ->
              forall "d2" VDesc $ \d2 ->
              (vP $$ d1) .->. (vP $$ d2) .->. (vP $$ (VDesc_Sum d1 d2))) .->.
             (forall "x" VDesc $ \x -> vP $$ x)
           , In $ CS.Desc_Elim)
tySynth (Annot p Sem) ctxt =
    return ( VDesc .->. VSet 0 .->. VSet 0, In $ CS.Sem )
tySynth (Annot p (Mu t)) ctxt =
    do tm <- tyCheck t ctxt VDesc
       return (VSet 0, In $ CS.Mu tm)

tySynth (Annot p (MuI t1 t2)) ctxt =
    do tm1 <- tyCheck t1 ctxt (VSet 0)
       let v = tm1 `evalIn` ctxt
       tm2 <- tyCheck t2 ctxt (v .->. VIDesc v)
       return (v .->. VSet 0, In $ CS.MuI tm1 tm2)

tySynth (Annot p Induction) ctxt =
    return ( forall "F" VDesc               $ \f ->
             forall "P" (VMu f .->. VSet 2) $ \p ->
             (forall "x" (vsem f $$ VMu f) $ \x ->
              (vlift $$ f $$ VMu f $$ p $$ x) .->.
              p $$ (VConstruct x)) .->.
             (forall "x" (VMu f) $ \x -> p $$ x)
           , In CS.Induction)

tySynth (Annot p (Proj1 t)) ctxt =
    do (tP, tmP) <- tySynth t ctxt
       case tP of
         VSigma _ tA _ -> return (tA, In $ CS.Proj1 tmP)
         v             -> Error p (Proj1FromNonSigma ctxt v)

tySynth (Annot p (Proj2 t)) ctxt =
    do (tP, tmP) <- tySynth t ctxt
       case tP of
         VSigma _ _ tB -> return (tB (vfst $ tmP `evalIn` ctxt), In $ CS.Proj2 tmP)
         v             -> Error p (Proj2FromNonSigma ctxt v)

{------------------------------------------------------------------------------}
-- Descriptions of indexed types
tySynth (Annot p IDesc) ctxt =
    do return (VSet 0 .->. VSet 1, In $ CS.IDesc)
       
tySynth (Annot p IDesc_Elim) ctxt =
    do return ( forall "I" (VSet 0) $ \i ->
                forall "P" (VIDesc i .->. VSet 10) $ \p ->
                (forall "x" i $ \x -> p $$ VIDesc_Id x) .->.
                (forall "A" (VSet 0) $ \a -> p $$ VIDesc_K a) .->.
                (forall "D1" (VIDesc i) $ \d1 ->
                 forall "D2" (VIDesc i) $ \d2 ->
                 (p $$ d1) .->.
                 (p $$ d2) .->.
                 (p $$ (VIDesc_Pair d1 d2))) .->.
                (forall "A" (VSet 0) $ \a ->
                 forall "D" (a .->. VIDesc i) $ \d ->
                 (forall "x" a $ \x -> p $$ (d $$ x)) .->.
                 (p $$ (VIDesc_Sg a d))) .->.
                (forall "A" (VSet 0) $ \a ->
                 forall "D" (a .->. VIDesc i) $ \d ->
                 (forall "x" a $ \x -> p $$ (d $$ x)) .->.
                 (p $$ (VIDesc_Pi a d))) .->.
                (forall "D" (VIDesc i) $ \d -> p $$ d)
              , In $ CS.IDesc_Elim
              )

tySynth (Annot p t) ctxt =
    Error p UnableToSynthesise
