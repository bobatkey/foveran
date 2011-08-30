{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing.Conversion.Value
    ( Value (..)
    , (.->.)
    , forall
    , (.*.)
    , (.+.)

    , ($$)

    , vfst
    , vsnd
    , vcase
    , velimEmpty
    , velimeq

    , vdesc_elim
    , videsc_elim

    , vsem
    , vsemI

    , vliftTy
    , vlift
    , vinduction
    , vliftITy
    , vliftI
    , vmuI
    , vinductionI

    , reflect
    , reifyType
    , reify
    )
    where

import Text.Show.Functions ()

import Control.Applicative

import Data.Maybe (fromMaybe)
import Data.Rec

import Language.Foveran.Syntax.Identifier (Ident)
import Language.Foveran.Syntax.Checked

{------------------------------------------------------------------------------}
data Value
    = VSet   Int

    | VPi    (Maybe Ident) Value (Value -> Value)
    | VLam   Ident (Value -> Value)

    | VSigma (Maybe Ident) Value (Value -> Value)
    | VPair  Value Value

    | VSum   Value Value
    | VInl   Value
    | VInr   Value

    | VUnit
    | VUnitI

    | VEmpty

    | VEq    Value Value Value Value
    | VRefl

    | VDesc
    | VMu         Value
    | VDesc_K     Value
    | VDesc_Id
    | VDesc_Prod  Value Value
    | VDesc_Sum   Value Value
    | VConstruct  Value

    | VIDesc      Value
    | VMuI        Value Value Value
    | VIDesc_K    Value
    | VIDesc_Id   Value
    | VIDesc_Pair Value Value
    | VIDesc_Sg   Value Value
    | VIDesc_Pi   Value Value

    | VNeutral   (Int -> Term)
    deriving Show

{------------------------------------------------------------------------------}
forall :: Ident -> Value -> (Value -> Value) -> Value
forall nm tA tB = VPi (Just nm) tA tB

(.->.) :: Value -> Value -> Value
vA .->. vB = VPi Nothing vA $ const vB

(.*.) :: Value -> Value -> Value
vA .*. vB = VSigma Nothing vA $ const vB

(.+.) :: Value -> Value -> Value
vA .+. vB = VSum vA vB

infixr 5 .->.

{------------------------------------------------------------------------------}
($$) :: Value -> Value -> Value
($$) (VLam _ f)   v = f v
($$) v            _ = error $ "internal: vapp given non-function: " ++ show v

vfst :: Value -> Value
vfst (VPair v _) = v
vfst v           = error $ "internal: vfst given non-pair: " ++ show v

vsnd :: Value -> Value
vsnd (VPair _ v) = v
vsnd v           = error $ "internal: vsnd given non-pair: " ++ show v

vmuI :: Value -> Value -> Value
vmuI a b = VLam "i" $ VMuI a b

{------------------------------------------------------------------------------}
vcase :: Value ->
         Value ->
         Value ->
         Ident -> (Value -> Value) ->
         Ident -> (Value -> Value) ->
         Ident -> (Value -> Value) ->
         Value
vcase (VInl v)     vA vB x vP y vL z vR = vL v
vcase (VInr v)     vA vB x vP y vL z vR = vR v
vcase (VNeutral n) vA vB x vP y vL z vR
    = reflect (vP (VNeutral n))
              (In <$> (Case
                       <$> n
                       <*> reifyType vA
                       <*> reifyType vB
                       <*> pure x <*> tmBound (\tmV -> reify (VSet 0) (vP (reflect (VSum vA vB) tmV)))
                       <*> pure y <*> tmBound (\tmV -> let v = reflect vA tmV in reify (vP $ VInl v) (vL v))
                       <*> pure z <*> tmBound (\tmV -> let v = reflect vB tmV in reify (vP $ VInr v) (vR v))))
vcase _            _  _  _ _  _ _  _ _  = error "internal: type error when eliminating case"

{------------------------------------------------------------------------------}
velimEmpty :: Value -> Value -> Value
velimEmpty a (VNeutral n) = reflect a (pure (In ElimEmpty)
                                       `tmApp` reifyType a
                                       `tmApp` n)

{------------------------------------------------------------------------------}
velimeq tA ta tb VRefl a e tP tp = tp
velimeq tA ta tb (VNeutral n) a e tP tp =
    reflect (tP tA tb)
            (In <$> (ElimEq
                     <$> reifyType tA
                     <*> reify tA ta
                     <*> reify tA tb
                     <*> n
                     <*> pure a <*> pure e <*> tmBound (\tma -> tmBound (\tme -> reifyType (tP (reflect tA tma) (reflect (VEq tA tA ta (reflect tA tma)) tme))))
                     <*> reify (tP ta VRefl) tp))

{------------------------------------------------------------------------------}
vsem :: Value -> Value
vsem vD = loop vD
    where
      loop (VDesc_K v)        = VLam "X" $ \_  -> v
      loop VDesc_Id           = VLam "X" $ \vX -> vX
      loop (VDesc_Prod v1 v2) = VLam "X" $ \vX -> (loop v1 $$ vX) .*. (loop v2 $$ vX)
      loop (VDesc_Sum v1 v2)  = VLam "X" $ \vX -> (loop v1 $$ vX) .+. (loop v2 $$ vX)
      loop (VNeutral tm)      =
          reflect (VSet 0 .->. VSet 0)
                  (pure (In Sem) `tmApp` tm)

{------------------------------------------------------------------------------}
vsemI :: Value
vsemI = VLam "I" $ \i ->
        VLam "D" $ \d ->
        VLam "X" $ \x ->
        videsc_elim i (VLam "D2" $ \d -> VSet 2)
          (VLam "i" $ \i -> x $$ i)
          (VLam "A" $ \a -> a)
          (VLam "D₁" $ \d1 ->
           VLam "D₂" $ \d2 ->
           VLam "semD₁" $ \semd1 ->
           VLam "semD₂" $ \semd2 ->
           semd1 .*. semd2)
          (VLam "A" $ \a ->
           VLam "D" $ \d ->
           VLam "semD" $ \semD ->
           VSigma (Just "a") a (\a -> semD $$ a))
          (VLam "A" $ \a ->
           VLam "D" $ \d ->
           VLam "semD" $ \semD ->
           VPi (Just "a") a (\a -> semD $$ a))
          d

{------------------------------------------------------------------------------}
vdesc_elim vP vK vI vPr vSu = loop
    where
      loop (VDesc_K v)        = vK $$ v
      loop VDesc_Id           = vI
      loop (VDesc_Prod v1 v2) = vPr $$ v1 $$ v2 $$ loop v1 $$ loop v2
      loop (VDesc_Sum  v1 v2) = vSu $$ v1 $$ v2 $$ loop v1 $$ loop v2
      loop (VNeutral n)       =
          reflect (vP $$ VNeutral n)
                  (pure (In Desc_Elim)
                   `tmApp` reify (VDesc .->. VSet 1) vP
                   `tmApp` reify (forall "A" (VSet 0) $ \x ->
                                  vP $$ VDesc_K x) vK
                   `tmApp` reify (vP $$ VDesc_Id) vI
                   `tmApp` reify (forall "F" VDesc $ \f ->
                                  forall "G" VDesc $ \g ->
                                  (vP $$ f) .->.
                                  (vP $$ g) .->.
                                  (vP $$ (VDesc_Prod f g))) vPr
                   `tmApp` reify (forall "F" VDesc $ \f ->
                                  forall "G" VDesc $ \g ->
                                  (vP $$ f) .->.
                                  (vP $$ g) .->.
                                  (vP $$ (VDesc_Sum f g))) vSu
                   `tmApp` n)
      loop x                  =
          error $ "internal: type error in the evaluator: vdesc_elim"

{------------------------------------------------------------------------------}
videsc_elim vI vP vId vK vPair vSg vPi = loop
    where
      loop (VIDesc_Id i)       = vId $$ i
      loop (VIDesc_K a)        = vK $$ a
      loop (VIDesc_Pair d1 d2) = vPair $$ d1 $$ d2 $$ loop d1 $$ loop d2
      loop (VIDesc_Sg a d)     = vSg $$ a $$ d $$ (VLam "a" $ \a -> loop (d $$ a))
      loop (VIDesc_Pi a d)     = vPi $$ a $$ d $$ (VLam "a" $ \a -> loop (d $$ a))
      loop (VNeutral n)        = reflect (vP $$ VNeutral n)
                                         (pure (In IDesc_Elim)
                                          `tmApp` reify (VSet 0) vI
                                          `tmApp` reify (VIDesc vI .->. VSet 10) vP
                                          `tmApp` reify (forall "x" vI $ \x -> vP $$ VIDesc_Id x) vId
                                          `tmApp` reify (forall "A" (VSet 0) $ \a -> vP $$ VIDesc_K a) vK
                                          `tmApp` reify (forall "D1" (VIDesc vI) $ \d1 ->
                                                         forall "D2" (VIDesc vI) $ \d2 ->
                                                         (vP $$ d1) .->.
                                                         (vP $$ d2) .->.
                                                         (vP $$ VIDesc_Pair d1 d2)) vPair
                                          `tmApp` reify (forall "A" (VSet 0) $ \a ->
                                                         forall "D" (a .->. VIDesc vI) $ \d ->
                                                         (forall "x" a $ \x -> vP $$ (d $$ x)) .->.
                                                         (vP $$ VIDesc_Sg a d)) vSg
                                          `tmApp` reify (forall "A" (VSet 0) $ \a ->
                                                         forall "D" (a .->. VIDesc vI) $ \d ->
                                                         (forall "x" a $ \x -> vP $$ (d $$ x)) .->.
                                                         (vP $$ VIDesc_Pi a d)) vPi
                                          `tmApp` n)
      loop x                   = error $ "internal: type error in the evaluator: videsc_elim"

{------------------------------------------------------------------------------}
-- FIXME: is this the right level? why not Set_1, or Set_0? Some kind
-- of level-shifting thing?
vliftTy :: Value
vliftTy = forall "D" VDesc $ \vD ->
          forall "A" (VSet 0) $ \vA ->
          forall "P" (vA .->. VSet 2) $ \vP ->
          (vsem vD $$ vA) .->. VSet 2

vlift :: Value
vlift = VLam "D" $ \d ->
        VLam "X" $ \vA ->
        VLam "P" $ \p ->
        VLam "x" $ \v ->
        vdesc_elim (VLam "D" $ \d ->
                    (vsem d $$ vA) .->. VSet 2)
                   (VLam "A" $ \a ->
                    VLam "x" $ \x ->
                    VUnit)
                   (VLam "x" $ \x ->
                    p $$ x)
                   (VLam "F" $ \fd ->
                    VLam "G" $ \gd ->
                    VLam "f" $ \f ->
                    VLam "g" $ \g ->
                    VLam "x" $ \x ->
                    VSigma Nothing (f $$ vfst x) (\_ -> g $$ vsnd x))
                   (VLam "F" $ \fd ->
                    VLam "G" $ \gd ->
                    VLam "f" $ \f ->
                    VLam "g" $ \g ->
                    VLam "x" $ \x ->
                    vcase x
                          (vsem fd $$ vA)
                          (vsem gd $$ vA)
                          "x" (\_ -> VSet 2)
                          "x" (\x -> f $$ x)
                          "x" (\x -> g $$ x))
                   d
                   $$ v

{------------------------------------------------------------------------------}
vall :: Value
vall = VLam "D" $ \vF ->
       VLam "X" $ \vX ->
       VLam "P" $ \vP ->
       VLam "p" $ \vp ->
       vdesc_elim (VLam "D" $ \vD ->
                   forall "xs" (vsem vD $$ vX) $ \xs ->
                   vlift $$ vD $$ vX $$ vP $$ xs)
                  (VLam "A" $ \a ->
                   VLam "x" $ \x ->
                   VUnitI)
                  (VLam "x" $ \x ->
                   vp $$ x)
                  (VLam "F" $ \vF ->
                   VLam "G" $ \vG ->
                   VLam "f" $ \vf ->
                   VLam "g" $ \vg ->
                   VLam "x" $ \x ->
                   VPair (vf $$ vfst x) (vg $$ vsnd x))
                  (VLam "F" $ \vF ->
                   VLam "G" $ \vG ->
                   VLam "f" $ \vf ->
                   VLam "g" $ \vg ->
                   VLam "x" $ \x ->
                   vcase x
                         (vsem vF $$ vX)
                         (vsem vG $$ vX)
                         "d" (\d -> vlift $$ VDesc_Sum vF vG $$ vX $$ vP $$ d)
                         "y" (\y -> vf $$ y)
                         "z" (\z -> vg $$ z))
                  vF

{------------------------------------------------------------------------------}
vinduction :: Value -> Value -> Value -> Value -> Value
vinduction vF vP vK = loop
    where
      loop (VConstruct x) =
          vK $$ x $$ (vall $$ vF $$ (VMu vF) $$ vP $$ (VLam "x" loop) $$ x)
      loop (VNeutral n) =
          reflect (vP $$ VNeutral n)
                  (pure (In Induction)
                   `tmApp` reify VDesc vF
                   `tmApp` reify (VMu vF .->. VSet 2) vP
                   `tmApp` reify (VPi (Just "x") (vsem vF $$ VMu vF) $ \x ->
                                  (vlift $$ vF $$ VMu vF $$ vP $$ x) .->.
                                  vP $$ VConstruct x)
                                 vK
                   `tmApp` n)

{------------------------------------------------------------------------------}
vliftITy :: Value
vliftITy = forall "I" (VSet 0) $ \vI ->
           forall "D" (VIDesc vI) $ \vD ->
           forall "A" (vI .->. VSet 0) $ \vA ->
           forall "P" (forall "i" vI $ \vi -> vA $$ vi .->. VSet 2) $ \_ ->
           vsemI $$ vI $$ vD $$ (VLam "i" $ \vi -> vA $$ vi) .->.
           VSet 2

vliftI :: Value
vliftI = VLam "I" $ \vI ->
         VLam "D" $ \vD ->
         VLam "A" $ \vA ->
         VLam "P" $ \vP ->
         VLam "x" $ \vx ->
         videsc_elim vI (VLam "D" $ \vD ->
                         vsemI $$ vI $$ vD $$ (VLam "i" $ \vi -> vA $$ vi) .->.
                         VSet 2)
           (VLam "i" $ \vi ->
            VLam "a" $ \va ->
            vP $$ vi $$ va)
           (VLam "A'" $ \vA' ->
            VLam "a" $ \va ->
            VUnit)
           (VLam "D1" $ \vD1 ->
            VLam "D2" $ \vD2 ->
            VLam "lift1" $ \lift1 ->
            VLam "lift2" $ \lift2 ->
            VLam "p" $ \p ->
            (lift1 $$ vfst p) .*. (lift2 $$ vsnd p))
           (VLam "B" $ \vB ->
            VLam "D" $ \vD ->
            VLam "liftD" $ \vliftD ->
            VLam "p" $ \vp ->
            vliftD $$ vfst vp $$ vsnd vp)
           (VLam "B" $ \vB ->
            VLam "D" $ \vD ->
            VLam "liftD" $ \vliftD ->
            VLam "f" $ \f ->
            forall "b" vB $ \vb -> vliftD $$ vb $$ (f $$ vb))
           vD $$ vx

vallI :: Value
vallI = VLam "I" $ \vI ->
        VLam "D" $ \vD ->
        VLam "A" $ \vA ->
        VLam "P" $ \vP ->
        VLam "p" $ \vp ->
        VLam "xs" $ \xs ->
        videsc_elim vI (VLam "D" $ \vD ->
                        forall "xs" (vsemI $$ vI $$ vD $$ (VLam "i" $ \vi -> vA $$ vi)) $ \xs ->
                        vliftI $$ vI $$ vD $$ vA $$ vP $$ xs)
          (VLam "x" $ \x ->
           VLam "xs" $ \xs ->
           vp $$ x $$ xs)
          (VLam "A" $ \vA ->
           VLam "xs" $ \xs ->
           VUnitI)
          (VLam "D1" $ \vD1 ->
           VLam "D2" $ \vD2 ->
           VLam "all1" $ \all1 ->
           VLam "all2" $ \all2 ->
           VLam "x" $ \x ->
           VPair (all1 $$ vfst x) (all2 $$ vsnd x))
          (VLam "B" $ \vB ->
           VLam "D" $ \vD ->
           VLam "all" $ \all ->
           VLam "x" $ \x ->
           all $$ vfst x $$ vsnd x)
          (VLam "B" $ \vB ->
           VLam "D" $ \vD ->
           VLam "all" $ \all ->
           VLam "x" $ \x ->
           VLam "b" $ \b -> all $$ b $$ (x $$ b))
          vD $$ xs

vinductionI vI vD vP vk = loop
    where
      loop vi (VConstruct x) =
          vk $$ vi $$ x $$ (vallI $$ vI $$ (vD $$ vi) $$ vmuI vI vD $$ vP $$ (VLam "i" $ \i -> VLam "x" $ \x -> loop i x) $$ x)
      loop vi (VNeutral n) =
          reflect (vP $$ vi $$ VNeutral n)
                  (pure (In InductionI)
                   `tmApp` reify (VSet 0) vI
                   `tmApp` reify (vI .->. VIDesc vI) vD
                   `tmApp` reify (forall "i" vI $ \i -> (vmuI vI vD $$ i) .->. VSet 2) vP
                   `tmApp` reify (forall "i" vI $ \i ->
                                  forall "x" (vsemI $$ vI $$ (vD $$ i) $$ vmuI vI vD) $ \x ->
                                  (vliftI $$ vI $$ (vD $$ i) $$ vmuI vI vD $$ vP $$ x) .->.
                                  vP $$ i $$ VConstruct x) vk
                   `tmApp` reify vI vi
                   `tmApp` n)

{------------------------------------------------------------------------------}
reflect :: Value -> (Int -> Term) -> Value
reflect (VPi nm tA tB)   tm = VLam (fromMaybe "x" nm) $ \d -> reflect (tB d) (tm `tmApp` reify tA d)
reflect (VSigma _ tA tB) tm = let v1 = reflect tA (tmFst tm)
                                  v2 = reflect (tB v1) (tmSnd tm)
                              in VPair v1 v2
reflect VUnit            tm = VUnitI
reflect _                tm = VNeutral tm


{------------------------------------------------------------------------------}
reifyType :: Value -> (Int -> Term)
reifyType (VPi x v f)     = \i -> In $ Pi x (reifyType v i) (reifyType (f (reflect v $ vbound i)) (i+1))
reifyType (VSigma x v f)  = \i -> In $ Sigma x (reifyType v i) (reifyType (f (reflect v $ vbound i)) (i+1))
reifyType (VSum v1 v2)    = \i -> In $ Sum (reifyType v1 i) (reifyType v2 i)
reifyType (VSet l)        = \i -> In $ Set l
reifyType VUnit           = \i -> In $ Unit
reifyType VEmpty          = \i -> In $ Empty
reifyType (VEq vA vB va vb) = \i -> In $ Eq (reifyType vA i) (reifyType vB i) (reify vA va i) (reify vB vb i)
reifyType VDesc           = \i -> In $ Desc
reifyType (VMu v)         = \i -> In $ Mu (reify VDesc v i)
reifyType (VMuI v1 v2 v3) = (\i -> In $ MuI (reifyType v1 i) (reify (v1 .->. VIDesc v1) v2 i)) `tmApp` reify v1 v3
reifyType (VIDesc s)      = pure (In IDesc) `tmApp` reifyType s
reifyType (VNeutral t)    = \i -> t i
reifyType v               = error ("internal: reifyType given non-type: " ++ show v)


{------------------------------------------------------------------------------}
reify :: Value -> Value -> (Int -> Term)

reify (VSet _) a = reifyType a

reify (VPi _ tA tB)    (VLam nm f) = \i -> let d = reflect tA (vbound i)
                                           in In $ Lam nm $ reify (tB d) (f d) (i + 1)
reify (VPi _ tA tB)    _           = error "internal: reify: values of type Pi-blah should only be VLam"

reify (VSigma _ tA tB) e = let v1 = vfst e
                               v2 = vsnd e
                           in \i -> In $ Pair (reify tA v1 i) (reify (tB v1) v2 i)

reify (VSum tA tB)     (VInl v) = \i -> In $ Inl (reify tA v i)
reify (VSum tA tB)     (VInr v) = \i -> In $ Inr (reify tB v i)

reify VUnit            VUnitI   = \i -> In $ UnitI
reify VUnit            _        = error "internal: reify: values of type unit should only be VUnitI"

reify VDesc            (VDesc_K v)         = \i -> In $ Desc_K (reifyType v i)
reify VDesc            VDesc_Id            = \i -> In $ Desc_Id
reify VDesc            (VDesc_Prod v1 v2)  = \i -> In $ Desc_Prod (reify VDesc v1 i) (reify VDesc v2 i)
reify VDesc            (VDesc_Sum v1 v2)   = \i -> In $ Desc_Sum (reify VDesc v1 i) (reify VDesc v2 i)
reify (VMu tA)         (VConstruct v)      = \i -> In $ Construct (reify (vsem tA $$ (VMu tA)) v i)
reify (VMuI tI tD ti)  (VConstruct v)      = \i -> In $ Construct (reify (vsemI $$ tI $$ (tD $$ ti) $$ (vmuI tI tD)) v i)
reify (VIDesc tI)      (VIDesc_Id x)       = \i -> In $ IDesc_Id (reify tI x i)
reify (VIDesc tI)      (VIDesc_K a)        = \i -> In $ IDesc_K (reifyType a i)
reify (VIDesc tI)      (VIDesc_Pair d1 d2) = \i -> In $ IDesc_Pair (reify (VIDesc tI) d1 i) (reify (VIDesc tI) d2 i)
reify (VIDesc tI)      (VIDesc_Sg a d)     = \i -> In $ IDesc_Sg (reifyType a i) (reify (a .->. VIDesc tI) d i)
reify (VIDesc tI)      (VIDesc_Pi a d)     = \i -> In $ IDesc_Pi (reifyType a i) (reify (a .->. VIDesc tI) d i)
reify (VEq tA _ ta _)  VRefl               = \i -> In $ Refl
reify _                (VNeutral tm)       = tm
reify ty               v                   = error $ "reify: attempt to reify: " ++ show v ++ " at type " ++ show ty
