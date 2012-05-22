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

    , videsc_bind

    , vsem
    , vsemI
    , vmapI

    , vliftTy
    , vlift
    , vinduction
    , vliftI
    , vmuI
    , vinductionI
    , veliminate

    , vgroup
    , vgroupUnit
    , vgroupMul
    , vgroupInv

    , reflect
    , reifyType0
    , reify
    )
    where

import Text.Show.Functions ()

import Control.Applicative

import Data.Maybe (fromMaybe)
import Data.Rec

import qualified Data.Map as M -- for normalising abelian group expressions

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
    | VIDesc_Bind Value (Int -> Term) Ident (Value -> Value) -- ^ suspended 'bind' applications

    | VMapI       (Value -> Value) Value (Int -> Term)
    | VSemI       Value (Int -> Term) Ident (Value -> Value)

    | VGroup      Ident Abelian (Maybe (Value, Value))
    | VGroupTerm  [(Bool, Int -> Term)]

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
bound :: Value -> (Value -> (Int -> Term)) -> Int -> Term
bound ty f = tmBound (\tm -> f (reflect ty tm))

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
                       <*> pure (Irrelevant x) <*> bound (VSum vA vB) (\v -> reify (VSet 0) (vP v))
                       <*> pure (Irrelevant y) <*> bound vA           (\v -> reify (vP $ VInl v) (vL v))
                       <*> pure (Irrelevant z) <*> bound vB           (\v -> reify (vP $ VInr v) (vR v))))
vcase _            _  _  _ _  _ _  _ _  = error "internal: type error when eliminating case"

{------------------------------------------------------------------------------}
velimEmpty :: Value -- ^ a purported element of the empty type
           -> Value -- ^ result type
           -> Value -- ^ an element of the result type
velimEmpty (VNeutral n) a = reflect a (In <$> (ElimEmpty <$> n <*> reifyType a))

{------------------------------------------------------------------------------}
velimeq :: Value -- ^ The type of the equality 'A'
        -> Value -- ^ Element 'a' of 'A'
        -> Value -- ^ Element 'b' of 'A'
        -> Value -- ^ A proof 'e' that 'a' equals 'b'
        -> Ident -- ^ Identifier for the element of 'A'
        -> Ident -- ^ Identifier for the proof of equality
        -> (Value -> Value -> Value) -- ^ The elimination type 'P'
        -> Value -- ^ Value of type 'P a refl'
        -> Value -- ^ Value of type 'P b e'
velimeq tA ta tb VRefl a e tP tp = tp
velimeq tA ta tb (VNeutral n) a e tP tp =
    reflect (tP tb (VNeutral n))
            (In <$> (ElimEq
                     <$> reifyType tA
                     <*> reify tA ta
                     <*> reify tA tb
                     <*> n
                     <*> pure (Irrelevant a) <*> pure (Irrelevant e)
                     <*> bound tA (\va -> bound (VEq tA tA ta va) (\ve -> reifyType (tP va ve)))
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

vsemI :: Value -> Value -> Ident -> (Value -> Value) -> Value
vsemI vI vD x vA = loop vD
    where
      loop (VIDesc_Id i)       = vA i
      loop (VIDesc_K a)        = a
      loop (VIDesc_Pair d1 d2) = loop d1 .*. loop d2
      loop (VIDesc_Sg a d)     = VSigma (Just "a") a (\a -> loop (d $$ a))
      loop (VIDesc_Pi a d)     = VPi (Just "a") a (\a -> loop (d $$ a))
      loop (VIDesc_Bind vI tm y vf) =
          VSemI vI tm y (\v -> loop (vf v))

vmapI :: Value ->
         Value ->
         Ident -> (Value -> Value) ->
         Ident -> (Value -> Value) ->
         Value ->
         Value ->
         Value
vmapI vI vD i1 vA i2 vB vf vx = loop vD vx
    where
      loop (VIDesc_Id i)       a           = vf $$ i $$ a
      loop (VIDesc_K _)        a           = a
      loop (VIDesc_Pair d1 d2) (VPair x y) = VPair (loop d1 x) (loop d2 y)
      loop (VIDesc_Sg c d)     (VPair x y) = VPair x (loop (d $$ x) y)
      loop (VIDesc_Pi c d)     (VLam nm f) = VLam nm $ \v -> loop (d $$ v) (f v)
      loop (VIDesc_Bind vI tmD i vA) (VMapI vB vg tmx) =
          VMapI vB (VLam i $ \vi -> VLam "b" $ \vb -> loop (vA vi) (vg $$ vi $$ vb)) tmx

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
      loop v                   = reflect (vP $$ v)
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
                                          `tmApp` reify (VIDesc vI) v)

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
      loop v = error ("internal: vinduction stuck on " ++ show v)

{------------------------------------------------------------------------------}
videsc_bind :: Value
            -> Value
            -> Value
            -> Ident
            -> (Value -> Value)
            -> Value
videsc_bind vA vB vc x vf = loop vc
    where
      loop (VIDesc_Id i)       = vf i
      loop (VIDesc_K vB)       = VIDesc_K vB
      loop (VIDesc_Pair d1 d2) = VIDesc_Pair (loop d1) (loop d2)
      loop (VIDesc_Sg vB d)    = VIDesc_Sg vB (VLam "b" $ \v -> loop (d $$ v)) -- FIXME: get the binder name from 'd'
      loop (VIDesc_Pi vB d)    = VIDesc_Pi vB (VLam "b" $ \v -> loop (d $$ v))
      loop (VIDesc_Bind vI tm y vf) =
          VIDesc_Bind vI tm y (\v -> loop (vf v))

vliftI :: Value   -- ^ index type
       -> Value   -- ^ description
       -> Ident -> (Value -> Value)
       -> Ident -> Ident -> (Value -> Value -> Value)
       -> Value
       -> Value
vliftI vI vD x vA i a vP vx = loop vD vx
    where
      loop (VIDesc_Id i)       vx = vP i vx
      loop (VIDesc_K vB)       vx = VUnit
      loop (VIDesc_Pair d1 d2) vx = loop d1 (vfst vx) .*. loop d2 (vsnd vx)
      loop (VIDesc_Sg vB d)    vx = loop (d $$ vfst vx) (vsnd vx)
      loop (VIDesc_Pi vB d)    vx = forall "b" vB $ \vb -> loop (d $$ vb) (vx $$ vb)
      loop v vx =
          VNeutral (In <$> (LiftI <$> reifyType vI
                                  <*> reify (VIDesc vI) v
                                  <*> pure (Irrelevant x)
                                  <*> bound vI (\v -> reifyType (vA v))
                                  <*> pure (Irrelevant i)
                                  <*> pure (Irrelevant a)
                                  <*> bound vI (\vi -> bound (vA vi) (\va -> reifyType (vP vi va)))
                                  <*> reify (vsemI vI v x vA) vx))

vallI :: Value
vallI = VLam "I" $ \vI ->
        VLam "D" $ \vD ->
        VLam "A" $ \vA ->
        VLam "P" $ \vP ->
        VLam "p" $ \vp ->
        VLam "xs" $ \xs ->
        videsc_elim vI (VLam "D" $ \vD ->
                        forall "xs" (vsemI vI vD "i" (vA $$)) $ \xs ->
                        vliftI vI vD "i" (vA $$) "i" "a" (\i a -> vP $$ i $$ a) xs)
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

vinductionI :: Value -- ^ The index type (@I : Set@)
            -> Value -- ^ The description (@D : IDesc I@)
            -> Value -- ^ The predicate (@P : (i : I) -> MuI D i -> Set@)
            -> Value -- ^ The body (@k : (i : I) -> semI[D i, i. MuI D i] -> liftI[D i, i. MuI D i, i x. P i x] -> P i (construct x)@)
            -> Value -- ^ The index (@i : I@)
            -> Value -- ^ The target (@x : MuI D i@)
            -> Value -- ^ The result (@P i x@)
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
                                  forall "x" (vsemI vI (vD $$ i) "i" (vmuI vI vD $$)) $ \x ->
                                  (vliftI vI (vD $$ i) "i" (vmuI vI vD $$) "i" "a" (\i a -> vP $$ i $$ a) x) .->.
                                  vP $$ i $$ VConstruct x) vk
                   `tmApp` reify vI vi
                   `tmApp` n)

veliminate :: Value -- ^ The index type (@I : Set@)
           -> Value -- ^ The description (@D : I -> IDesc I@)
           -> Value -- ^ The index (@i : I@)
           -> Value -- ^ The target (@xs : MuI I D i@)
           -> Ident -> Ident -> (Value -> Value -> Value) -- ^ The predicate (@i : I, x : MuI I D i |- P type@)
           -> Ident -> Ident -> Ident -> (Value -> Value -> Value -> Value) -- ^ The body
           -> Value
veliminate vI vD vi vt i1 x1 vP i2 x2 p2 vK = loop vi vt
    where
      loop vi (VConstruct x) =
          vK vi x
             -- FIXME: vallI should be a built-in, because it needs to
             -- define stuff with type arguments
             (vallI $$ vI $$ (vD $$ vi) $$ vmuI vi vD
                    $$ (VLam "i" $ \i -> VLam "x" $ \x -> vP i x)
                    $$ (VLam "i" $ \i -> VLam "x" $ \x -> loop i x)
                    $$ x)
      loop vi (VNeutral n) =
          reflect (vP vi (VNeutral n))
                  (In <$> (Eliminate
                           <$> reifyType vI
                           <*> reify (vI .->. VIDesc vI) vD
                           <*> reify vI vi
                           <*> n
                           <*> pure (Irrelevant i1) <*> pure (Irrelevant x1)
                           <*> bound vI (\vi -> bound (VMuI vI vD vi) (\vx -> reifyType (vP vi vx)))
                           <*> pure (Irrelevant i2) <*> pure (Irrelevant x2) <*> pure (Irrelevant p2)
                           <*> bound vI (\vi ->
                                 bound (vsemI vI (vD $$ vi) "i" (vmuI vI vD $$)) (\vx ->
                                   bound (vliftI vI (vD $$ vi) "i" (vmuI vI vD $$) "i" "a" vP vx) (\vp ->
                                     reify (vP vi (VConstruct vx)) (vK vi vx vp))))))
      loop vi x = error $ "internal: eliminate/loop got : " ++ show x

{------------------------------------------------------------------------------}
vgroup :: Ident -> Abelian -> Maybe Value -> Value
vgroup nm ab Nothing   = VGroup nm ab Nothing
vgroup nm ab (Just ty) = VLam "x" $ \x -> VGroup nm ab (Just (ty, x))

vgroupUnit :: Value
vgroupUnit = VGroupTerm []

vgroupMul :: Value -> Value -> Value
vgroupMul (VGroupTerm tms1) (VGroupTerm tms2) = VGroupTerm (tms1 ++ tms2)
vgroupMul _                 _                 = error "internal: type error discovered in vgroupMul"

vgroupInv :: Value -> Value
vgroupInv (VGroupTerm tms) = VGroupTerm $ reverse $ map (\(inverted,tm) -> (not inverted,tm)) tms
vgroupInv _                = error "internal: type error discovered in vgroupInv"

{------------------------------------------------------------------------------}
reflect :: Value -> (Int -> Term) -> Value
reflect (VPi nm tA tB)   tm = VLam (fromMaybe "x" nm) $ \d -> reflect (tB d) (tm `tmApp` reify tA d)
reflect (VSigma _ tA tB) tm = let v1 = reflect tA (tmFst tm)
                                  v2 = reflect (tB v1) (tmSnd tm)
                              in VPair v1 v2
reflect VUnit            tm = VUnitI
reflect (VIDesc vA)      tm = VIDesc_Bind vA tm "i" VIDesc_Id
reflect (VSemI vI tmD i vA) tm = VMapI vA (VLam i $ \i -> VLam "x" $ \x -> x) tm
reflect (VGroup nm ab _) tm = VGroupTerm [(False, tm)]
reflect _                tm = VNeutral tm


{------------------------------------------------------------------------------}
reifyType :: Value -> (Int -> Term)
reifyType (VPi x v f)     = \i -> In $ Pi (Irrelevant x) (reifyType v i) (reifyType (f (reflect v $ vbound i)) (i+1))
reifyType (VSigma x v f)  = \i -> In $ Sigma (Irrelevant x) (reifyType v i) (reifyType (f (reflect v $ vbound i)) (i+1))
reifyType (VSum v1 v2)    = \i -> In $ Sum (reifyType v1 i) (reifyType v2 i)
reifyType (VSet l)        = \i -> In $ Set l
reifyType VUnit           = \i -> In $ Unit
reifyType VEmpty          = \i -> In $ Empty
reifyType (VEq vA vB va vb) = \i -> In $ Eq (reifyType vA i) (reifyType vB i) (reify vA va i) (reify vB vb i)
reifyType VDesc           = \i -> In $ Desc
reifyType (VMu v)         = \i -> In $ Mu (reify VDesc v i)
reifyType (VMuI v1 v2 v3) = (\i -> In $ MuI (reifyType v1 i) (reify (v1 .->. VIDesc v1) v2 i)) `tmApp` reify v1 v3
reifyType (VIDesc s)      = pure (In IDesc) `tmApp` reifyType s
reifyType (VSemI vI tmD i vA) =
    In <$> (SemI <$> reifyType vI <*> tmD <*> pure (Irrelevant i) <*> bound vI (\v -> reifyType (vA v)))
reifyType (VGroup nm ab Nothing)  = \i -> In $ Group nm ab Nothing
reifyType (VGroup nm ab (Just (t1, t2))) = (In <$> (Group nm ab <$> (Just <$> reifyType t1))) `tmApp` reify t1 t2
reifyType (VNeutral t)    = \i -> t i
reifyType v               = error ("internal: reifyType given non-type: " ++ show v)

reifyType0 :: Value -> Term
reifyType0 v = reifyType v 0

{------------------------------------------------------------------------------}
reify :: Value -> Value -> (Int -> Term)

reify (VSet _) a = reifyType a

reify (VPi _ tA tB)    (VLam nm f) = \i -> let d = reflect tA (vbound i)
                                           in In $ Lam (Irrelevant nm) $ reify (tB d) (f d) (i + 1)
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
reify (VMuI tI tD ti)  (VConstruct v)      = \i -> In $ Construct (reify (vsemI tI (tD $$ ti) "i" (vmuI tI tD $$)) v i)
reify (VIDesc tI)      (VIDesc_Id x)       = \i -> In $ IDesc_Id (reify tI x i)
reify (VIDesc tI)      (VIDesc_K a)        = \i -> In $ IDesc_K (reifyType a i)
reify (VIDesc tI)      (VIDesc_Pair d1 d2) = \i -> In $ IDesc_Pair (reify (VIDesc tI) d1 i) (reify (VIDesc tI) d2 i)
reify (VIDesc tI)      (VIDesc_Sg a d)     = \i -> In $ IDesc_Sg (reifyType a i) (reify (a .->. VIDesc tI) d i)
reify (VIDesc tI)      (VIDesc_Pi a d)     = \i -> In $ IDesc_Pi (reifyType a i) (reify (a .->. VIDesc tI) d i)
reify (VIDesc tI)      (VIDesc_Bind vA tm x vf) =
     In <$> (IDesc_Bind <$> reifyType vA <*> reifyType tI <*> tm <*> pure (Irrelevant x) <*> bound vA (\v -> reify (VIDesc tI) (vf v)))
reify (VIDesc tI)      v                   = error $ "internal: reify: non-canonical value of VIDesc: " ++ show v
reify (VSemI vI tmD i vA) (VMapI vB vf tmX) =
    In <$> (MapI <$> reifyType vI <*> tmD
                 <*> pure (Irrelevant i) <*> bound vI (\i -> reifyType (vB i))
                 <*> pure (Irrelevant i) <*> bound vI (\i -> reifyType (vA i))
                 <*> reify (forall "i" vI $ \vi -> vB vi .->. vA vi) vf
                 <*> tmX)
reify (VSemI vI tmD i vA) v                = error $ "internal: reify: non-canonical value of VSemI: " ++ show v
reify (VEq tA _ ta _)  VRefl               = \i -> In $ Refl
reify (VGroup nm ab _) (VGroupTerm tms)    = reifyGroupTerm tms ab
reify _                (VNeutral tm)       = tm
reify ty               v                   = error $ "internal: reify: attempt to reify: " ++ show v ++ " at type " ++ show ty

reifyGroupTerm :: [(Bool, Int -> Term)] -> Abelian -> Int -> Term
reifyGroupTerm l ab i =
    foldr smartMul (In GroupUnit) $ map doInverses $ normaliser $ map toTerm l
    where
      toTerm (inverted, tm) = (inverted, tm i)

      doInverses (True, tm)  = In $ GroupInv tm
      doInverses (False, tm) = tm

      normaliser = case ab of
                     IsAbelian  -> collapseAb M.empty
                     NotAbelian -> collapse []

      collapse []             []             = []
      collapse l1             []             = reverse l1
      collapse []             ((inv, v):l2)  = collapse [(inv,v)] l2
      collapse ((inv1,v1):l1) ((inv2,v2):l2) =
          if inv1 == not inv2 && v1 == v2 then
              collapse l1 l2
          else
              collapse ((inv2,v2):(inv1,v1):l1) l2

      toNum True  = -1
      toNum False = 1

      collapseAb m [] = map toTermAb (M.assocs m)
          where
            toTermAb (tm, n) =
                let t = foldr smartMul (In GroupUnit) (replicate (abs n) tm) in
                if n < 0 then (True, t) else (False, t)
      collapseAb m ((inv, tm):l) =
          case M.lookup tm m of
            Nothing -> collapseAb (M.insert tm (toNum inv) m) l
            Just n  ->
                let n' = n + toNum inv in
                if n' == 0 then collapseAb (M.delete tm m) l
                           else collapseAb (M.insert tm n' m) l

      smartMul x (In GroupUnit) = x
      smartMul x y              = In $ GroupMul x y