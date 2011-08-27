{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing.Conversion.Value
    ( Value (..)
    , (.->.)
    , forall
    , (.*.)
    , (.+.)

    , tmFree

    , ($$)

    , vfst
    , vsnd
    , vcase
    , velimEmpty

    , vdesc_elim
    , videsc_elim

    , vsem
    , vsemI

    , vliftTy
    , vlift
    , vinduction
    , vmuI

    , reflect
    , reifyType
    , reify

    , vTy
    , vtysem
    , vtypred
    , vCtxt
    , vctxtsem
    , vctxtpred
--    , vparam
    , vparam2
    )
    where

import Text.Show.Functions ()

import Control.Applicative

import qualified Data.Text as T
import Data.Maybe (fromMaybe)
import Data.Rec

import Language.Foveran.Syntax.Identifier (Ident)
import Language.Foveran.Syntax.Checked

import Debug.Trace

{------------------------------------------------------------------------------}

{-
data Neutral
    = NApp       Neutral Value Value
    | NFree      Ident
    | NBound     Int
    | NFst       Neutral
    | NSnd       Neutral
    | NCase      Neutral Ident (Value -> Value) Ident (Value -> Value) Ident (Value -> Value)
    | NElimEmpty Neutral Value
    | NSem       Neutral
    | NDescElim  Neutral Value Value Value Value Value
    | NIDescElim Neutral Value Value Value Value Value Value Value
    | NInduction Neutral Value Value Value
    deriving Show

vNeutral :: Neutral -> Value
vNeutral = undefined

tmBound' :: (Value -> Int -> Term) -> Int -> Term
tmBound' f i = f (vNeutral $ NBound i) (i+1)

-- maybe, instead of storing the type with the 'NApp', we could get
-- reifyNeutral to return the type. This would require a typing
-- environment to be passed in. Otherwise, we need to magic up a type
-- from somewhere during evaluation. This means we'd need to know the
-- types of the components of the sum type in NCase, because they'll
-- be needed to add to the typing environment to be passed to reify.

-- This seems to me to be repeating a whole load of work all the
-- time... In the reflect/reify version we only ever need to construct
-- a new tuple for each product once.

reifyNeutral :: Neutral -> (Int -> Term)
reifyNeutral (NApp n v vTy)
    = reifyNeutral n `tmApp` reify vTy v
reifyNeutral (NFree s)
    = tmFree s
reifyNeutral (NBound i)
    = \j -> In $ Bound (j - i - 1) -- and tmBound
reifyNeutral (NFst n)
    = tmFst $ reifyNeutral n
reifyNeutral (NSnd n)
    = tmSnd $ reifyNeutral n
reifyNeutral (NCase n x vP l vL r vR)
    = In <$> (Case
              <$> reifyNeutral n
              <*> undefined -- don't need these under this regime, which might mean it is better
              <*> undefined -- 
              <*> pure x <*> tmBound' (\tmV -> reifyType (vP tmV))
              <*> pure l <*> tmBound' (\tmV -> reify (vP $ VInl tmV) (vL tmV))
              <*> pure r <*> tmBound' (\tmV -> reify (vP $ VInr tmV) (vR tmV)))
reifyNeutral (NElimEmpty n vA)
    = pure (In ElimEmpty) `tmApp` reifyType vA `tmApp` reifyNeutral n
reifyNeutral (NSem n)
    = pure (In Sem) `tmApp` reifyNeutral n
reifyNeutral (NDescElim n vP vK vI vPr vSu)
    = pure (In Desc_Elim)
      `tmApp` reify (VDesc .->. VSet 1) vP
      `tmApp` reify (forall "A" (VSet 0) $ \vA -> vP $$ VDesc_K vA) vK
      `tmApp` reify (vP $$ VDesc_Id) vI
      `tmApp` reify (forall "F" VDesc $ \f -> forall "G" VDesc $ \g -> (vP $$ f) .->. (vP $$ g) .->. (vP $$ (VDesc_Prod f g))) vPr
      `tmApp` reify (forall "F" VDesc $ \f -> forall "G" VDesc $ \g -> (vP $$ f) .->. (vP $$ g) .->. (vP $$ (VDesc_Sum f g))) vSu
      `tmApp` reifyNeutral n


-- Now, to do parametricity reflection with this representation...
--
-- When the return type is 'v', then the returned value must be neutral...
-- if it is 'NApp', then we have to find a way of reabstracting the argument in order to apply the param function again
-- if it is 'NCase', then we have to check to see whether it returns a 
-}

{------------------------------------------------------------------------------}
-- combinators for building (codes for) types
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
                       <*> pure x <*> tmBound (VSum vA vB) (\tmV -> reify (VSet 0) (vP (reflect (VSum vA vB) tmV)))
                       <*> pure y <*> tmBound vA (\tmV -> let v = reflect vA tmV in reify (vP $ VInl v) (vL v))
                       <*> pure z <*> tmBound vB (\tmV -> let v = reflect vB tmV in reify (vP $ VInr v) (vR v))))
{-
vcase (VInnerNeutral n) vA vB x vP y vL z vR
    = reflectInner ty
                   (InnerCase <$> n
                              <*> pure y <*> (\i -> reifyInner ty (vL (reflectInner tyA (vinnerbound i))) (i+1))
                              <*> pure z <*> (\i -> reifyInner ty (vR (reflectInner tyB (vinnerbound i))) (i+1))
    where
      ty = reifyInnerType' (vP $ VInnerNeutral n) -- is this OK?
      tyA = reifyInnerType' vA
      tyB = reifyInnerType' vB
-}
vcase _            _  _  _ _  _ _  _ _  = error "internal: type error when eliminating case"

-- basically, if we get VInnerNeutral as an argument, then we make a
-- best effort to reify it as an inner language term. We look at the
-- type argument, and if it normalises to an inner language type, then
-- we 

-- what if we have
--   foo : (n : nat) → (A : Set) → (A → A) → A → A
-- and
--   x : A + A |- foo (case x for Nat with inl a. 2; inr b. 3) A succ zero : A
-- ??
--
-- nice case:
--   x : A + A |- case x for A with inl a. a; inr b. b : A

-- so if the case appears in a context that is not an inner term then
-- we are stuck.

-- this matches codes for types that are in the image of the ty-sem
-- constructor.
--reifyInnerType' :: Value -> Maybe InnerType
--reifyInnerType' (VPi _ vA vB) = reifyInnerType' vA :=> reifyInnerType' (vB (VNeutral undefined))
--reifyInnerType' VInnerTypeVar = return Base
--reifyInnerType' (VSum vA vB)  = SumTy <$> reifyInnerType' vA <*> reifyInnerType' vB

{------------------------------------------------------------------------------}
velimEmpty :: Value -> Value -> Value
velimEmpty a (VNeutral n) = reflect a (pure (In ElimEmpty)
                                       `tmApp` reifyType a
                                       `tmApp` n)

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
tmApp :: (a -> Term) -> (a -> Term) -> (a -> Term)
tmApp t1 t2 = In <$> (App <$> t1 <*> t2)

tmFst :: (a -> Term) -> (a -> Term)
tmFst t = In . Proj1 <$> t

tmSnd :: (a -> Term) -> (a -> Term)
tmSnd t = In . Proj2 <$> t

tmInl :: (a -> Term) -> (a -> Term)
tmInl t = In . Inl <$> t

tmInr :: (a -> Term) -> (a -> Term)
tmInr t = In . Inr <$> t

-- FIXME: make vbound and tmbound a bit more rational
vbound :: Value -> (Int,Maybe Int) -> ((Int,Maybe Int) -> Term)
vbound v (i,Nothing) (j,Nothing) = In $ Bound (j - i - 1) v
vbound v (i,Nothing) (j,Just _)  = In $ Bound (j - i - 1) v
vbound v (i,Just i') (j,Just j') = In $ BoundLocal (j' - i' - 1)

tmBound :: Value -> (((Int,Maybe Int) -> Term) -> ((Int,Maybe Int) -> Term)) -> (Int,Maybe Int) -> Term
tmBound v f (i,Nothing) = f (vbound v (i,Nothing)) (i+1,Nothing)
tmBound v f (i,Just i') = f (vbound v (i,Just i')) (i,Just (i'+1))

tmFree :: Value -> Ident -> a -> Term
tmFree v nm = \i -> In $ Free nm v

{------------------------------------------------------------------------------}
reflect :: Value -> ((Int,Maybe Int) -> Term) -> Value
reflect (VPi nm tA tB)   tm = VLam (fromMaybe "x" nm) $ \d -> reflect (tB d) (tm `tmApp` reify tA d)
reflect (VSigma _ tA tB) tm = let v1 = reflect tA (tmFst tm)
                                  v2 = reflect (tB v1) (tmSnd tm)
                              in VPair v1 v2
reflect VUnit            tm = VUnitI
reflect _                tm = VNeutral tm


{------------------------------------------------------------------------------}
reifyType :: Value -> ((Int,Maybe Int) -> Term)
reifyType (VPi x v f)     = \i -> In $ Pi x (reifyType v i) (tmBound v (\x -> reifyType (f (reflect v x))) i)
reifyType (VSigma x v f)  = \i -> In $ Sigma x (reifyType v i) (tmBound v (\x -> reifyType (f (reflect v x))) i)
reifyType (VSum v1 v2)    = \i -> In $ Sum (reifyType v1 i) (reifyType v2 i)
reifyType (VSet l)        = \i -> In $ Set l
reifyType VUnit           = \i -> In $ Unit
reifyType VEmpty          = \i -> In $ Empty
reifyType VDesc           = \i -> In $ Desc
reifyType (VMu v)         = \i -> In $ Mu (reify VDesc v i)
reifyType (VMuI v1 v2 v3) = (\i -> In $ MuI (reifyType v1 i) (reify (v1 .->. VIDesc v1) v2 i)) `tmApp` reify v1 v3
reifyType (VIDesc s)      = pure (In IDesc) `tmApp` reifyType s
reifyType (VNeutral t)    = \i -> t i
reifyType v               = error ("internal: reifyType given non-type: " ++ show v)


{------------------------------------------------------------------------------}
reify :: Value -> Value -> ((Int,Maybe Int) -> Term)

reify (VSet _) a = reifyType a

reify (VPi _ tA tB)    (VLam nm f) = tmBound tA $ \x -> let d = reflect tA x in In . Lam nm <$> reify (tB d) (f d)
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
reify _                (VNeutral tm)       = tm
reify ty                v                   = error $ "reify: attempt to reify: " ++ show v ++ " at type " ++ show ty

--------------------------------------------------------------------------------
-- parametricity stuff
{-
data InnerTerm
    = InnerBound   Int
    | InnerApp     InnerTerm InnerTerm
    | InnerLam     Ident InnerTerm
    deriving Show

vinnerbound :: Int -> (Int -> Maybe InnerTerm)
vinnerbound i j = return $ InnerBound (j - i - 1)

data InnerType
    = Base
    | InnerType :=> InnerType
    deriving Show

--------------------------------------------------------------------------------
reifyInnerType :: Value -> Maybe InnerType
reifyInnerType (VConstruct (VInl VUnitI))        = pure Base
reifyInnerType (VConstruct (VInr (VPair t1 t2))) = (:=>) <$> reifyInnerType t1 <*> reifyInnerType t2
reifyInnerType (VNeutral _)                      = Nothing

--------------------------------------------------------------------------------
reifyInner :: InnerType -> Value -> (Int -> Maybe InnerTerm)
reifyInner Base        (VInnerNeutral tm) =
    tm
reifyInner (t1 :=> t2) (VLam nm f)        =
    \i -> let d = reflectInner t1 (vinnerbound i)
          in InnerLam nm <$> reifyInner t2 (f d) (i+1)
reifyInner _           (VNeutral _)       =
    \i -> Nothing
reifyInner t           v                  =
    error ("reifyInner: attempt to reify " ++ show v ++ " at type " ++ show t)

reflectInner :: InnerType -> (Int -> Maybe InnerTerm) -> Value
reflectInner Base        tm =
    VInnerNeutral tm
reflectInner (t1 :=> t2) tm =
    VLam "x" $ \x -> reflectInner t2 $ \i -> InnerApp <$> tm i <*> reifyInner t1 x i
--------------------------------------------------------------------------------
-}
vTyDesc = VDesc_Sum (VDesc_K VUnit)
                    (VDesc_Prod VDesc_Id VDesc_Id)

vTy = VMu vTyDesc

vtyinduction vP base arr =
    vinduction vTyDesc vP
               (VLam "t" $ \t ->
                vcase t VUnit (vTy .*. vTy)
                      "t" (\t -> vlift $$ vTyDesc $$ vTy $$ vP $$ t .->. vP $$ (VConstruct t))
                      "u" (\u -> VLam "u'" $ \u' -> base)
                      "p" (\p -> VLam "q" $ \q -> arr $$ vfst p $$ vsnd p $$ vfst q $$ vsnd q))

vtysem = vtyinduction (VLam "t" $ \t -> VSet 0 .->. VSet 0)
                      (VLam "A" $ \a -> a)
                      (VLam "t1" $ \t1 ->
                       VLam "t2" $ \t2 ->
                       VLam "s1" $ \s1 ->
                       VLam "s2" $ \s2 ->
                       VLam "A" $ \a ->
                       (s1 $$ a) .->. (s2 $$ a))

vtypred t vA vP =
    vtyinduction (VLam "t" $ \t -> vtysem t $$ vA .->. VSet 0)
                 (VLam "a" $ \a -> vP $$ a)
                 (VLam "t1" $ \t1 ->
                  VLam "t2" $ \t2 ->
                  VLam "P1" $ \p1 ->
                  VLam "P2" $ \p2 ->
                  VLam "f" $ \f ->
                  forall "a" (vtysem t1 $$ vA) $ \a -> (p1 $$ a) .->. (p2 $$ (f $$ a)))
                 t

{-
vparam :: Value -> -- type
          Value -> -- term
          Value -> -- set
          Value -> -- predicate
          Value    -- proof of abstraction theorem, or neutral
vparam vty vterm vA vP =
    case v of
      Just v  -> v
      Nothing -> 
          reflect (vtypred vty vA vP $$ (vterm $$ vA))
                  (pure (In Param)
                   `tmApp` reify vTy vty
                   `tmApp` reify (forall "A" (VSet 0) $ \a -> vtysem vty $$ a) vterm
                   `tmApp` reifyType vA
                   `tmApp` reify (vA .->. VSet 0) vP)
    where
      v = do
        ty <- reifyInnerType vty
        tm <- reifyInner ty (vterm $$ VNeutral (const undefined)) 0 -- FIXME: is this the right thing to do?
        return (absThm tm [])

      sem :: InnerTerm -> [Value] -> Value
      sem (InnerBound i)     env = env !! i
      sem (InnerLam nm tm)   env = VLam nm $ \v -> sem tm (v:env)
      sem (InnerApp tm1 tm2) env = sem tm1 env $$ sem tm2 env

      absThm :: InnerTerm -> [(Value,Value)] -> Value
      absThm (InnerBound i)     env = snd (env !! i)
      absThm (InnerLam nm tm)   env = VLam nm $ \x -> VLam ("φ" `T.append` nm) $ \phix -> absThm tm ((x,phix):env)
      absThm (InnerApp tm1 tm2) env = absThm tm1 env $$ sem tm2 (map fst env) $$ absThm tm2 env
-}

--------------------------------------------------------------------------------
vCtxtDesc = VDesc_Sum (VDesc_K VUnit)
                      (VDesc_Prod VDesc_Id (VDesc_K vTy))
vCtxt = VMu vCtxtDesc

vctxtinduction vP veps vext =
    vinduction vCtxtDesc vP
               (VLam "G" $ \vG ->
                vcase vG VUnit (vCtxt .*. vTy)
                      "G" (\vG -> vlift $$ vCtxtDesc $$ vCtxt $$ vP $$ vG .->. vP $$ (VConstruct vG))
                      "u" (\u -> VLam "u" $ \u' -> veps)
                      "p" (\p -> VLam "q" $ \q -> vext $$ vfst p $$ vsnd p $$ vfst q))

vctxtsem = vctxtinduction (VLam "G" $ \vG -> VSet 0 .->. VSet 0)
                          (VLam "A" $ \a -> VUnit)
                          (VLam "G" $ \vG ->
                           VLam "t " $ \t ->
                           VLam "sG" $ \sG ->
                           VLam "A" $ \a ->
                           (sG $$ a) .*. (vtysem t $$ a))

vctxtpred vG vA vP =
    vctxtinduction (VLam "G" $ \vG -> vctxtsem vG $$ vA .->. VSet 0)
                   (VLam "u" $ \u -> VUnit)
                   (VLam "G" $ \vG ->
                    VLam "t" $ \t ->
                    VLam "pG" $ \pG ->
                    VLam "e" $ \p ->
                    (pG $$ vfst p) .*. (vtypred t vA vP $$ vsnd p))
                   vG

vparam2 :: Value -> -- context
           Value -> -- type
           Value -> -- term
           Value -> -- concrete type
           Value -> -- predicate
           Value -> -- environment
           Value -> -- environment proof
           Value    -- proof of the abstraction theorem
vparam2 vG vT vTm vA vP = loop vG vT vTm
    where
      -- if vT is neutral, then stop
      -- if vT is a function type, then advance
      -- if vT is a base type, then intend to reify and analyse the term
      loop vG vT@(VNeutral n) vTm venv vphienv
          = reflect (vtypred vT vA vP $$ (vTm $$ vA $$ venv))
                    (pure (In Param)
                     `tmApp` reify vCtxt vG
                     `tmApp` n
                     `tmApp` reify (forall "A" (VSet 0) $ \a -> vctxtsem vG $$ a .->. vtysem vT $$ a) vTm
                     `tmApp` reifyType vA
                     `tmApp` reify (vA .->. VSet 0) vP
                     `tmApp` reify (vctxtsem vG $$ vA) venv
                     `tmApp` reify (vctxtpred vG vA vP $$ venv) vphienv)
      loop vG (VConstruct (VInr (VPair vT1 vT2))) vTm venv vphienv
          = VLam "x" $ \x ->
            VLam "φx" $ \phix ->
            loop (VConstruct (VInr (VPair vG vT1)))
                 vT2
                 (VLam "A" $ \a -> VLam "γ" $ \g -> vTm $$ a $$ vfst g $$ vsnd g)
                 (VPair venv x)
                 (VPair vphienv phix)
      loop vG vT@(VConstruct (VInl VUnitI)) vTm venv vphienv
          = --trace (show tm) $
            case scan tm of
              Nothing ->
                  reflect (vtypred vT vA vP $$ (vTm $$ vA $$ venv))
                          (pure (In Param)
                           `tmApp` reify vCtxt vG
                           `tmApp` reify vTy vT
                           `tmApp` reify (forall "A" (VSet 0) $ \a -> vctxtsem vG $$ a .->. vtysem vT $$ a) vTm
                           `tmApp` reifyType vA
                           `tmApp` reify (vA .->. VSet 0) vP
                           `tmApp` reify (vctxtsem vG $$ vA) venv
                           `tmApp` reify (vctxtpred vG vA vP $$ venv) vphienv
                          )
              Just (v,_) -> v
          where
            In (Lam nmA (In (Lam nmEnv tm))) =
                reify (forall "A" (VSet 0) $ \a -> vctxtsem vG $$ a .->. vtysem vT $$ a) vTm (0,Just 0)

            -- references to the environment will look like Proj2 (Proj1* (BoundLocal 0))
            -- to reflect the arguments, we re-interpret the reified normal-form term as a value, abstracted over the type variable and the context variable

            ctxtFst (VConstruct (VInr (VPair vG _))) = vG
            ctxtSnd (VConstruct (VInr (VPair _ vT))) = vT

            isEnvProj (In (BoundLocal 0)) = return (vphienv, vG)
            isEnvProj (In (Proj1 n))      = (\(x,y) -> (vfst x, ctxtFst y)) <$> isEnvProj n
            isEnvProj _                   = Nothing

            scan (In (Proj2 n)) = do (phi,ty) <- isEnvProj n
                                     return (vsnd phi, ctxtSnd ty)
            scan (In (App f x)) = do (phi,ty) <- scan f
                                     let VConstruct (VInr (VPair vT1 vT2)) = ty
                                     let va = VLam nmA $ \a -> VLam nmEnv $ \env -> evalNF x [env,a]
                                     return (phi $$ (va $$ vA $$ venv) $$ loop vG vT1 va venv vphienv, vT2)
            scan _              = Nothing

withBound :: ([Value] -> a) -> ([Value] -> Value -> a)
withBound p = \env v -> p (v:env)

evalNF (In (Bound i v))    = pure $ reflect v (vbound v (-i-1,Nothing))
evalNF (In (BoundLocal i)) = (!! i)
evalNF (In (Free nm v))    = pure $ reflect v (tmFree v nm)
evalNF (In (Lam nm t))     = VLam nm <$> withBound (evalNF t)
evalNF (In (Proj1 t))      = vfst <$> evalNF t
evalNF (In (Proj2 t))      = vsnd <$> evalNF t
evalNF (In (App t1 t2))    = ($$) <$> evalNF t1 <*> evalNF t2
-- FIXME: and everything else...

-- now look at tm. if it is an application, and the head is a
-- reference to the inner context, then extract the appropriate member
-- of vphienv and then work our way back up the spine, converting each
-- normal-form term back into a value abstracted over the type and
-- context.


    -- These problems appear to be fixed now...
            -- problem: by feeding in '0' we are generating clashes
            -- between the genuinely free variables, and the bound
            -- variables. We really need to feed in a separate
            -- variable stream that allows us to reify this term here.

            -- problem 2: how do we recover the original values of the
            -- free-but-bound variables?  we turn 'vbound i' into 0 -
            -- i - 1 = - (i+1). This should be recoverable.

            -- I think what I need to do is to turn the local lambdas
            -- into something different. Maybe an additional parameter
            -- to the reify function that is carried through
            -- everywhere?





-- otherwise reify vTm at the type (forall "A" (VSet 0) $ \a -> vctxtsem vG $$ a .->. vtysem vTy $$ a) and level 0

-- Then inspect the term



-- Why not just try to call 'reify' on vterm? with '0' as the offset

-- Then have a look at the returned term. It will always be in
-- beta-eta-normal form. So we will get (Lam (Lam -- neutral --))
-- Look at the neutral term:
--  App t1 t2 : get a parametricity proof for t1, and a value for t2 and a param proof for t2
--  Case blah blah blah : do the appropriate thing for the parametricity proof for this term?

--  if we get out something that isn't in the little inner language of
--  simple types, then turn it into a stuck instance of param

-- to turn things back into values, we basically just go over and
-- replace all the appropriate bound variables with lambda
-- abstractions. Then do an eval... This seems like it might be hard.

--  key is that normal forms of the type (A : Set) → [[t]]A are just
--  normal forms of the simply-typed lambda calculus...

-- 