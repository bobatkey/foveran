{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing.Conversion
       ( Value (..)
       , evaluate
       , reifyType0
       , ($$)
       , (.->.)
       , forall
       , reflect
       , vsem
       , vfst
       , vlift
       )
       where

import Control.Applicative
import Text.Show.Functions
import Data.Maybe (fromMaybe)
import Data.Rec
import Language.Foveran.Syntax.Checked

-- working from “Normalisation by Evaluation for Martin-Löf Type
-- Theory with One Universe” by Abel, Aehlig and Dybjer.

{------------------------------------------------------------------------------}
data Value
    = VLam   Ident (Value -> Value)
    | VSet   Int
    | VPi    (Maybe Ident) Value (Value -> Value)
    | VSigma (Maybe Ident) Value (Value -> Value)
    | VSum   Value Value
    | VPair  Value Value
    | VInl   Value
    | VInr   Value
    | VUnit
    | VUnitI
    | VEmpty
    | VDesc
    | VDesc_K Value
    | VDesc_Id
    | VDesc_Prod Value Value
    | VDesc_Sum  Value Value
    | VMu        Value
    | VConstruct Value  Value
      
    | VIDesc      Value
    | VIDesc_K    Value Value
    | VIDesc_Id   Value Value
    | VIDesc_Pair Value Value Value
    | VIDesc_Sg   Value Value Value
    | VIDesc_Pi   Value Value Value
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

vsem :: Value
vsem = VLam "d" $ vdesc_elim (VLam "d" $ \_ -> VSet 0 .->. VSet 0)
                             (VLam "A" $ \a -> VLam "X" $ \_ -> a)
                             (VLam "X" $ \x -> x)
                             (VLam "d1" $ \_ -> VLam "d2" $ \_ ->
                              VLam "F" $ \f -> VLam "G" $ \g -> 
                              VLam "X" $ \x -> (f $$ x) .*. (g $$ x))
                             (VLam "d1" $ \_ -> VLam "d2" $ \_ ->
                              VLam "F" $ \f -> VLam "G" $ \g -> 
                              VLam "X" $ \x -> (f $$ x) .+. (g $$ x))

vmap :: Value
vmap = VLam "F" $ \f ->
       VLam "A" $ \a ->
       VLam "B" $ \b ->
       VLam "f" $ \f' ->
       vdesc_elim (VLam "d" $ \d -> (vsem $$ d $$ a) .->. (vsem $$ d $$ b))
                  (VLam "A" $ \_ -> VLam "x" $ \x -> x)
                  (VLam "x" $ \x -> f' $$ x)
                  (VLam "d1" $ \d1 ->
                   VLam "d2" $ \d2 ->
                   VLam "g" $ \g ->
                   VLam "h" $ \h ->
                   VLam "p" $ \p -> VPair (g $$ (vfst p)) (h $$ (vsnd p)))
                  (VLam "d1" $ \d1 ->
                   VLam "d2" $ \d2 ->
                   VLam "g" $ \g ->
                   VLam "h" $ \h ->
                   VLam "s" $ \s -> vcase s
                                          (vsem $$ d1 $$ a)
                                          (vsem $$ d2 $$ a)
                                          "x" (\_ -> vsem $$ (VDesc_Sum d1 d2) $$ b)
                                          "x" (\x -> VInl (g $$ x))
                                          "x" (\x -> VInr (h $$ x)))
                  f

vlift :: Value
vlift = VLam "D" $ \d ->
        VLam "X" $ \vA ->
        VLam "P" $ \p ->
        VLam "x" $ \v ->
        vdesc_elim (VLam "D" $ \d -> (vsem $$ d $$ vA) .->. VSet 2)
                   (VLam "A" $ \a -> VLam "x" $ \x -> VUnit)
                   (VLam "x" $ \x -> p $$ x)
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
                          (vsem $$ fd $$ vA)
                          (vsem $$ gd $$ vA)
                          "x" (\_ -> VSet 2)
                          "x" (\x -> f $$ x)
                          "x" (\x -> g $$ x))
                   d
                   $$ v

vdesc_elim vP vK vI vPr vSu = loop
    where
      loop (VDesc_K v)        = vK $$ v
      loop VDesc_Id           = vI
      loop (VDesc_Prod v1 v2) = vPr $$ v1 $$ v2 $$ loop v1 $$ loop v2
      loop (VDesc_Sum  v1 v2) = vSu $$ v1 $$ v2 $$ loop v1 $$ loop v2
      loop (VNeutral n)       = reflect (vP $$ VNeutral n)
                                        (pure (In Desc_Elim)
                                         `tmApp` reify (VDesc .->. VSet 1) vP
                                         `tmApp` reify (forall "A" (VSet 0) $ \x -> vP $$ VDesc_K x) vK
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
      loop x                  = error $ "internal: type error in the evaluator: vdesc_elim"

videsc_elim vI vP vId vK vPair vSg vPi = loop
    where
      loop (VIDesc_Id _ i)       = vId $$ i
      loop (VIDesc_K _ a)        = vK $$ a
      loop (VIDesc_Pair _ d1 d2) = vPair $$ d1 $$ d2 $$ loop d1 $$ loop d2
      loop (VIDesc_Sg _ a d)     = vSg $$ a $$ d $$ (VLam "a" $ \a -> loop (d $$ a))
      loop (VIDesc_Pi _ a d)     = vPi $$ a $$ d $$ (VLam "a" $ \a -> loop (d $$ a))
      loop (VNeutral n)          = reflect (vP $$ VNeutral n)
                                           (pure (In IDesc_Elim) 
                                            `tmApp` reify (VSet 0) vI
                                            `tmApp` reify (VIDesc vI .->. VSet 10) vP
                                            `tmApp` reify (forall "x" vI $ \x -> vP $$ VIDesc_Id vI x) vId
                                            `tmApp` reify (forall "A" (VSet 0) $ \a -> vP $$ VIDesc_K vI a) vK
                                            `tmApp` reify (forall "D1" (VIDesc vI) $ \d1 ->
                                                           forall "D2" (VIDesc vI) $ \d2 ->
                                                           (vP $$ d1) .->.
                                                           (vP $$ d2) .->.
                                                           (vP $$ VIDesc_Pair vI d1 d2)) vPair
                                            `tmApp` reify (forall "A" (VSet 0) $ \a ->
                                                           forall "D" (a .->. VIDesc vI) $ \d ->
                                                           (forall "x" a $ \x -> vP $$ (d $$ x)) .->.
                                                           (vP $$ VIDesc_Sg vI a d)) vSg
                                            `tmApp` reify (forall "A" (VSet 0) $ \a ->
                                                           forall "D" (a .->. VIDesc vI) $ \d ->
                                                           (forall "x" a $ \x -> vP $$ (d $$ x)) .->.
                                                           (vP $$ VIDesc_Pi vI a d)) vPi
                                            `tmApp` n)
      loop x                  = error $ "internal: type error in the evaluator: videsc_elim"
                                            
vcase :: Value -> Value -> Value -> Ident -> (Value -> Value) -> Ident -> (Value -> Value) -> Ident -> (Value -> Value) -> Value
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

vall :: Value
vall = VLam "D" $ \vF ->
       VLam "X" $ \vX ->
       VLam "P" $ \vP ->
       VLam "p" $ \vp ->
       vdesc_elim (VLam "D" $ \vD -> forall "xs" (vsem $$ vD $$ vX) $ \xs -> vlift $$ vD $$ vX $$ vP $$ xs)
                  (VLam "A" $ \a -> VLam "x" $ \x -> VUnitI)
                  (VLam "x" $ \x -> vp $$ x)
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
                         (vsem $$ vF $$ vX)
                         (vsem $$ vG $$ vX)
                         "d" (\d -> vlift $$ VDesc_Sum vF vG $$ vX $$ vP $$ d)
                         "y" (\y -> vf $$ y)
                         "z" (\z -> vg $$ z))
                  vF

vinduction :: Value -> Value -> Value -> Value -> Value
vinduction vF vP vK = loop
    where
      loop (VConstruct _ x) = vK $$ x $$ (vall $$ vF $$ (VMu vF) $$ vP $$ (VLam "x" loop) $$ x)
      loop (VNeutral n) =
          reflect (vP $$ VNeutral n)
                  (pure (In Induction)
                   `tmApp` reify VDesc vF
                   `tmApp` reify (VMu vF .->. VSet 2) vP
                   `tmApp` reify (VPi (Just "x") (vsem $$ vF $$ VMu vF) $ \x ->
                                  (vlift $$ vF $$ VMu vF $$ vP $$ x) .->.
                                  vP $$ VConstruct vF x)
                                 vK
                   `tmApp` n)

velimEmpty :: Value -> Value -> Value
velimEmpty a (VNeutral n) = reflect a (pure (In ElimEmpty)
                                       `tmApp` reifyType a
                                       `tmApp` n)

($$) :: Value -> Value -> Value
($$) (VLam _ f)   v = f v
($$) v            _ = error $ "internal: vapp given non-function: " ++ show v

vfst :: Value -> Value
vfst (VPair v _) = v
vfst v           = error $ "internal: vfst given non-pair: " ++ show v

vsnd :: Value -> Value
vsnd (VPair _ v) = v
vsnd v           = error $ "internal: vsnd given non-pair: " ++ show v

{------------------------------------------------------------------------------}
reflect :: Value -> (Int -> Term) -> Value
reflect (VPi nm tA tB)   tm = VLam (fromMaybe "x" nm) $ \d -> reflect (tB d) (tm `tmApp` reify tA d)
reflect (VSigma _ tA tB) tm = let v1 = reflect tA (tmFst tm)
                                  v2 = reflect (tB v1) (tmSnd tm)
                              in VPair v1 v2
reflect VUnit            tm = VUnitI
reflect _                tm = VNeutral tm

reifyType :: Value -> (Int -> Term)
reifyType (VPi x v f)    = \i -> In $ Pi x (reifyType v i) (reifyType (f (reflect v $ vbound i)) (i+1))
reifyType (VSigma x v f) = \i -> In $ Sigma x (reifyType v i) (reifyType (f (reflect v $ vbound i)) (i+1))
reifyType (VSum v1 v2)   = \i -> In $ Sum (reifyType v1 i) (reifyType v2 i)
reifyType (VSet l)       = \i -> In $ Set l
reifyType VUnit          = \i -> In $ Unit
reifyType VEmpty         = \i -> In $ Empty
reifyType VDesc          = \i -> In $ Desc
reifyType (VMu v)        = \i -> In $ Mu (reify VDesc v i)
reifyType (VIDesc s)     = pure (In IDesc) `tmApp` reifyType s
reifyType (VNeutral t)   = \i -> t i
reifyType v              = error ("internal: reifyType given non-type: " ++ show v)



reify :: Value -> Value -> (Int -> Term)

reify (VSet _)         a = reifyType a

reify (VPi _ tA tB)    (VLam nm f) = \i -> let d = reflect tA (vbound i)
                                           in In $ Lam nm $ reify (tB d) (f d) (i + 1)
reify (VPi _ tA tB)    _           = error "internal: reify: values of type Pi-blah should only by VLam"

reify (VSigma _ tA tB) e = let v1 = vfst e
                               v2 = vsnd e
                           in \i -> In $ Pair (reify tA v1 i) (reify (tB v1) v2 i)

reify (VSum tA tB)     (VInl v) = \i -> In $ Inl (reify tA v i)
reify (VSum tA tB)     (VInr v) = \i -> In $ Inr (reify tB v i)

reify VUnit            VUnitI   = \i -> In $ UnitI
reify VUnit            _        = error "internal: reify: values of type unit should only be VUnitI"

reify VDesc            (VDesc_K v)        = \i -> In $ Desc_K (reifyType v i)
reify VDesc            VDesc_Id           = \i -> In $ Desc_Id
reify VDesc            (VDesc_Prod v1 v2) = \i -> In $ Desc_Prod (reify VDesc v1 i) (reify VDesc v2 i)
reify VDesc            (VDesc_Sum v1 v2)  = \i -> In $ Desc_Sum (reify VDesc v1 i) (reify VDesc v2 i)
reify (VMu tA)         (VConstruct v1 v2) = pure (In Construct) `tmApp` reify VDesc v1
                                                                `tmApp` reify (vsem $$ v1 $$ (VMu v1)) v2
reify (VIDesc tI)      (VIDesc_Id i x)    = pure (In IDesc_Id) `tmApp` reifyType i
                                                               `tmApp` reify i x
reify (VIDesc tI)      (VIDesc_K i a)     = pure (In IDesc_K) `tmApp` reifyType i
                                                              `tmApp` reifyType a
reify (VIDesc tI)      (VIDesc_Pair i d1 d2) = pure (In IDesc_Pair) `tmApp` reifyType i
                                                                    `tmApp` reify (VIDesc tI) d1
                                                                    `tmApp` reify (VIDesc tI) d2
reify (VIDesc tI)      (VIDesc_Sg i a d)  = pure (In IDesc_Sg) `tmApp` reifyType i
                                                               `tmApp` reifyType a
                                                               `tmApp` reify (a .->. VIDesc i) d
reify (VIDesc tI)      (VIDesc_Pi i a d)  = pure (In IDesc_Pi) `tmApp` reifyType i
                                                               `tmApp` reifyType a
                                                               `tmApp` reify (a .->. VIDesc i) d
reify _                (VNeutral tm)      = tm
reify _                v                  = error $ "reify: attempt to reify: " ++ show v

{------------------------------------------------------------------------------}
-- Evaluation
type Eval a = ([Value], Ident -> (Value, Maybe Value)) -> a

getBound k (env, _) = env !! k

getDef nm (_, context) = case def of
                           Nothing -> reflect ty (tmFree nm)
                           Just d  -> d
    where
      (ty, def) = context nm

withBound :: Eval a -> Eval (Value -> a)
withBound p = \(env,defs) v -> p (v:env, defs)

eval :: TermCon (Eval Value) -> Eval Value
eval (Bound k)     = getBound k
eval (Free nm)     = getDef nm

eval (Set l)       = pure $ VSet l

eval (Pi nm t1 t2) = VPi nm <$> t1 <*> withBound t2
eval (Lam nm t)    = VLam nm <$> withBound t
eval (App t1 t2)   = ($$) <$> t1 <*> t2

eval (Sigma nm t1 t2) = VSigma nm <$> t1 <*> withBound t2
eval (Pair t1 t2)     = VPair <$> t1 <*> t2
eval (Proj1 t)        = vfst <$> t
eval (Proj2 t)        = vsnd <$> t

eval (Sum t1 t2)             = VSum <$> t1 <*> t2
eval (Inl t)                 = VInl <$> t
eval (Inr t)                 = VInr <$> t
eval (Case t tA tB x tP y tL z tR) = vcase <$> t
                                     <*> tA
                                     <*> tB
                                     <*> pure x <*> withBound tP
                                     <*> pure y <*> withBound tL
                                     <*> pure z <*> withBound tR

eval Unit      = pure VUnit
eval UnitI     = pure VUnitI
eval Empty     = pure VEmpty
eval ElimEmpty = pure $ VLam "A" $ \a -> VLam "x" $ \x -> velimEmpty a x

eval Desc               = pure VDesc
eval (Desc_K t)         = VDesc_K <$> t
eval Desc_Id            = pure VDesc_Id
eval (Desc_Prod t1 t2)  = VDesc_Prod <$> t1 <*> t2
eval (Desc_Sum t1 t2)   = VDesc_Sum <$> t1 <*> t2
eval Desc_Elim          = pure (VLam "P" $ \p ->
                                VLam "K" $ \k ->
                                VLam "Id" $ \i ->
                                VLam "Pr" $ \pr ->
                                VLam "Su" $ \su ->
                                VLam "Tg" $ \tg ->
                                vdesc_elim p k i pr su tg)
eval (Mu t)             = VMu <$> t
eval Construct          = pure (VLam "F" $ \f -> VLam "x" $ \x -> VConstruct f x)
eval Induction          = pure (VLam "F" $ \f ->
                                VLam "P" $ \p ->
                                VLam "k" $ \k ->
                                VLam "x" $ \x ->
                                vinduction f p k x)

eval IDesc              = pure (VLam "I" $ \i -> VIDesc i)
eval IDesc_K            = pure (VLam "I" $ \i -> VLam "A" $ \a -> VIDesc_K i a)
eval IDesc_Id           = pure (VLam "I" $ \i -> VLam "i" $ \x -> VIDesc_Id i x)
eval IDesc_Pair         = pure (VLam "I" $ \i -> VLam "d1" $ \d1 -> VLam "d2" $ \d2 -> VIDesc_Pair i d1 d2)
eval IDesc_Sg           = pure (VLam "I" $ \i -> VLam "A" $ \a -> VLam "d" $ \d -> VIDesc_Sg i a d)
eval IDesc_Pi           = pure (VLam "I" $ \i -> VLam "A" $ \a -> VLam "d" $ \d -> VIDesc_Pi i a d)
eval IDesc_Elim         = pure (VLam "I" $ \i ->
                                VLam "P" $ \p ->
                                VLam "pId" $ \pId ->
                                VLam "pK"  $ \pK ->
                                VLam "pPair" $ \pPair ->
                                VLam "pSg" $ \pSg ->
                                VLam "pPi" $ \pPi ->
                                VLam "d" $ \d ->
                                videsc_elim i p pId pK pPair pSg pPi d)

{------------------------------------------------------------------------------}
evaluate :: Term -> [Value] -> (Ident -> (Value, Maybe Value)) -> Value
evaluate t env defs = foldRec eval t (env,defs)

reifyType0 :: Value -> Term
reifyType0 v = reifyType v 0
