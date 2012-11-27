{-# LANGUAGE OverloadedStrings, DeriveFunctor, GeneralizedNewtypeDeriving, DoAndIfThenElse #-}

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

    , videsc_elim

    , videsc_bind

    , vsemI
    , vmapI

    , vliftI
    , vmuI
    , veliminate

    , vgroup
    , vgroupUnit
    , vgroupMul
    , vgroupInv

    , reflect
    , reifyType0
    , reifyTypeForDisplay
    , reify
    , reify0
    , reifyForDisplay
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
data ReificationOpts
    = ReificationOpts
      { foldDefinitions :: Bool
      }

newtype ReifyFam a = ReifyFam { runReifyFam :: (ReificationOpts, Int) -> a }
    deriving (Functor, Monad, Applicative, Show)

instance Binding ReifyFam where
    binder (ReifyFam f) = ReifyFam $ \(opts,i) -> f (opts,i+1)
    variable c = ReifyFam $ \(_,i) -> ReifyFam $ \(_,j) -> c (j - i)

getReificationOpts :: ReifyFam ReificationOpts
getReificationOpts = ReifyFam $ \(opts,_) -> opts

withFullReification :: ReifyFam a -> ReifyFam a
withFullReification r =
    ReifyFam $ \(_,i) -> runReifyFam r (ReificationOpts False, i)

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

    | VUnit  (Maybe Ident)
    | VUnitI

    | VEmpty

    | VEq    Value Value Value Value
    | VRefl

    | VConstruct  (Maybe Ident) Value

    | VIDesc      Value
    | VMuI        Value Value Value
    | VIDesc_K    Value
    | VIDesc_Id   Value
    | VIDesc_Pair Value Value
    | VIDesc_Sg   Value Value
    | VIDesc_Pi   Value Value
    | VIDesc_Bind Value (ReifyFam Term) Ident (Value -> Value) -- ^ suspended 'bind' applications

    | VMapI       (Value -> Value) Value (ReifyFam Term)
    | VSemI       Value (ReifyFam Term) Ident (Value -> Value)

    | VGroup      Ident Abelian (Maybe (Value, Value))
    | VGroupTerm  [(Bool, ReifyFam Term)]

    | VNeutral   (ReifyFam Term)
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
bound :: Value -> (Value -> ReifyFam Term) -> ReifyFam Term
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
velimEmpty (VNeutral n) a =
    reflect a (In <$> (ElimEmpty <$> n <*> reifyType a))

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
      loop (VIDesc_Id i)       a = vf $$ i $$ a
      loop (VIDesc_K _)        a = a
      loop (VIDesc_Pair d1 d2) a = VPair (loop d1 (vfst a)) (loop d2 (vsnd a))
      loop (VIDesc_Sg c d)     a = VPair (vfst a) (loop (d $$ vfst a) (vsnd a))
      loop (VIDesc_Pi c d)     f = VLam "x" $ \v -> loop (d $$ v) (f $$ v)
      loop (VIDesc_Bind vI tmD i vA) (VMapI vB vg tmx) =
          VMapI vB (VLam i $ \vi -> VLam "b" $ \vb -> loop (vA vi) (vg $$ vi $$ vb)) tmx

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
      loop (VIDesc_K vB)       vx = VUnit Nothing
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

veliminate :: Value -- ^ The index type (@I : Set@)
           -> Value -- ^ The description (@D : I -> IDesc I@)
           -> Value -- ^ The index (@i : I@)
           -> Value -- ^ The target (@xs : MuI I D i@)
           -> Ident -> Ident -> (Value -> Value -> Value) -- ^ The predicate (@i : I, x : MuI I D i |- P type@)
           -> Ident -> Ident -> Ident -> (Value -> Value -> Value -> Value) -- ^ The body
           -> Value
veliminate vI vD vi vt i1 x1 vP i2 x2 p2 vK = loop vi vt
    where
      loop vi (VConstruct _ x) =
          vK vi x
             -- FIXME: vallI should be a built-in, because it needs to
             -- define stuff with type arguments
             (vallI $$ vI $$ (vD $$ vi) $$ vmuI vI vD
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
                                     reify (vP vi (VConstruct Nothing vx)) (vK vi vx vp))))))
      loop vi x = error $ "internal: eliminate/loop got : " ++ show x

{------------------------------------------------------------------------------}
vgroup :: Ident -> Abelian -> Maybe Value -> Value
vgroup nm ab Nothing   = VGroup nm ab Nothing
vgroup nm ab (Just ty) = VLam "x" $ \x -> VGroup nm ab (Just (ty, x))

vgroupUnit :: Value
vgroupUnit = VGroupTerm []

vgroupMul :: Value -> Value -> Value
vgroupMul (VGroupTerm tms1) (VGroupTerm tms2) = VGroupTerm (tms1 ++ tms2)
vgroupMul _                 _    = error "internal: type error discovered in vgroupMul"

vgroupInv :: Value -> Value
vgroupInv (VGroupTerm tms) = VGroupTerm $ reverse $ map (\(inverted,tm) -> (not inverted,tm)) tms
vgroupInv _                = error "internal: type error discovered in vgroupInv"

{------------------------------------------------------------------------------}
reflect :: Value -> ReifyFam Term -> Value
reflect (VPi nm tA tB)   tm = VLam (fromMaybe "x" nm) $ \d -> reflect (tB d) (tm `tmApp` reify tA d)
reflect (VSigma _ tA tB) tm = let v1 = reflect tA (tmFst tm)
                                  v2 = reflect (tB v1) (tmSnd tm)
                              in VPair v1 v2
reflect (VUnit _)        tm = VUnitI
reflect (VIDesc vA)      tm = VIDesc_Bind vA tm "i" VIDesc_Id
reflect (VSemI vI tmD i vA) tm = VMapI vA (VLam i $ \i -> VLam "x" $ \x -> x) tm
reflect (VGroup nm ab _) tm = VGroupTerm [(False, tm)]
reflect _                tm = VNeutral tm


{------------------------------------------------------------------------------}
reifyType :: Value -> ReifyFam Term
reifyType (VPi x v f)     = In <$> (Pi (Irrelevant x) <$> reifyType v <*> bound v (\v -> reifyType (f v)))
reifyType (VSigma x v f)  = In <$> (Sigma (Irrelevant x) <$> reifyType v <*> bound v (\v -> reifyType (f v)))
reifyType (VSum v1 v2)    = In <$> (Sum <$> reifyType v1 <*> reifyType v2)
reifyType (VSet l)        = In <$> pure (Set l)
reifyType (VUnit tag)     = In <$> pure (Unit (Irrelevant tag))
reifyType VEmpty          = In <$> pure Empty
reifyType (VEq vA vB va vb) = In <$> (Eq <$> reifyType vA <*> reifyType vB <*> reify vA va <*> reify vB vb)
reifyType (VMuI v1 v2 v3) = (In <$> (MuI <$> reifyType v1 <*> reify (v1 .->. VIDesc v1) v2)) `tmApp` reify v1 v3
reifyType (VIDesc s)      = pure (In IDesc) `tmApp` reifyType s
reifyType (VSemI vI tmD i vA) =
    In <$> (SemI <$> reifyType vI <*> tmD <*> pure (Irrelevant i) <*> bound vI (\v -> reifyType (vA v)))
reifyType (VGroup nm ab Nothing)         = In <$> pure (Group nm ab Nothing)
reifyType (VGroup nm ab (Just (t1, t2))) = (In <$> (Group nm ab <$> (Just <$> reifyType t1))) `tmApp` reify t1 t2
reifyType (VNeutral t)    = t
reifyType v               = error ("internal: reifyType given non-type: " ++ show v)

reifyType0 :: Value -> Term
reifyType0 v = runReifyFam (reifyType v) (ReificationOpts False, 0)

reifyTypeForDisplay :: Value -> Term
reifyTypeForDisplay v = runReifyFam (reifyType v) (ReificationOpts True, 0)

{------------------------------------------------------------------------------}
reify0 :: Value -> Value -> Term
reify0 vty v = runReifyFam (reify vty v) (ReificationOpts False, 0)

reifyForDisplay :: Value -> Value -> Term
reifyForDisplay vty v = runReifyFam (reify vty v) (ReificationOpts True, 0)

-- | `reify type value`
reify :: Value -> Value -> ReifyFam Term

reify (VSet _) a = reifyType a

reify (VPi _ tA tB)    (VLam nm f) = In <$> (Lam (Irrelevant nm) <$> bound tA (\v -> reify (tB v) (f v)))
reify (VPi _ tA tB)    _           = error "internal: reify: values of type Pi-blah should only be VLam"

reify (VSigma _ tA tB) e = let v1 = vfst e
                               v2 = vsnd e
                           in In <$> (Pair <$> reify tA v1 <*> reify (tB v1) v2)

reify (VSum tA tB)     (VInl v) = In <$> (Inl <$> reify tA v)
reify (VSum tA tB)     (VInr v) = In <$> (Inr <$> reify tB v)

reify (VUnit _)        VUnitI   = In <$> pure UnitI
reify (VUnit _)        _        = error "internal: reify: values of type unit should only be VUnitI"

reify (VMuI tI tD ti)  (VConstruct tag v)  = In <$> (Construct (Irrelevant tag) <$> reify (vsemI tI (tD $$ ti) "i" (vmuI tI tD $$)) v)
reify (VIDesc tI)      (VIDesc_Id x)       = In <$> (IDesc_Id <$> reify tI x)
reify (VIDesc tI)      (VIDesc_K a)        = In <$> (IDesc_K <$> reifyType a)
reify (VIDesc tI)      (VIDesc_Pair d1 d2) = In <$> (IDesc_Pair <$> reify (VIDesc tI) d1 <*> reify (VIDesc tI) d2)
reify (VIDesc tI)      (VIDesc_Sg a d)     = In <$> (IDesc_Sg <$> reifyType a <*> reify (a .->. VIDesc tI) d)
reify (VIDesc tI)      (VIDesc_Pi a d)     = In <$> (IDesc_Pi <$> reifyType a <*> reify (a .->. VIDesc tI) d)
reify (VIDesc tI)      (VIDesc_Bind vA tm x vf) = do
  opts    <- getReificationOpts
  tmf     <- withFullReification $ bound vA (\v -> reify (VIDesc tI) (vf v))
  tmf_iid <- withFullReification $ bound tI (\v -> reify (VIDesc tI) (VIDesc_Id v))
  tyA     <- withFullReification $ reifyType vA
  tyI     <- withFullReification $ reifyType tI
  -- FIXME: this will check equality using the 'display' terms
  if foldDefinitions opts && tyA == tyI && tmf == tmf_iid then
      tm
  else
     In <$> (IDesc_Bind <$> reifyType vA
                        <*> reifyType tI
                        <*> tm
                        <*> pure (Irrelevant x)
                        <*> bound vA (\v -> reify (VIDesc tI) (vf v)))
reify (VIDesc tI)      v                   = error $ "internal: reify: non-canonical value of VIDesc: " ++ show v
reify (VSemI vI tmD i vA) (VMapI vB vf tmX) = do
  opts   <- getReificationOpts
  tyA    <- withFullReification $ bound vI (\i -> reifyType (vA i))
  tyB    <- withFullReification $ bound vI (\i -> reifyType (vB i))
  tmf    <- withFullReification $ reify (forall "i" vI $ \vi -> vB vi .->. vA vi) vf
  tm_id  <- reify (forall "i" vI $ \vi -> vA vi .->. vA vi) (VLam i $ \i -> VLam "x" $ \x -> x)
  -- FIXME: split up the reification options to be finer-grained
  if foldDefinitions opts && tyA == tyB && tmf == tm_id then
      tmX
  else
    In <$> (MapI <$> reifyType vI <*> tmD
                 <*> pure (Irrelevant i) <*> bound vI (\i -> reifyType (vB i))
                 <*> pure (Irrelevant i) <*> bound vI (\i -> reifyType (vA i))
                 <*> reify (forall "i" vI $ \vi -> vB vi .->. vA vi) vf
                 <*> tmX)
reify (VSemI vI tmD i vA) v                = error $ "internal: reify: non-canonical value of VSemI: " ++ show v
reify (VEq tA _ ta _)  VRefl               = In <$> pure Refl
reify (VGroup nm ab _) (VGroupTerm tms)    = reifyGroupTerm tms ab
reify _                (VNeutral tm)       = tm
reify ty               v                   = error $ "internal: reify: attempt to reify: " ++ show v ++ " at type " ++ show ty

{-
-- FIXME: this is a clunky, fixed heuristic. should try to work out
-- from a definition's body which args are to be used as triggers.
isUnfoldTrigger :: Value -> Bool
isUnfoldTrigger (VDefnRef _ v _ _) = isUnfoldTrigger v
isUnfoldTrigger (VInl _)           = True
isUnfoldTrigger (VInr _)           = True
isUnfoldTrigger (VRefl)            = True
isUnfoldTrigger (VConstruct _ _)   = True
isUnfoldTrigger (VIDesc_K _)       = True
isUnfoldTrigger (VIDesc_Id _)      = True
isUnfoldTrigger (VIDesc_Pair _ _)  = True
isUnfoldTrigger (VIDesc_Sg _ _)    = True
isUnfoldTrigger (VIDesc_Pi _ _)    = True
isUnfoldTrigger _                  = False

reifyDefnRef :: Ident -> Value -> [Value] -> ReifyFam Term
reifyDefnRef identifier vty args =
    doArgs vty (reverse args) (tmFree identifier)
    where
      doArgs vty                []       tm = tm
      doArgs (VDefnRef _ v _ _) args     tm = doArgs v args tm
      doArgs (VPi _ vA vB)      (a:args) tm = doArgs (vB a) args (tm `tmApp` reify vA a)
-}

reifyGroupTerm :: [(Bool, ReifyFam Term)] -> Abelian -> ReifyFam Term
reifyGroupTerm l ab = ReifyFam $ \x ->
                      foldr smartMul (In GroupUnit) $ map doInverses $ normaliser $ map (toTerm x) l
    where
      toTerm x (inverted, tm) = (inverted, runReifyFam tm x)

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