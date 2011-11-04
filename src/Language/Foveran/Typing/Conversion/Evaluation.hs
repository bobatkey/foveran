{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing.Conversion.Evaluation
    ( evaluate
    )
    where

import Control.Applicative
import Data.Rec (foldRec)
import Language.Foveran.Syntax.Checked
import Language.Foveran.Typing.Conversion.Value

{------------------------------------------------------------------------------}
type Environment = ([Value], Ident -> (Value, Maybe Value))

type Eval a = Environment -> a

lookupBound :: Int -> Eval Value
lookupBound k (env, _) = env !! k

lookupFree :: Ident -> Eval Value
lookupFree nm (_, context) =
    case context nm of
      (ty, Nothing)  -> reflect ty (tmFree nm)
      (ty, Just def) -> def


binder :: Eval a -> Eval (Value -> a)
binder p = \(env,defs) v -> p (v:env, defs)


eval :: TermCon (Eval Value) -> Eval Value
eval (Bound k)     = lookupBound k
eval (Free nm)     = lookupFree nm

eval (Set l)       = pure $ VSet l

eval (Pi nm t1 t2) = VPi nm <$> t1 <*> binder t2
eval (Lam nm t)    = VLam nm <$> binder t
eval (App t1 t2)   = ($$) <$> t1 <*> t2

eval (Sigma nm t1 t2) = VSigma nm <$> t1 <*> binder t2
eval (Pair t1 t2)     = VPair <$> t1 <*> t2
eval (Proj1 t)        = vfst <$> t
eval (Proj2 t)        = vsnd <$> t

eval (Sum t1 t2)             = VSum <$> t1 <*> t2
eval (Inl t)                 = VInl <$> t
eval (Inr t)                 = VInr <$> t
eval (Case t tA tB x tP y tL z tR) = vcase <$> t
                                     <*> tA
                                     <*> tB
                                     <*> pure x <*> binder tP
                                     <*> pure y <*> binder tL
                                     <*> pure z <*> binder tR

eval Unit      = pure VUnit
eval UnitI     = pure VUnitI
eval Empty     = pure VEmpty
eval (ElimEmpty x a) = velimEmpty <$> x <*> a

eval (Eq tA tB ta tb) = VEq <$> tA <*> tB <*> ta <*> tb
eval Refl             = pure VRefl
eval (ElimEq tA ta tb teq a e tP tp) =
    velimeq <$> tA <*> ta <*> tb <*> teq <*> pure a <*> pure e <*> binder (binder tP) <*> tp
                                   
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
eval Sem                = pure (VLam "D" $ vsem)
eval (Mu t)             = VMu <$> t
eval (Construct t)      = VConstruct <$> t
eval Induction          = pure (VLam "F" $ \f ->
                                VLam "P" $ \p ->
                                VLam "k" $ \k ->
                                VLam "x" $ \x ->
                                vinduction f p k x)

eval IDesc              = pure (VLam "I" $ \i -> VIDesc i)
eval (IDesc_K t)        = VIDesc_K <$> t
eval (IDesc_Id t)       = VIDesc_Id <$> t
eval (IDesc_Pair t1 t2) = VIDesc_Pair <$> t1 <*> t2
eval (IDesc_Sg t1 t2)   = VIDesc_Sg <$> t1 <*> t2
eval (IDesc_Pi t1 t2)   = VIDesc_Pi <$> t1 <*> t2
eval IDesc_Elim         = pure (VLam "I" $ \i ->
                                VLam "P" $ \p ->
                                VLam "pId" $ \pId ->
                                VLam "pK"  $ \pK ->
                                VLam "pPair" $ \pPair ->
                                VLam "pSg" $ \pSg ->
                                VLam "pPi" $ \pPi ->
                                VLam "d" $ \d ->
                                videsc_elim i p pId pK pPair pSg pPi d)
eval (MuI t1 t2)        = vmuI <$> t1 <*> t2
eval InductionI         = pure (VLam "I" $ \vI ->
                                VLam "D" $ \vD ->
                                VLam "P" $ \vP ->
                                VLam "k" $ \vk ->
                                VLam "i" $ \vi ->
                                VLam "x" $ \vx ->
                                vinductionI vI vD vP vk vi vx)

{------------------------------------------------------------------------------}
evaluate :: Term -> [Value] -> (Ident -> (Value, Maybe Value)) -> Value
evaluate t env defs = foldRec eval t (env,defs)
