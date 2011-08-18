{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing.Conversion.Evaluation
    ( evaluate
    , reifyType0
    , vlift
    )
    where

import Control.Applicative
import Data.Rec
import Language.Foveran.Syntax.Checked
import Language.Foveran.Typing.Conversion.Value


{------------------------------------------------------------------------------}
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

{------------------------------------------------------------------------------}
evaluate :: Term -> [Value] -> (Ident -> (Value, Maybe Value)) -> Value
evaluate t env defs = foldRec eval t (env,defs)

reifyType0 :: Value -> Term
reifyType0 v = reifyType v 0
