{-# LANGUAGE OverloadedStrings, TypeOperators #-}

module Language.Foveran.Typing.Conversion.Evaluation
    ( DefinitionContext (..)
    , lookupType
    , evalIn
    , evalInWith )
    where

import Control.Applicative
import Data.Rec (foldRec, Rec (In))
import Language.Foveran.Syntax.Checked
import Language.Foveran.Typing.Conversion.Value

{------------------------------------------------------------------------------}
class DefinitionContext ctxt where
    lookupDefinition :: Ident -> ctxt -> Maybe (Value, Maybe Value)

lookupType :: DefinitionContext ctxt => Ident -> ctxt -> Maybe Value
lookupType identifier ctxt = fst <$> lookupDefinition identifier ctxt

{------------------------------------------------------------------------------}
type Environment ctxt holeContext = ([Value], ctxt, holeContext)

type Eval ctxt holeContext a = Environment ctxt holeContext -> a

lookupBound :: Int -> Eval ctxt holeContext Value
lookupBound k (env, _, _) = env !! k

lookupFree :: DefinitionContext ctxt =>
              Ident
           -> Eval ctxt holeContext Value
lookupFree nm (_, context, _) =
    case lookupDefinition nm context of
      Nothing             -> error "Evaluation: unbound identifier"
      Just (ty, Nothing)  -> reflect ty (tmFree nm)
      Just (ty, Just def) -> def

lookupHole :: DefinitionContext holeContext =>
              Ident
           -> Eval ctxt holeContext Value
lookupHole identifier (_, _, holeContext) =
    case lookupDefinition identifier holeContext of
      Nothing             -> error "Evaluation: unbound hole"
      Just (ty, Nothing)  -> reflect ty (\_ -> In $ Hole identifier)
      Just (ty, Just def) -> def

binder :: Eval ctxt holeContext a -> Eval ctxt holeContext (Value -> a)
binder p = \(env,defs,holes) v -> p (v:env, defs, holes)


eval :: (DefinitionContext ctxt, DefinitionContext holeContext) =>
        TermCon (Eval ctxt holeContext Value)
     -> Eval ctxt holeContext Value
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

eval (Hole nm)          = lookupHole nm

{------------------------------------------------------------------------------}
evalInWith :: (DefinitionContext ctxt, DefinitionContext holeContext) =>
              Term
           -> ctxt
           -> holeContext
           -> [Value]
           -> Value
evalInWith term context holeContext environment =
    foldRec eval term (environment, context, holeContext)

evalIn :: (DefinitionContext ctxt, DefinitionContext holeContext) =>
          Term
       -> ctxt
       -> holeContext
       -> Value
evalIn term context holeContext = evalInWith term context holeContext []
