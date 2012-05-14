{-# LANGUAGE OverloadedStrings, TypeOperators #-}

module Language.Foveran.Typing.Conversion.Evaluation
    ( evalIn
    , evalInWith )
    where

import Control.Applicative
import Data.Rec (foldRec, Rec (In))
import Data.Traversable (sequenceA)
import Language.Foveran.Syntax.Checked
import Language.Foveran.Typing.Hole
import Language.Foveran.Typing.DefinitionContext
import Language.Foveran.Typing.Conversion.Value

{------------------------------------------------------------------------------}
type Environment ctxt = ([Value], ctxt, Holes)

type Eval ctxt a = Environment ctxt -> a

lookupBound :: Int -> Eval ctxt Value
lookupBound k (env, _, _) = env !! k

lookupFree :: DefinitionContext ctxt =>
              Ident
           -> Eval ctxt Value
lookupFree nm (_, context, _) =
    case lookupDefinition nm context of
      Nothing             -> error "Evaluation: unbound identifier"
      Just (ty, Nothing)  -> reflect ty (tmFree nm)
      Just (ty, Just def) -> def

doHole :: DefinitionContext ctxt =>
          Ident
       -> Eval ctxt ([Value] -> Value)
doHole identifier (_, context, holes) arguments =
    case holeGoal of
      GoalIsType  -> VNeutral term
      GoalType ty -> reflect (evalInWith ty context holes arguments) term
    where
      hole = lookupHole identifier holes

      holeContext = getHoleContext hole
      holeGoal    = getHoleGoal hole

      term = In <$> (Hole identifier <$> reifyArguments arguments holeContext)

      reifyArguments []       []               i = []
      reifyArguments (v:args) ((ident,ty):tys) i = reify vty v i:reifyArguments args tys i
          where vty = evalInWith ty context holes args
      reifyArguments _        _                i = error "Incorrect number of arguments to hole"

binder :: Eval ctxt a -> Eval ctxt (Value -> a)
binder p = \(env,defs,holes) v -> p (v:env, defs, holes)


eval :: DefinitionContext ctxt =>
        TermCon (Eval ctxt Value)
     -> Eval ctxt Value
eval (Bound k)     = lookupBound k
eval (Free nm)     = lookupFree nm

eval (Set l)       = pure $ VSet l

eval (Pi nm t1 t2) = VPi (fromIrrelevant nm) <$> t1 <*> binder t2
eval (Lam nm t)    = VLam (fromIrrelevant nm) <$> binder t
eval (App t1 t2)   = ($$) <$> t1 <*> t2

eval (Sigma nm t1 t2) = VSigma (fromIrrelevant nm) <$> t1 <*> binder t2
eval (Pair t1 t2)     = VPair <$> t1 <*> t2
eval (Proj1 t)        = vfst <$> t
eval (Proj2 t)        = vsnd <$> t

eval (Sum t1 t2)             = VSum <$> t1 <*> t2
eval (Inl t)                 = VInl <$> t
eval (Inr t)                 = VInr <$> t
eval (Case t tA tB x tP y tL z tR) = vcase <$> t
                                     <*> tA
                                     <*> tB
                                     <*> pure (fromIrrelevant x) <*> binder tP
                                     <*> pure (fromIrrelevant y) <*> binder tL
                                     <*> pure (fromIrrelevant z) <*> binder tR

eval Unit      = pure VUnit
eval UnitI     = pure VUnitI
eval Empty     = pure VEmpty
eval (ElimEmpty x a) = velimEmpty <$> x <*> a

eval (Eq tA tB ta tb) = VEq <$> tA <*> tB <*> ta <*> tb
eval Refl             = pure VRefl
eval (ElimEq tA ta tb teq a e tP tp) =
    velimeq <$> tA <*> ta <*> tb <*> teq <*> pure (fromIrrelevant a) <*> pure (fromIrrelevant e) <*> binder (binder tP) <*> tp
                                   
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
eval (IDesc_Bind tA tB t1 x t2) =
    videsc_bind <$> tA <*> tB <*> t1 <*> pure (fromIrrelevant x) <*> binder t2
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
eval (SemI tI tD i tA)  = vsemI <$> tI <*> tD <*> pure (fromIrrelevant i) <*> binder tA
eval (MapI tI tD i1 tA i2 tB tf tx) =
    vmapI <$> tI <*> tD <*> pure (fromIrrelevant i1) <*> binder tA <*> pure (fromIrrelevant i2) <*> binder tB <*> tf <*> tx
eval (LiftI tI tD x tA i a tP tx) =
    vliftI <$> tI <*> tD <*> pure (fromIrrelevant x) <*> binder tA <*> pure (fromIrrelevant i) <*> pure (fromIrrelevant a) <*> binder (binder tP) <*> tx
eval InductionI         = pure (VLam "I" $ \vI ->
                                VLam "D" $ \vD ->
                                VLam "P" $ \vP ->
                                VLam "k" $ \vk ->
                                VLam "i" $ \vi ->
                                VLam "x" $ \vx ->
                                vinductionI vI vD vP vk vi vx)

eval (Group nm ab ty)   = vgroup nm ab <$> sequenceA ty
eval GroupUnit          = pure vgroupUnit
eval (GroupMul t1 t2)   = vgroupMul <$> t1 <*> t2
eval (GroupInv t)       = vgroupInv <$> t

eval (Hole nm tms)      = doHole nm <*> sequenceA tms

{------------------------------------------------------------------------------}
evalInWith :: DefinitionContext ctxt =>
              Term
           -> ctxt
           -> Holes
           -> [Value]
           -> Value
evalInWith term context holeContext environment =
    foldRec eval term (environment, context, holeContext)

evalIn :: DefinitionContext ctxt =>
          Term
       -> ctxt
       -> Holes
       -> Value
evalIn term context holeContext = evalInWith term context holeContext []
