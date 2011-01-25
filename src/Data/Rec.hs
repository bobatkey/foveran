{-# LANGUAGE RankNTypes #-}

module Data.Rec
    ( Rec (..)
    , AnnotRec (..)
    , translate
    , translateStar
    , translateRec
    , foldRec
    , foldAnnot
    )
    where

import Data.Functor
import Data.FreeMonad
import Text.Position

data Rec f = In (f (Rec f))

foldRec :: Functor f => (f a -> a) -> Rec f -> a
foldRec f (In x) = f (foldRec f <$> x)

-- class Eq2 f where
--   (===) :: Eq a => f a -> f a -> Bool

-- instance Eq2 f => Eq (Rec f) where
--   In x == In y = x === y

translateRec :: (Functor m, Functor f) =>
                ({- forall x. -} f (m (Rec g)) -> m (g (Rec g))) -> 
                Rec f ->
                m (Rec g)
translateRec f (In x) = In <$> f (translateRec f <$> x)

data AnnotRec a f = Annot a (f (AnnotRec a f))

instance Regioned a => Regioned (AnnotRec a f) where
    regionLeft (Annot a _) = regionLeft a
    regionRight (Annot a _) = regionRight a

foldAnnot :: Functor f => (f x -> x) -> AnnotRec a f -> x
foldAnnot f (Annot _ x) = f (foldAnnot f <$> x)

dropAnnot :: Functor f => AnnotRec a f -> Rec f
dropAnnot (Annot _ x) = In (fmap dropAnnot x)

translate :: (Functor m, Functor f) =>
             (forall x. f (m x) -> m (g x)) -> 
             AnnotRec a f ->
             m (AnnotRec a g)
translate f (Annot a x) = Annot a <$> f (translate f <$> x)

translateStar :: (Functor m, Functor f, Functor g) =>
                 (forall x. f (m x) -> m (FM g x)) -> 
                 AnnotRec a f ->
                 m (AnnotRec a g)
translateStar f (Annot a x) = annotate <$> f (translateStar f <$> x)
    where annotate (Var x)   = x
          annotate (Layer x) = Annot a (annotate <$> x)
