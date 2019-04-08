module Data.Profunctor.Optic.Lens (
    module Data.Profunctor.Optic.Lens
  , module Export
) where

import Control.Arrow ((&&&))

import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Operators
import Data.Void (Void, absurd)

import Data.Profunctor.Strong as Export

{- Hedgehog predicates
viewUpdate :: Eq s => LensP s s a a -> s -> Bool
viewUpdate (LensP v u) s = u ((v s), s) == s

updateView :: Eq a => LensP s s a a -> a -> s -> Bool
updateView (LensP v u) a s = v (u (a, s)) == a

updateUpdate :: Eq s => LensP s s a a -> a -> a -> s -> Bool
updateUpdate (LensP v u) a1 a2 s = u (a2, (u (a1, s))) == u (a2, s)

-}

lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens sa sbt = dimap (sa &&& id) (uncurry . flip $ sbt) . first'

-- Analogous to (***) from 'Control.Arrow'
(***) :: Lens s t a b -> Lens s' t' a' b' -> Lens (s, s') (t, t') (a, a') (b, b')
(***) = paired

lensOf
  :: (s -> a)
  -> (s -> b -> t) 
  -> Lens (c, s) (d, t) (c, a) (d, b)
lensOf f g = through Paired runPaired (lens f g)

cloneLens :: ALens s t a b -> Lens s t a b
cloneLens l = withLens l $ \x y p -> lens x y p

withLens :: ALens s t a b -> ((s -> a) -> (s -> b -> t) -> r) -> r
withLens l f = case l (LensP id $ \_ b -> b) of LensP x y -> f x y

---------------------------------------------------------------------
-- Common lenses 
---------------------------------------------------------------------

-- | There is a `Unit` in everything.
united :: forall a. Lens' a ()
united = lens (const ()) const

-- | There is everything in `Void`.
devoid :: forall a. Lens' Void a
devoid = lens absurd const

_1 :: Lens (a,c) (b,c) a b
_1 = first'

_2 :: Lens (c,a) (c,b) a b
_2 = second'
