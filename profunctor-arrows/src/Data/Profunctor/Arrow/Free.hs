{-# LANGUAGE GADTs #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ExistentialQuantification #-}
module Data.Profunctor.Arrow.Free where

import Control.Category hiding ((.), id)
import Data.Profunctor
import Data.Profunctor.Arrow
import Data.Profunctor.Traversing
import qualified Control.Category as C

import Prelude

-- | Free monoid in the category of profunctors.
--
-- See <https://arxiv.org/abs/1406.4823> section 6.2.
-- 
--
data Free p a b where
  Parr :: (a -> b) -> Free p a b
  Free :: p x b -> Free p a x -> Free p a b

instance Profunctor p => Profunctor (Free p) where
  dimap l r (Parr f) = Parr (dimap l r f)
  dimap l r (Free f g) = Free (rmap r f) (lmap l g)

instance Profunctor p => Category (Free p) where
  id = Parr id
  Parr g . f = rmap g f
  Free h g . f = Free h (g <<< f)

instance Strong p => Strong (Free p) where
  first' (Parr f) = Parr (first' f)
  first' (Free f g) = Free (first' f) (first' g)

instance Choice p => Choice (Free p) where
  left' (Parr f) = Parr (left' f)
  left' (Free f g) = Free (left' f) (left' g)

instance Closed p => Closed (Free p) where
  closed (Parr f) = Parr (closed f)
  closed (Free f g) = Free (closed f) (closed g)

instance Traversing p => Traversing (Free p) where
  traverse' (Parr f) = Parr (traverse' f)
  traverse' (Free f g) = Free (traverse' f) (traverse' g)

instance Mapping p => Mapping (Free p) where
  map' (Parr f) = Parr (map' f)
  map' (Free f g) = Free (map' f) (map' g)

-- | Given a natural transformation this returns a profunctor.
--
foldFree :: Category q => Profunctor q => p :-> q -> Free p a b -> q a b
foldFree _ (Parr ab) = arr ab
foldFree pq (Free p f) = pq p <<< foldFree pq f

-- | Lift a natural transformation from @f@ to @g@ into a natural transformation from @'Free' f@ to @'Free' g@.
hoistFree :: p :-> q -> Free p a b -> Free q a b
hoistFree _ (Parr ab)  = Parr ab
hoistFree pq (Free p f) = Free (pq p) (hoistFree pq f)

-- Analog of 'Const' for pliftows
newtype Append r a b = Append { getAppend :: r }

instance Profunctor (Append r) where
  dimap _ _ (Append x) = Append x

instance Monoid r => Category (Append r) where
  id = Append mempty
  Append x . Append y = Append (x <> y)
