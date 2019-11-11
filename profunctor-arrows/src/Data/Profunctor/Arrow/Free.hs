{-# LANGUAGE GADTs #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ExistentialQuantification #-}
module Data.Profunctor.Arrow.Free where

import Control.Arrow (Arrow, Kleisli(..))
import Control.Category hiding ((.), id)
import Control.Comonad (Comonad, Cokleisli(..))
import Control.Monad hiding (join)
import Data.Profunctor
import Data.Profunctor.Extra

import qualified Control.Arrow as A
import qualified Control.Category as C

import Data.Profunctor.Arrow
import Data.Profunctor.Composition
import Data.Profunctor.Choice
import Data.Profunctor.Closed
import Data.Profunctor.Strong
import Data.Profunctor.Traversing
import Data.Profunctor.Mapping
import Data.Profunctor.Monad
import Data.Profunctor.Yoneda
--import Data.Profunctor.Free

import Prelude

import Data.Kind
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Monoid (Any(..))
import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S


{-
A free prearrow is one that gives us an instance of Category and Profunctor for any type with minimal effort from that type. 
A truly free prearrow would provide (.) and dimap. But we can actually separate those two and do them one at a time. 
If we separate (.) and dimap, we can start with the data source, give it a Profunctor instance on Free, and then give it a Category instance that preserves the Profunctor instance. 
This will be valuable because it means we can change the Profunctor instance and the data source in isolation from each other and from the Category instance.
-}

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
