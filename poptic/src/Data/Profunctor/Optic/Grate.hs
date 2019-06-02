
module Data.Profunctor.Optic.Grate (
    module Data.Profunctor.Optic.Grate
  , module Export
  , Costar (..)
) where

import Data.Distributive
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Operator
import Data.Profunctor.Optic.Prelude

import Data.Profunctor.Closed as Export

import Control.Monad.IO.Unlift
import UnliftIO.Exception

{- 
'Closed' lets you lift a profunctor through any representable functor (aka Naperian container). 
In the special case where the indexing type is finitary (e.g. 'Bool') then the tabulated type is isomorphic to a fixed length vector (e.g. '(,)').
The identity container is representable, and representable functors are closed under composition.

See https://www.cs.ox.ac.uk/jeremy.gibbons/publications/proyo.pdf section 4.6

The resulting 'Grate' optic sits between 'Iso' and 'Over'. This is witnessed by  

Profunctor Grate: Grate s t a b ~ Closed p => p a b -> p s t
Van Laarhoven Grate: forall f. Functor f => (f a -> b) -> (f s -> t)
Normal Grate: ((s -> a) -> b) -> t

Laws:
given a van Laarhoven Grate, 

grate :: Functor F => (F a -> b) -> (F s -> t) we expect the following to hold:

grate runIdentity = runIdentity

-- curry' :: Closed p => p (a, b) c -> p a (b -> c)
grate (g . fmap f . getCompose) = grate g . fmap (grate f) . getCompose
-}


grate :: (((s -> a) -> b) -> t) -> Grate s t a b
grate f pab = dimap (flip ($)) f (closed pab)

unlifting :: MonadUnliftIO m => Grate (m a) (m b) (IO a) (IO b)
unlifting = grate withRunInIO

masking :: MonadUnliftIO m => Grate (m a) (m b) (m a) (m b)
masking = grate mask

---------------------------------------------------------------------
-- 
---------------------------------------------------------------------

-- | The 'GrateRep' profunctor precisely characterizes 'Grate'.

newtype GrateRep a b s t = GrateRep { unGrateRep :: ((s -> a) -> b) -> t }

instance Profunctor (GrateRep a b) where
  dimap f g (GrateRep z) = GrateRep $ \d -> g (z $ \k -> d (k . f))

instance Closed (GrateRep a b) where
  -- closed :: p a b -> p (x -> a) (x -> b)
  closed (GrateRep z) = GrateRep $ \f x -> z $ \k -> f $ \g -> k (g x)

type AGrate s t a b = Optic (GrateRep a b) s t a b

withGrate :: AGrate s t a b -> ((s -> a) -> b) -> t
withGrate g = h where GrateRep h = (g (GrateRep $ \f -> f id))

cloneGrate :: AGrate s t a b -> Grate s t a b
cloneGrate = grate . withGrate

--TODO port to Grate s t a b
reviewGrate :: GrateRep a b s t -> b -> t
reviewGrate (GrateRep e) b = e (const b)

zipFWithOf :: Functor f => GrateRep a b s t -> (f a -> b) -> (f s -> t)
zipFWithOf (GrateRep e) comb fs = e (\get -> comb (fmap get fs))

zipWithOf' :: GrateRep a b s t -> (a -> a -> b) -> (s -> s -> t)
zipWithOf' (GrateRep e) op s1 s2 = e (\get -> get s1 `op` get s2)

--unzipFWithOf :: (forall f. Functor f => (f a -> b) -> f s -> t) -> Grate s t a b
--unzipFWithOf :: (((s -> a) -> b) -> (s -> s) -> t) -> Grate s t a b 
--unzipFWithOf f = flip f id

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- Grate s t a b -> Over s t a b
-- Every 'Grate' is an 'Over'.
overGrate :: (((s -> a) -> b) -> t) -> (a -> b) -> s -> t
overGrate sabt ab s = sabt $ \sa -> ab (sa s)

-- Iso s t a b -> Grate s t a b
-- Every 'Iso' is an 'Grate'.
envMod :: (s -> a) -> (b -> t) -> ((s -> a) -> b) -> t
envMod sa bt sab = bt (sab sa)

cotraversed :: Distributive f => Grate (f a) (f b) a b
cotraversed = grate $ \f -> cotraverse f id

cotraversing :: (Distributive t, Functor f) => (f a -> b) -> f (t a) -> t b
cotraversing = cotraverseOf cotraversed
