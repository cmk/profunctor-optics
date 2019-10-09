
module Data.Profunctor.Optic.Grate (
    module Data.Profunctor.Optic.Grate
  , module Export
  , Costar (..)
) where


import Data.Distributive
import Data.Profunctor.Closed (Closed)
import qualified Data.Profunctor.Closed as C

import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Prelude hiding (Representable(..))
import Data.Profunctor.Rep as Export (Corepresentable(..))

import Control.Monad.Trans.Cont

import qualified Control.Exception as Ex
import Data.Functor.Rep (Representable(..))

---------------------------------------------------------------------
-- 'Grate'
---------------------------------------------------------------------

{- 
'Closed' lets you lift a profunctor through any representable functor (aka Naperian container). 
In the special case where the indexing type is finitary (e.g. 'Bool') then the tabulated type is isomorphic to a fixed length vector (e.g. '(,)').
The identity container is representable, and representable functors are closed under composition.

See https://www.cs.ox.ac.uk/jeremy.gibbons/publications/proyo.pdf section 4.6

The resulting 'Grate' optic sits between 'Iso' and 'Setter'. This is witnessed by  

Profunctor Grate: Grate s t a b ~ Closed p => p a b -> p s t
Van Laarhoven Grate: forall f. Functor f => (f a -> b) -> (f s -> t)
Normal Grate: ((s -> a) -> b) -> t

Laws:
given a van Laarhoven Grate, 

grate :: Functor f => (f a -> b) -> (f s -> t) we expect the following to hold:

grate runIdentity = runIdentity

-- curry' :: Closed p => p (a, b) c -> p a (b -> c)
grate (g . fmap f . getCompose) = grate g . fmap (grate f) . getCompose

unzipping :: (((s -> a) -> b) -> (s -> s) -> t) -> Grate s t a b
unzipping f = grate $ flip f id

-}


unzipping :: (forall f. Functor f => (f a -> b) -> f s -> t) -> Grate s t a b
unzipping = under

-- ^ @
-- grate :: (((s -> a) -> b) -> t) -> Grate s t a b
-- @
--
-- Build a grate from a nested continuation.
--
-- /Caution/: In order for the 'Grate' to be well-defined, you must ensure that the two grate laws hold:
--
-- * @grate ($ s) === s@
--
-- * @grate (\k -> h (k . sabt)) === sabt (\k -> h ($ k))@
--
-- Note: The 'grate' laws are that of an algebra for a parameterised continuation monad.
--
grate :: (((s -> a) -> b) -> t) -> Grate s t a b
grate sabt = dimap (flip ($)) sabt . closed

cloneGrate :: AGrate s t a b -> Grate s t a b
cloneGrate k = withGrate k grate

---------------------------------------------------------------------
-- 'GrateRep'
---------------------------------------------------------------------

-- | The 'GrateRep' profunctor precisely characterizes 'Grate'.
--
newtype GrateRep a b s t = GrateRep { unGrateRep :: ((s -> a) -> b) -> t }

type AGrate s t a b = Optic (GrateRep a b) s t a b

type AGrate' s a = AGrate s s a a

instance Profunctor (GrateRep a b) where
  dimap f g (GrateRep z) = GrateRep $ \d -> g (z $ \k -> d (k . f))

instance Costrong (GrateRep a b) where
  unfirst = unfirstCorep

newtype PolyCont a b s = PolyCont { runPolyCont :: (s -> a) -> b }

instance Functor (PolyCont a b) where
  fmap st (PolyCont sab) = PolyCont $ \ta -> sab (ta . st)

instance Cosieve (GrateRep a b) (PolyCont a b) where
  cosieve (GrateRep f) = \c -> f (runPolyCont c)

instance Corepresentable (GrateRep a b) where
  type Corep (GrateRep a b) = PolyCont a b

  cotabulate f = GrateRep $ f . PolyCont

instance Closed (GrateRep a b) where
  closed (GrateRep z) = GrateRep $ \f x -> z $ \k -> f $ \g -> k (g x)

reviewGrate :: GrateRep a b s t -> b -> t
reviewGrate (GrateRep e) b = e (const b)

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

withGrate :: AGrate s t a b -> ((((s -> a) -> b) -> t) -> r) -> r
withGrate x k = case x (GrateRep $ \f -> f id) of GrateRep sabt -> k sabt

reviewOf :: Grate s t a b -> b -> t
reviewOf x b = withGrate x $ \grt -> grt (const b)

zipWithOf :: Grate s t a b -> (a -> a -> b) -> s -> s -> t
zipWithOf x comb s1 s2 = withGrate x $ \grt -> grt $ \get -> comb (get s1) (get s2)

zipFWithOf :: Functor f => Grate s t a b -> (f a -> b) -> (f s -> t)
zipFWithOf x comb fs = withGrate x $ \grt -> grt $ \get -> comb (fmap get fs)

zip3WithOf :: Grate s t a b -> (a -> a -> a -> b) -> (s -> s -> s -> t)
zip3WithOf x comb s1 s2 s3 = withGrate x $ \grt -> grt $ \get -> comb (get s1) (get s2) (get s3)

---------------------------------------------------------------------
-- Common grates
---------------------------------------------------------------------

-- | Every 'Iso' is an 'Grate'.
--
adapted :: (s -> a) -> (b -> t) -> Grate s t a b
adapted sa bt = grate $ \sab -> bt (sab sa)

-- | An 'Under' accessing the range of a function.
--
range :: Grate (c -> a) (c -> b) a b
range = closed

-- ^ @
-- represented :: Representable f => Grate (f a) (f b) a b
-- @
--
represented :: Representable f => Grate (f a) (f b) a b
represented = dimap index tabulate . closed

distributed :: Distributive f => Grate (f a) (f b) a b
distributed = grate $ \f -> cotraverse f id

curried :: Grate a (b -> c) (a, b) c
curried = lmap (,) . closed

masked :: Grate (IO a) (IO b) (IO a) (IO b)
masked = grate Ex.mask

continued :: Grate a (Cont r a) r r
continued = grate cont

continuedWith :: Cont r a -> Grate b (Cont r b) r (a -> r)
continuedWith c = grate (`withCont` c) 

-- | Depend on a silent configuration parameter.
configured :: (x -> a -> a) -> x -> Grate' a a
configured f x = dimap (flip f) ($ x) . closed

-- | Provide an initial value to a 'Semigroup'.
pointed :: Semigroup a => a -> Grate' a a 
pointed = configured (<>)

equaled :: Eq a => a -> Grate a b Bool b
equaled x = dimap (==) ($ x) . closed

-- | Translate between different 'Star's.
starred :: Grate (Star f a b) (Star g s t) (a -> f b) (s -> g t)
starred = grate $ \o -> Star $ o runStar

-- | Translate between different 'Costar's.
costarred :: Grate (Costar f a b) (Costar g s t) (f a -> b) (g s -> t)
costarred = grate $ \o -> Costar $ o runCostar

-- | Translate between different 'Forget's.
forgotten :: Grate (Forget m a b) (Forget n s t) (a -> m) (s -> n)
forgotten = grate $ \o -> Forget $ o runForget
