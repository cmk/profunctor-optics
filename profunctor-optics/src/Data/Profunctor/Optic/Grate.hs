
module Data.Profunctor.Optic.Grate (
    module Data.Profunctor.Optic.Grate
  , module Export
  , Costar (..)
) where


import Data.Distributive
import Data.Profunctor.Sieve
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Prelude hiding (Representable(..))

import Data.Profunctor.Closed as Export

import Control.Monad.Trans.Cont

import qualified Control.Exception as Ex
import Data.Functor.Rep

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
-}

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

-- | 'resetting' promotes a \"semantic editor combinator\" to a form of grate that can only lift unary functions.
--
-- /Caution/: In order for the generated family to be well-defined, you must ensure that the two functors laws hold:
--
-- * @sec id === id@
--
-- * @sec f . sec g === sec (f . g)@
--
--resetting :: ((a -> b) -> s -> t) -> Grate s t a b

resetting :: Applicative f => Representable f => Rep f -> ((a -> b) -> s -> t) -> UnderLike f s t a b
resetting i sec = between Costar runCostar $ \f -> sec (f . pure) . flip index i

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

instance Closed (GrateRep a b) where
  closed (GrateRep z) = GrateRep $ \f x -> z $ \k -> f $ \g -> k (g x)

reviewGrate :: GrateRep a b s t -> b -> t
reviewGrate (GrateRep e) b = e (const b)

---------------------------------------------------------------------
-- Primitive Operators
---------------------------------------------------------------------

withGrate :: AGrate s t a b -> ((((s -> a) -> b) -> t) -> r) -> r
withGrate x k = case x (GrateRep $ \f -> f id) of GrateRep sabt -> k sabt

-- @ cotraverseOf distributed == cotraverse @
cotraverseOf :: UnderLike f s t a b -> (f a -> b) -> (f s -> t)
cotraverseOf = between runCostar Costar

unfoldMapOf :: UnfoldLike r t b -> (r -> b) -> r -> t
unfoldMapOf = between (dcostar Const) (ucostar getConst) 

zipWithOf :: GrateRep a b s t -> (a -> a -> b) -> (s -> s -> t)
zipWithOf (GrateRep e) op s1 s2 = e (\get -> get s1 `op` get s2)

zipFWithOf :: Functor f => GrateRep a b s t -> (f a -> b) -> (f s -> t)
zipFWithOf (GrateRep e) comb fs = e (\get -> comb (fmap get fs))

-- special case of cotraverse where f = (a,a)
--zipWithOf :: Optic Zipped s t a b -> (a -> a -> b) -> s -> s -> t
--zipWithOf = between runZipped Zipped

---------------------------------------------------------------------
-- Common grates
---------------------------------------------------------------------

-- | Every 'Iso' is an 'Grate'.
--
adapted :: (s -> a) -> (b -> t) -> Grate s t a b
adapted sa bt = grate $ \sab -> bt (sab sa)

-- | A grate accessing the range of a function.
--
-- @
-- range == dimap tabulate index . closed
-- @
--
range :: Grate (r -> a) (r -> b) a b
range = distributed

-- ^ @
-- yoneda :: Representable f => Grate (f a) (f b) a b
-- @
--
yoneda :: Representable f => Grate (f a) (f b) a b
yoneda = dimap index tabulate . closed

distributed :: Distributive f => Grate (f a) (f b) a b
distributed = grate $ \f -> cotraverse f id

masked :: Grate (IO a) (IO b) (IO a) (IO b)
masked = grate Ex.mask

shifted :: Grate a (Cont r a) r (Cont r r)
shifted = grate shift 

continued :: Grate a (Cont r a) r r
continued = grate cont

continuedWith :: Cont r a -> Grate b (Cont r b) r (a -> r)
continuedWith c = grate (flip withCont c) 

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
