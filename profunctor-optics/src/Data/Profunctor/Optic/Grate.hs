
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

-- ^ @
-- yoneda :: Representable f => Grate (f a) (f b) a b
-- @
--
--
--
yoneda :: Representable f => Grate (f a) (f b) a b
yoneda = dimap index tabulate . closed

-- ^ @
-- cod :: Grate (r -> a) (r -> b) a b
-- @
--
-- A grate accessing the codomain of a function.
--
cod :: Grate (r -> a) (r -> b) a b
cod = dimap tabulate index . closed

cod' :: Grate (r -> a) (r -> b) a b
cod' = distributed

distributed :: Distributive f => Grate (f a) (f b) a b
distributed = grate $ \f -> cotraverse f id

distributed' :: Distributive f => Under (f a) (f b) a b 
distributed' = cowander cotraverse




{-

-- Pipes.Lift
type Proxy m r = m r
liftCatchError = undefined :: Monad m => ((e -> m (Proxy m r)) -> m (Proxy m r) -> m (Proxy m r)) -> (e -> Proxy m r) -> Proxy m r -> Proxy m r

-- ResourceT
resourceMask :: MonadResource m => ((forall a. ResourceT IO a -> ResourceT IO a) -> ResourceT IO b) -> m b


unlifting :: MonadUnliftIO m => Grate (m a) (m b) (IO a) (IO b)
unlifting = grate withRunInIO

asyncWithUnmasking :: MonadUnliftIO m => Grate (m a) (m (Async b)) (m a) (m b)
asyncWithUnmasking = grate asyncWithUnmask

-}

--lowered :: (Monoid s, Semiring s) => Grate s t s t
--lowered = grate $ \f -> f (one <>)

equaling :: Eq a => a -> Grate a b Bool b
equaling x = dimap (==) ($ x) . closed

-- Depend on an unknown configuration parameter x.
reading :: (x -> a -> a) -> x -> Grate' a a
reading f x = dimap (flip f) ($ x) . closed

emptied :: Semigroup a => a -> Grate' a a 
emptied = reading (<>)

masking :: Grate (IO a) (IO b) (IO a) (IO b)
masking = grate Ex.mask

shifted :: Grate a (Cont r a) r (Cont r r)
shifted = grate shift 

continued :: Grate a (Cont r a) r r
continued = grate cont

continuedWith :: Cont r a -> Grate b (Cont r b) r (a -> r)
continuedWith c = grate (flip withCont c) 

-- | Translate between different 'Star's.
starred :: Grate (Star f1 d1 c1) (Star f2 d2 c2) (d1 -> f1 c1) (d2 -> f2 c2)
starred = grate $ \o -> Star $ o runStar

-- | Translate between different 'Costar's.
costarred :: Grate (Costar f d c) (Costar f1 d1 c1) (f d -> c) (f1 d1 -> c1)
costarred = grate $ \o -> Costar $ o runCostar

-- | Translate between different 'Forget's.
forgotten :: Grate (Forget r1 a1 b1) (Forget r2 a2 b2) (a1 -> r1) (a2 -> r2)
forgotten = grate $ \o -> Forget $ o runForget

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- Grate s t a b -> Setter s t a b
-- Every 'Grate' is an 'Setter'.
overGrate :: (((s -> a) -> b) -> t) -> (a -> b) -> s -> t
overGrate sabt ab s = sabt $ \sa -> ab (sa s)

fromIso :: Iso s t a b -> Grate s t a b
fromIso x = withIso x $ \sa bt -> grate (env sa bt)

-- Iso s t a b -> Grate s t a b
-- Every 'Iso' is an 'Grate'.
env :: (s -> a) -> (b -> t) -> ((s -> a) -> b) -> t
env sa bt sab = bt (sab sa)

-- special case of cotraverse where f = (a,a)
zipWithOf :: Optic Zipped s t a b -> (a -> a -> b) -> s -> s -> t
zipWithOf = between runZipped Zipped

-- cotraverseOf == between runCostar Costar 
cotraverseOf :: Optic (Costar f) s t a b -> (f a -> b) -> (f s -> t)
cotraverseOf o f = tf where Costar tf = o (Costar f)

cotraversing :: Functor f => Distributive t => (f a -> b) -> f (t a) -> t b
cotraversing = cotraverseOf distributed

---------------------------------------------------------------------
-- 
---------------------------------------------------------------------

-- | The 'GrateRep' profunctor precisely characterizes 'Grate'.

newtype GrateRep a b s t = GrateRep { unGrateRep :: ((s -> a) -> b) -> t }

data GrateRep' a b s t = forall c. GrateRep' (s -> (c -> a))  ((c -> b) -> t)


instance Profunctor (GrateRep a b) where
  dimap f g (GrateRep z) = GrateRep $ \d -> g (z $ \k -> d (k . f))

instance Closed (GrateRep a b) where
  -- closed :: p a b -> p (x -> a) (x -> b)
  closed (GrateRep z) = GrateRep $ \f x -> z $ \k -> f $ \g -> k (g x)

--type AGrate s t a b = Optic (GrateRep a b) s t a b

withGrate :: Optic (GrateRep a b) s t a b -> ((s -> a) -> b) -> t
withGrate o = h where GrateRep h = o (GrateRep $ \f -> f id)

cloneGrate :: Optic (GrateRep a b) s t a b -> Grate s t a b
cloneGrate = grate . withGrate

reviewGrate :: GrateRep a b s t -> b -> t
reviewGrate (GrateRep e) b = e (const b)

zipFWithOf :: Functor f => GrateRep a b s t -> (f a -> b) -> (f s -> t)
zipFWithOf (GrateRep e) comb fs = e (\get -> comb (fmap get fs))

zipWithOf' :: GrateRep a b s t -> (a -> a -> b) -> (s -> s -> t)
zipWithOf' (GrateRep e) op s1 s2 = e (\get -> get s1 `op` get s2)


type EGrate s t a b = forall c. (s -> (c -> a), (c -> b) -> t)

withGrate' :: EGrate s t a b -> ((s -> a) -> b) -> t
withGrate' (f, g) sab = g $ sab . flip f


zipWithNaperian :: ((c, c) -> c2) -> ((b -> c), (b -> c)) -> b -> c2 
zipWithNaperian op (f, g) = op . (f &&& g)

zipWithOf'' :: EGrate s t a b -> ((a, a) -> b) -> (s, s) -> t
zipWithOf'' (f, g) op = g . zipWithNaperian op . (f *** f)

{-
zipWithNaperian :: (c -> c -> c2) -> (b -> c) -> (b -> c) -> b -> c2 
zipWithNaperian op f g = uncurry op . (f &&& g)

zipWithGrate :: GrateRep' a b s t -> (a -> a -> b) -> (s, s) -> t
zipWithGrate (GrateRep' f g) op = g . uncurry (zipWithNaperian op) . (f *** f)
-}
--unzipFWithOf :: (forall f. Functor f => (f a -> b) -> f s -> t) -> Grate s t a b
--unzipFWithOf :: (((s -> a) -> b) -> (s -> s) -> t) -> Grate s t a b 
--unzipFWithOf f = flip f id


