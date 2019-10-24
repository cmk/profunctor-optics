
module Data.Profunctor.Optic.Grate (
    module Data.Profunctor.Optic.Grate
  , module Export
  , Costar (..)
) where


import Data.Distributive
import Data.Profunctor.Closed as Export

import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Prelude hiding (Representable(..))
import Data.Profunctor.Rep as Export (Corepresentable(..))

import Control.Monad.Trans.Reader
import Control.Monad.Trans.Cont

import qualified Control.Exception as Ex
import qualified Data.Functor.Rep as F


---------------------------------------------------------------------
-- 'Grate'
---------------------------------------------------------------------

{-
'Closed' lets you lift a profunctor through any representable functor (aka Naperian container).
In the special case where the indexing type is finitary (e.g. 'Bool') then the tabulated type is isomorphic to a fixed length vector (e.g. '(,)').
The identity container is representable, and representable functors are closed lower composition.

See https://www.cs.ox.ac.uk/jeremy.gibbons/publications/proyo.pdf section 4.6

The resulting 'Grate' optic sits between 'Iso' and 'Setter'. This is witnessed by

Profunctor Grate: Grate s t a b ~ Closed p => p a b -> p s t
Van Laarhoven Grate: forall f. Functor f => (f a -> b) -> (f s -> t)
Normal Grate: ((s -> a) -> b) -> t

∀ F:Functor. (F a -> b) -> (F s -> t)
 ≅ [ flip ]
∀ F:Functor. F s -> (F a -> b) -> t
 ≅ [ yoneda ]
∀ F:Functor. (∀ c. (s -> c) -> F c) -> (F a -> b) -> t
 = [ definition of natural transformation ]
∀ F:Functor. (((->) s) :~> F) -> (F a -> b) -> t
 ≅ [ higher-order yoneda]
((->) s a -> b) -> t
 =
((s -> a) -> b) -> t
 =
Grate s t a b


Laws:
given a van Laarhoven Grate,

unzipping :: Functor f => (f a -> b) -> (f s -> t) we expect the following to hold:

unzipping runIdentity = runIdentity

-- curry' :: Closed p => p (a, b) c -> p a (b -> c)
unzipping (g . fmap f . getCompose) = unzipping g . fmap (grate f) . getCompose

-}

-- | Build a grate from an unzipping function.
--
--unzipping :: (forall f. Functor f => (f a -> b) -> f s -> t) -> Grate s t a b
--unzipping = under

-- | Build a grate from a nested continuation.
--
-- \( \quad \mathsf{Grate}\;S\;A = \exists I, S \cong I \to A \)
--
-- /Caution/: In order for the 'Grate' to be well-defined, you must ensure that the two grate laws hold:
--
-- * @grate ($ s) ≡ s@
--
-- * @grate (\k -> h (k . sabt)) ≡ sabt (\k -> h ($ k))@
--
-- See 'Data.Profunctor.Optic.Property'.
--
grate :: (((s -> a) -> b) -> t) -> Grate s t a b
grate sabt = dimap (flip ($)) sabt . closed

-- ^ @
-- ungrate :: Grate s t a b -> ((s -> a) -> b) -> t
-- @
--
-- Demote a grate to its normal, higher-order function, form.
--
-- @
-- ungrate . grate ≡ id
-- grate . ungrate ≡ id
-- @
--
ungrate :: Grate s t a b -> ((s -> a) -> b) -> t
ungrate g = withGrate g id

-- | Transform a Van Laarhoven-encoded grate into a profunctor-encoded one.
--
gratevl :: (forall g. Functor g => (g a -> b) -> g s -> t) -> Grate s t a b
gratevl g = undefined --flip g id

-- | Construct a 'Grate' from a pair of inverses.
--
inverting :: (s -> a) -> (b -> t) -> Grate s t a b
inverting sa bt = grate $ \sab -> bt (sab sa)

-- | TODO: Document
--
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

newtype PCont a b s = PCont { runPCont :: (s -> a) -> b }

runPCont' :: PCont a i a -> i
runPCont' (PCont h) = h id

instance Functor (PCont a b) where
  fmap st (PCont sab) = PCont $ \ta -> sab (ta . st)

instance Cosieve (GrateRep a b) (PCont a b) where
  cosieve (GrateRep f) = \c -> f (runPCont c)

instance Corepresentable (GrateRep a b) where
  type Corep (GrateRep a b) = PCont a b

  cotabulate f = GrateRep $ f . PCont

instance Closed (GrateRep a b) where
  closed (GrateRep z) = GrateRep $ \f x -> z $ \k -> f $ \g -> k (g x)

-- | TODO: Document
--
reviewGrate :: GrateRep a b s t -> b -> t
reviewGrate (GrateRep e) b = e (const b)

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | TODO: Document, replace with GrateLike
--
withGrate :: AGrate s t a b -> ((((s -> a) -> b) -> t) -> r) -> r
withGrate x k = case x (GrateRep $ \f -> f id) of GrateRep sabt -> k sabt

-- | Set all fields to the given value.
--
constOf :: AGrate s t a b -> b -> t
constOf x b = withGrate x $ \grt -> grt (const b)

-- | Transform a profunctor grate into a Van Laarhoven grate.
--
zipFWithOf :: Functor f => AGrate s t a b -> (f a -> b) -> (f s -> t)
zipFWithOf x comb fs = withGrate x $ \grt -> grt $ \get -> comb (fmap get fs)

-- | TODO: Document
--
-- @\f -> zipWithOf closed (zipWithOf closed f) === zipWithOf (closed . closed)@
--
zipWithOf :: AGrate s t a b -> (a -> a -> b) -> s -> s -> t
zipWithOf x comb s1 s2 = withGrate x $ \grt -> grt $ \get -> comb (get s1) (get s2)

-- | TODO: Document
--
zip3WithOf :: AGrate s t a b -> (a -> a -> a -> b) -> (s -> s -> s -> t)
zip3WithOf x comb s1 s2 s3 = withGrate x $ \grt -> grt $ \get -> comb (get s1) (get s2) (get s3)

-- | TODO: Document
--
zip4WithOf :: AGrate s t a b -> (a -> a -> a -> a -> b) -> (s -> s -> s -> s -> t)
zip4WithOf x comb s1 s2 s3 s4 = withGrate x $ \grt -> grt $ \get -> comb (get s1) (get s2) (get s3) (get s4)

---------------------------------------------------------------------
-- Common grates
---------------------------------------------------------------------

-- | A 'Grate' accessing the contents of a distributive functor.
--
distributed :: Distributive f => Grate (f a) (f b) a b
distributed = grate $ \f -> cotraverse f id

-- | A 'Grate' accessing the contents of a representable functor.
--
represented :: F.Representable f => Grate (f a) (f b) a b
represented = dimap F.index F.tabulate . closed

-- | Access the range of a 'ReaderT'.
--
ranged :: Distributive m => Grate (ReaderT r m a) (ReaderT r m b) a b
ranged = distributed

-- | TODO: Document
--
curried :: Grate a (b -> c) (a , b) c
curried = lmap (,) . closed

-- | TODO: Document
--
masked :: Grate (IO a) (IO b) (IO a) (IO b)
masked = grate Ex.mask

-- | TODO: Document
--
continued :: Grate a (Cont r a) r r
continued = grate cont

-- | TODO: Document
--
continuedWith :: Cont r a -> Grate b (Cont r b) r (a -> r)
continuedWith c = grate (`withCont` c)

-- | Depend on a silent configuration parameter.
configured :: (x -> a -> a) -> x -> Grate' a a
configured f x = dimap (flip f) ($ x) . closed

-- | Provide an initial value to a 'Semigroup'.
pointed :: Semigroup a => a -> Grate' a a
pointed = configured (<>)

-- | Translate between different 'Star's.
starred :: Grate (Star f a b) (Star g s t) (a -> f b) (s -> g t)
starred = grate $ \o -> Star $ o runStar

-- | Translate between different 'Costar's.
costarred :: Grate (Costar f a b) (Costar g s t) (f a -> b) (g s -> t)
costarred = grate $ \o -> Costar $ o runCostar
