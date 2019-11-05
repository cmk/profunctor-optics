
module Data.Profunctor.Optic.Grate where

import Control.Monad.Reader
import Control.Monad.Cont
import Control.Monad.IO.Unlift
import Data.Distributive
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Rep (unfirstCorep)
import qualified Data.Functor.Rep as F
import qualified Control.Exception as Ex

---------------------------------------------------------------------
-- 'Grate'
---------------------------------------------------------------------

-- | Build a 'Grate' from a nested continuation.
--
-- \( \quad \mathsf{Grate}\;S\;A = \exists I, S \cong I \to A \)
--
-- The resulting optic is the corepresentable counterpart to 'Lens', and sits between 'Iso' and 'Setter'.
--
-- See <https://www.cs.ox.ac.uk/jeremy.gibbons/publications/proyo.pdf> section 4.6
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

instance Closed (GrateRep a b) where
  closed (GrateRep z) = GrateRep $ \f x -> z $ \k -> f $ \g -> k (g x)

instance Costrong (GrateRep a b) where
  unfirst = unfirstCorep

instance Cosieve (GrateRep a b) (PCont a b) where
  cosieve (GrateRep f) (PCont g) = f g

instance Corepresentable (GrateRep a b) where
  type Corep (GrateRep a b) = PCont a b

  cotabulate f = GrateRep $ f . PCont

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

-- | Zip over a 'Grate'. 
--
-- @\f -> zipWithOf closed (zipWithOf closed f) === zipWithOf (closed . closed)@
--
zipWithOf :: AGrate s t a b -> (a -> a -> b) -> s -> s -> t
zipWithOf x comb s1 s2 = withGrate x $ \grt -> grt $ \get -> comb (get s1) (get s2)

-- | Zip over a 'Grate'.
--
zip3WithOf :: AGrate s t a b -> (a -> a -> a -> b) -> (s -> s -> s -> t)
zip3WithOf x comb s1 s2 s3 = withGrate x $ \grt -> grt $ \get -> comb (get s1) (get s2) (get s3)

-- | Zip over a 'Grate'.
--
zip4WithOf :: AGrate s t a b -> (a -> a -> a -> a -> b) -> (s -> s -> s -> s -> t)
zip4WithOf x comb s1 s2 s3 s4 = withGrate x $ \grt -> grt $ \get -> comb (get s1) (get s2) (get s3) (get s4)

-- | Transform a profunctor grate into a Van Laarhoven grate.
--
-- This is a more restricted version of 'cotraverseOf'
--
zipFWithOf :: Functor f => AGrate s t a b -> (f a -> b) -> f s -> t
zipFWithOf x comb fs = withGrate x $ \grt -> grt $ \get -> comb (fmap get fs)

---------------------------------------------------------------------
-- Common grates
---------------------------------------------------------------------

-- | Access the contents of a distributive functor.
--
distributed :: Distributive f => Grate (f a) (f b) a b
distributed = grate $ \f -> cotraverse f id

-- | A 'Grate' accessing the contents of a representable functor.
--
represented :: F.Representable f => Grate (f a) (f b) a b
represented = dimap F.index F.tabulate . closed

-- | TODO: Document
--
applied :: Grate a (b -> c) (a , b) c
applied = lmap (,) . closed

-- | Provide an initial value to a 'Semigroup'.
--
pointed :: Semigroup a => a -> Grate' a a
pointed = parametrized (<>)

-- | Depend on a silent configuration parameter.
--
-- >>> zipWithOf (parametrized (+) 1) (*) 2 2 
-- 9 
--
parametrized :: (x -> a -> a) -> x -> Grate' a a
parametrized f x = dimap (flip f) ($ x) . closed

-- | TODO: Document
--
masked :: MonadUnliftIO m => Grate (m a) (m b) (m a) (m b)
masked = grate mask
 where
  mask f = withRunInIO $ \run -> Ex.mask $ \unmask -> run $ f $ liftIO . unmask . run

-- | TODO: Document
--
unlifted :: MonadUnliftIO m => Grate (m a) (m b) (IO a) (IO b)
unlifted = grate withRunInIO

-- | Access the range of a 'ReaderT'.
--
forwarded :: Distributive m => Grate (ReaderT r m a) (ReaderT r m b) a b
forwarded = distributed

-- | TODO: Document
--
continued :: Grate a (Cont r a) r r
continued = grate cont

-- | Translate between different 'Star's.
--
starred :: Grate (Star f a b) (Star g s t) (a -> f b) (s -> g t)
starred = grate $ \o -> Star $ o runStar

-- | Translate between different 'Costar's.
--
costarred :: Grate (Costar f a b) (Costar g s t) (f a -> b) (g s -> t)
costarred = grate $ \o -> Costar $ o runCostar
