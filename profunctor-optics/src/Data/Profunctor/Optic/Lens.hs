module Data.Profunctor.Optic.Lens where

import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Task (Store(..))
import Data.Void (Void, absurd)

import qualified Data.Map.Lazy as MapL
import qualified Data.Map.Strict as MapS
import qualified Data.Set as Set
import qualified Data.IntMap.Lazy as IntMapL
import qualified Data.IntMap.Strict as IntMapS
import qualified Data.IntSet as IntSet
import qualified Data.Profunctor.Optic.Type.VL as VL

---------------------------------------------------------------------
-- 'Lens' 
---------------------------------------------------------------------

-- | Build a 'Strong' optic from a getter and setter.
--
-- \( \quad \mathsf{Lens}\;S\;A = \exists C, S \cong C \times A \)
--
-- /Caution/: In order for the generated lens family to be well-defined,
-- you must ensure that the three lens laws hold:
--
-- * @sa (sbt s a) ≡ a@
--
-- * @sbt s (sa s) ≡ s@
--
-- * @sbt (sbt s a1) a2 ≡ sbt s a2@
--
-- See 'Data.Profunctor.Optic.Property'.
--
lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens sa sbt = dimap (id &&& sa) (uncurry sbt) . psecond

-- | Build a 'Costrong' optic from a getter and setter. 
--
-- * @relens f g ≡ \f g -> re (lens f g)@
--
-- * @review $ relens f g ≡ f@
--
-- * @set . re $ re (lens f g) ≡ g@
--
-- A 'Relens' is a 'Review', so you can specialise types to obtain:
--
-- @ 'review' :: 'Relens'' s a -> a -> s @
--
relens :: (b -> t) -> (b -> s -> a) -> Relens s t a b
relens sa sbt = unsecond . dimap (uncurry sbt) (id &&& sa)

-- | Transform a Van Laarhoven lens into a profunctor lens.
--
lensVL :: (forall f. Functor f => (a -> f b) -> s -> f t) -> Lens s t a b
lensVL  o = dimap ((values &&& info) . o (Store id)) (uncurry id) . psecond

-- | Build a 'Lens' from its free tensor representation.
--
matched :: (s -> (x , a)) -> ((x , b) -> t) -> Lens s t a b
matched f g = dimap f g . psecond

-- | TODO: Document
--
cloneLens :: ALens s t a b -> Lens s t a b
cloneLens o = withLens o lens 

---------------------------------------------------------------------
-- 'LensRep'
---------------------------------------------------------------------

-- | The `LensRep` profunctor precisely characterizes a 'Lens'.
data LensRep a b s t = LensRep (s -> a) (s -> b -> t)

type ALens s t a b = Optic (LensRep a b) s t a b

type ALens' s a = ALens s s a a

instance Profunctor (LensRep a b) where

  dimap f g (LensRep sa sbt) = LensRep (sa . f) (\s -> g . sbt (f s))

instance Strong (LensRep a b) where

  first' (LensRep sa sbt) =
    LensRep (\(a, _) -> sa a) (\(s, c) b -> ((sbt s b), c))

  second' (LensRep sa sbt) =
    LensRep (\(_, a) -> sa a) (\(c, s) b -> (c, (sbt s b)))

--FreeStrong (IsoRep a b) s t = IsoRep a b s (s -> t) = (s -> a, b -> s -> t)
--FreeChoice (IsoRep a b) s t = IsoRep a b ? ? = (s -> (Either a t), b -> t).

newtype FreeStrong p s t = FreeStrong (p s (s -> t))

instance Profunctor p => Profunctor (FreeStrong p) where
  dimap l r (FreeStrong p) = FreeStrong (dimap l (dimap l r) p)

instance Profunctor p => Strong (FreeStrong p) where
  first' (FreeStrong p) = FreeStrong (dimap fst first p)

mapFreeStrong :: (Profunctor p, Profunctor q) => (p :-> q) -> (FreeStrong p :-> FreeStrong q)
mapFreeStrong eta (FreeStrong p) = FreeStrong (eta p)

lowerFS :: Strong p => FreeStrong p a b -> p a b
lowerFS (FreeStrong p) = peval p

unitFS :: Profunctor p => p :-> FreeStrong p
unitFS p = FreeStrong (rmap const p)

-- 'counit' preserves strength.
-- <https://r6research.livejournal.com/27858.html>
counitFS :: Strong p => FreeStrong p :-> p
counitFS (FreeStrong p) = dimap dup apply (pfirst p)

toFreeStrong :: Profunctor p => Pastro p a b -> FreeStrong p a b
toFreeStrong (Pastro l m r) = FreeStrong (dimap (fst . r) (\y a -> l (y, (snd (r a)))) m)

toPastro :: FreeStrong p a b -> Pastro p a b
toPastro (FreeStrong p) = Pastro apply p dup

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Analogous to @(***)@ from 'Control.Arrow'
--
pairing :: Lens s1 t1 a1 b1 -> Lens s2 t2 a2 b2 -> Lens (s1 , s2) (t1 , t2) (a1 , a2) (b1 , b2)
pairing = paired

-- | TODO: Document
--
lens2 :: (s -> a) -> (s -> b -> t) -> Lens (c, s) (d, t) (c, a) (d, b)
lens2 f g = between runPaired Paired (lens f g)

-- | TODO: Document
--
withLens :: ALens s t a b -> ((s -> a) -> (s -> b -> t) -> r) -> r
withLens l f = case l (LensRep id $ \_ b -> b) of LensRep x y -> f x y

---------------------------------------------------------------------
-- Common lenses 
---------------------------------------------------------------------

-- | TODO: Document
--
_1 :: Lens (a , c) (b , c) a b
_1 = pfirst

-- | TODO: Document
--
_2 :: Lens (c , a) (c , b) a b
_2 = psecond

-- | TODO: Document
--
lower1 :: Iso s t (a , x) (b , x) -> Lens s t a b
lower1 = (. _1)

-- | TODO: Document
--
lower2 :: Iso s t (x , a) (x , b) -> Lens s t a b
lower2 = (. _2)

-- | There is a `Unit` in everything.
--
unit :: Lens' a ()
unit = lens (const ()) const

-- | There is everything in a `Void`.
--
void :: Lens' Void a
void = lens absurd const

-- | TODO: Document
--
uncurried :: Lens (a , b) c a (b -> c)
uncurried = rmap apply . pfirst

-- | TODO: Document
--
ix :: Eq k => k -> Lens' (k -> v) v
ix k = lens ($ k) (\g v' x -> if (k == x) then v' else g x)

-- | TODO: Document
--
at :: Ord k => k -> Lens' (MapL.Map k v) (Maybe v)
at k = lens (MapL.lookup k) (flip $ maybe (MapL.delete k) (MapL.insert k))

-- | TODO: Document
--
at' :: Ord k => k -> Lens' (MapS.Map k v) (Maybe v)
at' k = lens (MapS.lookup k) (flip $ maybe (MapS.delete k) (MapS.insert k))

-- | TODO: Document
--
contains :: Ord k => k -> Lens' (Set.Set k) Bool
contains k = lens (Set.member k) (flip $ \nv -> if nv then Set.insert k else Set.delete k)

-- | TODO: Document
--
intAt :: Int -> Lens' (IntMapL.IntMap v) (Maybe v)
intAt k = lens (IntMapL.lookup k) (flip $ maybe (IntMapL.delete k) (IntMapL.insert k))

-- | TODO: Document
--
intAt' :: Int -> Lens' (IntMapS.IntMap v) (Maybe v)
intAt' k = lens (IntMapS.lookup k) (flip $ maybe (IntMapS.delete k) (IntMapS.insert k))

-- | TODO: Document
--
intContains :: Int -> Lens' IntSet.IntSet Bool
intContains k = lens (IntSet.member k) (flip $ \nv -> if nv then IntSet.insert k else IntSet.delete k)
