module Data.Profunctor.Optic.Lens (
    module Data.Profunctor.Optic.Lens
  , module Export
) where

import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Task (Store(..))
import Data.Void (Void, absurd)
import Data.Profunctor.Strong as Export

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

-- | Build a lens from a getter and setter.
--
-- /Caution/: In order for the generated lens family to be well-defined,
-- you must ensure that the three lens laws hold:
--
-- * @sa (sbt s a) === a@
--
-- * @sbt s (sa s) === s@
--
-- * @sbt (sbt s a1) a2 === sbt s a2@
--
lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens sa sbt = dimap (id &&& sa) (uncurry sbt) . second'

colens :: (s -> a) -> (s -> b -> t) -> Colens b a t s 
colens sa sbt = unsecond . dimap (uncurry sbt) (id &&& sa)
 
-- | Transform a Van Laarhoven-encoded lens into a profunctor-encoded one.
--
-- Use this to interoperate with optics from the 'lens' library.
lensVL :: VL.Lens s t a b -> Lens s t a b
lensVL o = dimap ((values &&& info) . o (Store id)) (uncurry id) . second'

cloneLens :: ALens s t a b -> Lens s t a b
cloneLens l = withLens l $ \x y p -> lens x y p

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

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- Analogous to (***) from 'Control.Arrow'
pairing' :: Lens s t a b -> Lens s' t' a' b' -> Lens (s, s') (t, t') (a, a') (b, b')
pairing' = paired

lens2
  :: (s -> a)
  -> (s -> b -> t) 
  -> Lens (c, s) (d, t) (c, a) (d, b)
lens2 f g = between runPaired Paired (lens f g)

withLens :: ALens s t a b -> ((s -> a) -> (s -> b -> t) -> r) -> r
withLens l f = case l (LensRep id $ \_ b -> b) of LensRep x y -> f x y


---------------------------------------------------------------------
-- Common lenses 
---------------------------------------------------------------------

_1 :: Lens (a , c) (b , c) a b
_1 = first'

_2 :: Lens (c , a) (c , b) a b
_2 = second'

lower1 :: Iso s t (a , x) (b , x) -> Lens s t a b
lower1 = (. _1)

lower2 :: Iso s t (x , a) (x , b) -> Lens s t a b
lower2 = (. _2)

-- | There is a `Unit` in everything.
unit :: forall a. Lens' a ()
unit = lens (const ()) const

-- | There is everything in a `Void`.
void :: forall a. Lens' Void a
void = lens absurd const

uncurried :: Lens (a , b) c a (b -> c)
uncurried = rmap eval . first'

ix :: Eq k => k -> Lens' (k -> v) v
ix k = lens ($ k) (\g v' x -> if (k == x) then v' else g x)

at :: Ord k => k -> Lens' (MapL.Map k v) (Maybe v)
at k = lens (MapL.lookup k) (flip $ maybe (MapL.delete k) (MapL.insert k))

at' :: Ord k => k -> Lens' (MapS.Map k v) (Maybe v)
at' k = lens (MapS.lookup k) (flip $ maybe (MapS.delete k) (MapS.insert k))

contains :: Ord k => k -> Lens' (Set.Set k) Bool
contains k = lens (Set.member k) (flip $ \nv -> if nv then Set.insert k else Set.delete k)

intAt :: Int -> Lens' (IntMapL.IntMap v) (Maybe v)
intAt k = lens (IntMapL.lookup k) (flip $ maybe (IntMapL.delete k) (IntMapL.insert k))

intAt' :: Int -> Lens' (IntMapS.IntMap v) (Maybe v)
intAt' k = lens (IntMapS.lookup k) (flip $ maybe (IntMapS.delete k) (IntMapS.insert k))

intContains :: Int -> Lens' IntSet.IntSet Bool
intContains k = lens (IntSet.member k) (flip $ \nv -> if nv then IntSet.insert k else IntSet.delete k)
