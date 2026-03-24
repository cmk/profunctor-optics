{-# LANGUAGE DerivingVia              #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
-- | Sort and Cosort carriers, generic representable sort functions,
-- lens-based sort operators, and merge combinators.
module Data.Profunctor.Optic.Sort (
    -- * Sort
    Sort(..)
  , runSort
    -- * Sort combinators
  , (%.)
  , bindSort
  , catSort
  , sortC
  , remapSort
  , eitherSort
  , maybeSort
  , zipsSorting

    -- * Cosort
  , Cosort(..)

    -- * Sort carriers (Ord, Map)
  , mkSort
  , mkSortN

    -- * Generic representable sort
  , sortingRep
  , sortUniqueRep
  , sortTaggedRep
  , groupTaggedRep

    -- * Lens-based operators (List)
  , sorts
  , sortsDesc
  , groups
  , nubs

    -- * Container construction (List)
  , toMapOf
  , countsOf

    -- * Post-sort foldMapOf (List)
  , foldSorts
  , foldSorts1
  , mconcatSorts

    -- * Sort as String sort
  , sortingString

    -- * Merge (Sort + containers merge)
  , merges
  , innerMerges
  , outerMerges
  , leftMerges
  , rightMerges

    -- * Sort merge tactics
  , sortedMatched
  , sortedMissing
) where

import Data.Ord (Down(..))
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Types (Lens')
import Prelude ((+), (-))

import qualified Control.Category as C
import qualified Data.Bifunctor as B
import qualified Data.Map.Strict as Map
import qualified Data.Map.Merge.Strict as Merge

-- | Local view helper to avoid circular import with View.hs.
viewOf :: Lens' s a -> s -> a
viewOf o s = getConst $ runStar (o (Star Const)) s
{-# INLINE viewOf #-}

---------------------------------------------------------------------
-- Sort
---------------------------------------------------------------------

-- | An indexed continuation profunctor for discrimination.
--
-- @Sort i k a b = (i -> (k, a)) -> b@
--
-- The indexed generalization of @Fmt@ from @stringfmt@:
-- @Fmt m a b = Sort m () a b@
--
-- @Sort@ is @Costar (Compose ((->) i) ((,) k))@. Most instances
-- derive via this representation. @Choice@ is hand-rolled (needs
-- @Coapplicative@ on the @Corep@ functor, requiring @Monoid i@).
--
-- @
--                Profunctor  Closed  Costrong  Cochoice  Choice    Cosieve  Corepresentable  Category
-- Sort i k          ✓          ✓       ✓         ✓      ✓(Mon i)    ✓           ✓          ✓(Mon i)
-- @
--
newtype Sort i k a b = Sort { unSort :: (i -> (k, a)) -> b }
  deriving (Functor, Applicative, Monad)
    via Costar (Compose ((->) i) ((,) k)) a
  deriving (Profunctor, Closed, Costrong, Cochoice)
    via Costar (Compose ((->) i) ((,) k))

-- | @Choice@ via @Coapplicative@ on @Compose ((->) i) ((,) k)@.
-- Samples at @mempty@ to decide the @Either@ branch.
instance Monoid i => Choice (Sort i k) where
  left' (Sort f) = Sort $ \inp ->
    case coapply (Compose inp) of
      Left  (Compose ika) -> Left  (f ika)
      Right (Compose ikb) -> Right (copure (Compose ikb))

instance Cosieve (Sort i k) (Compose ((->) i) ((,) k)) where
  cosieve (Sort f) = f . getCompose
  {-# INLINE cosieve #-}

instance Corepresentable (Sort i k) where
  type Corep (Sort i k) = Compose ((->) i) ((,) k)
  cotabulate f = Sort (f . Compose)
  {-# INLINE cotabulate #-}

-- | @Category@ with @(.)@ = pipeline composition (no constraint
-- on @k@) and @id@ = extract value at @mempty@ (needs @Monoid i@).
instance Monoid i => Category (Sort i k) where
  id = Sort $ \inp -> snd (inp mempty)
  Sort f . Sort g = Sort $ \inp -> f (\i -> (fst (inp i), g inp))
  {-# INLINE id #-}
  {-# INLINE (.) #-}

-- | Run a 'Sort' carrier on an input function.
{-# INLINE runSort #-}
runSort :: Sort i k a b -> (i -> (k, a)) -> b
runSort = unSort

---------------------------------------------------------------------
-- Sort combinators
---------------------------------------------------------------------

-- | Pipeline two 'Sort' passes.
--
-- @f %. g@ runs @g@ on the full input to produce a single @b@,
-- then @f@ sees that @b@ at every position, paired with the
-- original keys (unchanged).
infixr 9 %.
{-# INLINE (%.) #-}
(%.) :: Sort i k b c -> Sort i k a b -> Sort i k a c
Sort f %. Sort g = Sort $ \inp ->
  f (\i -> (fst (inp i), g inp))

-- | Indexed bind: inspect the key at each position and choose
-- a continuation.
{-# INLINE bindSort #-}
bindSort :: Sort i k a b -> (k -> Sort i k a' a) -> Sort i k a' b
bindSort (Sort m) f = Sort $ \inp ->
  m (\i -> let (k, _) = inp i in (k, unSort (f k) inp))

-- | Fold multiple 'Sort' passes.
{-# INLINE catSort #-}
catSort :: (Monoid i, Foldable f) => f (Sort i k a a) -> Sort i k a a
catSort = foldr (%.) C.id

-- | Constant: embed a key-value pair.
{-# INLINE sortC #-}
sortC :: (k, a) -> Sort i k a (k, a)
sortC ka = Sort $ const ka

-- | Remap keys.
{-# INLINE remapSort #-}
remapSort :: (k1 -> k2) -> Sort i k2 a b -> Sort i k1 a b
remapSort f (Sort g) = Sort $ \inp -> g (B.first f . inp)

-- | Sort an 'Either': apply left sort to 'Left's, right sort to 'Right's.
-- Samples at 'mempty' to decide the branch.
{-# INLINE eitherSort #-}
eitherSort :: Monoid i => Sort i k a c -> Sort i k b c -> Sort i k (a + b) c
eitherSort (Sort l) (Sort r) = Sort $ \inp ->
  case snd (inp mempty) of
    Left a0  -> l (\i -> B.second (either id (const a0)) (inp i))
    Right b0 -> r (\i -> B.second (either (const b0) id) (inp i))

-- | Sort a 'Maybe': apply sort to 'Just's, use default for 'Nothing's.
{-# INLINE maybeSort #-}
maybeSort :: Monoid i => c -> Sort i k a c -> Sort i k (Maybe a) c
maybeSort def (Sort f) = Sort $ \inp ->
  case snd (inp mempty) of
    Nothing -> def
    Just a0 -> f (\i -> B.second (maybe a0 id) (inp i))

-- | Merge two 'Sort' results pointwise.
{-# INLINE zipsSorting #-}
zipsSorting :: (b -> b -> b) -> Sort i k a b -> Sort i k a b -> Sort i k a b
zipsSorting f (Sort h1) (Sort h2) = Sort $ \inp -> f (h1 inp) (h2 inp)

---------------------------------------------------------------------
-- Cosort
---------------------------------------------------------------------

-- | The Star\/Costar adjoint of 'Sort'.
--
-- Where @Sort i k a b = (i -> (k, a)) -> b@ consumes a keyed stream
-- (Costar-based), @Cosort i k a b = a -> k -> (i, b)@ constructs
-- keyed results (Star-based).
--
-- @Sort@ and @Cosort@ are related by the adjunction
-- @Compose ((->) i) ((,) k) ⊣ Compose ((->) k) ((,) i)@, i.e.
-- the currying adjunction composed with itself.
--
-- See "Data.Profunctor.Optic.Dual" for the general Star\/Costar
-- duality, and 'Data.Profunctor.Optic.Iso.adjuncted' for the
-- concrete witness.
newtype Cosort i k a b = Cosort { runCosort :: a -> k -> (i, b) }
  deriving (Functor)
    via Star (Compose ((->) k) ((,) i)) a
  deriving (Profunctor, Strong)
    via Star (Compose ((->) k) ((,) i))

instance Sieve (Cosort i k) (Compose ((->) k) ((,) i)) where
  sieve (Cosort f) a = Compose (f a)
  {-# INLINE sieve #-}

instance Representable (Cosort i k) where
  type Rep (Cosort i k) = Compose ((->) k) ((,) i)
  tabulate f = Cosort $ \a -> getCompose (f a)
  {-# INLINE tabulate #-}

instance Monoid i => Choice (Cosort i k) where
  left' (Cosort f) = Cosort $ \ea k -> case ea of
    Left  a -> B.second Left  (f a k)
    Right b -> (mempty, Right b)
  {-# INLINE left' #-}

---------------------------------------------------------------------
-- Sort carriers (Ord, Map)
---------------------------------------------------------------------

-- | Identity carrier for finite index types.
-- Groups by key, producing a 'Map' of toListOf.
mkSort :: (Bounded i, Enum i, Ord k) => Sort i k a (Map.Map k [a])
mkSort = Sort $ \inp ->
  Map.fromListWith (flip (++)) [ ki `seq` a `seq` (ki, [a])
                                | i <- [minBound..maxBound]
                                , let (ki, a) = inp i ]
{-# INLINEABLE mkSort #-}

-- | Identity carrier for Int-indexed containers of known size.
--
-- /Benchmark: 0.90–0.99x vs direct Map.fromListWith (zero-cost). See "Data.Profunctor.Optic.Bench"./
--
mkSortN :: Ord k => Int -> Sort Int k a (Map.Map k [a])
mkSortN n = Sort $ \inp ->
  Map.fromListWith (flip (++)) [ ki `seq` a `seq` (ki, [a])
                                | i <- [0..n-1]
                                , let (ki, a) = inp i ]
{-# INLINEABLE mkSortN #-}

---------------------------------------------------------------------
-- Generic representable sort
---------------------------------------------------------------------

-- | Sort any @Int@-indexed representable container by key.
sortingRep :: Ord k
           => (c -> Int) -> (c -> Int -> a) -> ([a] -> c')
           -> (a -> k) -> c -> Map.Map k c'
sortingRep len idx build key c =
  let n = len c
      result = runSort (mkSortN n) (\i -> (key (idx c i), idx c i))
  in  fmap build result
{-# INLINE sortingRep #-}

-- | Sort + deduplicate: keep first element per key.
sortUniqueRep :: Ord k
              => (c -> Int) -> (c -> Int -> a) -> (a -> c')
              -> (a -> k) -> c -> Map.Map k c'
sortUniqueRep len idx build key c =
  fmap (build . head) $ sortingRep len idx id key c
{-# INLINE sortUniqueRep #-}

-- | Tagged sort: sort keys + permute values in tandem.
sortTaggedRep :: Ord k
              => (ck -> Int) -> (ck -> Int -> k) -> (cv -> Int -> v)
              -> ([k] -> ck') -> ([v] -> cv')
              -> ck -> cv -> Map.Map k (ck', cv')
sortTaggedRep klen kidx vidx kbuild vbuild ks vs =
  let n = klen ks
      result = runSort (mkSortN n) (\i -> (kidx ks i, (kidx ks i, vidx vs i)))
  in  fmap (\pairs -> (kbuild (map fst pairs), vbuild (map snd pairs))) result
{-# INLINE sortTaggedRep #-}

-- | Group by key, returning Map from keys to value containers.
groupTaggedRep :: Ord k
               => (ck -> Int) -> (ck -> Int -> k) -> (cv -> Int -> v)
               -> ([v] -> cv') -> ck -> cv -> Map.Map k cv'
groupTaggedRep klen kidx vidx vbuild ks vs =
  let n = klen ks
      result = runSort (mkSortN n) (\i -> (kidx ks i, vidx vs i))
  in  fmap vbuild result
{-# INLINE groupTaggedRep #-}

---------------------------------------------------------------------
-- Lens-based operators (List)
---------------------------------------------------------------------

-- | Sort a list through a lens. Returns @[]@ on empty input.
sorts :: Ord a => Lens' s a -> [s] -> [[s]]
sorts _ [] = []
sorts o xs = Map.elems $ Map.fromListWith (flip (++))
  [(viewOf o s, [s]) | s <- xs]

-- | Sort a list in descending order through a lens.
sortsDesc :: Ord a => Lens' s a -> [s] -> [[s]]
sortsDesc _ [] = []
sortsDesc o xs = Map.elems $ Map.fromListWith (flip (++))
  [(Down (viewOf o s), [s]) | s <- xs]

-- | Group a list through a lens.
groups :: Ord a => Lens' s a -> [s] -> [[s]]
groups = sorts

-- | Deduplicate a list through a lens, keeping first per group.
nubs :: Ord a => Lens' s a -> [s] -> [s]
nubs _ [] = []
nubs o xs = map head $ sorts o xs

---------------------------------------------------------------------
-- Container construction (List)
---------------------------------------------------------------------

-- | Build a 'Map.Map' keyed by lens focus from a list.
toMapOf :: Ord a => Lens' s a -> [s] -> Map.Map a [s]
toMapOf _ [] = Map.empty
toMapOf o xs = Map.fromListWith (flip (++)) [(viewOf o s, [s]) | s <- xs]

-- | Count occurrences per key from a list.
countsOf :: Ord a => Lens' s a -> [s] -> Map.Map a Int
countsOf _ [] = Map.empty
countsOf o xs = Map.fromListWith (+) [(viewOf o s, 1 :: Int) | s <- xs]

---------------------------------------------------------------------
-- Post-sort foldMapOf (List)
---------------------------------------------------------------------

-- | Sort through a lens, then right-fold each group.
foldSorts :: Ord a => Lens' s a -> (s -> r -> r) -> r -> [s] -> [r]
foldSorts o g z xs = map (foldr g z) (sorts o xs)

-- | Sort through a lens, then reduce each non-empty group.
foldSorts1 :: Ord a => Lens' s a -> (s -> s -> s) -> [s] -> [s]
foldSorts1 o f xs = map (foldr1 f) (sorts o xs)

-- | Sort through a lens, then monoidal concat per group.
mconcatSorts :: (Ord a, Monoid m) => Lens' s a -> (s -> m) -> [s] -> [m]
mconcatSorts o g xs = map (foldMap g) (sorts o xs)

---------------------------------------------------------------------
-- String sort
---------------------------------------------------------------------

-- | Sort a 'String' by a key on each character.
sortingString :: Ord k => (Char -> k) -> String -> Map.Map k String
sortingString = sortingRep length (\s i -> s !! i) id

---------------------------------------------------------------------
-- Merge (Sort + containers merge)
---------------------------------------------------------------------

-- | Merge two toListOf through lenses using containers merge tactics.
merges :: Ord a
           => Lens' s a -> Lens' t a
           -> Merge.SimpleWhenMissing a [s] c
           -> Merge.SimpleWhenMissing a [t] c
           -> Merge.SimpleWhenMatched a [s] [t] c
           -> [s] -> [t] -> Map.Map a c
merges lo ro wml wmr wm xs ys =
  Merge.merge wml wmr wm (toMapOf lo xs) (toMapOf ro ys)

-- | Inner merge: only keys present in both inputs.
innerMerges :: Ord a
            => Lens' s a -> Lens' t a
            -> (a -> [s] -> [t] -> c)
            -> [s] -> [t] -> Map.Map a c
innerMerges lo ro f =
  merges lo ro Merge.dropMissing Merge.dropMissing (Merge.zipWithMatched f)

-- | Full outer merge.
outerMerges :: Ord a
            => Lens' s a -> Lens' t a
            -> (a -> [s] -> c) -> (a -> [t] -> c) -> (a -> [s] -> [t] -> c)
            -> [s] -> [t] -> Map.Map a c
outerMerges lo ro fl fr fb =
  merges lo ro (Merge.mapMissing fl) (Merge.mapMissing fr) (Merge.zipWithMatched fb)

-- | Left merge: all keys from left.
leftMerges :: Ord a
           => Lens' s a -> Lens' t a
           -> (a -> [s] -> c) -> (a -> [s] -> [t] -> c)
           -> [s] -> [t] -> Map.Map a c
leftMerges lo ro fl fb =
  merges lo ro (Merge.mapMissing fl) Merge.dropMissing (Merge.zipWithMatched fb)

-- | Right merge: all keys from right.
rightMerges :: Ord a
            => Lens' s a -> Lens' t a
            -> (a -> [t] -> c) -> (a -> [s] -> [t] -> c)
            -> [s] -> [t] -> Map.Map a c
rightMerges lo ro fr fb =
  merges lo ro Merge.dropMissing (Merge.mapMissing fr) (Merge.zipWithMatched fb)

---------------------------------------------------------------------
-- Sort merge tactics
---------------------------------------------------------------------

-- | Construct a 'WhenMatched' merge tactic from a Sort.
-- Uses @i = ()@ (one position per key).
sortedMatched :: Sort () k (x, y) z -> Merge.SimpleWhenMatched k x y z
sortedMatched (Sort h) = Merge.zipWithMatched $ \k x y ->
  h (const (k, (x, y)))

-- | Construct a 'WhenMissing' merge tactic from a Sort.
-- Uses @i = ()@ (one position per key).
sortedMissing :: Sort () k x y -> Merge.SimpleWhenMissing k x y
sortedMissing (Sort h) = Merge.mapMissing $ \k x ->
  h (const (k, x))
