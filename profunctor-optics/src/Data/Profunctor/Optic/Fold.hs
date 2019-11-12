module Data.Profunctor.Optic.Fold (
    -- * Types
    Fold0
  , AFold0
  , Fold
  , AFold
  , Fold1
  , AFold1
    -- * Constructors
  , folding
  , folding1
  , unfolding 
  , folded0 
  , folded 
  , afolded
  , afolded'
  , folded1
  , afolded1
  , afolded1'
  , unfolded 
  , aunfolded
  , aunfolded'
  , folded_
  , folded1_
  , failing 
  , recursing
  , recursing1 
  , corecursing 
  , toFold0
  , toFold 
  , toFold1
  , fromFold0 
  , cloneFold
  , cloneFold1
    -- * Representatives
  , Fold0Rep
  , Pre
    -- * Primitive operators
  , maybeOf
  , previewOf
  , foldMapOf
  , foldMap1Of 
  , unfoldMapOf
  , foldOf 
  , fold1Of 
  , unfoldOf 
  , toListOf
  , toNelOf
  , toPureOf
    -- * Common optics
  , unital
  , unital1
  , presemiring
  , summed
  , summed1
  , multiplied 
  , multiplied1 
  , premapped 
  , premappedM
    -- * Derived operators
  , (^?)
  , is
  , isnt
  , preview 
  , preuse
  , (^..)
  , foldsr
  , foldsl
  , foldsl'
  , foldsM'
  , endo 
  , endoM 
  , has
  , hasnt 
  , nulls 
  , min
  , max
  , pmin
  , pmax
  , joins
  , joins'
  , meets
  , meets'
  , all 
  , any 
  , elem 
  , notElem 
) where

import Control.Foldl (EndoM(..))
import Control.Monad ((<=<))
import Control.Monad.Reader as Reader hiding (lift)
import Control.Monad.State as State hiding (lift)
import Data.Foldable (Foldable, foldMap, traverse_)
import Data.Functor.Foldable (Corecursive, Recursive, Base)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe
import Data.Monoid
import Data.Prd (Prd(..), Min(..), Max(..))
import Data.Prd.Lattice (Lattice(..))
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Prism (just)
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.View (to, from, view, cloneView)
import Data.Semiring (Semiring(..))
import qualified Control.Foldl as L
import qualified Data.Functor.Foldable as F
import qualified Data.List as L (unfoldr)
import qualified Data.List.NonEmpty as NEL
import qualified Data.Prd as Prd
import qualified Data.Semiring as Rng
import qualified Prelude as Pre 

---------------------------------------------------------------------
-- 'Fold0', 'Fold' & 'Unfold'
---------------------------------------------------------------------

-- | Transform a Van Laarhoven 'Fold' into a profunctor 'Fold'.
--
folding :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> Fold s a
folding f = coercer . lift f . coercer
{-# INLINE folding #-}

-- | Transform a Van Laarhoven 'Fold1' into a profunctor 'Fold1'.
--
-- See 'Data.Profunctor.Optic.Property'.
--
folding1 :: (forall f. Apply f => (a -> f b) -> s -> f t) -> Fold1 s a
folding1 f = coercer . lift f . coercer
{-# INLINE folding1 #-}

-- | Transform a Van Laarhoven 'Unfold' into a profunctor 'Unfold'.
--
unfolding :: (forall f. Functor f => (f a -> b) -> f s -> t) -> Unfold t b
unfolding f = coercel . lower f . coercel
{-# INLINE unfolding #-}

-- | Obtain a 'Fold0' from a partial function.
--
-- @
-- 'folded0' ('maybeOf' o) ≡ o
-- 'folded0' ('view' o) ≡ o . 'just'
-- @
--
-- >>> preview (folded0 listToMaybe) "foo"
-- Just 'f'
--
-- >>> [Just 1, Nothing] ^.. folded id . folded0 id
-- [1]
--
folded0 :: (s -> Maybe a) -> Fold0 s a
folded0 f = to (\s -> maybe (Left s) Right (f s)) . right'
{-# INLINE folded0 #-}

-- | Obtain a 'Fold' using a 'Traversable' functor.
--
-- @
-- 'folded' f ≡ 'traversed' . 'to' f
-- 'folded' f ≡ 'folding' 'traverse' . 'to' f
-- @
--
folded :: Traversable f => (s -> a) -> Fold (f s) a
folded f = folding traverse . to f
{-# INLINE folded #-}


-- | TODO: Document
--
afolded :: Monoid r => ((a -> r) -> s -> r) -> AFold r s a
afolded o = Star #. (Const #.) #. o .# (getConst #.) .# runStar
{-# INLINE afolded #-}

-- | TODO: Document
--
afolded' :: Foldable f => AFold r (f a) a
afolded' = afolded foldMap
{-# INLINE afolded' #-}

-- | Obtain a 'Fold1' using a 'Traversable1' functor.
--
-- @
-- 'folded1' f ≡ 'traversed1' . 'to' f
-- 'folded1' f ≡ 'folding1' 'traverse1' . 'to' f
-- @
--
folded1 :: Traversable1 f => (s -> a) -> Fold1 (f s) a
folded1 f = folding1 traverse1 . to f
{-# INLINE folded1 #-}

-- | TODO: Document
--
afolded1 :: Semigroup r => ((a -> r) -> s -> r) -> AFold1 r s a
afolded1 o = Star #. (Const #.) #. o .# (getConst #.) .# runStar
{-# INLINE afolded1 #-}

-- | TODO: Document
--
afolded1' :: Foldable1 f => AFold1 r (f a) a
afolded1' = afolded1 foldMap1
{-# INLINE afolded1' #-}

-- | Obtain an 'Unfold' using a 'Distributive' functor. 
--
-- @
-- 'unfolded' f ≡ 'cotraversed' . 'from' f
-- 'unfolded' f ≡ 'unfolding' 'cotraverse' . 'from' f
-- @
--
unfolded :: Distributive f => (b -> t) -> Unfold (f t) b
unfolded f = unfolding cotraverse . from f
{-# INLINE unfolded #-}

-- | TODO: Document
--
aunfolded :: ((r -> b) -> r -> t) -> AUnfold r t b
aunfolded o = Costar #. (.# getConst) #. o .#  (.# Const) .# runCostar  
{-# INLINE aunfolded #-}

-- | TODO: Document
--
aunfolded' :: AUnfold b [t] (Maybe (t, b))
aunfolded' = aunfolded L.unfoldr
{-# INLINE aunfolded' #-}

-- | Obtain a 'Fold' by lifting an operation that returns a 'Foldable' result.
--
-- @ 
-- 'folded_' ('toListOf' o) ≡ o
-- 'folded_' f ≡ 'to' f . 'folding' 'traverse_'
-- 'folded_' f ≡ 'coercer' . 'lmap' f . 'lift' 'traverse_'
-- @
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- This can be useful to lift operations from @Data.List@ and elsewhere into a 'Fold'.
--
-- >>> [1,2,3,4] ^.. folded_ tail
-- [2,3,4]
--
folded_ :: Foldable f => (s -> f a) -> Fold s a
folded_ f = to f . folding traverse_
{-# INLINE folded_ #-}

-- | Obtain a 'Fold1' by lifting an operation that returns a 'Foldable1' result.
--
-- @ 
-- 'folded1_' ('toNelOf' o) ≡ o
-- 'folded1_' f ≡ 'to' f . 'folding1' 'traverse_'
-- 'folded1_' f ≡ 'coercer' . 'lmap' f . 'lift' 'traverse_'
-- @
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- This can be useful to lift operations from @Data.List.NonEmpty@ and elsewhere into a 'Fold1'.
--
-- >>> 1 :| [2,3,4] ^.. folded1_ tail
-- [2,3,4]
--
folded1_ :: Foldable1 f => (s -> f a) -> Fold1 s a
folded1_ f = to f . folding1 traverse1_
{-# INLINE folded1_ #-}

infixl 3 `failing` -- Same as (<|>)

-- | Try the first 'Fold0'. If it returns no entry, try the second one.
--
failing :: AFold0 a s a -> AFold0 a s a -> Fold0 s a
failing a b = folded0 $ \s -> maybe (preview b s) Just (preview a s)
{-# INLINE failing #-}

{-
import Data.Functor.Foldable (ListF(..))

fromListF :: Num a => ListF a (Sum a) -> Sum a
fromListF Nil = mempty
fromListF (Cons a r) = Sum a <> r

foldMapOf (recursing) fromListF $ [1..5]
Sum {getSum = 15}
-}

-- | TODO: Document
--
recursing :: Recursive s => AFold a s (Base s a)
recursing = afolded F.fold
{-# INLINE recursing #-}

-- | TODO: Document
--
recursing1 :: Recursive s => AFold1 a s (Base s a)
recursing1 = afolded1 F.fold
{-# INLINE recursing1 #-}

-- | TODO: Document
--
corecursing :: Corecursive t => AUnfold b t (Base t b)
corecursing = aunfolded F.unfold
{-# INLINE corecursing #-}

-- | Obtain a 'Fold0' from a 'View'.
--
-- @
-- 'toFold0' o ≡ o . 'just'
-- 'toFold0' o ≡ 'folded0' ('view' o)
-- @
--
toFold0 :: View s (Maybe a) -> Fold0 s a
toFold0 = (. just)
{-# INLINE toFold0 #-}

-- | Obtain a 'Fold' from a 'View' or 'AFold'.
--
toFold :: AView s a -> Fold s a
toFold = to . view
{-# INLINE toFold #-}

-- | Obtain a 'Fold1' from a 'View' or 'AFold1'.
--
toFold1 :: AView s a -> Fold1 s a
toFold1 = to . view
{-# INLINE toFold1 #-}

-- | Obtain a partial 'View' from a 'Fold0' 
--
fromFold0 ::  AFold0 a s a -> View s (Maybe a)
fromFold0 = to . preview
{-# INLINE fromFold0 #-}

-- | Obtain a 'Fold' from a 'AFold'.
--
cloneFold :: Monoid a => AFold a s a -> View s a
cloneFold = cloneView
{-# INLINE cloneFold #-}

-- | Obtain a 'Fold1' from a 'AFold1'.
--
cloneFold1 :: Semigroup a => AFold1 a s a -> View s a
cloneFold1 = cloneView
{-# INLINE cloneFold1 #-}

---------------------------------------------------------------------
-- 'Fold0Rep'
---------------------------------------------------------------------

newtype Fold0Rep r a b = Fold0Rep { runFold0Rep :: a -> Maybe r }

type AFold0 r s a = Optic' (Fold0Rep r) s a

instance Functor (Fold0Rep r a) where
  fmap _ (Fold0Rep p) = Fold0Rep p

instance Contravariant (Fold0Rep r a) where
  contramap _ (Fold0Rep p) = Fold0Rep p

instance Profunctor (Fold0Rep r) where
  dimap f _ (Fold0Rep p) = Fold0Rep (p . f)

instance Choice (Fold0Rep r) where
  left' (Fold0Rep p) = Fold0Rep (either p (const Nothing))
  right' (Fold0Rep p) = Fold0Rep (either (const Nothing) p)

instance Cochoice (Fold0Rep r) where
  unleft  (Fold0Rep k) = Fold0Rep (k . Left)
  unright (Fold0Rep k) = Fold0Rep (k . Right)

instance Strong (Fold0Rep r) where
  first' (Fold0Rep p) = Fold0Rep (p . fst)
  second' (Fold0Rep p) = Fold0Rep (p . snd)

instance Sieve (Fold0Rep r) (Pre r) where
  sieve = (Pre .) . runFold0Rep

instance Representable (Fold0Rep r) where
  type Rep (Fold0Rep r) = Pre r
  tabulate = Fold0Rep . (getPre .)
  {-# INLINE tabulate #-}

-- | 'Pre' is 'Maybe' with a phantom type variable.
--
newtype Pre a b = Pre { getPre :: Maybe a } deriving (Eq, Ord, Show)

instance Functor (Pre a) where fmap _ (Pre p) = Pre p

instance Contravariant (Pre a) where contramap _ (Pre p) = Pre p

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | TODO: Document
--
maybeOf :: AFold0 a s a -> s -> Maybe a
maybeOf = flip previewOf Just

-- | TODO: Document
--
previewOf :: Optic' (Fold0Rep r) s a -> (a -> Maybe r) -> s -> Maybe r
previewOf o = runFold0Rep #. o .# Fold0Rep

-- | Map parts of a structure to a monoid and combine the results.
--
-- @
-- 'Data.Foldable.foldMap' = 'foldMapOf' 'folding''
-- @
--
-- >>> foldMapOf both id (["foo"], ["bar", "baz"])
-- ["foo","bar","baz"]
--
-- @
-- 'foldMapOf' ::                  'Iso'' s a        -> (a -> r) -> s -> r
-- 'foldMapOf' ::                  'Lens'' s a       -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Monoid' r    => 'Prism'' s a      -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Monoid' r    => 'Traversal'' s a  -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Monoid' r    => 'Affine'' s a     -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Monoid' r    => 'Fold' s a        -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Semigroup' r => 'Fold1' s a       -> (a -> r) -> s -> r
-- @
--
foldMapOf :: Monoid r => AFold r s a -> (a -> r) -> s -> r
foldMapOf o = (getConst #.) #. runStar #. o .# Star .# (Const #.)
{-# INLINE foldMapOf #-}

-- | Map parts of a structure to a semigroup and combine the results.
--
foldMap1Of :: Semigroup r => AFold1 r s a -> (a -> r) -> s -> r
foldMap1Of o = (getConst #.) #. runStar #. o .# Star .# (Const #.)
{-# INLINE foldMap1Of #-}

-- | TODO: Document
--
-- >>> unfoldMapOf (from succ) (*2) 3
-- 7
--
-- Compare 'Data.Profunctor.Optic.View.reviews'.
--
unfoldMapOf :: AUnfold r t b -> (r -> b) -> r -> t
unfoldMapOf o = (.# Const) #. runCostar #. o .# Costar .# (.# getConst)
{-# INLINE unfoldMapOf #-}

-- | TODO: Document
--
foldOf :: Monoid a => AFold a s a -> s -> a
foldOf = flip foldMapOf id
{-# INLINE foldOf #-}

-- | TODO: Document
--
fold1Of :: Semigroup a => AFold1 a s a -> s -> a
fold1Of = flip foldMap1Of id
{-# INLINE fold1Of #-}

-- | TODO: Document
--
unfoldOf :: AUnfold b t b -> b -> t
unfoldOf = flip unfoldMapOf id
{-# INLINE unfoldOf #-}

-- | Collect the foci of a `Fold` into a list.
--
toListOf :: AFold (Endo [a]) s a -> s -> [a]
toListOf o = foldsr o (:) []
{-# INLINE toListOf #-}

-- | Extract a 'NonEmpty' of the targets of 'Fold1'.
--
-- >>> toNelOf bitraversed1 ('h' :| "ello", 'w' :| "orld")
-- "hello" :| ["world"]
--
-- @
-- 'toNelOf' :: 'View' s a        -> s -> NonEmpty a
-- 'toNelOf' :: 'Fold1' s a       -> s -> NonEmpty a
-- 'toNelOf' :: 'Lens'' s a       -> s -> NonEmpty a
-- 'toNelOf' :: 'Iso'' s a        -> s -> NonEmpty a
-- 'toNelOf' :: 'Traversal1'' s a -> s -> NonEmpty a
-- 'toNelOf' :: 'Prism'' s a      -> s -> NonEmpty a
-- @
--
toNelOf :: AFold1 (NonEmptyDList a) s a -> s -> NonEmpty a
toNelOf l = flip getNonEmptyDList [] . foldMap1Of l (NonEmptyDList #. (:|))
{-# INLINE toNelOf #-}

-- | TODO: Document
-- 
-- @
-- toPureOf :: Fold s a -> s -> [a]
-- toPureOf :: Applicative f => Setter s t a b -> s -> f a
-- @
--
toPureOf :: Applicative f => Monoid (f a) => AFold (f a) s a -> s -> f a
toPureOf o = foldMapOf o pure
{-# INLINE toPureOf #-}

---------------------------------------------------------------------
-- Common 'Fold's
---------------------------------------------------------------------

-- | Compute the result of an expression in a unital semiring.
--
-- @ 
-- 'unital' ≡ 'summed' . 'multiplied'
-- @
--
-- >>> foldOf unital [[1,2], [3,4 :: Int]]
-- 14
--
-- For semirings without a distinct multiplicative unit this is 
-- equivalent to @const mempty@:
--
-- >>> foldOf unital $ (fmap . fmap) Just [[1,2], [3,4 :: Int]]
-- Just 0
--
-- In this situation you most likely want to use 'unital1'.
--
unital :: Foldable f => Foldable g => Monoid r => Semiring r => AFold r (f (g a)) a
unital = summed . multiplied

-- | Semiring fold with no multiplicative unit.
--
-- @ 
-- 'unital1' ≡ 'summed' . 'multiplied1'
-- @
--
-- >>> foldOf unital1 $ (fmap . fmap) Just [1 :| [2], 3 :| [4 :: Int]]
-- Just 14
--
unital1 :: Foldable f => Foldable1 g => Monoid r => Semiring r => AFold r (f (g a)) a
unital1 = summed . multiplied1

-- | Semiring fold with no additive or multiplicative unit.
--
-- @ 
-- 'presemiring' ≡ 'summed1' . 'multiplied1'
-- @
--
presemiring :: Foldable1 f => Foldable1 g => Semiring r => AFold1 r (f (g a)) a
presemiring = summed1 . multiplied1

-- | Compute the monoidal sum of a 'Fold'.
--
-- >>> 1 <> 2 <> 3 <> 4 :: Int
-- 10
-- >>> foldOf summed [1,2,3,4 :: Int]
-- 10
--
-- 'summed' and 'multiplied' compose just as they do in arithmetic:
--
-- >>> 1 >< 2 <> 3 >< 4 :: Int
-- 14
-- >>> foldOf (summed . multiplied) [[1,2], [3,4 :: Int]]
-- 14
-- >>> 1 <> 2 >< 3 <> 4 :: Int
-- 21
-- >>> foldOf (multiplied . summed) [[1,2], [3,4 :: Int]]
-- 21
--
summed :: Foldable f => Monoid r => AFold r (f a) a
summed = afolded foldMap

-- | Compute the semigroup sum of a 'Fold1'.
--
-- >>> 1 <> 2 <> 3 <> 4 :: Int
-- 10
-- >>> fold1Of summed1 $ 1 :| [2,3,4 :: Int]
-- 10
--
summed1 :: Foldable1 f => Semigroup r => AFold1 r (f a) a
summed1 = afolded1 foldMap1

-- | Compute the semiring product of a 'Fold'.
--
-- >>> 1 >< 2 >< 3 >< 4 :: Int
-- 24
-- >>> foldOf multiplied [1,2,3,4 :: Int]
-- 24
--
-- For semirings without a distinct multiplicative unit this is 
-- equivalent to @const mempty@:
--
-- >>> foldOf multiplied $ fmap Just [1..(5 :: Int)]
-- Just 0
--
-- In this situation you most likely want to use 'multiplied1'.
--
multiplied :: Foldable f => Monoid r => Semiring r => AFold r (f a) a
multiplied = afolded Rng.product

-- | Compute the semiring product of a 'Fold1'.
--
-- >>> fold1Of multiplied1 $ fmap Just (1 :| [2..(5 :: Int)])
-- Just 120 
--
multiplied1 :: Foldable1 f => Semiring r => AFold1 r (f a) a
multiplied1 = afolded1 Rng.product1

-- | Precompose with a Moore machine.
--
premapped :: Cayley b a -> L.Fold a c -> L.Fold b c
premapped o (L.Fold h z k) = L.Fold (foldsl' o h) z k

-- | Precompose with an effectful Moore machine.
--
premappedM :: Monad m => CayleyM m b a -> L.FoldM m a c -> L.FoldM m b c
premappedM o (L.FoldM h z k) = L.FoldM (foldsM' o h) z k

---------------------------------------------------------------------
-- Derived operators
---------------------------------------------------------------------

infixl 8 ^?

-- | An infix variant of 'preview''.
--
-- @
-- ('^?') ≡ 'flip' 'preview''
-- @
--
-- Perform a safe 'head' of a 'Fold' or 'Traversal' or retrieve 'Just'
-- the result from a 'View' or 'Lens'.
--
-- When using a 'Traversal' as a partial 'Lens', or a 'Fold' as a partial
-- 'View' this can be a convenient way to extract the optional value.
--
-- >>> Left 4 ^? left
-- Just 4
--
-- >>> Right 4 ^? left
-- Nothing
--
(^?) :: s -> AFold0 a s a -> Maybe a
s ^? o = maybeOf o s

-- | Check to see if this 'Fold0' doesn't match.
--
-- >>> is just Nothing
-- False
--
is :: AFold0 a s a -> s -> Bool
is k s = isJust (preview k s)
{-# INLINE is #-}

-- | Check to see if this 'Fold0' doesn't match.
--
-- >>> isnt just Nothing
-- True
--
isnt :: AFold0 a s a -> s -> Bool
isnt k s = not (isJust (preview k s))
{-# INLINE isnt #-}

-- | TODO: Document
--
preview :: MonadReader s m => AFold0 a s a -> m (Maybe a)
preview o = Reader.asks $ maybeOf o

-- | TODO: Document
--
preuse :: MonadState s m => AFold0 a s a -> m (Maybe a)
preuse o = State.gets $ preview o

infixl 8 ^..

-- | Infix version of 'toListOf'.
--
-- @
-- 'Data.Foldable.toList' xs ≡ xs '^..' 'folded'
-- ('^..') ≡ 'flip' 'toListOf'
-- @
--
-- >>> [[1,2], [3 :: Int]] ^.. id
-- [[[1,2], [3]]]
-- >>> [[1,2], [3 :: Int]] ^.. traversed
-- [[1,2], [3]]
-- >>> [[1,2], [3 :: Int]] ^.. traversed . traversed
-- [1,2,3]
--
-- >>> (1,2) ^.. bitraversed
-- [1,2]
--
-- @
-- ('^..') :: s -> 'View' s a     -> [a]
-- ('^..') :: s -> 'Fold' s a       -> [a]
-- ('^..') :: s -> 'Lens'' s a      -> [a]
-- ('^..') :: s -> 'Iso'' s a       -> [a]
-- ('^..') :: s -> 'Traversal'' s a -> [a]
-- ('^..') :: s -> 'Prism'' s a     -> [a]
-- ('^..') :: s -> 'Affine'' s a    -> [a]
-- @
--
(^..) :: s -> AFold (Endo [a]) s a -> [a]
(^..) = flip toListOf
{-# INLINE (^..) #-}

-- | Right fold over a 'Fold'.
--
-- >>> foldsr'' folded (<>) (zero :: Int) [1..5]
-- 15
--
foldsr :: AFold (Endo r) s a -> (a -> r -> r) -> r -> s -> r
foldsr p f r = (`appEndo` r) . foldMapOf p (Endo . f)

-- | Left fold over a 'Fold'.
--
foldsl :: AFold (Dual (Endo c)) s a -> (c -> a -> c) -> c -> s -> c
foldsl p f r = (`appEndo` r) . getDual . foldMapOf p (Dual . Endo . flip f)

-- | Fold lift the elements of a structure, associating to the left, but strictly.
--
-- @
-- 'Data.Foldable.foldl'' ≡ 'foldsl'' 'folded'
-- @
--
-- @
-- 'foldsl'' :: 'Iso'' s a        -> (c -> a -> c) -> c -> s -> c
-- 'foldsl'' :: 'Lens'' s a       -> (c -> a -> c) -> c -> s -> c
-- 'foldsl'' :: 'View' s a        -> (c -> a -> c) -> c -> s -> c
-- 'foldsl'' :: 'Fold' s a        -> (c -> a -> c) -> c -> s -> c
-- 'foldsl'' :: 'Traversal'' s a  -> (c -> a -> c) -> c -> s -> c
-- 'foldsl'' :: 'Traversal0'' s a -> (c -> a -> c) -> c -> s -> c
-- @
--
foldsl' :: AFold (Endo (Endo c)) s a -> (c -> a -> c) -> c -> s -> c
foldsl' o f c s = foldsr o f' (Endo id) s `appEndo` c
  where f' x (Endo k) = Endo $ \z -> k $! f z x
{-# INLINE foldsl' #-}

-- | A strict monadic left fold.
--
foldsM' :: Monad m => AFold (Endo (EndoM m r)) s a -> (r -> a -> m r) -> r -> s -> m r
foldsM' o f c s = foldsr o f' mempty s `appEndoM` c
  where f' x (EndoM k) = EndoM $ \z -> (f $! z) x >>= k

-- | TODO: Document
--
endo :: AFold (Endo (a -> a)) s (a -> a) -> s -> a -> a
endo o = foldsr o (.) id

-- | TODO: Document
--
endoM :: Monad m => AFold (Endo (a -> m a)) s (a -> m a) -> s -> a -> m a
endoM o = foldsr o (<=<) pure

-- | Determine whether a `Fold` has at least one focus.
--
has :: AFold Any s a -> s -> Bool
has p = getAny . foldMapOf p (const (Any True))

-- | Determine whether a `Fold` does not have a focus.
--
hasnt :: AFold All s a -> s -> Bool
hasnt p = getAll . foldMapOf p (const (All False))

-- | TODO: Document
--
nulls :: AFold All s a -> s -> Bool
nulls o = all o (const False)

-- | Find the minimum of a totally ordered set. 
--
min :: Ord a => AFold (Endo (Endo a)) s a -> a -> s -> a
min o = foldsl' o Pre.min

-- | Find the maximum of a totally ordered set.
--
max :: Ord a => AFold (Endo (Endo a)) s a -> a -> s -> a
max o = foldsl' o Pre.max

-- | Find the (partial) minimum of a partially ordered set.
--
pmin :: Eq a => Prd a => AFold (Endo (EndoM Maybe a)) s a -> a -> s -> Maybe a
pmin o = foldsM' o Prd.pmin

-- | Find the (partial) minimum of a partially ordered set.
--
pmax :: Eq a => Prd a => AFold (Endo (EndoM Maybe a)) s a -> a -> s -> Maybe a
pmax o = foldsM' o Prd.pmax

-- | Find the (partial) joins of a sublattice. 
--
joins :: Lattice a => AFold (Endo (Endo a)) s a -> a -> s -> a
joins o = foldsl' o (\/)

-- | Find the joins of a sublattice or return the bottom element.
--
joins' :: Lattice a => Min a => AFold (Endo (Endo a)) s a -> s -> a
joins' o = joins o minimal

-- | Find the (partial) meets of a sublattice.
--
meets :: Lattice a => AFold (Endo (Endo a)) s a -> a -> s -> a
meets o = foldsl' o (/\)

-- | Find the meets of a sublattice or return the top element.
--
meets' :: Lattice a => Max a => AFold (Endo (Endo a)) s a -> s -> a
meets' o = meets o maximal

-- | TODO: Document
--
all :: AFold All s a -> (a -> Bool) -> s -> Bool
all o p = getAll . foldMapOf o (All . p)

-- | TODO: Document
--
any :: AFold Any s a -> (a -> Bool) -> s -> Bool
any o p = getAny . foldMapOf o (Any . p)

-- | Determine whether a `Fold` contains a given element.
elem :: Eq a => AFold Any s a -> a -> s -> Bool
elem p a = any p (== a)

-- | Determine whether a `Fold` not contains a given element.
notElem :: Eq a => AFold All s a -> a -> s -> Bool
notElem p a = all p (/= a)

------------------------------------------------------------------------------
-- NonEmptyDList
------------------------------------------------------------------------------

newtype NonEmptyDList a
  = NonEmptyDList { getNonEmptyDList :: [a] -> NEL.NonEmpty a }

instance Semigroup (NonEmptyDList a) where
  NonEmptyDList f <> NonEmptyDList g = NonEmptyDList (f . NEL.toList . g)
