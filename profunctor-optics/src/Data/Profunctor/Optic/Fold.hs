{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Fold (
    -- * Types
    Fold
  , Ixfold
  , AFold
  , AIxfold
  , Fold0
  , AFold0
  , Fold1
  , AFold1
  , Cofold
  , ACofold
    -- * Constructors
  , fold0 
  , foldVl
  , fold1Vl
  , cofoldVl 
  , folding 
  , folding1
  , cofolding
  , folding_
  , folding1_
  , failing
  , afold
  , afold1
  , acofold
  , toFold0
  , toFold 
  , toFold1
  , fromFold0 
  , cloneFold
  , cloneFold1
    -- * Representatives
  , Fold0Rep(..)
  , Pre(..)
    -- * Primitive operators
  , previewOf
  , foldMapOf
  , ifoldMapOf
  , foldMap1Of 
  , cofoldMapOf
  , foldOf 
  , fold1Of 
  , cofoldOf 
  , toPureOf
  , productOf
  , product1Of
    -- * Optics
  , folded0
  , folded
  , folded1 
  , cofolded 
  , folded_ 
  , folded1_
  , unital
  , nonunital
  , presemiring
  , summed
  , summed1
  , multiplied 
  , multiplied1 
    -- * Operators
  , (^?)
  , preview 
  , preuse
  , (^..)
  , foldsr
  , foldsl
  , foldsl'
  --, foldsM'
  , lists
  , nelists
  , traverses_
  , concats
  , finds
  , has
  , hasnt 
  , nulls
  , asums
  , joins
  , joins'
  , meets
  , meets'
  , pelem
    -- * Indexed operators
  , (^%%)
  , ixfoldsr
  , ixfoldsrFrom
  , ixfoldsl
  , ixfoldslFrom
  , ixfoldsrM
  , ixfoldsrMFrom
  , ixfoldslM
  , ixfoldslMFrom
  , ixlists
  , ixlistsFrom
  , ixtraverses_
  , ixconcats
  , ixfinds
    -- * MonadUnliftIO 
  , tries
  , tries_ 
  , catches
  , catches_
  , handles
  , handles_
    -- * Auxilliary Types
  , All, Any
  , Nedl(..)
) where

import Control.Applicative
import Control.Exception (Exception)
import Control.Monad ((<=<), void)
import Control.Monad.IO.Unlift
import Control.Monad.Reader as Reader hiding (lift)
import Control.Monad.State as State hiding (lift)
import Data.Foldable (Foldable, foldMap, traverse_)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe
import Data.Monoid hiding (All(..), Any(..))
import Data.Prd (Prd(..), Min(..), Max(..))
import Data.Prd.Lattice (Lattice(..))
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Prism (right, just, async)
import Data.Profunctor.Optic.Traversal (matches, is)
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.View (to, from, primViewOf, view, cloneView)
import Data.Semiring (Semiring(..), Prod(..))
import qualified Control.Exception as Ex
import qualified Data.List.NonEmpty as NEL
import qualified Data.Prd as Prd
import qualified Data.Semiring as Rng

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> import Control.Exception hiding (catches)
-- >>> import Data.Maybe
-- >>> import Data.Monoid
-- >>> import Data.Semiring hiding (unital,nonunital, presemiring)
-- >>> import Data.List.NonEmpty (NonEmpty(..))
-- >>> import Data.List.Index
-- >>> import qualified Data.List.NonEmpty as NE
-- >>> import Data.Functor.Identity
-- >>> :load Data.Profunctor.Optic
-- >>> let ixtraversed :: Ixtraversal Int [a] [b] a b ; ixtraversed = ixtraversalVl itraverse


---------------------------------------------------------------------
-- 'Fold0', 'Fold' & 'Cofold'
---------------------------------------------------------------------

-- | Obtain a 'Fold0' directly.
--
-- @
-- 'fold0' . 'preview' ≡ id
-- 'fold0' ('view' o) ≡ o . 'just'
-- @
--
-- >>> preview (fold0 . preview $ selected even) (2, "yes")
-- Just "yes"
--
-- >>> preview (fold0 . preview $ selected even) (3, "no")
-- Nothing
--
-- >>> preview (fold0 listToMaybe) "foo"
-- Just 'f'
--
fold0 :: (s -> Maybe a) -> Fold0 s a
fold0 f = to (\s -> maybe (Left s) Right (f s)) . right'
{-# INLINE fold0 #-}

infixl 3 `failing` -- Same as (<|>)

-- | Try the first 'Fold0'. If it returns no entry, try the second one.
--
failing :: AFold0 a s a -> AFold0 a s a -> Fold0 s a
failing a b = fold0 $ \s -> maybe (preview b s) Just (preview a s)
{-# INLINE failing #-}

-- | Obtain a 'Fold' directly.
--
-- @ 
-- 'folding_' ('lists' o) ≡ o
-- 'folding_' f ≡ 'to' f . 'foldVl' 'traverse_'
-- 'folding_' f ≡ 'coercer' . 'lmap' f . 'lift' 'traverse_'
-- @
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- This can be useful to repn operations from @Data.List@ and elsewhere into a 'Fold'.
--
-- >>> [1,2,3,4] ^.. folding_ tail
-- [2,3,4]
--
folding_ :: Foldable f => (s -> f a) -> Fold s a
folding_ f = to f . foldVl traverse_
{-# INLINE folding_ #-}

-- | Obtain a 'Fold' from a 'Traversable' functor.
--
-- @
-- 'folding' f ≡ 'traversed' . 'to' f
-- 'folding' f ≡ 'foldVl' 'traverse' . 'to' f
-- @
--
folding :: Traversable f => (s -> a) -> Fold (f s) a
folding f = foldVl traverse . to f
{-# INLINE folding #-}

--(\point f s -> maybe (point s) (uncurry f) $ g s)

--ifold0 f = 

-- | Obtain a 'Fold' from a Van Laarhoven 'Fold'.
--
foldVl :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> Fold s a
foldVl f = coercer . repn f . coercer
{-# INLINE foldVl #-}

-- | Obtain a 'Fold1' directly.
--
-- @ 
-- 'folding1_' ('nelists' o) ≡ o
-- 'folding1_' f ≡ 'to' f . 'fold1Vl' 'traverse1_'
-- 'folding1_' f ≡ 'coercer' . 'lmap' f . 'lift' 'traverse1_'
-- @
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- This can be useful to repn operations from @Data.List.NonEmpty@ and elsewhere into a 'Fold1'.
--
folding1_ :: Foldable1 f => (s -> f a) -> Fold1 s a
folding1_ f = to f . fold1Vl traverse1_
{-# INLINE folding1_ #-}

-- | Obtain a 'Fold1' from a 'Traversable1' functor.
--
-- @
-- 'folding1' f ≡ 'traversed1' . 'to' f
-- 'folding1' f ≡ 'fold1Vl' 'traverse1' . 'to' f
-- @
--
folding1 :: Traversable1 f => (s -> a) -> Fold1 (f s) a
folding1 f = fold1Vl traverse1 . to f
{-# INLINE folding1 #-}

-- | Obtain a 'Fold1' from a Van Laarhoven 'Fold1'.
--
-- See 'Data.Profunctor.Optic.Property'.
--
fold1Vl :: (forall f. Apply f => (a -> f b) -> s -> f t) -> Fold1 s a
fold1Vl f = coercer . repn f . coercer
{-# INLINE fold1Vl #-}

-- | Obtain an 'Cofold' from a 'Distributive' functor. 
--
-- @
-- 'cofolding' f ≡ 'cotraversed' . 'from' f
-- 'cofolding' f ≡ 'cofoldVl' 'cotraverse' . 'from' f
-- @
--
cofolding :: Distributive f => (b -> t) -> Cofold (f t) b
cofolding f = cofoldVl cotraverse . from f
{-# INLINE cofolding #-}

-- | Obtain a 'Cofold' from a Van Laarhoven 'Cofold'.
--
cofoldVl :: (forall f. Comonad f => (f a -> b) -> f s -> t) -> Cofold t b
cofoldVl f = coercel . corepn f . coercel
{-# INLINE cofoldVl #-}

-- | TODO: Document
--
afold :: ((a -> r) -> s -> r) -> AFold r s a
afold o = Star #. (Const #.) #. o .# (getConst #.) .# runStar
{-# INLINE afold #-}

-- | TODO: Document
--
afold1 :: Semigroup r => ((a -> r) -> s -> r) -> AFold1 r s a
afold1 o = Star #. (Const #.) #. o .# (getConst #.) .# runStar
{-# INLINE afold1 #-}

-- | TODO: Document
--
acofold :: ((r -> b) -> r -> t) -> ACofold r t b
acofold o = Costar #. (.# getConst) #. o .#  (.# Const) .# runCostar  
{-# INLINE acofold #-}

-- | Obtain a 'Fold0' from a 'View'.
--
-- @
-- 'toFold0' o ≡ o . 'just'
-- 'toFold0' o ≡ 'fold0' ('view' o)
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
previewOf :: Optic' (Fold0Rep r) s a -> (a -> Maybe r) -> s -> Maybe r
previewOf o = runFold0Rep #. o .# Fold0Rep

-- | Map parts of a structure to a monoid and combine the results.
--
-- @
-- 'Data.Foldable.foldMap' = 'foldMapOf' 'foldVl''
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
foldMapOf = primViewOf
{-# INLINE foldMapOf #-}

-- | TODO: Document
--
ifoldMapOf :: AIxfold r i s a -> (i -> a -> r) -> i -> s -> r
ifoldMapOf o f = curry $ primViewOf o (uncurry f)
{-# INLINE ifoldMapOf #-}

-- | Map parts of a structure to a semigroup and combine the results.
--
foldMap1Of :: Semigroup r => AFold1 r s a -> (a -> r) -> s -> r
foldMap1Of = primViewOf
{-# INLINE foldMap1Of #-}

-- | TODO: Document
--
-- >>> cofoldMapOf (from succ) (*2) 3
-- 7
--
-- Compare 'Data.Profunctor.Optic.View.primReviewOf'.
--
cofoldMapOf :: ACofold r t b -> (r -> b) -> r -> t
cofoldMapOf o = (.# Const) #. runCostar #. o .# Costar .# (.# getConst)
{-# INLINE cofoldMapOf #-}

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
cofoldOf :: ACofold b t b -> b -> t
cofoldOf = flip cofoldMapOf id
{-# INLINE cofoldOf #-}

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

-- | Compute the semiring product of a fold.
--
-- For semirings without a multiplicative unit this is equivalent to @const mempty@:
--
-- >>> productOf folded Just [1..(5 :: Int)]
-- Just 0
--
-- In this situation you most likely want to use 'product1Of'.
--
productOf :: Monoid r => Semiring r => AFold (Prod r) s a -> (a -> r) -> s -> r
productOf o p = getProd . foldMapOf o (Prod . p)
{-# INLINE productOf #-}

-- | Compute the semiring product of a non-empty fold.
--
product1Of :: Semiring r => AFold1 (Prod r) s a -> (a -> r) -> s -> r
product1Of o p = getProd . foldMap1Of o (Prod . p)
{-# INLINE product1Of #-}

---------------------------------------------------------------------
-- Common folds
---------------------------------------------------------------------

-- | Obtain a 'Fold0' from a partial function.
--
-- >>> [Just 1, Nothing] ^.. folded . folded0
-- [1]
--
folded0 :: Fold0 (Maybe a) a
folded0 = fold0 id
{-# INLINE folded0 #-}

-- | Obtain a 'Fold' from a 'Traversable' functor.
--
folded :: Traversable f => Fold (f a) a
folded = folding id
{-# INLINE folded #-}

-- | Obtain a 'Fold1' from a 'Traversable1' functor.
--
folded1 :: Traversable1 f => Fold1 (f a) a
folded1 = folding1 id
{-# INLINE folded1 #-}

-- | Obtain an 'Cofold' from a 'Distributive' functor. 
--
cofolded :: Distributive f => Cofold (f b) b
cofolded = cofolding id
{-# INLINE cofolded #-}

-- | The canonical 'Fold'.
--
folded_ :: Foldable f => Fold (f a) a
folded_ = folding_ id
{-# INLINE folded_ #-}

-- | The canonical 'Fold1'.
--
folded1_ :: Foldable1 f => Fold1 (f a) a
folded1_ = folding1_ id
{-# INLINE folded1_ #-}

-- | Compute the result of an expression in a unital semiring.
--
-- @ 
-- 'unital' ≡ 'summed' . 'multiplied'
-- @
--
-- >>> foldOf unital [[1,2], [3,4 :: Int]]
-- 14
--
-- For semirings without a multiplicative unit this is 
-- equivalent to @const mempty@:
--
-- >>> foldOf unital $ (fmap . fmap) Just [[1,2], [3,4 :: Int]]
-- Just 0
--
-- In this situation you most likely want to use 'nonunital'.
--
unital :: Foldable f => Foldable g => Monoid r => Semiring r => AFold r (f (g a)) a
unital = summed . multiplied
{-# INLINE unital #-}

-- | Semiring fold with no multiplicative unit.
--
-- @ 
-- 'nonunital' ≡ 'summed' . 'multiplied1'
-- @
--
-- >>> foldOf nonunital $ (fmap . fmap) Just [1 :| [2], 3 :| [4 :: Int]]
-- Just 14
--
nonunital :: Foldable f => Foldable1 g => Monoid r => Semiring r => AFold r (f (g a)) a
nonunital = summed . multiplied1
{-# INLINE nonunital #-}

-- | Semiring fold with no additive or multiplicative unit.
--
-- @ 
-- 'presemiring' ≡ 'summed1' . 'multiplied1'
-- @
--
presemiring :: Foldable1 f => Foldable1 g => Semiring r => AFold1 r (f (g a)) a
presemiring = summed1 . multiplied1
{-# INLINE presemiring #-}

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
-- >>> (1 <> 2) >< (3 <> 4) :: Int
-- 21
-- >>> foldOf (multiplied . summed) [[1,2], [3,4 :: Int]]
-- 21
--
summed :: Foldable f => Monoid r => AFold r (f a) a
summed = afold foldMap
{-# INLINE summed #-}

-- | Compute the semigroup sum of a 'Fold1'.
--
-- >>> 1 <> 2 <> 3 <> 4 :: Int
-- 10
-- >>> fold1Of summed1 $ 1 :| [2,3,4 :: Int]
-- 10
--
summed1 :: Foldable1 f => Semigroup r => AFold1 r (f a) a
summed1 = afold1 foldMap1
{-# INLINE summed1 #-}

-- | Compute the semiring product of a 'Fold'.
--
-- >>> 1 >< 2 >< 3 >< 4 :: Int
-- 24
-- >>> foldOf multiplied [1,2,3,4 :: Int]
-- 24
--
-- For semirings without a multiplicative unit this is 
-- equivalent to @const mempty@:
--
-- >>> foldOf multiplied $ fmap Just [1..(5 :: Int)]
-- Just 0
--
-- In this situation you most likely want to use 'multiplied1'.
--
multiplied :: Foldable f => Monoid r => Semiring r => AFold r (f a) a
multiplied = afold Rng.product
{-# INLINE multiplied #-}

-- | Compute the semiring product of a 'Fold1'.
--
-- >>> fold1Of multiplied1 $ fmap Just (1 :| [2..(5 :: Int)])
-- Just 120 
--
multiplied1 :: Foldable1 f => Semiring r => AFold1 r (f a) a
multiplied1 = afold1 Rng.product1
{-# INLINE multiplied1 #-}

---------------------------------------------------------------------
-- Operators
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
(^?) = flip preview
{-# INLINE (^?) #-}

-- | TODO: Document
--
preview :: MonadReader s m => AFold0 a s a -> m (Maybe a)
preview o = Reader.asks $ previewOf o Just
{-# INLINE preview #-}

-- | TODO: Document
--
preuse :: MonadState s m => AFold0 a s a -> m (Maybe a)
preuse o = State.gets $ preview o
{-# INLINE preuse #-}

infixl 8 ^..

-- | Infix version of 'lists'.
--
-- @
-- 'Data.Foldable.toList' xs ≡ xs '^..' 'folding'
-- ('^..') ≡ 'flip' 'lists'
-- @
--
-- >>> [[1,2], [3 :: Int]] ^.. id
-- [[[1,2],[3]]]
-- >>> [[1,2], [3 :: Int]] ^.. traversed
-- [[1,2],[3]]
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
(^..) = flip lists
{-# INLINE (^..) #-}

-- | Right fold over a 'Fold'.
--
-- >>> foldsr folded (<>) 0 [1..5::Int]
-- 15
--
foldsr :: AFold (Endo r) s a -> (a -> r -> r) -> r -> s -> r
foldsr o f r = (`appEndo` r) . foldMapOf o (Endo . f)
{-# INLINE foldsr #-}

-- | Left fold over a 'Fold'.
--
foldsl :: AFold (Dual (Endo r)) s a -> (r -> a -> r) -> r -> s -> r
foldsl o f r = (`appEndo` r) . getDual . foldMapOf o (Dual . Endo . flip f)
{-# INLINE foldsl #-}

-- | Fold repn the elements of a structure, associating to the left, but strictly.
--
-- @
-- 'Data.Foldable.foldl'' ≡ 'foldsl'' 'folding'
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
foldsl' :: AFold (Endo (Endo r)) s a -> (r -> a -> r) -> r -> s -> r
foldsl' o f r s = foldsr o f' (Endo id) s `appEndo` r
  where f' x (Endo k) = Endo $ \z -> k $! f z x
{-# INLINE foldsl' #-}

-- | Collect an applicative over the targets of a fold.
--
-- >>> traverses_ both putStrLn ("hello","world")
-- hello
-- world
--
-- @
-- 'Data.Foldable.traverse_' ≡ 'traverses_' 'folded'
-- @
--
traverses_ :: Applicative f => AFold (Endo (f ())) s a -> (a -> f r) -> s -> f ()
traverses_ p f = foldsr p (\a fu -> void (f a) *> fu) (pure ())
{-# INLINE traverses_ #-}

-- | Collect the foci of a `Fold` into a list.
--
lists :: AFold (Endo [a]) s a -> s -> [a]
lists o = foldsr o (:) []
{-# INLINE lists #-}

{-
>>> nelists bitraversed1 ('h' :| "ello", 'w' :| "orld")
 "hello" :| ["world"]
-}

-- | Extract a 'NonEmpty' of the targets of 'Fold1'.
--
--
-- @
-- 'nelists' :: 'View' s a        -> s -> NonEmpty a
-- 'nelists' :: 'Fold1' s a       -> s -> NonEmpty a
-- 'nelists' :: 'Lens'' s a       -> s -> NonEmpty a
-- 'nelists' :: 'Iso'' s a        -> s -> NonEmpty a
-- 'nelists' :: 'Traversal1'' s a -> s -> NonEmpty a
-- 'nelists' :: 'Prism'' s a      -> s -> NonEmpty a
-- @
--
nelists :: AFold1 (Nedl a) s a -> s -> NonEmpty a
nelists l = flip getNedl [] . foldMap1Of l (Nedl #. (:|))
{-# INLINE nelists #-}

-- | Map a function over all the targets of a 'Fold' of a container and concatenate the resulting lists.
--
-- >>> concats both (\x -> [x, x + 1]) (1,3)
-- [1,2,3,4]
--
-- @
-- 'concatMap' ≡ 'concats' 'folded'
-- @
--
concats :: AFold [r] s a -> (a -> [r]) -> s -> [r]
concats = foldMapOf
{-# INLINE concats #-}

-- | Find the first focus of an optic that satisfies a predicate, if one exists.
--
-- >>> finds both even (1,4)
-- Just 4
--
-- >>> finds folded even [1,3,5,7]
-- Nothing
--
-- @
-- 'Data.Foldable.find' ≡ 'finds' 'folded'
-- @
--
finds :: AFold (Endo (Maybe a)) s a -> (a -> Bool) -> s -> Maybe a
finds o f = foldsr o (\a y -> if f a then Just a else y) Nothing
{-# INLINE finds #-}

-- | Determine whether a `Fold` has at least one focus.
--
has :: AFold Any s a -> s -> Bool
has o = foldMapOf o (const True)
{-# INLINE has #-}

-- | Determine whether a `Fold` does not have a focus.
--
hasnt :: AFold All s a -> s -> Bool
hasnt o = productOf o (const False)
{-# INLINE hasnt #-}

-- | TODO: Document
--
nulls :: AFold All s a -> s -> Bool
nulls o = productOf o (const False)
{-# INLINE nulls #-}

-- | The sum of a collection of actions, generalizing 'concatOf'.
--
-- >>> asums both ("hello","world")
-- "helloworld"
--
-- >>> asums both (Nothing, Just "hello")
-- Just "hello"
--
-- @
-- 'asum' ≡ 'asums' 'folded'
-- @
--
asums :: Alternative f => AFold (Endo (Endo (f a))) s (f a) -> s -> f a
asums o = foldsl' o (<|>) empty
{-# INLINE asums #-}

-- | Compute the join of the targets of a fold. 
--
joins :: Lattice a => AFold (Endo (Endo a)) s a -> a -> s -> a
joins o = foldsl' o (\/)
{-# INLINE joins #-}

-- | Compute the join of the targets of a fold including a least element.
--
joins' :: Lattice a => Min a => AFold (Endo (Endo a)) s a -> s -> a
joins' o = joins o minimal
{-# INLINE joins' #-}

-- | Compute the meet of the targets of a fold.
--
meets :: Lattice a => AFold (Endo (Endo a)) s a -> a -> s -> a
meets o = foldsl' o (/\)
{-# INLINE meets #-}

-- | Compute the meet of the targets of a fold including a greatest element.
--
meets' :: Lattice a => Max a => AFold (Endo (Endo a)) s a -> s -> a
meets' o = meets o maximal
{-# INLINE meets' #-}

-- | Determine whether the targets of a `Fold` contain an element equivalent to a given element.
--
pelem :: Prd a => AFold Any s a -> a -> s -> Bool
pelem o a = foldMapOf o (Prd.=~ a)
{-# INLINE pelem #-}

------------------------------------------------------------------------------
-- Indexed operators
------------------------------------------------------------------------------

infixl 8 ^%%

-- | Infix version of 'ixlists'.
--
(^%%) :: Monoid i => s -> AIxfold (Endo [(i, a)]) i s a -> [(i, a)]
(^%%) = flip ixlists
{-# INLINE (^%%) #-}

-- | Indexed right fold over an 'Ixfold'.
--
-- @
-- 'foldsr' o ≡ 'ixfoldsr' o '.' 'const'
-- @
--
-- >>> ixfoldsr ixtraversed (\i a -> ((show i ++ ":" ++ show a ++ ", ") ++)) [] [1,3,5,7,9]
-- "0:1, 1:3, 2:5, 3:7, 4:9, "
--
ixfoldsr :: Monoid i => AIxfold (Endo r) i s a -> (i -> a -> r -> r) -> r -> s -> r
ixfoldsr o f = ixfoldsrFrom o f mempty
{-# INLINE ixfoldsr #-}

-- | Indexed right fold over an 'Ixfold', using an initial index value.
--
ixfoldsrFrom :: AIxfold (Endo r) i s a -> (i -> a -> r -> r) -> i -> r -> s -> r
ixfoldsrFrom o f i r = (`appEndo` r) . ifoldMapOf o (\i -> Endo . f i) i
{-# INLINE ixfoldsrFrom #-}

-- | Indexed left fold over an 'Ixfold'.
--
-- @
-- 'foldsl' ≡ 'ixfoldsl' '.' 'const'
-- @
--
ixfoldsl :: Monoid i => AIxfold (Dual (Endo r)) i s a -> (i -> r -> a -> r) -> r -> s -> r
ixfoldsl o f = ixfoldslFrom o f mempty 
{-# INLINE ixfoldsl #-}

-- | Indexed left fold over an 'Ixfold', using an initial index value.
--
ixfoldslFrom :: AIxfold (Dual (Endo r)) i s a -> (i -> r -> a -> r) -> i -> r -> s -> r
ixfoldslFrom o f i r = (`appEndo` r) . getDual . ifoldMapOf o (\i -> Dual . Endo . flip (f i)) i
{-# INLINE ixfoldslFrom #-}

-- | Indexed monadic right fold over an 'Ixfold'.
--
-- @
-- 'foldsrM' ≡ 'ixfoldrM' '.' 'const'
-- @
--
ixfoldsrM :: Monoid i => Monad m => AIxfold (Dual (Endo (r -> m r))) i s a -> (i -> a -> r -> m r) -> r -> s -> m r
ixfoldsrM o f z0 xs = ixfoldsl o f' return xs z0
  where f' i k x z = f i x z >>= k
{-# INLINE ixfoldsrM #-}

-- | Indexed monadic right fold over an 'Ixfold', using an initial index value.
--
ixfoldsrMFrom :: Monad m => AIxfold (Dual (Endo (r -> m r))) i s a -> (i -> a -> r -> m r) -> i -> r -> s -> m r
ixfoldsrMFrom o f i z0 xs = ixfoldslFrom o f' i return xs z0
  where f' i k x z = f i x z >>= k
{-# INLINE ixfoldsrMFrom #-}

-- | Indexed monadic left fold over an 'Ixfold'.
--
-- @
-- 'foldslM' ≡ 'ixfoldslM' '.' 'const'
-- @
--
ixfoldslM :: Monoid i => Monad m => AIxfold (Endo (r -> m r)) i s a -> (i -> r -> a -> m r) -> r -> s -> m r
ixfoldslM o f z0 xs = ixfoldsr o f' return xs z0
  where f' i x k z = f i z x >>= k
{-# INLINE ixfoldslM #-}

-- | Indexed monadic left fold over an 'Ixfold', using an initial index value.
--
ixfoldslMFrom :: Monad m => AIxfold (Endo (r -> m r)) i s a -> (i -> r -> a -> m r) -> i -> r -> s -> m r
ixfoldslMFrom o f i z0 xs = ixfoldsrFrom o f' i return xs z0
  where f' i x k z = f i z x >>= k
{-# INLINE ixfoldslMFrom #-}

-- | Extract the key-value pairs from an 'Ixfold'.
--
-- @
-- 'lists' l ≡ 'map' 'snd' '.' 'ixlists' l
-- @
--
ixlists :: Monoid i => AIxfold (Endo [(i, a)]) i s a -> s -> [(i, a)]
ixlists o = ixfoldsr o (\i a -> ((i,a):)) []
{-# INLINE ixlists #-}

-- | Extract the key-value pairs from an 'Ixfold', using an initial index value.
--
ixlistsFrom :: AIxfold (Endo [(i, a)]) i s a -> i -> s -> [(i, a)]
ixlistsFrom o i = ixfoldsrFrom o (\i a -> ((i,a):)) i []
{-# INLINE ixlistsFrom #-}

-- | Collect an applicative over the targets of an indexed fold.
--
ixtraverses_ :: Monoid i => Applicative f => AIxfold (Endo (f ())) i s a -> (i -> a -> f r) -> s -> f ()
ixtraverses_ p f = ixfoldsr p (\i a fu -> void (f i a) *> fu) (pure ())
{-# INLINE ixtraverses_ #-}

-- | Concatenate the results of a function of the elements of an 'IndexedFold' or 'IndexedTraversal'
-- with access to the index.
--
-- When you don't need access to the index then 'concats'  is more flexible in what it accepts.
--
-- @
-- 'concats' o ≡ 'ixconcats' o '.' 'const'
-- @
--
-- >>> ixconcats ixtraversed (\i x -> [i + x, i + x + 1]) [1,2,3,4]
-- [1,2,3,4,5,6,7,8]
--
ixconcats :: Monoid i => AIxfold [r] i s a -> (i -> a -> [r]) -> s -> [r]
ixconcats o f = ifoldMapOf o f mempty
{-# INLINE ixconcats #-}

-- | Find the first focus of an indexed optic that satisfies a predicate, if one exists.
--
ixfinds :: Monoid i => AIxfold (Endo (Maybe (i, a))) i s a -> (i -> a -> Bool) -> s -> Maybe (i, a)
ixfinds o f = ixfoldsr o (\i a y -> if f i a then Just (i,a) else y) Nothing
{-# INLINE ixfinds #-}

------------------------------------------------------------------------------
-- 'MonadUnliftIO'
------------------------------------------------------------------------------

-- | Test for synchronous exceptions that match a given optic.
--
-- In the style of 'safe-exceptions' this function rethrows async exceptions 
-- synchronously in order to preserve async behavior,
-- 
-- @
-- 'tries' :: 'MonadUnliftIO' m => 'AFold0' e 'Ex.SomeException' e -> m a -> m ('Either' e a)
-- 'tries' 'exception' :: 'MonadUnliftIO' m => 'Exception' e => m a -> m ('Either' e a)
-- @
--
tries :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> m a -> m (Either e a)
tries o a = withRunInIO $ \run -> run (Right `liftM` a) `Ex.catch` \e ->
  if is async e then throwM e else run $ maybe (throwM e) (return . Left) (preview o e)
{-# INLINE tries #-}

-- | A variant of 'tries' that returns synchronous exceptions.
--
tries_ :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> m a -> m (Maybe a)
tries_ o a = preview right `liftM` tries o a
{-# INLINE tries_ #-}

-- | Catch synchronous exceptions that match a given optic.
--
-- Rethrows async exceptions synchronously in order to preserve async behavior.
--
-- @
-- 'catches' :: 'MonadUnliftIO' m => 'AFold0' e 'Ex.SomeException' e -> m a -> (e -> m a) -> m a
-- 'catches' 'exception' :: 'MonadUnliftIO' m => Exception e => m a -> (e -> m a) -> m a
-- @
--
-- >>> catches (only Overflow) (throwIO Overflow) (\_ -> return "caught")
-- "caught"
--
catches :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> m a -> (e -> m a) -> m a
catches o a ea = withRunInIO $ \run -> run a `Ex.catch` \e ->
  if is async e then throwM e else run $ maybe (throwM e) ea (preview o e)
{-# INLINE catches #-}

-- | Catch synchronous exceptions that match a given optic, discarding the match.
--
-- >>> catches_ (only Overflow) (throwIO Overflow) (return "caught")
-- "caught"
--
catches_ :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> m a -> m a -> m a
catches_ o x y = catches o x $ const y
{-# INLINE catches_ #-}

-- | Flipped variant of 'catches'.
--
-- >>> handles (only Overflow) (\_ -> return "caught") $ throwIO Overflow
-- "caught"
--
handles :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> (e -> m a) -> m a -> m a
handles o = flip $ catches o
{-# INLINE handles #-}

-- | Flipped variant of 'catches_'.
--
-- >>> handles_ (only Overflow) (return "caught") $ throwIO Overflow
-- "caught"
--
handles_ :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> m a -> m a -> m a
handles_ o = flip $ catches_ o
{-# INLINE handles_ #-}

throwM :: MonadIO m => Exception e => e -> m a
throwM = liftIO . Ex.throwIO
{-# INLINE throwM #-}

------------------------------------------------------------------------------
-- Auxilliary Types
------------------------------------------------------------------------------

type All = Prod Bool

type Any = Bool

-- A non-empty difference list.
newtype Nedl a = Nedl { getNedl :: [a] -> NEL.NonEmpty a }

instance Semigroup (Nedl a) where
  Nedl f <> Nedl g = Nedl (f . NEL.toList . g)
