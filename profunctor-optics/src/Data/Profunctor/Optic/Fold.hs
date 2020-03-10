{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Data.Profunctor.Optic.Fold (
    -- * Fold0
    Fold0
  , fold0
  , failing
  , toFold0
  , fromFold0 
    -- * Fold
  , Fold
  , fold_
  , folding 
  , foldVl
  , afold
    -- * Fold1
  , Fold1
  , fold1_
  , folding1
  , fold1Vl
  , afold1
    -- * Optics
  , folded0
  , filtered
  , folded
  , folded_
  , folded1 
  , folded1_
    -- * Operators
  , (^?)
  , preview 
  , preuse
  , fits
  , lists
  , (^..)
  , nelists
  , folds
  , folds1
  , foldsa
  , foldsr
  , foldsl
  , foldsr'
  , foldsl'
  , foldsrM
  , foldslM
  , traverses_
  , concats
  , aconcats
  , mins 
  , maxes
  , sums
  , multiplies
  , endo
  , endoM
  , finds
  , exists
  , contains
    -- * Auxilliary Types
  , Nedl(..)
) where

import Control.Applicative as A
import Control.Monad (void)
import Control.Monad.Reader as Reader hiding (lift)
import Control.Monad.State as State hiding (lift)
import Data.Foldable (Foldable, traverse_)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe
import Data.Monoid
import Data.Semiring as Rng
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Combinator
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Traversal
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Prism
import Data.Profunctor.Optic.View

import Prelude (Ord,min,max)
import qualified Data.List.NonEmpty as NEL

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XRankNTypes
-- >>> import Control.Exception hiding (catches)
-- >>> import Data.Functor.Identity
-- >>> import Data.List.NonEmpty (NonEmpty(..))
-- >>> import qualified Data.List.NonEmpty as NE
-- >>> import Data.Int
-- >>> import Data.Map as Map
-- >>> import Data.Maybe
-- >>> import Data.Monoid
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- 'Fold0'
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

infixl 3 `failing`

-- | If the first 'Fold0' exists no focus then try the second one.
--
failing :: AFold0 a s a -> AFold0 a s a -> Fold0 s a
failing a b = fold0 $ \s -> maybe (preview b s) Just (preview a s)
{-# INLINE failing #-}

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

-- | Obtain a 'View' from a 'Fold0' 
--
fromFold0 ::  AFold0 a s a -> View s (Maybe a)
fromFold0 = to . preview
{-# INLINE fromFold0 #-}

---------------------------------------------------------------------
-- 'Fold'
---------------------------------------------------------------------

-- | Obtain a 'Fold' directly.
--
-- @ 
-- 'fold_' ('lists' o) ≡ o
-- 'fold_' f ≡ 'to' f . 'foldVl' 'traverse_'
-- 'fold_' f ≡ 'coercer' . 'lmap' f . 'lift' 'traverse_'
-- @
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- This can be useful to lift operations from @Data.List@ and elsewhere into a 'Fold'.
--
-- >>> [1,2,3,4] ^.. fold_ tail
-- [2,3,4]
--
fold_ :: Foldable f => (s -> f a) -> Fold s a
fold_ f = to f . foldVl traverse_
{-# INLINE fold_ #-}

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

-- | Obtain a 'Fold' from a Van Laarhoven 'Fold'.
--
foldVl :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> Fold s a
foldVl f = coercer . traversalVl f . coercer
{-# INLINE foldVl #-}

-- | TODO: Document
--
afold :: Monoid r => ((a -> r) -> s -> r) -> AFold r s a
afold = afold1
{-# INLINE afold #-}

---------------------------------------------------------------------
-- 'Fold1'
---------------------------------------------------------------------

-- | Obtain a 'Fold1' directly.
--
-- @ 
-- 'fold1_' ('nelists' o) ≡ o
-- 'fold1_' f ≡ 'to' f . 'fold1Vl' 'traverse1_'
-- 'fold1_' f ≡ 'coercer' . 'lmap' f . 'lift' 'traverse1_'
-- @
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- This can be useful to repn operations from @Data.List.NonEmpty@ and elsewhere into a 'Fold1'.
--
fold1_ :: Foldable1 f => (s -> f a) -> Fold1 s a
fold1_ f = to f . fold1Vl traverse1_
{-# INLINE fold1_ #-}

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

-- | TODO: Document
--
afold1 :: Semigroup r => ((a -> r) -> s -> r) -> AFold1 r s a
afold1 f = Star #. (Const #.) #. f .# (getConst #.) .# runStar
{-# INLINE afold1 #-}

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

-- | The canonical 'Fold0'. 
--
-- >>> [Just 1, Nothing] ^.. folded . folded0
-- [1]
--
folded0 :: Fold0 (Maybe a) a
folded0 = fold0 id
{-# INLINE folded0 #-}

-- | Filter another optic.
--
-- >>> [1..10] ^.. folded . filtered even
-- [2,4,6,8,10]
--
filtered :: (a -> Bool) -> Fold0 a a
filtered p = traversal0Vl (\point f a -> if p a then f a else point a) . coercer
{-# INLINE filtered #-}

-- | Obtain a 'Fold' from a 'Traversable' functor.
--
folded :: Traversable f => Fold (f a) a
folded = folding id
{-# INLINE folded #-}

-- | The canonical 'Fold'.
--
-- @
-- 'Data.Foldable.foldMap' ≡ 'withFold' 'folded_''
-- @
--
folded_ :: Foldable f => Fold (f a) a
folded_ = fold_ id
{-# INLINE folded_ #-}

-- | Obtain a 'Fold1' from a 'Traversable1' functor.
--
folded1 :: Traversable1 f => Fold1 (f a) a
folded1 = folding1 id
{-# INLINE folded1 #-}

-- | The canonical 'Fold1'.
--
-- @
-- 'Data.Semigroup.Foldable.foldMap1' ≡ 'withFold1' 'folded1_''
-- @
--
folded1_ :: Foldable1 f => Fold1 (f a) a
folded1_ = fold1_ id
{-# INLINE folded1_ #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

infixl 8 ^?

-- | An infix alias for 'preview''.
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
-- >>> Left 4 ^? left'
-- Just 4
-- >>> Right 4 ^? left'
-- Nothing
--
(^?) :: s -> AFold0 a s a -> Maybe a
(^?) = flip preview
{-# INLINE (^?) #-}

-- | TODO: Document
--
preview :: MonadReader s m => AFold0 a s a -> m (Maybe a)
preview o = Reader.asks $ withFold0 o Just
{-# INLINE preview #-}

-- | TODO: Document
--
preuse :: MonadState s m => AFold0 a s a -> m (Maybe a)
preuse o = State.gets $ preview o
{-# INLINE preuse #-}

-- | Check whether the optic fits.
--
-- >>> fits just Nothing
-- False
--
fits :: AFold0 a s a -> s -> Bool
fits o s = isJust (preview o s)
{-# INLINE fits #-}

-- | Collect the foci of an optic into a list.
--
lists :: AFold (Endo [a]) s a -> s -> [a]
lists o = foldsr o (:) []
{-# INLINE lists #-}

infixl 8 ^..

-- | Infix alias of 'lists'.
--
-- @
-- 'Data.Foldable.toList' xs ≡ xs '^..' 'folding'
-- ('^..') ≡ 'flip' 'lists'
-- @
--
-- >>> [[1,2], [3 :: Int64]] ^.. id
-- [[[1,2],[3]]]
-- >>> [[1,2], [3 :: Int64]] ^.. traversed
-- [[1,2],[3]]
-- >>> [[1,2], [3 :: Int64]] ^.. traversed . traversed
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
-- ('^..') :: s -> 'Traversal0'' s a    -> [a]
-- @
--
(^..) :: s -> AFold (Endo [a]) s a -> [a]
(^..) = flip lists
{-# INLINE (^..) #-}

-- | Extract a 'NonEmpty' of the foci of an optic.
--
-- >>> nelists bitraversed1 ('h' :| "ello", 'w' :| "orld")
-- ('h' :| "ello") :| ['w' :| "orld"]
--
nelists :: AFold1 (Nedl a) s a -> s -> NonEmpty a
nelists l = flip getNedl [] . withFold1 l (Nedl #. (:|))
{-# INLINE nelists #-}

-- | TODO: Document
--
folds :: Monoid a => AFold a s a -> s -> a
folds = flip withFold id
{-# INLINE folds #-}

-- | TODO: Document
--
folds1 :: Semigroup a => AFold1 a s a -> s -> a
folds1 = flip withFold1 id
{-# INLINE folds1 #-}

-- | TODO: Document
-- 
-- @
-- foldsa :: Fold s a -> s -> [a]
-- foldsa :: Applicative f => Setter s t a b -> s -> f a
-- @
--
foldsa :: Applicative f => Monoid (f a) => AFold (f a) s a -> s -> f a
foldsa = flip withFold pure
{-# INLINE foldsa #-}

-- | Right fold over an optic.
--
-- >>> foldsr folded (+) 0 [1..5::Int64]
-- 15
--
foldsr :: AFold (Endo r) s a -> (a -> r -> r) -> r -> s -> r
foldsr o f r = (`appEndo` r) . withFold o (Endo . f)
{-# INLINE foldsr #-}

-- | Left fold over an optic.
--
foldsl :: AFold ((Endo-Dual) r) s a -> (r -> a -> r) -> r -> s -> r
foldsl o f r = (`appEndo` r) . getDual . withFold o (Dual . Endo . flip f)
{-# INLINE foldsl #-}

-- | Strict right fold over an optic.
--
foldsr' :: AFold ((Endo-Dual) (Endo r)) s a -> (a -> r -> r) -> r -> s -> r
foldsr' l f z0 xs = foldsl l f' (Endo id) xs `appEndo` z0 where f' (Endo k) x = Endo $ \ z -> k $! f x z
{-# INLINE foldsr' #-}

-- | Strict left fold over an optic.
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
foldsl' :: AFold ((Endo-Endo) r) s a -> (r -> a -> r) -> r -> s -> r
foldsl' o f r s = foldsr o f' (Endo id) s `appEndo` r where f' x (Endo k) = Endo $ \z -> k $! f z x
{-# INLINE foldsl' #-}

-- | Monadic right fold over an optic.
--
foldsrM :: Monad m => AFold ((Endo-Dual) (r -> m r)) s a -> (a -> r -> m r) -> r -> s -> m r
foldsrM l f z0 xs = foldsl l f' return xs z0 where f' k x z = f x z >>= k
{-# INLINE foldsrM #-}

-- | Monadic left fold over an optic.
--
foldslM :: Monad m => AFold (Endo (r -> m r)) s a -> (r -> a -> m r) -> r -> s -> m r
foldslM o f z0 xs = foldsr o f' return xs z0 where f' x k z = f z x >>= k
{-# INLINE foldslM #-}

-- | Applicative fold over an optic.
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

-- | Map a function over the foci of an optic and concatenate the resulting lists.
--
-- >>> concats both (\x -> [x, x + 1]) (1,3)
-- [1,2,3,4]
--
-- @
-- 'concatMap' ≡ 'concats' 'folded'
-- @
--
concats :: AFold [r] s a -> (a -> [r]) -> s -> [r]
concats = withFold
{-# INLINE concats #-}

-- | The sum of a collection of actions, generalizing 'concats'.
--
-- >>> aconcats both ("hello","world")
-- "helloworld"
--
-- >>> aconcats both (Nothing, Just "hello")
-- Just "hello"
--
-- @
-- 'asum' ≡ 'aconcats' 'folded'
-- @
--
aconcats :: Alternative f => AFold ((Endo-Endo) (f a)) s (f a) -> s -> f a
aconcats o = foldsl' o (<|>) A.empty
{-# INLINE aconcats #-}

-- | Compute the minimum of the targets of a totally ordered fold. 
--
mins :: Ord a => AFold ((Endo-Endo) a) s a -> a -> s -> a
mins o = foldsl' o min

-- | Compute the maximum of the targets of a totally ordered fold.
--
maxes :: Ord a => AFold ((Endo-Endo) a) s a -> a -> s -> a
maxes o = foldsl' o max

-- | The sum of a collection.
--
sums :: (Additive-Monoid) a => AFold ((Endo-Endo) a) s a -> s -> a
sums o = foldsl' o (+) zero

-- | The product of a collection.
--
multiplies :: (Multiplicative-Monoid) a => AFold ((Endo-Endo) a) s a -> s -> a
multiplies o = foldsl' o (*) one


-- | TODO: Document
--
endo :: AFold (Endo (a -> a)) s (a -> a) -> s -> a -> a
endo o = foldsr o (.) id

-- | TODO: Document
--
endoM :: Monad m => AFold (Endo (a -> m a)) s (a -> m a) -> s -> a -> m a
endoM o = foldsr o (<=<) pure

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
finds :: AFold ((Maybe-Endo) a) s a -> (a -> Bool) -> s -> Maybe a
finds o f = foldsr o (\a y -> if f a then Just a else y) Nothing
{-# INLINE finds #-}

-- | Determine whether an optic exists at least one focus.
--
exists :: AFold (Additive Bool) s a -> s -> Bool
exists o s = unAdditive $ withFold o (const $ Additive True) s
{-# INLINE exists #-}

-- | Determine whether the targets of a `Fold` contain a given element.
--
contains :: Eq a => AFold (Additive Bool) s a -> a -> s -> Bool
contains o a s = unAdditive $ withFold o (\x -> Additive $ x == a) s
{-# INLINE contains #-}


------------------------------------------------------------------------------
-- Auxilliary Types
------------------------------------------------------------------------------

-- A non-empty difference list.
newtype Nedl a = Nedl { getNedl :: [a] -> NEL.NonEmpty a }

instance Semigroup (Nedl a) where
  Nedl f <> Nedl g = Nedl (f . NEL.toList . g)
