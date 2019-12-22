{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Prelude (
    re
  , invert
  , (&)
    -- * Composition
  , (.) 
  , (%)
  , (#)
    -- * View operators
  , view
  , (^.)
  , iview
  , (^%)
  , review
  , (#^)
    -- * Setter operators
  , set
  , (.~)
  , iset
  , (%~)
  , kset
  , (#~)
  , over
  , (..~)
  , iover
  , (%%~)
  , kover
  , (##~)
  , (<>~)
  , (><~)
    -- * Fold operators
  , preview
  , (^?)
  , is
  , isnt
  , matches
  , lists
  , (^..)
  , ilists
  , ilistsFrom
  , (^%%)
  , folds
  , foldsa
  , foldsp
  , foldsr
  , ifoldsr
  , ifoldsrFrom
  , foldsl
  , ifoldsl
  , ifoldslFrom
  , foldsr'
  , ifoldsr'
  , foldsl'
  , ifoldsl'
  , foldsrM
  , ifoldsrM
  , foldslM
  , ifoldslM
  , traverses_
  , itraverses_
  , asums
  , concats
  , iconcats
  , endo
  , endoM
  , finds
  , ifinds
  , has
  , hasnt 
  , elem
  , pelem
  , joins
  , joins'
  , meets
  , meets'
  , min 
  , max 
) where

import Control.Monad (void)
import Control.Monad.Reader as Reader hiding (lift)
import Data.Bifunctor (Bifunctor(..))
import Data.Bool.Instance () -- Semigroup / Monoid / Semiring instances
import Data.Foldable (Foldable, foldMap, traverse_)
import Data.Function
import Data.Maybe
import Data.Monoid hiding (All(..), Any(..))
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.View
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Index
import Data.Profunctor.Optic.Setter
import Data.Profunctor.Optic.Fold
import Data.Profunctor.Optic.Option
import Data.Profunctor.Optic.Traversal
import Data.Profunctor.Optic.Affine
import Data.Prd (Prd, Minimal(..), Maximal(..))
import Data.Prd.Lattice (Lattice(..))
import Data.Semiring (Semiring(..), Prod(..))

import qualified Control.Applicative as A
import qualified Data.Prd as Prd
import qualified Data.Semiring as Rng
import qualified Prelude as Pre

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> import Control.Exception hiding (catches)
-- >>> import Data.Functor.Identity
-- >>> import Data.List.Optic
-- >>> import Data.Int.Instance ()
-- >>> import Data.Map as Map
-- >>> import Data.Maybe
-- >>> import Data.Monoid
-- >>> import Data.Semiring hiding (unital,nonunital,presemiring)
-- >>> import Data.Sequence as Seq hiding ((><))
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- Fold operators
---------------------------------------------------------------------

-- | The sum of a collection of actions, generalizing 'concats'.
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
asums o = foldsl' o (<|>) A.empty
{-# INLINE asums #-}

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

-- | Concatenate the results of a function of the foci of an indexed optic.
--
-- @
-- 'concats' o ≡ 'iconcats' o '.' 'const'
-- @
--
-- >>> iconcats itraversed (\i x -> [i + x, i + x + 1]) [1,2,3,4]
-- [1,2,3,4,5,6,7,8]
--
iconcats :: Monoid i => AIxfold [r] i s a -> (i -> a -> [r]) -> s -> [r]
iconcats o f = withIxfold o f mempty
{-# INLINE iconcats #-}

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
finds :: AFold (Endo (Maybe a)) s a -> (a -> Bool) -> s -> Maybe a
finds o f = foldsr o (\a y -> if f a then Just a else y) Nothing
{-# INLINE finds #-}

-- | Find the first focus of an indexed optic that satisfies a predicate, if one exists.
--
ifinds :: Monoid i => AIxfold (Endo (Maybe (i, a))) i s a -> (i -> a -> Bool) -> s -> Maybe (i, a)
ifinds o f = ifoldsr o (\i a y -> if f i a then Just (i,a) else y) Nothing
{-# INLINE ifinds #-}

-- | Determine whether an optic has at least one focus.
--
has :: AFold Any s a -> s -> Bool
has o = withFold o (const True)
{-# INLINE has #-}

-- | Determine whether an optic does not have a focus.
--
hasnt :: AFold All s a -> s -> Bool
hasnt o = foldsp o (const False)
{-# INLINE hasnt #-}

-- | Determine whether the targets of a `Fold` contain a given element.
--
elem :: Eq a => AFold Any s a -> a -> s -> Bool
elem o a = withFold o (== a)

-- | Determine whether the foci of an optic contain an element equivalent to a given element.
--
pelem :: Prd a => AFold Any s a -> a -> s -> Bool
pelem o a = withFold o (Prd.=~ a)
{-# INLINE pelem #-}

-- | Compute the minimum of the targets of a totally ordered fold. 
--
min :: Ord a => AFold (Endo (Endo a)) s a -> a -> s -> a
min o = foldsl' o Pre.min

-- | Compute the maximum of the targets of a totally ordered fold.
--
max :: Ord a => AFold (Endo (Endo a)) s a -> a -> s -> a
max o = foldsl' o Pre.max

-- | Compute the join of the foci of an optic. 
--
joins :: Lattice a => AFold (Endo (Endo a)) s a -> a -> s -> a
joins o = foldsl' o (\/)
{-# INLINE joins #-}

-- | Compute the join of the foci of an optic including a least element.
--
joins' :: Lattice a => Minimal a => AFold (Endo (Endo a)) s a -> s -> a
joins' o = joins o minimal
{-# INLINE joins' #-}

-- | Compute the meet of the foci of an optic .
--
meets :: Lattice a => AFold (Endo (Endo a)) s a -> a -> s -> a
meets o = foldsl' o (/\)
{-# INLINE meets #-}

-- | Compute the meet of the foci of an optic including a greatest element.
--
meets' :: Lattice a => Maximal a => AFold (Endo (Endo a)) s a -> s -> a
meets' o = meets o maximal
{-# INLINE meets' #-}
