module Data.Profunctor.Optic.Fold1 where

import Data.Semigroup
import Data.Profunctor.Optic.Type 
import Data.Profunctor.Optic.Operator
import Data.Profunctor.Optic.Prelude

import Data.Profunctor.Optic.View (view, to)
import Data.Profunctor.Optic.Prism (_Just, filtering)
import Data.Foldable (traverse_)
--import Data.Functor.Const (Const(..))

import Control.Monad ((<=<))
import Control.Monad.Reader as Reader
import Control.Monad.State as State

import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE


---------------------------------------------------------------------
-- 'Fold1'
---------------------------------------------------------------------


{-
 have to pick some Foldable. List is a safe choice (DList would be more efficient).

Fold1 laws:

fold_complete :: Fold1 s a -> Bool
fold_complete o = tripping o $ folding1 (toNelOf o)
-}

-- folding1 (0 :|) :: Fold1 [Int] Int
folding1 :: Foldable1 f => (s -> f a) -> Fold1 s a
folding1 f = to f . wander1 traverse1_

-- folding1' First :: Traversable1 f => Fold1 (f a) (First a)
-- folding1' Min :: Traversable1 f => Fold1 (f a) (Min a)
folding1' :: Traversable1 f => (s -> a) -> Fold1 (f s) a
folding1' f = wander1 traverse1 . to f

--cloneFold1 :: Semigroup r => Folding r s a -> Fold1 s a
--cloneFold1 f = to $ \s -> getConst (f Const s)


---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------


fold1Of :: Semigroup a => Folding a s a -> s -> a
fold1Of = flip foldMap1Of id

-- >>> foldMap1Of (folding1 (0 :|)) Min [1..10]
-- Min {getMin = 0}
foldMap1Of :: Semigroup r => Folding r s a -> (a -> r) -> s -> r
foldMap1Of = foldMapOf



-- @
-- toPureOf :: Fold s a -> s -> [a]
-- toPureOf :: (Applicative f, Monoid (f a)) => Fold s a -> s -> f a
-- toPureOf :: Applicative f => Over s t a b -> s -> f a
-- @
--toPureOf :: Applicative f => Folding (f a) s a -> s -> f a
--toPureOf o = foldMapOf o pure

-- | Collects the foci of a `Fold1` into a non-empty list.
--toNelOf :: Folding (Endo (NonEmpty a)) s a -> s -> NonEmpty a
--toNelOf o = undefined


