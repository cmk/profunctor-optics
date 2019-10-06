module Data.Profunctor.Optic.Fold.Semigroup where

import Data.Profunctor.Optic.Fold

import Data.Semigroup
import Data.Profunctor.Optic.Type 
import Data.Profunctor.Optic.Prelude

import Data.Profunctor.Optic.Getter (view, to)
import Data.Profunctor.Optic.Prism (_Just, filtering)
import Data.Foldable (traverse_)
--import Data.Functor.Const (Const(..))
import Control.Monad ((<=<))
import Control.Monad.Reader as Reader
import Control.Monad.State as State




{-
-- | A variant of 'foldr' that has no base case,
-- and thus may only be applied to non-empty structures.
--
-- @'Data.Foldable.foldr1' f = 'foldr1Of' 'folded'@
--
foldr1Of :: Fold1 s a -> (a -> a -> a) -> s -> a
foldr1Of f xs = fromMaybe (errorWithoutStackTrace "foldr1: empty structure") (foldr mf Nothing xs)
  where
    mf x m = Just (case m of
		 Nothing -> x
		 Just y  -> f x y)

-- | A variant of 'foldl' that has no base case,
-- and thus may only be applied to non-empty structures.
--
-- @'foldl1' f = 'List.foldl1' f . 'toList'@
foldl1Of :: (a -> a -> a) -> t a -> a
foldl1 f xs = fromMaybe (errorWithoutStackTrace "foldl1: empty structure") (foldl mf Nothing xs)
  where
    mf m y = Just (case m of
		 Nothing -> y
		 Just x  -> f x y)
-}
