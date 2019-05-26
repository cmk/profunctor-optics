module Data.Profunctor.Optic.Operators (
    module Data.Profunctor.Optic.Operators
  , swap
) where

import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Type
import Data.Either.Validation

import Control.Monad.Reader as Reader
import Control.Monad.State as State


import Data.Profunctor.Unsafe
--import Control.Monad.Reader.Class as Reader








re :: Optic (Re p a b) s t a b -> Optic p b a t s
re o = (between runRe Re) o id


-- ^ @
-- over :: Setter s t a b -> (a -> r) -> s -> r
-- over :: Monoid r => Fold s t a b -> (a -> r) -> s -> r
-- @
over :: Optic (->) s t a b -> (a -> b) -> s -> t
over = id


-- ^ @
-- review :: AReview t b -> b -> t
-- @
--
review :: AReview t b -> b -> t
review o = h . Const where Costar h = o (Costar getConst)



-- | 'view o == foldMapOf o id'
view :: MonadReader s m => AGetter a s a -> m a
view o = Reader.asks $ foldMapOf o id

views :: MonadReader s m => AGetter r s a -> (a -> r) -> m r
views o f = Reader.asks $ foldMapOf o f 
{-# INLINE views #-}


-- ^ @
-- match :: Traversal s t a b -> s -> Either t a
-- @
match :: Optic (Star (Either a)) s t a b -> s -> Either t a
match o = swap . h where Star h = o (Star Left)

-- | A more restrictive variant of 'match'.
--match' :: Optic (Matched a) s t a b -> s -> Either t a
--match' o = (between Matched runMatched) o Right




previewOf :: Optic (Star (Pre a)) s t a b -> s -> Maybe a
--previewOf o = between ((runPre .) . runStar) (Star . ((Pre . Just) .)) o id
previewOf o = runPre #. h where Star h = o (Star (Pre #. Just))

foldMapOf :: Optic (Star (Const r)) s t a b -> (a -> r) -> s -> r
--foldMapOf o f = between ((getConst .) . runStar) (Star . ((Const . f) .)) o id
foldMapOf o f = getConst #. h where Star h = o (Star (Const #. f))

foldMapOf' :: Optic (Forget r) s t a b -> (a -> r) -> s -> r
foldMapOf' = between runForget Forget


-- ^ @
-- traverseOf :: Functor f => Lens s t a b -> (a -> f b) -> s -> f t
-- traverseOf :: Applicative f => Traversal s t a b -> (a -> f b) -> s -> f t
-- @
traverseOf :: Optic (Star f) s t a b -> (a -> f b) -> s -> f t
traverseOf = between runStar Star -- tf where Star tf = o (Star f)

cotraverseOf :: Optic (Costar f) s t a b -> (f a -> b) -> (f s -> t)
cotraverseOf = between runCostar Costar -- o f = tf where Costar tf = o (Costar f) -- = between Costar runCostar

validateOf
  :: Optic (Star (Validation a)) s t a b 
  -> s 
  -> Validation t a
validateOf o = swap . h where Star h = o (Star Failure)


zipWithOf :: Optic Zipped s t a b -> (a -> a -> b) -> s -> s -> t
zipWithOf = between runZipped Zipped








