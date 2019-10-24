module Data.Profunctor.Optic.Review
  (
  -- * AReview
    Review
  , AReview
  , PrimReview
  , unto
  , un
  , relike
  , re
  , review, reviews
  --, reuse, reuses
  , (#)
  , untoBoth
  , untoEither
  ) where

import Control.Monad.Reader as Reader

import Data.Profunctor.Optic.View
import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Type 

------------------------------------------------------------------------------
-- 'Review'
------------------------------------------------------------------------------


-- | Convert a function into a 'Review'.
--  Analagous to 'to' for 'View'.
--
-- @
-- 'unto' :: (b -> t) -> 'PrimReview' s t a b
-- @
--
-- @
-- 'unto' = 'un' . 'to'
-- @
--
unto :: (b -> t) -> PrimReview s t a b 
unto f = coercel . rmap f

-- | Turn a 'View' around to get a 'Review'
--
-- @
-- 'un' = 'unto' . 'view'
-- 'unto' = 'un' . 'to'
-- @
--
-- >>> un (to length) # [1,2,3]
-- 3
un :: AView s a -> PrimReview b a t s
un = unto . (`views` id)

-- | Build a constant-valued (index-preserving) 'PrimReview' from an arbitrary value.
--
-- @
-- 'relike' a '.' 'relike' b ≡ 'relike' a
-- 'relike' a '#' b ≡ a
-- 'relike' a '#' b ≡ 'unto' ('const' a) '#' b
-- @
--
relike :: t -> PrimReview s t a b
relike t = unto (const t)


-- | TODO: Document
--
untoBoth :: AReview t1 b -> AReview t2 b -> PrimReview s (t1 , t2) a b
untoBoth l r = unto (review l &&& review r)

-- | TODO: Document
--
untoEither :: AReview t b1 -> AReview t b2 -> PrimReview s t a (b1 + b2)
untoEither l r = unto (review l ||| review r)

-- | TODO: Document
--
cloneReview :: AReview t b -> PrimReview t t b b
cloneReview = unto . review


---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | This can be used to turn an 'Iso' or 'Prism' around and 'view' a value (or the current environment) through it the other way,
-- applying a function.
--
-- @
-- 'reviews' ≡ 'views' '.' 're'
-- 'reviews' ('unto' f) g ≡ g '.' f
-- @
--
-- >>> reviews _Left isRight "mustard"
-- False
--
-- >>> reviews (unto succ) (*2) 3
-- 8
--
-- Usually this function is used in the @(->)@ 'Monad' with a 'Prism' or 'Iso', in which case it may be useful to think of
-- it as having one of these more restricted type signatures:
--
-- @
-- 'reviews' :: 'Iso'' s a   -> (s -> r) -> a -> r
-- 'reviews' :: 'Prism'' s a -> (s -> r) -> a -> r
-- @
--
-- However, when working with a 'Monad' transformer stack, it is sometimes useful to be able to 'review' the current environment, in which case
-- it may be beneficial to think of it as having one of these slightly more liberal type signatures:
--
-- @
-- 'reviews' :: 'MonadReader' a m => 'Iso'' s a   -> (s -> r) -> m r
-- 'reviews' :: 'MonadReader' a m => 'Prism'' s a -> (s -> r) -> m r
-- @
-- ^ @
-- 'reviews o f ≡ cofoldMapOf o f'
-- @
--
reviews :: MonadReader r m => AUnfold r t b -> (r -> b) -> m t
reviews o f = Reader.asks $ between (dcostar Const) (ucostar getConst) o f 
{-# INLINE reviews #-}

---------------------------------------------------------------------
-- Common reviews
---------------------------------------------------------------------

-- | TODO: Document
--
coerceld :: Review b b
coerceld = coercel

-- | TODO: Document
--
_L' :: PrimReview (a + c) (b + c) a b
_L' = coercel . rmap Left

-- | TODO: Document
--
_R' :: PrimReview (c + a) (c + b) a b
_R' = coercel . rmap Right

---------------------------------------------------------------------
-- Derived operators
---------------------------------------------------------------------

infixr 8 #

-- | An infix alias for 'review'. Dual to '^.'.
--
-- @
-- 'unto' f # x ≡ f x
-- l # x ≡ x '^.' 're' l
-- @
--
-- This is commonly used when using a 'Prism' as a smart constructor.
--
-- >>> _Left # 4
-- Left 4
--
-- But it can be used for any 'Prism'
--
-- >>> base 16 # 123
-- "7b"
--
-- @
-- (#) :: 'Iso''      s a -> a -> s
-- (#) :: 'Prism''    s a -> a -> s
-- (#) :: 'Review'    s a -> a -> s
-- (#) :: 'Equality'' s a -> a -> s
-- @
--
(#) :: AReview t b -> b -> t
o # b = review o b
{-# INLINE ( # ) #-}


-- ^ @
-- 'review o ≡ unfoldMapOf o id'
-- @
--
review :: MonadReader b m => AReview t b -> m t
review = (`reviews` id) 
{-# INLINE review #-}
