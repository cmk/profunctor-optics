module Data.Profunctor.Optic.Review
  (
  -- * Reviewing
    Review
  , Reviewing
  , PrimReview
  , unto
  , un
  , relike
  , re
  , review, reviews
  --, reuse, reuses
  , (#)
  , retagged
  , reviewBoth
  , reviewEither
  ) where

--import Control.Monad.Reader
import Control.Monad.Reader as Reader

--import Data.Profunctor.Optic.View
import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Type 
import Data.Profunctor.Optic.Operator

------------------------------------------------------------------------------
-- Review
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
unto f = icoerce . dimap id f


-- | Turn a 'View' around to get a 'Review'
--
-- @
-- 'un' = 'unto' . 'view'
-- 'unto' = 'un' . 'to'
-- @
--
-- >>> un (to length) # [1,2,3]
-- 3
un :: Viewing s a -> PrimReview b a t s
un = unto . (`foldMapOf` id)


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

--cloneReview :: Reviewing b t b -> PrimReview' t b
--cloneReview = unto . review

reviewBoth :: Reviewing t1 b -> Reviewing t2 b -> PrimReview s (t1, t2) a b
reviewBoth l r = unto (review l &&& review r)

reviewEither :: Reviewing t b1 -> Reviewing t b2 -> PrimReview s t a (Either b1 b2)
reviewEither l r = unto (review l ||| review r)


---------------------------------------------------------------------
-- Derived operators
---------------------------------------------------------------------

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
(#) :: Reviewing t b -> b -> t
o # b = review o b
{-# INLINE ( # ) #-}

-- ^ @
-- 'review o ≡ unfoldMapOf o id'
-- @
--
review :: MonadReader b m => Reviewing t b -> m t
review = Reader.asks . (`unfoldMapOf` id) 
{-# INLINE review #-}

-- ^ @
-- 'reviews o f ≡ unfoldMapOf o f'
-- @
--
reviews :: MonadReader r m => Unfolding r t b -> (r -> b) -> m t
reviews o f = Reader.asks $ unfoldMapOf o f 
{-# INLINE reviews #-}

infixr 8 #


{-

-- | Turn a 'Prism' or 'Control.Lens.Iso.Iso' around to build a 'View'.
--
-- If you have an 'Control.Lens.Iso.Iso', 'Control.Lens.Iso.from' is a more powerful version of this function
-- that will return an 'Control.Lens.Iso.Iso' instead of a mere 'View'.
--
-- >>> 5 ^.re _Left
-- Left 5
--
-- >>> 6 ^.re (_Left.unto succ)
-- Left 7
--
-- @
-- 'review'  ≡ 'view'  '.' 're'
-- 'reviews' ≡ 'views' '.' 're'
-- 'reuse'   ≡ 'use'   '.' 're'
-- 'reuses'  ≡ 'uses'  '.' 're'
-- @
--
-- @
-- 're' :: 'Prism' s t a b -> 'View' b t
-- 're' :: 'Iso' s t a b   -> 'View' b t
-- @
re :: (forall r. Reviewing r t b) -> View b t
re p = to (runIdentity #. unTagged #. p .# Tagged .# Identity)
{-# INLINE re #-}

-- | This can be used to turn an 'Control.Lens.Iso.Iso' or 'Prism' around and 'view' a value (or the current environment) through it the other way.
--
-- @
-- 'review' ≡ 'view' '.' 're'
-- 'review' . 'unto' ≡ 'id'
-- @
--
-- >>> review _Left "mustard"
-- Left "mustard"
--
-- >>> review (unto succ) 5
-- 6
--
-- Usually 'review' is used in the @(->)@ 'Monad' with a 'Prism' or 'Control.Lens.Iso.Iso', in which case it may be useful to think of
-- it as having one of these more restricted type signatures:
--
-- @
-- 'review' :: 'Iso'' s a   -> a -> s
-- 'review' :: 'Prism'' s a -> a -> s
-- @
--
-- However, when working with a 'Monad' transformer stack, it is sometimes useful to be able to 'review' the current environment, in which case
-- it may be beneficial to think of it as having one of these slightly more liberal type signatures:
--
-- @
-- 'review' :: 'MonadReader' a m => 'Iso'' s a   -> m s
-- 'review' :: 'MonadReader' a m => 'Prism'' s a -> m s
-- @
review :: MonadReader b m => Reviewing t b -> m t
review p = asks (runIdentity #. unTagged #. p .# Tagged .# Identity)
{-# INLINE review #-}




-}


-- | This can be used to turn an 'Control.Lens.Iso.Iso' or 'Prism' around and 'view' a value (or the current environment) through it the other way,
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
-- Usually this function is used in the @(->)@ 'Monad' with a 'Prism' or 'Control.Lens.Iso.Iso', in which case it may be useful to think of
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
--reviews :: MonadReader b m => Reviewing t b -> (t -> r) -> m r
--reviews :: MonadReader b m => (forall r. Reviewing b t b) -> (t -> r) -> m r
--reviews :: MonadReader b m => Reviewing b t b -> (t -> r) -> m r
--reviews p tr = asks (tr . review p)
--{-# INLINE reviews #-}

