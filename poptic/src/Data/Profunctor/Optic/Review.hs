module Data.Profunctor.Optic.Review
  (
  -- * Reviewing
    Review
  , AReview
  , PrimReview
  , unto
  , un
  , re
  , review --, reviews
  --, reuse, reuses
  --, ( # )
  --, retagged
  , Reviewing
  ) where


--import Data.Profunctor.Optic.Getter
import Data.Profunctor.Optic.Types -- (APrism, APrism', Prism, Prism', Review, under)
import Data.Profunctor.Optic.Operators
import Data.Tagged
------------------------------------------------------------------------------
-- Review
------------------------------------------------------------------------------

{- | Convert a function into a 'Review'.
--  Analagous to 'to' for 'Getter'.
--
-- @
-- 'unto' :: (b -> t) -> 'PrimReview' s t a b
-- @
--
-- @
-- 'unto' = 'un' . 'to'
-- @
-}
unto :: (b -> t) -> PrimReview s t a b 
unto f = icoerce . rmap f


-- | Turn a 'Getter' around to get a 'Review'
--
-- @
-- 'un' = 'unto' . 'view'
-- 'unto' = 'un' . 'to'
-- @
--
-- >>> un (to length) # [1,2,3]
-- 3
--un :: Optic (Forget a) s t a b -> Review a s --Optic p a a s s
un o = unto . foldMapOf o id

{-

-- | Turn a 'Prism' or 'Control.Lens.Iso.Iso' around to build a 'Getter'.
--
-- If you have an 'Control.Lens.Iso.Iso', 'Control.Lens.Iso.from' is a more powerful version of this function
-- that will return an 'Control.Lens.Iso.Iso' instead of a mere 'Getter'.
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
-- 're' :: 'Prism' s t a b -> 'Getter' b t
-- 're' :: 'Iso' s t a b   -> 'Getter' b t
-- @
re :: AReview t b -> Getter b t
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
review :: MonadReader b m => AReview t b -> m t
review p = asks (runIdentity #. unTagged #. p .# Tagged .# Identity)
{-# INLINE review #-}


infixr 8 #

-- | An infix alias for 'review'.
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
( # ) :: AReview t b -> b -> t
( # ) p = runIdentity #. unTagged #. p .# Tagged .# Identity
{-# INLINE ( # ) #-}

-}
