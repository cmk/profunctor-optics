module Data.Profunctor.Optic.Newtype (
    -- * Newtype isos
    wrapped
  , rewrapped
  , rewrapped'
    -- * Ala
  , ala
    -- * Re-exports
  , Newtype(..)
  , O
  ) where

import Control.Newtype.Generics (Newtype(..), O)
import Data.Profunctor.Optic (Iso, Iso', AIso, iso, dimap, withIso, au)
import Prelude (Functor(..), (.), ($))

-- | Obtain an 'Iso' from a newtype.
--
-- @
-- 'view' 'wrapped' f '.' f ≡ 'id'
-- f '.' 'view' 'wrapped' f ≡ 'id'
-- @
--
-- >>> view wrapped $ Identity 'x'
-- 'x'
--
-- >>> view wrapped (Const "hello")
-- "hello"
--
wrapped :: Newtype s => Iso' s (O s)
wrapped = dimap unpack pack
{-# INLINE wrapped #-}

-- | Work between newtype wrappers.
--
-- >>> Const "hello" & rewrapped ..~ length & getConst
-- 5
--
rewrapped :: Newtype s => Newtype t => Iso s t (O s) (O t)
rewrapped = withIso wrapped $ \sa _ -> withIso wrapped $ \_ bt -> iso sa bt
{-# INLINE rewrapped #-}

-- | Variant of 'rewrapped' that ignores its argument.
--
rewrapped' :: Newtype s => Newtype t => (O s -> s) -> Iso s t (O s) (O t)
rewrapped' _ = rewrapped
{-# INLINE rewrapped' #-}

-- | Based on /ala/ from Conor McBride's work on Epigram.
--
-- >>> ala Sum foldMap [1,2,3,4]
-- 10
--
-- >>> ala Any foldMap [True,False]
-- True
--
-- >>> ala Product foldMap [1,2,3,4]
-- 24
--
-- @
-- 'ala' :: 'Newtype' s => 'Newtype' t => ('O' s -> s) -> (('O' t -> t) -> e -> s) -> e -> O s
-- @
--
ala :: Newtype s => Newtype t => Functor f => (O s -> s) -> ((O t -> t) -> f s) -> f (O s)
ala = au . rewrapped'
{-# INLINE ala #-}
