{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Operator (
    (&)
  , (%)
  , (#)
  , (^.)
  , (^%)
  , (#^)
  , (..~)
  , (.~)
  , (**~)
  , (*~)
  , (//~)
  , (/~)
  , (%%~)
  , (%~)
  , (##~)
  , (#~)
) where

import Data.Function
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Index

import qualified Data.Bifunctor as B

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XRankNTypes
-- >>> import Data.List.Index as LI
-- >>> import Data.Int.Instance ()
-- >>> import Data.Maybe
-- >>> import Data.Monoid
-- >>> :load Data.Profunctor.Optic
-- >>> let iat :: Int -> Ixaffine' Int [a] a; iat i = iaffine' (\s -> flip LI.ifind s $ \n _ -> n==i) (\s a -> LI.modifyAt i (const a) s) 

infixr 4 .~, ..~, *~, **~, /~, //~, %~, %%~, #~, ##~

infixl 8 ^., ^%

infixr 8 #^

-- | View the focus of an optic.
--
-- Fixity and semantics are such that subsequent field accesses can be
-- performed with ('Prelude..').
--
-- >>> ("hello","world") ^. second'
-- "world"
--
-- >>> 5 ^. to succ
-- 6
--
-- >>> import Data.Complex
-- >>> ((0, 1 :+ 2), 3) ^. first' . second' . to magnitude
-- 2.23606797749979
--
(^.) :: s -> AView s a -> a
(^.) s o = withPrimView o id s
{-# INLINE ( ^. ) #-}

-- | View the focus of an indexed optic along with its index.
--
-- >>> ("foo", 42) ^% ifirst
-- (Just (),"foo")
--
-- >>> [(0,'f'),(1,'o'),(2,'o') :: (Int, Char)] ^% iat 2 . ifirst
-- (Just 2,2)
--
-- In order to 'iview' a 'Choice' optic (e.g. 'Ixaffine', 'Ixtraversal', 'Ixfold', etc),
-- /a/ must have a 'Monoid' instance:
--
-- >>> ([] :: [Int]) ^% iat 0
-- (Nothing,0)
--
-- >>> ([1] :: [Int]) ^% iat 0
-- (Just 0,1)
--
(^%) :: Monoid i => s -> AIxview i s a -> (Maybe i, a)
(^%) s o = withPrimView o (B.first Just) . (mempty,) $ s
{-# INLINE (^%) #-}

-- | Dual to '^.'.
--
-- @
-- 'from' f #^ x ≡ f x
-- o #^ x ≡ x '^.' 're' o
-- @
--
-- This is commonly used when using a 'Prism' as a smart constructor.
--
-- >>> left' #^ 4
-- Left 4
--
(#^) :: AReview t b -> b -> t
o #^ b = withPrimReview o id b
{-# INLINE (#^) #-}

-- | Map over an optic.
--
-- >>> Just 1 & just ..~ (+1)
-- Just 2
--
-- >>> Nothing & just ..~ (+1)
-- Nothing
--
-- >>> [1,2,3] & fmapped ..~ (*10)
-- [10,20,30]
--
-- >>> (1,2) & first' ..~ (+1) 
-- (2,2)
--
-- >>> (10,20) & first' ..~ show 
-- ("10",20)
--
(..~) :: Optic (->) s t a b -> (a -> b) -> s -> t
(..~) = id
{-# INLINE (..~) #-}

-- | Set all referenced fields to the given value.
--
(.~) :: Optic (->) s t a b -> b -> s -> t
(.~) o b = o (const b)
{-# INLINE (.~) #-}

-- | Map over a representable optic.
--
(**~) :: Optic (Star f) s t a b -> (a -> f b) -> s -> f t
(**~) = withStar
{-# INLINE (**~) #-}

-- | Set the focus of a representable optic.
--
(*~) :: Optic (Star f) s t a b -> f b -> s -> f t
(*~) o b = withStar o (const b)
{-# INLINE (*~) #-}

-- | Map over a co-representable optic.
--
(//~) :: Optic (Costar f) s t a b -> (f a -> b) -> f s -> t
(//~) = withCostar
{-# INLINE (//~) #-}

-- | Set the focus of a co-representable optic.
--
(/~) :: Optic (Costar f) s t a b -> b -> f s -> t
(/~) o b = withCostar o (const b)
{-# INLINE (/~) #-}

-- | Map over an indexed optic.
--
-- See also '##~'.
--
(%%~) :: Monoid i => AIxsetter i s t a b -> (i -> a -> b) -> s -> t
(%%~) o f = withIxsetter o f mempty
{-# INLINE (%%~) #-}

-- | Set the focus of an indexed optic.
--
--  See also '#~'.
--
-- /Note/ if you're looking for the infix 'over' it is '..~'.
--
(%~) :: Monoid i => AIxsetter i s t a b -> (i -> b) -> s -> t
(%~) o = (%%~) o . (const .)
{-# INLINE (%~) #-}

-- | Map over a coindexed optic.
-- 
-- Infix variant of 'kover'.
--
--  See also '%%~'.
--
(##~) :: Monoid k => ACxsetter k s t a b -> (k -> a -> b) -> s -> t 
(##~) o f = withCxsetter o f mempty
{-# INLINE (##~) #-}

-- | Set the focus of a coindexed optic.
--
--  See also '%~'.
--
(#~) :: Monoid k => ACxsetter k s t a b -> (k -> b) -> s -> t 
(#~) o kb = o ##~ flip (const kb) 
{-# INLINE (#~) #-}
