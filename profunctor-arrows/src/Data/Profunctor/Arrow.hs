{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}
module Data.Profunctor.Arrow (
    arr
  , ex1
  , ex2
  , inl
  , inr
  , braid
  , ebraid
  , loop
  , left
  , right
  , first
  , second
  , returnA
  , (***)
  , (+++)
  , (&&&)
  , (|||)
  , ($$$)
  , adivide
  , adivide'
  , adivided
  , aselect
  , aselect'
  , aselected
) where

import Control.Category hiding ((.), id)
import Data.Profunctor
import Data.Profunctor.Extra
import Prelude
import qualified Control.Category as C

-- | Lift a function into a profunctor arrow.
--
-- Usable w/ arrow syntax w/ the /Arrows/ & /RebindableSyntax/ extensions.
--
-- @
-- (a '>>>' b) '>>>' c = a '>>>' (b '>>>' c)
-- 'arr' f '>>>' a = 'dimap' f id a
-- a '>>>' arr f = 'dimap' id f a
-- 'arr' (g . f) = 'arr' f '>>>' 'arr' g
-- @
--
arr :: Category p => Profunctor p => (a -> b) -> p a b
arr f = rmap f C.id
{-# INLINE arr #-}

ex1 :: Category p => Profunctor p => p (a , b) b
ex1 = arr snd
{-# INLINE ex1 #-}

ex2 :: Category p => Profunctor p => p (a , b) a
ex2 = arr fst
{-# INLINE ex2 #-}

inl :: Category p => Profunctor p => p a (a + b)
inl = arr Left
{-# INLINE inl #-}

inr :: Category p => Profunctor p => p b (a + b)
inr = arr Right
{-# INLINE inr #-}

braid :: Category p => Profunctor p => p (a , b) (b , a)
braid = arr swap
{-# INLINE braid #-}

ebraid :: Category p => Profunctor p => p (a + b) (b + a)
ebraid = arr eswap
{-# INLINE ebraid #-}

loop :: Costrong p => p (a, d) (b, d) -> p a b
loop = unfirst
{-# INLINE loop #-}

left :: Choice p => p a b -> p (a + c) (b + c)
left = left'
{-# INLINE left #-}

right :: Choice p => p a b -> p (c + a) (c + b)
right = right'
{-# INLINE right #-}

-- @
-- first ('arr' f) = 'arr' (f '***' id)
-- first (a '>>>' b) = first a '>>>' first b
-- @
--
first :: Strong p => p a b -> p (a , c) (b , c)
first = first'
{-# INLINE first #-}

second :: Strong p => p a b -> p (c , a) (c , b)
second = second'
{-# INLINE second #-}

returnA :: Category p => Profunctor p => p a a
returnA = C.id
{-# INLINE returnA #-}

infixr 3 ***

(***) :: Category p => Strong p => p a1 b1 -> p a2 b2 -> p (a1 , a2) (b1 , b2)
x *** y = first x >>> arr swap >>> first y >>> arr swap
{-# INLINE (***) #-}

infixr 2 +++

(+++) :: Category p => Choice p => p a1 b1 -> p a2 b2 -> p (a1 + a2) (b1 + b2)
x +++ y = left x >>> arr eswap >>> left y >>> arr eswap
{-# INLINE (+++) #-}

infixr 3 &&&

(&&&) :: Category p => Strong p => p a b1 -> p a b2 -> p a (b1 , b2)
x &&& y = dimap fork id $ x *** y 
{-# INLINE (&&&) #-}

infixr 2 |||

(|||) :: Category p => Choice p => p a1 b -> p a2 b -> p (a1 + a2) b
x ||| y = dimap id join $ x +++ y
{-# INLINE (|||) #-}

infixr 0 $$$

($$$) :: Category p => Strong p => p a (b -> c) -> p a b -> p a c
($$$) f x = dimap fork apply (f *** x)
{-# INLINE ($$$) #-}

adivide :: Category p => Strong p => (a -> (a1 , a2)) -> p a1 b -> p a2 b -> p a b
adivide f x y = dimap f fst $ x *** y
{-# INLINE adivide #-}

adivide' :: Category p => Strong p => p a b -> p a b -> p a b
adivide' = adivide fork
{-# INLINE adivide' #-}

adivided :: Category p => Strong p => p a1 b -> p a2 b -> p (a1 , a2) b
adivided = adivide id
{-# INLINE adivided #-}

aselect :: Category p => Choice p => ((b1 + b2) -> b) -> p a b1 -> p a b2 -> p a b
aselect f x y = dimap Left f $ x +++ y
{-# INLINE aselect #-}

aselect' :: Category p => Choice p => p a b -> p a b -> p a b
aselect' = aselect join
{-# INLINE aselect' #-}

aselected :: Category p => Choice p => p a b1 -> p a b2 -> p a (b1 + b2)
aselected = aselect id
{-# INLINE aselected #-}
