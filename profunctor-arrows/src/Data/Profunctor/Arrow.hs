{-# LANGUAGE GADTs #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ExistentialQuantification #-}
module Data.Profunctor.Arrow where

import Control.Arrow (Arrow)
import Control.Category hiding ((.), id)
import Data.Profunctor
import Data.Profunctor.Extra
import Prelude
import qualified Control.Arrow as A
import qualified Control.Category as C

newtype PArrow p a b = PArrow { runPArrow :: forall x y. p (b , x) y -> p (a , x) y }

instance Profunctor p => Profunctor (PArrow p) where
  dimap f g (PArrow pp) = PArrow $ \p -> dimap (lft f) id (pp (dimap (lft g) id p))
    where lft h (a, b) = (h a, b)

instance Profunctor p => Category (PArrow p) where
  id = PArrow id

  PArrow pp . PArrow qq = PArrow $ \r -> qq (pp r)

instance Profunctor p => Strong (PArrow p) where
  first' (PArrow pp) = PArrow $ lmap assocr . pp . lmap assocl

toArrow :: Arrow a => PArrow a b c -> a b c
toArrow (PArrow aa) = A.arr (\x -> (x,())) >>> aa (A.arr fst)

fromArrow :: Arrow a => a b c -> PArrow a b c
fromArrow x = PArrow (\z -> A.first x >>> z)

-- @
-- (a '>>>' b) '>>>' c = a '>>>' (b '>>>' c)
-- 'arr' f '>>>' a = 'dimap' f id a
-- a '>>>' arr f = 'dimap' id f a
-- 'arr' (g . f) = 'arr' f '>>>' 'arr' g
-- @
--
arr :: Category p => Profunctor p => (a -> b) -> p a b
arr f = rmap f C.id

preturn :: Category p => Profunctor p => p a a
preturn = arr id

ex1 :: Category p => Profunctor p => p (a , b) b
ex1 = arr snd

ex2 :: Category p => Profunctor p => p (a , b) a
ex2 = arr fst

inl :: Category p => Profunctor p => p a (a + b)
inl = arr Left

inr :: Category p => Profunctor p => p b (a + b)
inr = arr Right

braid :: Category p => Profunctor p => p (a , b) (b , a)
braid = arr swp

braide :: Category p => Profunctor p => p (a + b) (b + a)
braide = arr eswp

loop :: Costrong p => p (a, d) (b, d) -> p a b
loop = unfirst

left :: Choice p => p a b -> p (a + c) (b + c)
left = left'

right :: Choice p => p a b -> p (c + a) (c + b)
right = right'

-- @
-- first ('arr' f) = 'arr' (f '***' id)
-- first (a '>>>' b) = first a '>>>' first b
-- @
--
first :: Strong p => p a b -> p (a , c) (b , c)
first = first'

second :: Strong p => p a b -> p (c , a) (c , b)
second = second'

returnA :: Category p => Profunctor p => p a a
returnA = C.id

infixr 3 ***

(***) :: Category p => Strong p => p a1 b1 -> p a2 b2 -> p (a1 , a2) (b1 , b2)
x *** y = first x >>> arr swp >>> first y >>> arr swp

infixr 2 +++

(+++) :: Category p => Choice p => p a1 b1 -> p a2 b2 -> p (a1 + a2) (b1 + b2)
x +++ y = left x >>> arr eswp >>> left y >>> arr eswp

infixr 3 &&&

(&&&) :: Category p => Strong p => p a b1 -> p a b2 -> p a (b1 , b2)
x &&& y = dimap fork id $ x *** y 

infixr 2 |||

(|||) :: Category p => Choice p => p a1 b -> p a2 b -> p (a1 + a2) b
x ||| y = achoose id x y

infixr 0 $$$

($$$) :: Category p => Strong p => p a (b -> c) -> p a b -> p a c
($$$) f x = dimap fork apply (f *** x)

achoose :: Category p => Choice p => (a -> (a1 + a2)) -> p a1 b -> p a2 b -> p a b
achoose f x y = dimap f join $ x +++ y

-- | Profunctor arrow equivalent of 'Data.Functor.Divisible.divide'.
--
adivide :: Category p => Strong p => (a -> (a1 , a2)) -> p a1 b -> p a2 b -> p a b
adivide f x y = dimap f fst $ x *** y

aselect :: Category p => Choice p => ((b1 + b2) -> b) -> p a b1 -> p a b2 -> p a b
aselect f x y = dimap Left f $ x +++ y

-- | Profunctor arrow equivalent of 'Data.Functor.Divisible.divided'.
--
adivided :: Category p => Strong p => p a1 b -> p a2 b -> p (a1 , a2) b
adivided = adivide id

aselected :: Category p => Choice p => p a b1 -> p a b2 -> p a (b1 + b2)
aselected = aselect id
