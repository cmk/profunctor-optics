module Data.Profunctor.Arrow where

import Control.Applicative (liftA2)
import Control.Category
import Control.Comonad (Comonad(..))
import Control.Monad (join)
import Data.Profunctor
import Data.Profunctor.Choice
import Data.Profunctor.Sieve
import Data.Profunctor.Strong
import Data.Void

import Prelude hiding ((.), id)

type (+) = Either
infixr 5 +

rgt :: (a -> b) -> Either a b -> b
rgt f = either f id
 
rgt' :: Either Void b -> b
rgt' = rgt absurd 

lft :: (b -> a) -> Either a b -> a
lft f = either id f

lft' :: Either a Void -> a
lft' = lft absurd

dup :: a -> (a , a)
dup = join (,)

dedup :: (a + a) -> a
dedup = join either id

swp :: (a1 , a2) -> (a2 , a1)
swp = snd &&& fst

coswp :: (a1 + a2) -> (a2 + a1)
coswp = Right ||| Left

apply :: (a , a -> b) -> b
apply = uncurry $ flip id

eval :: (b -> a , b) -> a
eval = uncurry id

coeval :: b -> (b -> a) + a -> a
coeval b = either ($ b) id

fstrong :: Functor f => f a -> b -> f (a , b)
fstrong f b = fmap (,b) f

fcostrong :: Traversable f => f (a + b) -> (f a) + b
fcostrong = coswp . traverse coswp

infixl 1 <-<
infixr 1 >->

(>->) :: Profunctor p => p a b -> (b -> c) -> p a c
(>->) = flip rmap

(<-<) :: Profunctor p => (a -> b) -> p b c -> p a c
(<-<) = lmap

lconst :: Profunctor p => b -> p b c -> p a c
lconst = lmap . const

rconst :: Profunctor p => c -> p a b -> p a c
rconst = rmap . const

shiftl :: Profunctor p => p (a + b) c -> p b (c + d)
shiftl = dimap Right Left

shiftr :: Profunctor p => p b (c , d) -> p (a , b) c
shiftr = dimap snd fst

strong :: Strong p => (a -> b -> c) -> p a b -> p a c
strong f = dimap dup (uncurry f) . second'

costrong :: Costrong p => ((a , b) -> c) -> p c a -> p b a
costrong f = unsecond . dimap f dup

choice :: Choice p => (c -> (a + b)) -> p b a -> p c a
choice f = dimap f dedup . right'

cochoice :: Cochoice p => (c -> (a + b)) -> p a c -> p a b
cochoice f = unright . dimap dedup f

pull :: Strong p => p a b -> p a (a , b)
pull = lmap dup . second'

papply :: Strong p => p a (a -> b) -> p a b
papply = rmap apply . pull

loop :: Costrong p => p (a , c) (b , c) -> p a b
loop = unfirst

arr :: Category p => Profunctor p => (a -> b) -> p a b
arr f = dimap id f id

unarr :: Comonad w => Sieve p w => p a b -> a -> b 
unarr = (extract .) . sieve

returnA :: Category p => Profunctor p => p a a
returnA = arr id

ex1 :: Category p => Profunctor p => p (a , b) b
ex1 = arr snd

ex2 :: Category p => Profunctor p => p (a , b) a
ex2 = arr fst

inl :: Category p => Profunctor p => p a (a + b)
inl = arr Left

inr :: Category p => Profunctor p => p b (a + b)
inr = arr Right

diag :: Category p => Profunctor p => p a (a , a)
diag = arr dup

codiag :: Category p => Profunctor p => p (b + b) b
codiag = arr dedup

infixr 3 ***

(***) :: Category p => Strong p => p a1 b1 -> p a2 b2 -> p (a1 , a2) (b1 , b2)
x *** y = first' x >>> arr swp >>> first' y >>> arr swp

infixr 2 +++

(+++) :: Category p => Choice p => p a1 b1 -> p a2 b2 -> p (a1 + a2) (b1 + b2)
x +++ y = left' x >>> arr coswp >>> left' y >>> arr coswp

infixr 3 &&&

(&&&) :: Category p => Strong p => p a b1 -> p a b2 -> p a (b1 , b2)
x &&& y = pliftA2 id x y

infixr 2 |||

(|||) :: Category p => Choice p => p a1 b -> p a2 b -> p (a1 + a2) b
x ||| y = pchoose id x y

infixr 0 $$$

($$$) :: Category p => Strong p => p a (b -> c) -> p a b -> p a c
($$$) f x = dimap dup eval (f *** x)

pliftA2 :: Category p => Strong p => ((b1 , b2) -> b) -> p a b1 -> p a b2 -> p a b
pliftA2 f x y = dimap dup f $ x *** y

pdivide :: Category p => Strong p => (a -> (a1 , a2)) -> p a1 b -> p a2 b -> p a b
pdivide f x y = dimap f fst $ x *** y

pselect :: Category p => Choice p => ((b1 + b2) -> b) -> p a b1 -> p a b2 -> p a b
pselect f x y = dimap Left f $ x +++ y

pchoose :: Category p => Choice p => (a -> (a1 + a2)) -> p a1 b -> p a2 b -> p a b
pchoose f x y = dimap f dedup $ x +++ y

pdivided :: Category p => Strong p => p a1 b -> p a2 b -> p (a1, a2) b
pdivided = pdivide id
