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

dup :: a -> (a , a)
dup = join (,)

dedup :: (a + a) -> a
dedup = join either id

swp :: (a₁ , a₂) -> (a₂ , a₁)
swp = snd &&& fst

coswp :: (a₁ + a₂) -> (a₂ + a₁)
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

lconst :: Profunctor p => b -> p b c -> p a c
lconst = lmap . const

rconst :: Profunctor p => c -> p a b -> p a c
rconst = rmap . const

select :: Category p => Choice p => p (a + (b, b -> a)) a
select = id ||| arr apply

diag :: Category p => Profunctor p => p a (a , a)
diag = arr dup

codiag :: Category p => Profunctor p => p (b + b) b
codiag = arr dedup

strong :: Strong p => ((a , b) -> c) -> p a b -> p a c
strong f = dimap dup f . second'

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

infixr 3 ***

(***) :: Category p => Strong p => p a₁ b₁ -> p a₂ b₂ -> p (a₁ , a₂) (b₁ , b₂)
x *** y = first' x >>> arr swp >>> first' y >>> arr swp

infixr 2 +++

(+++) :: Category p => Choice p => p a₁ b₁ -> p a₂ b₂ -> p (a₁ + a₂) (b₁ + b₂)
x +++ y = left' x >>> arr coswp >>> left' y >>> arr coswp

infixr 3 &&&

(&&&) :: Category p => Strong p => p a b₁ -> p a b₂ -> p a (b₁ , b₂)
x &&& y = pliftA2 id x y

infixr 2 |||

(|||) :: Category p => Choice p => p a₁ b -> p a₂ b -> p (a₁ + a₂) b
x ||| y = pchoose id x y

infixr 0 $$$

($$$) :: Category p => Strong p => p a (b -> c) -> p a b -> p a c
($$$) f x = dimap dup eval (f *** x)

pliftA2 :: Category p => Strong p => ((b₁ , b₂) -> b) -> p a b₁ -> p a b₂ -> p a b
pliftA2 f x y = dimap dup f $ x *** y

pdivide :: Category p => Strong p => (a -> (a₁ , a₂)) -> p a₁ b -> p a₂ b -> p a b
pdivide f x y = dimap f fst $ x *** y

pchoose :: Category p => Choice p => (a -> (a₁ + a₂)) -> p a₁ b -> p a₂ b -> p a b
pchoose f x y = dimap f dedup $ x +++ y

pselect :: Category p => Choice p => ((b₁ + b₂) -> b) -> p a b₁ -> p a b₂ -> p a b
pselect f x y = dimap Left f $ x +++ y

pdivided :: Category p => Strong p => p a₁ b -> p a₂ b -> p (a₁, a₂) b
pdivided = pdivide id
