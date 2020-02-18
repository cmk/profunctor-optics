module Data.Profunctor.Extra (
    type (+)
  , rgt
  , rgt'
  , lft
  , lft'
  , swap
  , eswap
  , fork
  , join
  , eval
  , apply
  , coeval 
  , branch
  , branch'
  , assocl
  , assocr
  , assocl' 
  , assocr'
  , eassocl
  , eassocr
  , eassocr'
  , forget1
  , forget2
  , forgetl
  , forgetr
  , unarr
  , peval 
  , constl
  , constr
  , shiftl
  , shiftr
  , coercel 
  , coercer
  , coercel'
  , coercer'
  , strong 
  , costrong
  , choice
  , cochoice
  , pull
  , repn
  , corepn
  , star
  , toStar
  , fromStar 
  , costar
  , uncostar
  , toCostar
  , fromCostar
  , pushr
  , pushl 
  , pliftA
  , pdivide
  , pappend
  , (<<*>>)
  , (****)
  , (&&&&)
) where

import Control.Applicative (liftA2)
import Control.Arrow ((|||),(&&&))
import Control.Category (Category)
import Control.Comonad (Comonad(..))
import Data.Bifunctor
import Data.Functor.Contravariant
import Data.Profunctor
import Data.Profunctor.Rep
import Data.Profunctor.Sieve
import Data.Tuple (swap)
import Data.Void
import Test.Logic
import Prelude
import qualified Control.Category as C (id)
import qualified Control.Monad as M (join)

coeval :: b -> (b -> a) + a -> a
coeval b = either ($ b) id
{-# INLINE coeval #-}

branch :: (a -> Bool) -> b -> c -> a -> b + c
branch f y z x = if f x then Right z else Left y
{-# INLINE branch #-}

branch' :: (a -> Bool) -> a -> a + a
branch' f x = branch f x x x
{-# INLINE branch' #-}

assocl :: (a , (b , c)) -> ((a , b) , c)
assocl (a, (b, c)) = ((a, b), c)
{-# INLINE assocl #-}

assocr :: ((a , b) , c) -> (a , (b , c))
assocr ((a, b), c) = (a, (b, c))
{-# INLINE assocr #-}

assocl' :: (a , b + c) -> (a , b) + c
assocl' = eswap . traverse eswap
{-# INLINE assocl' #-}

assocr' :: (a + b , c) -> a + (b , c)
assocr' (f, b) = fmap (,b) f
{-# INLINE assocr' #-}

eassocl :: a + (b + c) -> (a + b) + c
eassocl (Left a)          = Left (Left a)
eassocl (Right (Left b))  = Left (Right b)
eassocl (Right (Right c)) = Right c
{-# INLINE eassocl #-}

eassocr :: (a + b) + c -> a + (b + c)
eassocr (Left (Left a))  = Left a
eassocr (Left (Right b)) = Right (Left b)
eassocr (Right c)        = Right (Right c)
{-# INLINE eassocr #-}

eassocr' :: (a -> b) + c -> a -> b + c
eassocr' abc a = either (\ab -> Left $ ab a) Right abc
{-# INLINE eassocr' #-}

forget1 :: ((c, a) -> (c, b)) -> a -> b
forget1 f a = b where (c, b) = f (c, a)
{-# INLINE forget1 #-}

forget2 :: ((a, c) -> (b, c)) -> a -> b
forget2 f a = b where (b, c) = f (a, c)
{-# INLINE forget2 #-}

forgetl :: (c + a -> c + b) -> a -> b
forgetl f = go . Right where go = either (go . Left) id . f
{-# INLINE forgetl #-}

forgetr :: (a + c -> b + c) -> a -> b
forgetr f = go . Left where go = either id (go . Right) . f
{-# INLINE forgetr #-}

unarr :: Comonad w => Sieve p w => p a b -> a -> b 
unarr = (extract .) . sieve
{-# INLINE unarr #-}

peval :: Strong p => p a (a -> b) -> p a b
peval = rmap eval . pull
{-# INLINE peval #-}

constl :: Profunctor p => b -> p b c -> p a c
constl = lmap . const
{-# INLINE constl #-}

constr :: Profunctor p => c -> p a b -> p a c
constr = rmap . const
{-# INLINE constr #-}

shiftl :: Profunctor p => p (a + b) c -> p b (c + d)
shiftl = dimap Right Left
{-# INLINE shiftl #-}

shiftr :: Profunctor p => p b (c , d) -> p (a , b) c
shiftr = dimap snd fst
{-# INLINE shiftr #-}

coercel :: Profunctor p => Bifunctor p => p a b -> p c b
coercel = first absurd . lmap absurd
{-# INLINE coercel #-}

coercer :: Profunctor p => Contravariant (p a) => p a b -> p a c
coercer = rmap absurd . contramap absurd
{-# INLINE coercer #-}

coercel' :: Corepresentable p => Contravariant (Corep p) => p a b -> p c b
coercel' = corepn (. phantom)
{-# INLINE coercel' #-}

coercer' :: Representable p => Contravariant (Rep p) => p a b -> p a c
coercer' = repn (phantom .)
{-# INLINE coercer' #-}

strong :: Strong p => ((a , b) -> c) -> p a b -> p a c
strong f = dimap fork f . second'
{-# INLINE strong #-}

costrong :: Costrong p => ((a , b) -> c) -> p c a -> p b a
costrong f = unsecond . dimap f fork
{-# INLINE costrong #-}

choice :: Choice p => (c -> (a + b)) -> p b a -> p c a
choice f = dimap f join . right'
{-# INLINE choice #-}

cochoice :: Cochoice p => (c -> (a + b)) -> p a c -> p a b
cochoice f = unright . dimap join f
{-# INLINE cochoice #-}

pull :: Strong p => p a b -> p a (a , b)
pull = lmap fork . second'
{-# INLINE pull #-}

repn :: Representable p => ((a -> Rep p b) -> s -> Rep p t) -> p a b -> p s t
repn f = tabulate . f . sieve
{-# INLINE repn #-}

corepn :: Corepresentable p => ((Corep p a -> b) -> Corep p s -> t) -> p a b -> p s t
corepn f = cotabulate . f . cosieve
{-# INLINE corepn #-}

star :: Applicative f => Star f a a
star = Star pure
{-# INLINE star #-}

toStar :: Sieve p f => p d c -> Star f d c
toStar = Star . sieve
{-# INLINE toStar #-}

fromStar :: Representable p => Star (Rep p) a b -> p a b
fromStar = tabulate . runStar
{-# INLINE fromStar #-}

costar :: Foldable f => Monoid b => (a -> b) -> Costar f a b
costar f = Costar (foldMap f)
{-# INLINE costar #-}

uncostar :: Applicative f => Costar f a b -> a -> b
uncostar f = runCostar f . pure
{-# INLINE uncostar #-}

toCostar :: Cosieve p f => p a b -> Costar f a b
toCostar = Costar . cosieve
{-# INLINE toCostar #-}

fromCostar :: Corepresentable p => Costar (Corep p) a b -> p a b
fromCostar = cotabulate . runCostar
{-# INLINE fromCostar #-}

pushr :: Closed p => Representable p => Applicative (Rep p) => p (a , b) c -> p a b -> p a c
pushr = (<<*>>) . curry' 
{-# INLINE pushr #-}

pushl :: Closed p => Representable p => Applicative (Rep p) => p a c -> p b c -> p a (b -> c)
pushl p q = curry' $ pdivide id p q
{-# INLINE pushl #-}

pliftA :: Representable p => Applicative (Rep p) => (b -> c -> d) -> p a b -> p a c -> p a d
pliftA f x y = tabulate $ \s -> liftA2 f (sieve x s) (sieve y s)
{-# INLINE pliftA #-}

infixl 4 <<*>>

(<<*>>) :: Representable p => Applicative (Rep p) => p a (b -> c) -> p a b -> p a c
(<<*>>) = pliftA ($)
{-# INLINE (<<*>>) #-}

infixr 3 ****

(****) :: Representable p => Applicative (Rep p) => p a1 b1 -> p a2 b2 -> p (a1 , a2) (b1 , b2)
p **** q = dimap fst (,) p <<*>> lmap snd q
{-# INLINE (****) #-}

infixr 3 &&&&

(&&&&) ::  Representable p => Applicative (Rep p) => p a b1 -> p a b2 -> p a (b1 , b2)
p &&&& q = pliftA (,) p q
{-# INLINE (&&&&) #-}

pdivide :: Representable p => Applicative (Rep p) => (a -> (a1 , a2)) -> p a1 b -> p a2 b -> p a b
pdivide f p q = dimap f fst $ dimap fst (,) p <<*>> lmap snd q
{-# INLINE pdivide #-}

pappend :: Representable p => Applicative (Rep p) => p a b -> p a b -> p a b
pappend = pdivide fork
{-# INLINE pappend #-}
