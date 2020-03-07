{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Combinator (
    type (+)
  , (&)
    -- * Operations on (->) profunctors
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
  , branch
  , branch'
  , assocl
  , assocr
  , assocl' 
  , assocr'
  , eassocl
  , eassocr
    -- * Operations on arbitrary profunctors
  , constl
  , constr
  , shiftl
  , shiftr
  , coercel 
  , coercer
    -- * Operations on (co)-strong profunctors
  , strong 
  , costrong
  , choice
  , cochoice
  , pull
  , peval 
  , pushl
  , pushr 
    -- * Operations on (co)-representable profunctors
  , star
  , costar
  , unstar
  , uncostar
  , sieve'
  , cosieve'
  , tabulate' 
  , cotabulate'
  , repn
  , corepn
  , pure'
  , copure'
  , pappend
  , liftR2
    -- * Arrow-style combinators
  , (<<*>>)
  , (****)
  , (++++)
  , (&&&&)
  , (||||)
    -- * Divisible-style combinators
  , divide
  , divide'
  , codivide
  , codivide'
  , choose
  , choose'
  , cochoose
  , cochoose'
) where

import Data.Function
import Data.Profunctor.Closed
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Import

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

{-
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
-}

---------------------------------------------------------------------
-- Operations on arbitrary profunctors
---------------------------------------------------------------------

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

coercel :: Profunctor p => CoerceL p => p a b -> p c b
coercel = first absurd . lmap absurd
{-# INLINE coercel #-}

coercer :: Profunctor p => CoerceR p => p a b -> p a c
coercer = rmap absurd . contramap absurd
{-# INLINE coercer #-}

---------------------------------------------------------------------
-- Operations on (co)-strong profunctors
---------------------------------------------------------------------

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

peval :: Strong p => p a (a -> b) -> p a b
peval = rmap eval . pull
{-# INLINE peval #-}

pushl :: Closed p => Traversing1 p => p a c -> p b c -> p a (b -> c)
pushl p q = curry' $ divide id p q
{-# INLINE pushl #-}

pushr :: Closed p => Traversing1 p => p (a , b) c -> p a b -> p a c
pushr = (<<*>>) . curry' 
{-# INLINE pushr #-}

---------------------------------------------------------------------
-- Operations on (co)-representable profunctors
---------------------------------------------------------------------

star :: Applicative f => Star f a a
star = Star pure
{-# INLINE star #-}

costar :: Coapplicative f => Costar f a a
costar = Costar copure
{-# INLINE costar #-}

unstar :: Coapplicative f => Star f a b -> a -> b
unstar f = copure . runStar f
{-# INLINE unstar #-}

uncostar :: Applicative f => Costar f a b -> a -> b
uncostar f = runCostar f . pure
{-# INLINE uncostar #-}

sieve' :: Sieve p f => p d c -> Star f d c
sieve' = Star . sieve
{-# INLINE sieve' #-}

cosieve' :: Cosieve p f => p a b -> Costar f a b
cosieve' = Costar . cosieve
{-# INLINE cosieve' #-}

tabulate' :: Representable p => Star (Rep p) a b -> p a b
tabulate' = tabulate . runStar
{-# INLINE tabulate' #-}

cotabulate' :: Corepresentable p => Costar (Corep p) a b -> p a b
cotabulate' = cotabulate . runCostar
{-# INLINE cotabulate' #-}

repn :: Representable p => ((a -> Rep p b) -> s -> Rep p t) -> p a b -> p s t
repn f = tabulate . f . sieve
{-# INLINE repn #-}

corepn :: Corepresentable p => ((Corep p a -> b) -> Corep p s -> t) -> p a b -> p s t
corepn f = cotabulate . f . cosieve
{-# INLINE corepn #-}

pure' :: Traversing p => (a -> b) -> p a b 
pure' = tabulate . (pure .)
{-# INLINE pure' #-}

copure' :: Cotraversing p => (a -> b) -> p a b
copure' = cotabulate . (. copure)
{-# INLINE copure' #-}

pappend :: Traversing1 p => p a b -> p a b -> p a b
pappend = divide fork
{-# INLINE pappend #-}

liftR2 :: Traversing1 p => (b -> c -> d) -> p a b -> p a c -> p a d
liftR2 f x y = tabulate $ \s -> liftF2 f (sieve x s) (sieve y s)
{-# INLINE liftR2 #-}

---------------------------------------------------------------------
-- Arrow-style combinators
---------------------------------------------------------------------

infixl 4 <<*>>

-- | Profunctor version of '<*>'.
--
(<<*>>) :: Traversing1 p => p a (b -> c) -> p a b -> p a c
(<<*>>) = liftR2 ($)
{-# INLINE (<<*>>) #-}

infixr 3 ****

-- | Profunctor version of '***'.
--
(****) :: Traversing1 p => p a1 b1 -> p a2 b2 -> p (a1 , a2) (b1 , b2)
p **** q = dimap fst (,) p <<*>> lmap snd q
{-# INLINE (****) #-}

infixr 2 ++++

-- | Profunctor version of '+++'.
--
(++++) :: Cotraversing1 p => p a1 b1 -> p a2 b2 -> p (a1 + a2) (b1 + b2)
p ++++ q = cotabulate $ bimap (cosieve p) (cosieve q) . coapply
{-# INLINE (++++) #-}

infixr 3 &&&&

-- | Profunctor version of '&&&'.
--
(&&&&) ::  Traversing1 p => p a b1 -> p a b2 -> p a (b1 , b2)
p &&&& q = liftR2 (,) p q
{-# INLINE (&&&&) #-}

infixr 2 ||||

-- | Profunctor version of '|||'.
--
(||||) :: Cotraversing1 p => p a1 b -> p a2 b -> p (a1 + a2) b
p |||| q = cotabulate $ either (cosieve p) (cosieve q) . coapply
{-# INLINE (||||) #-}

---------------------------------------------------------------------
-- Divisible-style combinators
---------------------------------------------------------------------

-- | Profunctor version of < hackage.haskell.org/package/contravariant/docs/Data-Functor-Contravariant-Divisible.html#v:divide divide >.
--
divide :: Traversing1 p => (a -> (a1 , a2)) -> p a1 b -> p a2 b -> p a b
divide f p q = dimap f fst $ p **** q
{-# INLINE divide #-}

divide' :: Traversing1 p => p a1 b -> p a2 b -> p (a1 , a2) b
divide' = divide id
{-# INLINE divide' #-}

codivide :: Cotraversing1 p => ((b1 + b2) -> b) -> p a b1 -> p a b2 -> p a b
codivide f p q = dimap Left f $ p ++++ q
{-# INLINE codivide #-}

codivide' :: Cotraversing1 p => p a b1 -> p a b2 -> p a (b1 + b2)
codivide' = codivide id
{-# INLINE codivide' #-}

-- | Profunctor version of < hackage.haskell.org/package/contravariant/docs/Data-Functor-Contravariant-Divisible.html#v:choose choose >.
--
choose :: Cotraversing1 p => (a -> (a1 + a2)) -> p a1 b -> p a2 b -> p a b 
choose f p q = dimap f join $ p ++++ q
{-# INLINE choose #-}

choose' :: Cotraversing1 p => p a1 b -> p a2 b -> p (a1 + a2) b 
choose' = choose id
{-# INLINE choose' #-}

cochoose :: Traversing1 p => ((b1 , b2) -> b) -> p a b1 -> p a b2 -> p a b
cochoose f p q = dimap fork f $ p **** q
{-# INLINE cochoose #-}

cochoose' :: Traversing1 p => p a b1 -> p a b2 -> p a (b1, b2)
cochoose' = cochoose id
{-# INLINE cochoose' #-}
