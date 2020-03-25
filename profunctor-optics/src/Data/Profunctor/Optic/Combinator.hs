{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Combinator (
    -- * Operations on arbitrary profunctors
    constl
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
  , represent
  , corepresent
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
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Import

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XRankNTypes
-- >>> import Data.Function ((&))
-- >>> :load Data.Profunctor.Optic

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

represent :: Representable p => ((a -> Rep p b) -> s -> Rep p t) -> p a b -> p s t
represent f = tabulate . f . sieve
{-# INLINE represent #-}

corepresent :: Corepresentable p => ((Corep p a -> b) -> Corep p s -> t) -> p a b -> p s t
corepresent f = cotabulate . f . cosieve
{-# INLINE corepresent #-}

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
