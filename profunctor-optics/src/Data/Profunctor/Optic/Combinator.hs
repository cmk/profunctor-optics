{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Combinator (
    -- * Constructors
    parr
  , coarr
  , star
  , costar
  , unstar
  , uncostar
    -- * Miscellaneous optics
  , constl
  , constr
  , shiftl
  , shiftr
  , coercel 
  , coercer
  , represent
  , corepresent
    -- * Operations on representable profunctors
  , (.)
  , (.~)
  , (..~)
  , over
  , (*~)
  , (**~)
  , reps
  , (/~)
  , (//~)
  , coreps
    -- * Arrow-style combinators
  , (<<*>>)
  , (****)
  , (++++)
  , (&&&&)
  , (||||)
  , liftR2
    -- * Divisible-style combinators
  , divide
  , divide'
  , codivide
  , codivide'
  , choose
  , choose'
  , cochoose
  , cochoose'
  , pappend
) where


import Control.Monad.State hiding (join)
import Data.Function
import Data.Profunctor.Strong
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Import
import qualified Data.Bifunctor as B
import qualified Data.Semigroup as S

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XRankNTypes
-- >>> import Data.Char
-- >>> import Data.Function ((&))
-- >>> import Data.Semigroup
-- >>> import qualified Data.Bifunctor as B
-- >>> import qualified Data.Map.Lazy as Map
-- >>> :load Data.Profunctor.Optic

parr :: Traversing p => (a -> b) -> p a b 
parr = tabulate . (pure .)
{-# INLINE parr #-}

coarr :: Cotraversing p => (a -> b) -> p a b
coarr = cotabulate . (. copure)
{-# INLINE coarr #-}

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

---------------------------------------------------------------------
-- Operations on arbitrary profunctors
---------------------------------------------------------------------

constl :: Profunctor p => b -> Optic p a c b c
constl = lmap . const
{-# INLINE constl #-}

constr :: Profunctor p => c -> Optic p a c a b
constr = rmap . const
{-# INLINE constr #-}

shiftl :: Profunctor p => Optic p b (c + d) (a + b) c
shiftl = dimap Right Left
{-# INLINE shiftl #-}

shiftr :: Profunctor p => Optic p (a , b) c b (c , d)
shiftr = dimap snd fst
{-# INLINE shiftr #-}

coercel :: Profunctor p => CoercingL p => Optic p c b a b
coercel = B.first absurd . lmap absurd
{-# INLINE coercel #-}

coercer :: Profunctor p => CoercingR p => Optic p a c a b
coercer = rmap absurd . contramap absurd
{-# INLINE coercer #-}

-- | TODO: Document
--
represent :: Representable p => ((a -> Rep p b) -> s -> Rep p t) -> Optic p s t a b
represent f = tabulate . f . sieve
{-# INLINE represent #-}

-- | TODO: Document
--
corepresent :: Corepresentable p => ((Corep p a -> b) -> Corep p s -> t) -> Optic p s t a b
corepresent f = cotabulate . f . cosieve
{-# INLINE corepresent #-}

---------------------------------------------------------------------
-- Operations on representable profunctors
---------------------------------------------------------------------

-- | Map over an 'Optic'.
--
-- @
-- 'over' o 'id' ≡ 'id' 
-- 'over' o f '.' 'over' o g ≡ 'over' o (f '.' g)
-- 'over' '.' 'setter' ≡ 'id'
-- 'over' '.' 'resetter' ≡ 'id'
-- @
--
-- >>> over fmapped (+1) (Just 1)
-- Just 2
-- >>> over fmapped (*10) [1,2,3]
-- [10,20,30]
-- >>> over first (+1) (1,2)
-- (2,2)
-- >>> over first show (10,20)
-- ("10",20)
--
over :: Optic (->) s t a b -> (a -> b) -> s -> t
over = id
{-# INLINE over #-}

infixr 4 .~, ..~

-- | Set the focus of an 'Optic'.
--
(.~) :: Optic (->) s t a b -> b -> s -> t
(.~) o b = o (const b)
{-# INLINE (.~) #-}

-- | Map over an 'Optic'.
--
-- >>> (10,20) & first ..~ show 
-- ("10",20)
--
(..~) :: Optic (->) s t a b -> (a -> b) -> s -> t
(..~) = over
{-# INLINE (..~) #-}

infixr 4 *~, **~, /~, //~

-- | Set the focus of a representable optic.
--
-- @since 0.0.3
(*~) :: Optic (Star f) s t a b -> f b -> s -> f t
(*~) o b = o **~ (const b)
{-# INLINE (*~) #-}

-- | Map over a representable optic.
--
-- >>> [66,97,116,109,97,110] & traversed **~ \a -> ("na", chr a)
-- ("nananananana","Batman")
--
-- @since 0.0.3
(**~) :: Optic (Star f) s t a b -> (a -> f b) -> s -> f t
(**~) o = runStar #. o .# Star
{-# INLINE (**~) #-}

-- | TODO: Document
--
reps :: Representable p => Optic p s t a b -> ((a -> Rep p b) -> s -> Rep p t)
reps o = sieve . o . tabulate
{-# INLINE reps #-}

-- | Set the focus of a co-representable optic.
--
-- @since 0.0.3
(/~) :: Optic (Costar f) s t a b -> b -> f s -> t
(/~) o b = o //~ (const b)
{-# INLINE (/~) #-}

-- | Map over a co-representable optic.
--
-- @since 0.0.3
(//~) :: Optic (Costar f) s t a b -> (f a -> b) -> f s -> t
(//~) o = runCostar #. o .# Costar
{-# INLINE (//~) #-}

-- | TODO: Document
--
coreps :: Corepresentable p => Optic p s t a b -> ((Corep p a -> b) -> Corep p s -> t)
coreps o = cosieve . o . cotabulate
{-# INLINE coreps #-}

---------------------------------------------------------------------
-- Arrow-style combinators
---------------------------------------------------------------------

infixl 4 <<*>>

-- | Profunctor variant of '<*>'.
--
(<<*>>) :: Traversing1 p => p a (b -> c) -> p a b -> p a c
(<<*>>) = liftR2 ($)
{-# INLINE (<<*>>) #-}

infixr 3 ****

-- | Profunctor variant of '***'.
--
(****) :: Traversing1 p => p a1 b1 -> p a2 b2 -> p (a1 , a2) (b1 , b2)
p **** q = dimap fst (,) p <<*>> lmap snd q
{-# INLINE (****) #-}

infixr 2 ++++

-- | Profunctor variant of '+++'.
--
(++++) :: Cotraversing1 p => p a1 b1 -> p a2 b2 -> p (a1 + a2) (b1 + b2)
p ++++ q = cotabulate $ B.bimap (cosieve p) (cosieve q) . coapply
{-# INLINE (++++) #-}

infixr 3 &&&&

-- | Profunctor variant of '&&&'.
--
(&&&&) ::  Traversing1 p => p a b1 -> p a b2 -> p a (b1 , b2)
p &&&& q = liftR2 (,) p q
{-# INLINE (&&&&) #-}

infixr 2 ||||

-- | Profunctor variant of '|||'.
--
(||||) :: Cotraversing1 p => p a1 b -> p a2 b -> p (a1 + a2) b
p |||| q = cotabulate $ either (cosieve p) (cosieve q) . coapply
{-# INLINE (||||) #-}

liftR2 :: Traversing1 p => (b -> c -> d) -> p a b -> p a c -> p a d
liftR2 f x y = tabulate $ \s -> liftF2 f (sieve x s) (sieve y s)
{-# INLINE liftR2 #-}

---------------------------------------------------------------------
-- Divisible-style combinators
---------------------------------------------------------------------

-- | Profunctor variant of < hackage.haskell.org/package/contravariant/docs/Data-Functor-Contravariant-Divisible.html#v:divide divide >.
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

-- | Profunctor variant of < hackage.haskell.org/package/contravariant/docs/Data-Functor-Contravariant-Divisible.html#v:choose choose >.
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

pappend :: Traversing1 p => p a b -> p a b -> p a b
pappend = divide fork
{-# INLINE pappend #-}

{-
pushl :: Closed p => Traversing1 p => p a c -> p b c -> p a (b -> c)
pushl p q = curry' $ divide id p q
{-# INLINE pushl #-}

pushr :: Closed p => Traversing1 p => p (a , b) c -> p a b -> p a c
pushr = (<<*>>) . curry' 
{-# INLINE pushr #-}
-}
