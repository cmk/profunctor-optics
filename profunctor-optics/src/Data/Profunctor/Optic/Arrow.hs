{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TupleSections         #-}

module Data.Profunctor.Optic.Arrow (
    -- * Operations on (->) profunctors
    rgt
  , rgt'
  , lft
  , lft'
  , swap
  , eswap
  , fork
  , fanout
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
  , forget1
  , forget2
  , forgetl
  , forgetr
    -- * Profunctor utilities
  , star
  , unstar
  , costar
  , uncostar
  , constL
  , constR
  , shiftedL
  , shiftedR
  , coercedL
  , coercedR
    -- * Arrow-style combinators
  , arrow
  , coarrow
  , (***)
  , (&&&)
  , (<<*>>)
  , (+++)
  , (|||)
  , liftR2
  , pappend
  , divide
  , divideWith
  , cochoose
  , cochooseWith
  , choose
  , chooseWith
  , codivide
  , codivideWith
  ) where

import Control.Coapplicative hiding (apply, branch)
import Data.Bifunctor (Bifunctor(..))
import Data.Functor (Functor(..), (<$>))
import Data.Functor.Apply (Apply, liftF2)
import Data.Functor.Coapply (Coapply, coapply, type (+))
import Data.Functor.Contravariant (Contravariant(..))
import Data.Profunctor.Types (Star(..), Costar(..), Profunctor(..))
import Data.Profunctor.Sieve (Sieve(..), Cosieve(..))
import Data.Profunctor.Rep (Representable(..), Corepresentable(..))
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Types (Traversing, Traversing1, Cotraversing, Cotraversing1)
import Data.Tuple (swap)
import Data.Void (Void, absurd)
import Prelude (Either(..), either, Bool, id, ($), (.), flip, uncurry, snd, fst, const, Applicative, pure, Traversable)
import qualified Data.Bifunctor as B

-- This module collects:
-- 1. Pure (->) profunctor utilities (formerly in Import.hs)
-- 2. Arrow-style profunctor combinators (formerly in Traversal.hs)

---------------------------------------------------------------------
-- Operations on (->) profunctors
---------------------------------------------------------------------

-- | \( \forall a: f (g a) \equiv a \)
rgt :: (a -> b) -> a + b -> b
rgt f = either f id
{-# INLINE rgt #-}

rgt' :: Void + b -> b
rgt' = rgt absurd
{-# INLINE rgt' #-}

lft :: (b -> a) -> a + b -> a
lft f = either id f
{-# INLINE lft #-}

lft' :: a + Void -> a
lft' = lft absurd
{-# INLINE lft' #-}

eswap :: (a1 + a2) -> (a2 + a1)
eswap (Left x) = Right x
eswap (Right x) = Left x
{-# INLINE eswap #-}

fork :: a -> (a , a)
fork a = (a, a)
{-# INLINE fork #-}

fanout :: (a -> b) -> (a -> c) -> a -> (b , c)
fanout f g a = (f a, g a)
{-# INLINE fanout #-}

join :: (a + a) -> a
join = either id id
{-# INLINE join #-}

eval :: (a , a -> b) -> b
eval = uncurry $ flip id
{-# INLINE eval #-}

apply :: (b -> a , b) -> a
apply = uncurry id
{-# INLINE apply #-}

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

---------------------------------------------------------------------
-- Profunctor utilities
---------------------------------------------------------------------

-- | TODO: Document
--
star :: Applicative f => Star f a a
star = Star pure
{-# INLINE star #-}

-- | TODO: Document
--
unstar :: Coapplicative f => Star f a b -> a -> b
unstar f = copure . runStar f
{-# INLINE unstar #-}

-- | TODO: Document
--
costar :: Coapplicative f => Costar f a a
costar = Costar copure
{-# INLINE costar #-}

-- | TODO: Document
--
uncostar :: Applicative f => Costar f a b -> a -> b
uncostar f = runCostar f . pure
{-# INLINE uncostar #-}

constL :: Profunctor p => b -> p b c -> p a c
constL = lmap . const
{-# INLINE constL #-}

constR :: Profunctor p => c -> p a b -> p a c
constR = rmap . const
{-# INLINE constR #-}

shiftedL :: Profunctor p => p (a + b) c -> p b (c + d)
shiftedL = dimap Right Left
{-# INLINE shiftedL #-}

shiftedR :: Profunctor p => p b (c , d) -> p (a , b) c
shiftedR = dimap snd fst
{-# INLINE shiftedR #-}

coercedL :: (Profunctor p, Bifunctor p) => p a b -> p c b
coercedL = B.first absurd . lmap absurd
{-# INLINE coercedL #-}

coercedR :: (Profunctor p, forall x. Contravariant (p x)) => p a b -> p a c
coercedR = rmap absurd . contramap absurd
{-# INLINE coercedR #-}

---------------------------------------------------------------------
-- Arrow-style combinators
---------------------------------------------------------------------

-- | TODO: Document
--
arrow :: Traversing p => (a -> b) -> p a b
arrow = tabulate . (pure .)
{-# INLINE arrow #-}

-- | TODO: Document
--
coarrow :: Cotraversing p => (a -> b) -> p a b
coarrow = cotabulate . (. copure)
{-# INLINE coarrow #-}

infixr 3 ***

-- | Profunctor variant of 'Control.Arrow.***'.
--
--(***) :: Traversing1 p => p a1 b1 -> p a2 b2 -> p (a1 , a2) (b1 , b2)
p *** q = dimap fst (,) p <<*>> lmap snd q
{-# INLINE (***) #-}

infixr 3 &&&

-- | Profunctor variant of 'Control.Arrow.&&&'.
--
(&&&) :: Traversing1 p => p a b1 -> p a b2 -> p a (b1 , b2)
p &&& q = liftR2 (,) p q
{-# INLINE (&&&) #-}

infixl 4 <<*>>

-- | Profunctor variant of '<*>'.
--
(<<*>>) :: Traversing1 p => p a (b -> c) -> p a b -> p a c
(<<*>>) = liftR2 ($)
{-# INLINE (<<*>>) #-}

infixr 2 +++

-- | Profunctor variant of 'Control.Arrow.+++'.
--
(+++) :: Cotraversing1 p => p a1 b1 -> p a2 b2 -> p (a1 + a2) (b1 + b2)
p +++ q = cotabulate $ B.bimap (cosieve p) (cosieve q) . coapply
{-# INLINE (+++) #-}

infixr 2 |||

-- | Profunctor variant of 'Control.Arrow.|||'.
--
(|||) :: Cotraversing1 p => p a1 b -> p a2 b -> p (a1 + a2) b
p ||| q = cotabulate $ either (cosieve p) (cosieve q) . coapply
{-# INLINE (|||) #-}

-- | TODO: Document
--
liftR2 :: Traversing1 p => (b -> c -> d) -> p a b -> p a c -> p a d
liftR2 f x y = tabulate $ \s -> liftF2 f (sieve x s) (sieve y s)
{-# INLINE liftR2 #-}

-- | TODO: Document
--
pappend :: Traversing1 p => p a b -> p a b -> p a b
pappend = divideWith fork
{-# INLINE pappend #-}

-- | TODO: Document
--
divide :: Traversing1 p => p a1 b -> p a2 b -> p (a1 , a2) b
divide = divideWith id
{-# INLINE divide #-}

-- | Profunctor variant of < hackage.haskell.org/package/contravariant/docs/Data-Functor-Contravariant-Divisible.html#v:divideWith divideWith >.
--
divideWith :: Traversing1 p => (a -> (a1 , a2)) -> p a1 b -> p a2 b -> p a b
divideWith f p q = dimap f fst $ p *** q
{-# INLINE divideWith #-}

-- | TODO: Document
--
cochoose :: Traversing1 p => p a b1 -> p a b2 -> p a (b1, b2)
cochoose = cochooseWith id
{-# INLINE cochoose #-}

-- | TODO: Document
--
cochooseWith :: Traversing1 p => ((b1 , b2) -> b) -> p a b1 -> p a b2 -> p a b
cochooseWith f p q = dimap fork f $ p *** q
{-# INLINE cochooseWith #-}

-- | TODO: Document
--
choose :: Cotraversing1 p => p a1 b -> p a2 b -> p (a1 + a2) b
choose = chooseWith id
{-# INLINE choose #-}

-- | Profunctor variant of < hackage.haskell.org/package/contravariant/docs/Data-Functor-Contravariant-Divisible.html#v:chooseWith chooseWith >.
--
chooseWith :: Cotraversing1 p => (a -> (a1 + a2)) -> p a1 b -> p a2 b -> p a b
chooseWith f p q = dimap f join $ p +++ q
{-# INLINE chooseWith #-}

-- | TODO: Document
--
codivide :: Cotraversing1 p => p a b1 -> p a b2 -> p a (b1 + b2)
codivide = codivideWith id
{-# INLINE codivide #-}

-- | TODO: Document
--
codivideWith :: Cotraversing1 p => ((b1 + b2) -> b) -> p a b1 -> p a b2 -> p a b
codivideWith f p q = dimap Left f $ p +++ q
{-# INLINE codivideWith #-}
