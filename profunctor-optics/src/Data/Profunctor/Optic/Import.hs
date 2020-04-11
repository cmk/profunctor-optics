{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TupleSections    #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}

module Data.Profunctor.Optic.Import (
    type (+)
  , type (-)
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
  , forget1
  , forget2
  , forgetl
  , forgetr
  , module Export
) where

import Control.Arrow as Export ((|||),(&&&),(+++),(***))
import Control.Applicative as Export (liftA2, Alternative(..))
import Control.Coapplicative as Export hiding (apply, branch)
import Control.Category as Export hiding ((.), id)
import Control.Monad as Export hiding (void, join)
import Data.Bool as Export
import Data.Distributive as Export
import Data.Foldable as Export (foldr, foldr')
import Data.Function ((&))
import Data.Functor as Export hiding (void)
import Data.Functor.Apply as Export
import Data.Functor.Coapply as Export hiding (apply, branch)
import Data.Semigroup.Foldable as Export
import Data.Semigroup.Traversable as Export
import Data.Functor.Compose as Export
import Data.Functor.Const as Export
import Data.Functor.Contravariant as Export
import Data.Functor.Identity as Export
import Data.Monoid as Export
import Data.Profunctor.Unsafe as Export
import Data.Profunctor.Types as Export
import Data.Profunctor.Strong as Export (Strong(..), Costrong(..))
import Data.Profunctor.Choice as Export (Choice(..), Cochoice(..))
import Data.Profunctor.Closed as Export (Closed(..))
import Data.Profunctor.Sieve as Export (Sieve(..), Cosieve(..))
import Data.Profunctor.Rep as Export (Representable(..), Corepresentable(..))
import Data.Tuple (swap)
import Data.Tagged as Export
import Data.Void as Export
import Prelude as Export hiding (Num(..),subtract,sum,product,(^),foldl,foldl1)
import qualified Control.Monad as M

-- | Hyphenation operator.
type (g - f) a = f (g a)


type (+) = Either

xor :: Bool -> Bool -> Bool
xor a b = (a || b) && not (a && b)

xor3 :: Bool -> Bool -> Bool -> Bool
xor3 a b c = (a `xor` (b `xor` c)) && not (a && b && c)

infixr 0 ==>

(==>) :: Bool -> Bool -> Bool
(==>) a b = not a || b

iff :: Bool -> Bool -> Bool
iff a b = a ==> b && b ==> a

infixr 1 <==>

(<==>) :: Bool -> Bool -> Bool
(<==>) = iff

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
fork = M.join (,)
{-# INLINE fork #-}

join :: (a + a) -> a
join = M.join either id
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
