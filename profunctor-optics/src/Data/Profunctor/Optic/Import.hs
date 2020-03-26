{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TupleSections    #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Profunctor.Optic.Import (
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
import Test.Logic
import Prelude as Export hiding (Num(..),subtract,sum,product,(^),foldl,foldl1)

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
