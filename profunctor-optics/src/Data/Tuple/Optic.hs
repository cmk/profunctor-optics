{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Tuple.Optic (
    curried
  , swapped
  , associated
  , first
  , second
  , t21
  , t22
  , t31
  , t32
  , t33
  , t41
  , t42
  , t43
  , t44
  , t51
  , t52
  , t53
  , t54
  , t55
) where

import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Lens

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

first :: Lens (a , c) (b , c) a b
first = first'

second :: Lens (c , a) (c , b) a b
second = second'

t21 :: Lens (a,b) (a',b) a a'
t21 = lensVl $ \f ~(a,b) -> (\a' -> (a',b)) <$> f a
{-# INLINE t21 #-}

t22 :: Lens (a,b) (a,b') b b'
t22 = lensVl $ \f ~(a,b) -> (\b' -> (a,b')) <$> f b
{-# INLINE t22 #-}

t31 :: Lens (a,b,c) (a',b,c) a a'
t31 = lensVl $ \f ~(a,b,c) -> (\a' -> (a',b,c)) <$> f a
{-# INLINE t31 #-}

t32 :: Lens (a,b,c) (a,b',c) b b'
t32 = lensVl $ \f ~(a,b,c) -> (\b' -> (a,b',c)) <$> f b
{-# INLINE t32 #-}

t33 :: Lens (a,b,c) (a,b,c') c c'
t33 = lensVl $ \f ~(a,b,c) -> (\c' -> (a,b,c')) <$> f c
{-# INLINE t33 #-}

t41 :: Lens (a,b,c,d) (a',b,c,d) a a'
t41 = lensVl $ \f ~(a,b,c,d) -> (\a' -> (a',b,c,d)) <$> f a
{-# INLINE t41 #-}

t42 :: Lens (a,b,c,d) (a,b',c,d) b b'
t42 = lensVl $ \f ~(a,b,c,d) -> (\b' -> (a,b',c,d)) <$> f b
{-# INLINE t42 #-}

t43 :: Lens (a,b,c,d) (a,b,c',d) c c'
t43 = lensVl $ \f ~(a,b,c,d) -> (\c' -> (a,b,c',d)) <$> f c
{-# INLINE t43 #-}

t44 :: Lens (a,b,c,d) (a,b,c,d') d d'
t44 = lensVl $ \f ~(a,b,c,d) -> (\d' -> (a,b,c,d')) <$> f d
{-# INLINE t44 #-}

t51 :: Lens (a,b,c,d,e) (a',b,c,d,e) a a'
t51 = lensVl $ \f ~(a,b,c,d,e) -> (\a' -> (a',b,c,d,e)) <$> f a
{-# INLINE t51 #-}

t52 :: Lens (a,b,c,d,e) (a,b',c,d,e) b b'
t52 = lensVl $ \f ~(a,b,c,d,e) -> (\b' -> (a,b',c,d,e)) <$> f b
{-# INLINE t52 #-}

t53 :: Lens (a,b,c,d,e) (a,b,c',d,e) c c'
t53 = lensVl $ \f ~(a,b,c,d,e) -> (\c' -> (a,b,c',d,e)) <$> f c
{-# INLINE t53 #-}

t54 :: Lens (a,b,c,d,e) (a,b,c,d',e) d d'
t54 = lensVl $ \f ~(a,b,c,d,e) -> (\d' -> (a,b,c,d',e)) <$> f d
{-# INLINE t54 #-}

t55 :: Lens (a,b,c,d,e) (a,b,c,d,e') e e'
t55 = lensVl $ \f ~(a,b,c,d,e) -> (\e' -> (a,b,c,d,e')) <$> f e
{-# INLINE t55 #-}

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------


