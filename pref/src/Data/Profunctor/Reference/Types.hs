{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ExistentialQuantification     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# LANGUAGE RankNTypes #-}


{-# LANGUAGE ScopedTypeVariables, TypeOperators , KindSignatures, GADTs, DataKinds #-}

--for tupled constraints
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}


{-# LANGUAGE TypeApplications #-}

{-# LANGUAGE TemplateHaskell #-}
-- {-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ConstraintKinds, StandaloneDeriving, DeriveAnyClass #-}
-- {-# LANGUAGE PolyKinds #-}
-- {-# LANGUAGE ImpredicativeTypes #-}



 {-# OPTIONS_GHC -w #-}
-- | Environment values with stateful capabilities.
module Data.Profunctor.Reference.Types where


import Data.Kind (Constraint, Type)
import Data.Monoid (First)

import Data.Profunctor.Optic
import Control.Concurrent.STM (STM)
import Control.Applicative (Const(..))
import Data.Tuple (swap)
import Data.Bitraversable


import Data.Function ((&)) 
import Data.Void
import Data.IORef



type X = Void

---------------------------------------------------------------------
--  PRef
---------------------------------------------------------------------


{- | A profunctor reference is a pair of mutable references bound 

together with a profunctor optic by existentializing over the read and

write reference types.

The type variables signify:

  * @r@ - The reference type (e.g. 'TVar', 'MVar', 'STRef', 'IORef' etc.)

  * @c@ - The constraint determining which operations can be performed.

  * @b@ - The contravariant write-only type.

  * @a@ - The covariant read-only type.


data Proxy a' a b' b m r Source#

A Proxy is a monad transformer that receives and sends information on both an upstream and downstream interface.

The type variables signify:

a' and a - The upstream interface, where (a')s go out and (a)s come in
b' and b - The downstream interface, where (b)s go out and (b')s come in
m - The base monad
r - The return value

-}


--data P rt rs c b a = forall s t. P (Optical c s t a b) !(r t) !(r s)

data P rt rs c b a = forall s t. P (Optical c s t a b) !(rt t) !(rs s)

data P' rs c a = forall s. P' (Optical c s s a a) !(rs s)

{-
type P = P IORef IORef
type PVar = P MVar MVar
type PChan = P Chan
type PStream = P InputStream OutputStream
-}

{-
-- experiment w/ removingOptical type
data QRef r c b a = forall s t. QRef (forall p. c p => Optic p s t a b) !(r t) !(r s)

withQRef 
  :: QRef r c b a 
  -> (forall s t . (forall p. c p => Optic p s t a b) -> r t -> r s -> x) 
  -> x
withQRef (QRef o rt rs) f = f o rt rs

data P rt rs c b a where 

  --P :: (Optic c s t a b) -> r t -> r s -> P rt rs c b a
  P :: forall a b c r s t. (forall p. c p => Optic p s t a b) -> r t -> r s -> P rt rs c b a
-}

instance Profunctor (P rt rs Profunctor) where  dimap bt sa (P o rt rs) = P (o . dimap sa bt) rt rs
instance Profunctor (P rt rs Strong) where dimap bt sa (P o rt rs) = P (o . dimap sa bt) rt rs
instance Profunctor (P rt rs Costrong) where dimap bt sa (P o rt rs) = P (o . dimap sa bt) rt rs
instance Profunctor (P rt rs Choice) where dimap bt sa (P o rt rs) = P (o . dimap sa bt) rt rs
instance Profunctor (P rt rs Cochoice) where dimap bt sa (P o rt rs) = P (o . dimap sa bt) rt rs
instance Profunctor (P rt rs Traversing) where dimap bt sa (P o rt rs) = P (o . dimap sa bt) rt rs
instance Profunctor (P rt rs Mapping) where dimap bt sa (P o rt rs) = P (o . dimap sa bt) rt rs
instance Profunctor (P rt rs Closed) where dimap bt sa (P o rt rs) = P (o . dimap sa bt) rt rs

instance Profunctor (P rt rs AffineFolding) where dimap bt sa (P o rt rs) = P (o . dimap sa bt) rt rs
instance Profunctor (P rt rs Folding) where dimap bt sa (P o rt rs) = P (o . dimap sa bt) rt rs
instance Profunctor (P rt rs Getting) where dimap bt sa (P o rt rs) = P (o . dimap sa bt) rt rs
instance Profunctor (P rt rs Reviewing) where dimap bt sa (P o rt rs) = P (o . dimap sa bt) rt rs
instance Profunctor (P rt rs AffineTraversing) where dimap bt sa (P o rt rs) = P (o . dimap sa bt) rt rs


instance Strong (P rt rs Costrong) where first' (P o rt rs) = P (o . unfirst) rt rs
instance Costrong (P rt rs Strong) where unfirst (P o rt rs) = P (o . first') rt rs

instance Choice (P rt rs Cochoice) where right' (P o rt rs) = P (o . unright) rt rs
instance Cochoice (P rt rs Choice) where unright (P o rt rs) = P (o . right') rt rs


-------------------------------------------------------------------------------
--  PRef'
-------------------------------------------------------------------------------


-- Note that P rt rs c a a is distinct from PRef' r c a in that it has
-- a read-only Ref and a write-only Ref of the same type, rather than one Ref for both reading and writing.
-- Because the Refs are existentialized this makes certain opimitations (e.g 'atomicModifyRef') 
-- unavaliable to a P rt rs c a a.
--
-- Note that for TVars 'atomicModifyRef' is equiv / makes no difference
--data PRef' r c a = forall s. PRef' (Optic' c s a) !(r s) 

--instance Functor (PRef' r c)

primGetter :: Bicontravariant p => (s -> a) -> Optic' p s a
primGetter sa = primgetting sa sa

{-
newtype LocalRef c s a = 
  LocalRef { unLocalRef :: Ref m r => forall r. ReaderT (PRef' STRef c s) (ST r) a }

modifyPRef' :: Ref r m => PRef' r Mapping a -> (a -> a) -> m ()
modifyPRef' (PRef' o rs) f = modifyRef' rs $ over o f

atomicModifyPRef' :: ARef r m => PRef' r Strong a -> (a -> (a, x)) -> m x
atomicModifyPRef' (PRef' o rs) f = atomicModifyRef' rs ssa
    where ssa = withLens o $ \sa sas -> \s -> let (a, x) = f . sa $! s in (sas s a, x)

-}





-- | Unbox a 'PRef' by providing an existential continuation.
withP 
  :: P rt rs c b a 
  -> (forall s t. Optical c s t a b -> rt t -> rs s -> x) 
  -> x
withP (P o rt rs) f = f o rt rs


{-


-- Affine PRef
--
aff :: Affine (Either c a, d) (Either c b, d) a b
aff = first' . right'

s = (Just "hi!", 2) :: (Maybe String, Int)
t = (Nothing, 2) :: (Maybe Int, Int)

rs <- newRef @IORef @IO s
rt <- newRef @IORef @IO t

o :: P IORef AffineLike Int String = P (_1 . _Just) rt rs
o' :: P IORef AffineLike String String = P (_1 . _Just) rs rs


modifyP o' tail >> readRef rs >>= print >> readRef rt >>= print
-- (Just "i!",2)
-- (Nothing,2)

modifyP o length >> readRef rs >>= print >> readRef rt >>= print
--(Just "i!",2)
--(Just 2,2)


-- Affine P 2
--

s = (Nothing, 2) :: (Maybe String, Int)
t = (Just 4, 2) :: (Maybe Int, Int)

rs <- newRef @IORef @IO s
rt <- newRef @IORef @IO t

o :: P IORef AffineLike Int String = P (_1 . _Just) rt rs
o' :: P IORef AffineLike String String = P (_1 . _Just) rs rs


modifyP o' tail >> readRef rs >>= print >> readRef rt >>= print
-- (Nothing,2)
-- (Just 4,2)

modifyP o length >> readRef rs >>= print >> readRef rt >>= print
-- (Nothing,2)
-- (Nothing,2)


-}







