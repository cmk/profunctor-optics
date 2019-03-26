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
{-# LANGUAGE ConstraintKinds, DeriveFunctor #-}
-- {-# LANGUAGE PolyKinds #-}
-- {-# LANGUAGE ImpredicativeTypes #-}

 {-# OPTIONS_GHC -w #-}
-- | Environment values with stateful capabilities.
module Data.Profunctor.PRef where


import Data.Kind (Constraint, Type)
import Data.Ref
import Data.Monoid (First)

import Data.Profunctor.Optic
--import Control.Lens
import Control.Concurrent.STM (STM)
import Control.Applicative (Const(..))
import Control.Monad.Reader (MonadReader)
import Data.Tuple (swap)
import Data.Bitraversable


import Data.Function ((&)) 

-- $setup
-- >>> :set -XTypeApplications
-- >>> :set -XScopedTypeVariables
-- >>> :set -XOverloadedStrings
-- >>> import Data.IORef
-- >>> import Data.Monoid (Sum(..))
-- >>> import Data.Profunctor.Optic


{-
-- Lens version
--type Optic p f s t a b = p a (f b) -> p s (f t)
type Ocular c d s t a b = forall p f. (c p, d f) => Optic p f s t a b  -- p a (f b) -> p s (f t)
data PRef r c d b a = forall s t. PRef (Ocular c d s t a b) !(r t) !(r s)

data PRef' r c d a = forall s. PRef' (Ocular c d s s a a) !(r s)

withPRef :: PRef r c d b a -> (forall s t. Ocular c d s t a b -> r t -> r s -> x) -> x
withPRef (PRef o rt rs) f = f o rt rs

newLocalPRef :: Ref m r => Ocular c d s t a b -> t -> s -> m (PRef r c d b a)
newLocalPRef o t s = (PRef o) <$> newRef t <*> newRef s

newLocalPRef' :: Ref m r => Ocular c d s s a a -> s -> m (PRef r c d a a)
newLocalPRef' o s = newLocalPRef o s s 

-- wont work for general PRef since 'Getter'/'Getting' are monomorphic.
--readPRef :: (c (Star (Const a)), Ref m r) => PRef r c b a -> m a
readPRef' :: (c (->), d (Const a), Ref m r) => PRef' r c d a -> m a
readPRef' (PRef' o s) = (^. o) <$> readRef s
-}


-- TODO use constraints library instead?
class (C '[Profunctor] p) => IsoLike p
instance (C '[Profunctor] p) => IsoLike p

class (C '[Profunctor, Strong] p) => LensLike p
instance (C '[Profunctor, Strong] p) => LensLike p

class (C '[Profunctor, Choice] p) => PrismLike p
instance (C '[Profunctor, Choice] p) => PrismLike p

class (C '[Profunctor, Strong, Choice] p) => AffineLike p
instance (C '[Profunctor, Strong, Choice] p) => AffineLike p


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
-}

data PRef r c b a = forall s t. PRef (Optic c s t a b) !(r t) !(r s)

instance Functor (PRef r c b)

instance Profunctor (PRef r Profunctor) where
  --dimap :: (b -> t) -> (s -> a) -> p t s -> p b a
  dimap bt sa (PRef o rt rs) = PRef (o . iso sa bt) rt rs


-- | Unbox a 'PRef' by providing an existential continuation.
withPRef 
  :: PRef r c b a 
  -> (forall s t. Optic c s t a b -> r t -> r s -> x) 
  -> x
withPRef (PRef o rt rs) f = f o rt rs


-- | Create a new 'PRef' with purely local state.
--
-- The optic argument is exposed for completeness, but in most cases
-- should be set to 'id'.
newLocalPRef 
  :: Ref m r 
  => Optic c s t a b 
  -> t 
  -> s 
  -> m (PRef r c b a)
newLocalPRef o t s = (PRef o) <$> newRef t <*> newRef s


-- | A variant of 'newLocalPRef' that uses the same ref for both read
--
-- and write operations. Note that this is distinct from a 'PRef''.
newLocalPRef'
  :: Ref m r 
  => Optic c s s a a 
  -> s 
  -> m (PRef r c a a)
newLocalPRef' o s = newLocalPRef o s s 


--newGlobalRef :: MonadRef m r => Optic c s t a b -> t -> s -> Ref r c b a 


-- | Read a value from a 'PRef' with profunctorial strength.
--
--
readPRef 
  :: Ref m r
  => c (Forget a)
  => PRef r c b a 
  -> m a
readPRef (PRef o _ s) = view o <$> readRef s


-- | Read a value from a 'PRef' with profunctorial choice.
previewPRef 
  :: Ref m r 
  => c (Preview a)
  => PRef r c b a 
  -> m (Maybe a)
previewPRef (PRef o _ s) = preview o <$> readRef s 


-- | A variant of 'previewPRef' that updates the write ref on failure.
matchPRef
  :: Ref m r
  => c (Matching a)
  => PRef r c b a 
  -> m (Maybe a)
matchPRef (PRef o rt rs) =
  do s <- readRef rs
     case matching o s of
       Left t -> 
         writeRef rt t >> return Nothing


-- | Modify a 'PRef'.
--
-- Note that this operation is lazy. Depending on use unevaluated 
-- expression thunks can pile up in memory resulting in a space leak. 
-- To update strictly use 'modifyPRef''.
--
-- Lens example:
--
-- >>> s = ("hi!",2) :: (String, Int)
-- >>> t = (4,2)  :: (Int, Int)
-- >>> rs <- newRef @IO @IORef s
-- >>> rt <- newRef @IO @IORef t
-- >>> o :: PRef IORef Strong Int String = PRef _1 rt rs
-- >>> o' :: PRef IORef Strong String String = PRef _1 rs rs
--
-- >>> modifyPRef o' tail >> readRef rs 
-- ("i!",2)
-- >>> readRef rt 
-- (4,2)
-- >>> modifyPRef o length >> readRef rs
-- ("i!",2)
-- >>> readRef rt 
-- (2,2)
--
--
-- Prism example:
--
-- >>> s = Just "hi!" :: Maybe String
-- >>> t = Nothing  :: Maybe Int
-- >>> rs <- newRef @IO @IORef s
-- >>> rt <- newRef @IO @IORef t
-- >>> o :: PRef IORef Choice Int String = PRef _Just rt rs
-- >>> o' :: PRef IORef Choice String String = PRef _Just rs rs
-- >>> modifyPRef o' tail >> readRef rs
-- Just "i!"
-- >>> readRef rt 
-- Nothing
-- >>> modifyPRef o length >> readRef rs
-- Just "i!"
-- >>> readRef rt 
-- Just 2
--
--
-- Traversal example:
--
-- >>> s = ["hi", "there"] :: [String]
-- >>> t = fmap Sum [1..10] :: [Sum Int]
-- >>> rs <- newRef @IO @IORef s
-- >>> rt <- newRef @IO @IORef t
-- >>> o :: PRef IORef Traversing (Sum Int) String = PRef traversed rt rs
-- >>> o' :: PRef IORef Traversing String String = PRef traversed rs rs
-- >>> modifyPRef o (Sum . length) >> readRef rs
-- ["hi","there"]
-- >>> readRef rt 
-- [Sum {getSum = 2},Sum {getSum = 5}]
-- >>> modifyPRef o' ("oh" ++) >> readRef rs
-- ["ohhi","ohthere"]
--
modifyPRef 
  :: Ref m r
  => c (->)
  => PRef r c b a 
  -> (a -> b) 
  -> m ()
modifyPRef (PRef o rt rs) f = readRef rs >>= writeRef rt . over o f


-- | Strict variant of 'modifyPRef'. This forces both the value stored
--
-- as well as the value returned. This function is atomic when r is a 
-- TVar or TMVar.
modifyPRef' :: (c (->), Ref m r) => PRef r c b a -> (a -> b) -> m ()
modifyPRef' (PRef o rt rs) f =
  do s <- readRef rs
     let t = over o f s
     t `seq` writeRef rt t


-- | Variant of 'writePRef' that opens both read & write refs.
--
-- Note this function is inefficient if you don't need profunctorial
-- strength, since it opens the read head. Use 'writePRef' instead
-- where constraints allow.
setPRef :: (c (->), Ref m r) => PRef r c b a -> b -> m ()
setPRef r a = modifyPRef r (const a)


-- | Variant of 'setPRef' that only opens the write ref.
--
-- Use with optics that do not require the 'Strong' constraint.
writePRef :: (c Tagged, Ref m r) => PRef r c b a -> b -> m ()
writePRef (PRef o rt _) b = writeRef rt . review o $ b




{-

class Ref m r => MRef m r where

    newEmptyRef :: m (r a)

    {- |
    Return the contents of a mutex reference. If the refence is currently empty, the transaction will retry. 
    After a takeRef, the refence is left empty.
    -}
    takeRef :: r a -> m a

    tryTakeRef :: r a -> m (Maybe a)

    putRef :: r a -> a -> m ()

    tryPutRef :: r a -> a -> m Bool

    swapRef :: r a -> a -> m a

    isEmptyRef :: r a -> m Bool





-- Affine PRef
--
aff :: Affine (Either c a, d) (Either c b, d) a b
aff = first' . right'

s = (Just "hi!", 2) :: (Maybe String, Int)
t = (Nothing, 2) :: (Maybe Int, Int)

rs <- newRef @IORef @IO s
rt <- newRef @IORef @IO t

o :: PRef IORef AffineLike Int String = PRef (_1 . _Just) rt rs
o' :: PRef IORef AffineLike String String = PRef (_1 . _Just) rs rs


modifyPRef o' tail >> readRef rs >>= print >> readRef rt >>= print
-- (Just "i!",2)
-- (Nothing,2)

modifyPRef o length >> readRef rs >>= print >> readRef rt >>= print
--(Just "i!",2)
--(Just 2,2)


-- Affine PRef 2
--

s = (Nothing, 2) :: (Maybe String, Int)
t = (Just 4, 2) :: (Maybe Int, Int)

rs <- newRef @IORef @IO s
rt <- newRef @IORef @IO t

o :: PRef IORef AffineLike Int String = PRef (_1 . _Just) rt rs
o' :: PRef IORef AffineLike String String = PRef (_1 . _Just) rs rs


modifyPRef o' tail >> readRef rs >>= print >> readRef rt >>= print
-- (Nothing,2)
-- (Just 4,2)

modifyPRef o length >> readRef rs >>= print >> readRef rt >>= print
-- (Nothing,2)
-- (Nothing,2)


-}







