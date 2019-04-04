{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE UndecidableInstances      #-}

{-# OPTIONS_GHC -w #-}
module Data.Profunctor.Reference.Types where

import Control.Category (Category)
import Control.Monad.Reader.Class
import Control.Monad.Writer.Class
import Control.Monad.State.Class
import Control.Monad.IO.Unlift
import Data.Profunctor.Optic

import Control.Arrow
import Data.IORef (IORef(..))

import qualified Data.IORef as IOR

import System.IO.Streams (InputStream, OutputStream)

import Control.Concurrent.MVar (MVar)
--import Control.Concurrent
import Control.Concurrent.STM (TArray, TBQueue, TQueue, TChan, TMVar, TVar)


import qualified Control.Category as C


---------------------------------------------------------------------
--  PRef
---------------------------------------------------------------------


{- | A profunctor reference is a pair of mutable references bound 

together with a profunctor optic by existentializing over the types
 
in the read and write references.

The type variables signify:

  * @c@ - The constraint determining which operations can be performed.

  * @rt@ - The write container reference (e.g. 'MVar', 'IO', 'IORef' etc.).

  * @rs@ - The read container reference (e.g. 'MVar', 'IO', 'IORef' etc.).

  * @b@ - The exposed (contravariant) write-only type.

  * @a@ - The exposed (covariant) read-only type.

-}

data PRef c rt rs b a = forall x y . PRef (Optical c x y a b) !(rs x) !(rt y)

data PRef' c rs a = forall x . PRef' (Optical' c x a) !(rs x)



instance Profunctor (PRef Profunctor rt rs) where dimap bt sa (PRef o rs rt) = PRef (o . dimap sa bt) rs rt

instance Profunctor (PRef Strong rt rs) where dimap bt sa (PRef o rs rt) = PRef (o . dimap sa bt) rs rt

instance Profunctor (PRef Costrong rt rs) where dimap bt sa (PRef o rs rt) = PRef (o . dimap sa bt) rs rt

instance Profunctor (PRef Choice rt rs) where dimap bt sa (PRef o rs rt) = PRef (o . dimap sa bt) rs rt

instance Profunctor (PRef Cochoice rt rs) where dimap bt sa (PRef o rs rt) = PRef (o . dimap sa bt) rs rt

instance Profunctor (PRef Closed rt rs) where dimap bt sa (PRef o rs rt) = PRef (o . dimap sa bt) rs rt

instance Profunctor (PRef Mapping rt rs) where dimap bt sa (PRef o rs rt) = PRef (o . dimap sa bt) rs rt

instance Profunctor (PRef Traversing rt rs) where dimap bt sa (PRef o rs rt) = PRef (o . dimap sa bt) rs rt

instance Profunctor (PRef AffineTraversing rt rs) where dimap bt sa (PRef o rs rt) = PRef (o . dimap sa bt) rs rt

instance Profunctor (PRef Folding rt rs) where dimap bt sa (PRef o rs rt) = PRef (o . dimap sa bt) rs rt

instance Profunctor (PRef AffineFolding rt rs) where dimap bt sa (PRef o rs rt) = PRef (o . dimap sa bt) rs rt

instance Profunctor (PRef Getting rt rs) where dimap bt sa (PRef o rs rt) = PRef (o . dimap sa bt) rs rt

instance Profunctor (PRef Reviewing rt rs) where dimap bt sa (PRef o rs rt) = PRef (o . dimap sa bt) rs rt



instance Strong (PRef Costrong rt rs) where first' (PRef o rs rt) = PRef (o . unfirst) rs rt

instance Costrong (PRef Strong rt rs) where unfirst (PRef o rs rt) = PRef (o . first') rs rt

instance Choice (PRef Cochoice rt rs) where right' (PRef o rs rt) = PRef (o . unright) rs rt

instance Cochoice (PRef Choice rt rs) where unright (PRef o rs rt) = PRef (o . right') rs rt

instance Category (PRef Profunctor rt rs) where 
  id = undefined -- TODO produce these w/ TH based on monoid instances from the underlying s,t
  bc . ab = compose_pxy ab bc

compose_iso :: AnIso s y a b -> AnIso x t b c -> Iso s t a c
compose_iso o o' = withIso o $ \ sa bt -> withIso o' $ \ s'a' b't' -> iso sa b't'

compose_pxy :: PRef Profunctor t x c b -> PRef Profunctor y s b a -> PRef Profunctor t s c a
compose_pxy (PRef obc _ ty) (PRef oab sx _) = (PRef (compose_iso oab obc) sx ty) 

-- | Unbox a 'Pxy' by providing an existentially quantified continuation.
withPRef 
  :: PRef c rt rs b a 
  -> (forall x y. Optical c x y a b -> rs x -> rt y -> r) 
  -> r
withPRef (PRef o sx ty) f = f o sx ty

{-

newtype LocalRef c s a = 
  LocalRef { unLocalRef :: Ref m r => forall r. ReaderT (PRef' STRef c s) (ST r) a }

modifyPRef' :: Ref r m => PRef' r Mapping a -> (a -> a) -> m ()
modifyPRef' (PRef' o rs) f = modifyRef' rs $ over o f

atomicModifyPRef' :: ARef r m => PRef' r Strong a -> (a -> (a, x)) -> m x
atomicModifyPRef' (PRef' o rs) f = atomicModifyRef' rs ssa
    where ssa = withLens o $ \sa sas -> \s -> let (a, x) = f . sa $! s in (sas s a, x)


type PIORef' c a = PRef' c IORef a

type PMVar c b a = PRef c MVar MVar b a

type PInputStream c a = PRef' c InputStream a

type POutputStream c b = PRef' c OutputStream b

type PTChan c b a = PRef c TChan TChan b a

type PTChan' c a = PRef' c TChan a

type PTQueue c b a = PRef c TQueue TQueue b a

type PTQueue' c a = PRef' c TQueue a

type PTBQueue c b a = PRef c TBQueue TBQueue b a

type PTBQueue' c a = PRef' c TBQueue a

-}

type PIORef c b a = PRef c IORef IORef b a

type PMVar c a = PRef' c MVar a

type PStream c b a = PRef c OutputStream InputStream b a


readPRefSimple 
  :: MonadIO m
  => c (Forget a)
  => PRef' c IORef a 
  -> m a
readPRefSimple (PRef' o rs) = liftIO $ view o <$> IOR.readIORef rs

modifyPRefSimple
  :: MonadIO m
  => c (->)
  => PRef' c IORef a 
  -> (a -> a) 
  -> m ()
modifyPRefSimple (PRef' o rs) f = liftIO $ IOR.readIORef rs >>= IOR.writeIORef rs . over o f


instance (MonadIO m, MonadReader (PRef' Strong IORef a) m) => MonadState a m where 

  get = do
    ref <- ask
    readPRefSimple ref

  put a = do
    ref <- ask
    liftIO $ modifyPRefSimple ref (const a)


instance (MonadIO m, MonadReader (PRef' Strong IORef a) m, Monoid a) => MonadWriter a m where 

  tell a = do
    ref <- ask
    liftIO $ modifyPRefSimple ref (`mappend` a)

  pass act = do
    (a, f) <- act
    ref <- ask
    liftIO $ modifyPRefSimple ref f
    return a

  listen act = do
    w1 <- ask >>= liftIO . readPRefSimple
    a <- act
    w2 <- do
      ref <- ask
      v <- liftIO $ readPRefSimple ref
      _ <- liftIO $ modifyPRefSimple ref (const w1)
      return v
    return (a, w2)

--instance (MonadUnliftIO m, MonadReader (PRef Reviewing IORef rs b a) m, Monoid b) => MonadWriter b m where 




-- TODO could generalize this to arbitrary comonads.
readPure
  :: c (Forget a)
  => PRef c rt Identity b a 
  -> a
readPure (PRef o rs _) = view o . runIdentity $ rs

-- fills the (read-side) role of the lens in a Has type class
readex :: MonadReader r m => c (Forget a) => PRef c rt ((->) r) b a -> m a
readex (PRef o rs _) = view o <$> asks rs


getex :: MonadState s m => c (Forget a) => PRef c rt ((->) s) b a -> m a
getex (PRef o rs _) = view o <$> gets rs

puts :: MonadState s m => (a -> s) -> a -> m ()
puts f = put . f

tells :: MonadWriter w m => (a -> w) -> a -> m ()
tells f = tell . f

--putex :: MonadState s m => c (Forget a) => PRef c rt ((->) s) b a -> m a
--putex p@(PRef o _ rt) = getex p >>= view o <$> gets rs

--tellex :: MonadWriter x m => c Tagged => PRef' c m a -> a -> m ()
--tellex (PRef' o _) b = tells (review o) b




-- data PRef c rt rs b a = forall x y . PRef (Optical c x y a b) !(rs x) !(rt y)

--instance MonadReader (PRef c m rs b a) m => c (Forget a) => MonadReader a m where
    
--    ask = ask >>= \(PRef o s _) -> 
--
--



pmaybe
  :: Optic (Costar Maybe) s t a b 
  -> a -> (a -> b) -> Maybe s -> t
pmaybe o a ab = costar' o ab (maybe a id)

--star' up down o f = outof runStar up (o . into Star down $ f)



-- TODO check dynamically whether a 'Show' instance is available, and supply a default if not.
--debug :: Show t => Optic (Star IO) s t a b -> (a -> b) -> s -> IO ()
--debug o = star (>>=print) o return

{-
>>>  statePRef traversed (\a -> (a+1, show a)) $ fmap Sum i
["Sum {getSum = 1}","Sum {getSum = 2}","Sum {getSum = 3}","Sum {getSum = 4}","Sum {getSum = 5}"]
-}

pstate :: Optic (Star ((,) a)) s t a b -> (a -> (a, b)) -> s -> t
pstate o f = star o snd f id

stateC
  :: (Foldable f, Monoid t) =>
     Optic (Star f) s t a b -> (a -> f b) -> s -> t
stateC o f = star o (foldMap id) f id

into :: ((a -> b) -> c) -> (r -> b) -> (a -> r) -> c
into up f = up . (f .)

outof :: (c -> a -> b) -> (b -> r) -> c -> a -> r
outof down g = (g .) . down


star
  :: Optic (Star f) s t a b
  -> (f t -> r)
  -> (c -> f b)
  -> (a -> c)
  -> s
  -> r
star o down up f = outof runStar down (o . into Star up $ f)

star' :: Optic (Star f) s t a b -> (f t -> r) -> (a -> f b) -> s -> r
star' o f g = star o f g id

costar
  :: (t -> d)
  -> Optic (Costar f) s t a b
  -> (c -> b)
  -> (f a -> c)
  -> f s
  -> d
costar down o up f = outof runCostar down (o . into Costar up $ f)

costar'
  :: Optic (Costar f) s t a b
  -> (c -> b)
  -> (f a -> c)
  -> f s
  -> t
costar' = costar id
