{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE UndecidableInstances      #-}

{-# OPTIONS_GHC -w #-}
module Data.Profunctor.Reference.Optic where

import Control.Arrow
import Control.Category (Category)
import Control.Concurrent.MVar (MVar)
import Control.Concurrent.STM (TArray, TBQueue, TQueue, TChan, TMVar, TVar)
import Control.Monad.Reader (MonadReader(..), asks)
import Control.Monad.State  (MonadState(..), gets)
import Control.Monad.Writer (MonadWriter(..))
import Control.Monad.IO.Unlift
import Data.IORef (IORef(..))
import Data.Profunctor.Optic
import System.IO.Streams (InputStream, OutputStream)

import qualified Control.Category as C
import qualified Data.IORef as IOR

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

dimapping :: (b' -> b) -> (a -> a') -> PRef Profunctor rt rs b a -> PRef Profunctor rt rs b' a'
dimapping bt sa (PRef o rs rt) = PRef (o . dimap sa bt) rs rt

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
  (PRef oab sx _) . (PRef obc _ ty) = (PRef (compose_iso oab obc) sx ty) 


compose_iso :: AnIso s y a b -> AnIso x t b c -> Iso s t a c
compose_iso o o' = withIso o $ \ sa bt -> withIso o' $ \ s'a' b't' -> iso sa b't'

--compose_lens :: ALens s y a b -> ALens x t b c -> Lens s t a c
--compose_lens o o' = withLens o $ \ sa sbt -> withLens o' $ \ s'a' s'b't' -> lens sa sb't'

-- | Unbox a 'Pxy' by providing an existentially quantified continuation.
withPRef 
  :: PRef c rt rs b a 
  -> (forall x y. Optical c x y a b -> rs x -> rt y -> r) 
  -> r
withPRef (PRef o sx ty) f = f o sx ty

{-

type PMVar c b a = PRef c MVar MVar b a

type PInputStream c a = PRef' c InputStream a

type POutputStream c b = PRef' c OutputStream b

type PTChan c b a = PRef c TChan TChan b a

type PTQueue c b a = PRef c TQueue TQueue b a

type PTBQueue c b a = PRef c TBQueue TBQueue b a


-}

type PIORef c b a = PRef c IORef IORef b a

type PStream c b a = PRef c OutputStream InputStream b a



--TODO : this is the key function. you can have your has-pattern using the raw accessor functions of your caps type. or just use 'rs = id' if you want 'o' to be your accessor. write this up.
has :: MonadReader r m => c (Star (Const a)) => PRef c rt ((->) r) b a -> m a
has (PRef o rs _) = view o <$> asks rs

getex :: MonadState s m => c (Star (Const a)) => PRef c rt ((->) s) b a -> m a
getex (PRef o rs _) = view o <$> gets rs

tellex :: MonadWriter w m => c (Costar (Const a)) => PRef c m rs b a -> b -> m () 
tellex (PRef o _ rt) b = undefined -- runTracedT rt (review o b)
-- runTraced :: Traced m a -> m -> a
puts :: MonadState s m => (a -> s) -> a -> m ()
puts f = put . f

--putex :: MonadState s m => c (Star (Const a)) => PRef c rt ((->) s) b a -> m a
--putex p@(PRef o _ rt) = getex p >>= view o <$> gets rs



-- TODO could generalize this to arbitrary comonads.
readPure
  :: c (Star (Const a))
  => PRef c rt Identity b a 
  -> a
readPure (PRef o rs _) = view o . runIdentity $ rs

-- fills the (read-side) role of the lens in a Has type class
--readex :: MonadReader r m => c (Forget a) => PRef c rt ((->) r) b a -> m a
--readex (PRef o rs _) = view o <$> asks rs




tells :: MonadWriter w m => (a -> w) -> a -> m ()
tells f = tell . f


--tellex :: MonadWriter x m => c Tagged => PRef' c m a -> a -> m ()
--tellex (PRef' o _) b = tells (review o) b




--instance MonadReader (PRef c m rs b a) m => c (Forget a) => MonadReader a m where
    
--    ask = ask >>= \(PRef o s _) -> 
--
--


{-
>>>  pstate traversed (\a -> (a+1, show a)) $ fmap Sum [1,2,3]
["Sum {getSum = 1}","Sum {getSum = 2}","Sum {getSum = 3}","Sum {getSum = 4}","Sum {getSum = 5}"]
-}

pstate 
  :: Optic (Star ((,) a)) s t a b
  -> (a -> (a, b)) -> s -> t
pstate o f = star o snd f id

pmaybe
  :: Optic (Costar Maybe) s t a b 
  -> a -> (a -> b) -> Maybe s -> t
pmaybe o a ab = costar' o ab (maybe a id)

--star' up down o f = outof runStar up (o . into Star down $ f)



-- TODO check dynamically whether a 'Show' instance is available, and supply a default if not.
--debug :: Show t => Optic (Star IO) s t a b -> (a -> b) -> s -> IO ()
--debug o = star (>>=print) o return





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
