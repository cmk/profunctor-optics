{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE QuantifiedConstraints     #-}

{-# OPTIONS_GHC -w #-}
module Data.Profunctor.Reference.PRefs (
    module Export
  , module Data.Profunctor.Reference.PRefs
) where

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
import Data.StateVar as Export
-- (HasGetter(..), HasSetter(..), HasUpdate(..), ($=), ($=!), ($~), ($~!))
import Data.Void
import System.IO.Streams (InputStream, OutputStream)

import qualified Data.StateVar as SV
import qualified Control.Category as C
import qualified Data.IORef as IOR


-- TODO consider using the version from contravariant.
-- | Dual function arrows.
newtype Op a b = Op { runOp :: b -> a }

type (<—) a b = Op a b

instance Category Op where
  id = Op id
  Op f . Op g = Op (g . f)

--type (<—) a b = b -> a

contra :: (c -> b) -> (a <— b) -> (a <— c)
contra f g = Op (runOp g . f)

--instance Contravariant (Op a) where contramap f g = Op (getOp g . f)

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

-- data PRefs c rt rs b a 
data PRefs c rt rs b a = forall x y . PRefs (Optical c x y a b) !(rs x) !(rt y)

-- TODO c :- Profunctor
dimap' :: (b' -> b) -> (a -> a') -> PRefs Profunctor rt rs b a -> PRefs Profunctor rt rs b' a'
dimap' bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Profunctor (PRefs Profunctor rt rs) where dimap = dimap'

instance Profunctor (PRefs Strong rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Profunctor (PRefs Costrong rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Profunctor (PRefs Choice rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Profunctor (PRefs Cochoice rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Profunctor (PRefs Closed rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Profunctor (PRefs Mapping rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Profunctor (PRefs Traversing rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Profunctor (PRefs AffineTraversing rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Profunctor (PRefs Folding rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Profunctor (PRefs AffineFolding rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Profunctor (PRefs Getting rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Profunctor (PRefs Reviewing rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Strong (PRefs Costrong rt rs) where first' (PRefs o rs rt) = PRefs (o . unfirst) rs rt

instance Costrong (PRefs Strong rt rs) where unfirst (PRefs o rs rt) = PRefs (o . first') rs rt

instance Choice (PRefs Cochoice rt rs) where right' (PRefs o rs rt) = PRefs (o . unright) rs rt

instance Cochoice (PRefs Choice rt rs) where unright (PRefs o rs rt) = PRefs (o . right') rs rt

instance Category (PRefs Profunctor rt rs) where 
  id = undefined -- TODO produce these w/ TH based on monoid instances from the underlying s,t
  (PRefs oab sx _) . (PRefs obc _ ty) = (PRefs (compose_iso oab obc) sx ty) 


compose_iso :: AnIso s y a b -> AnIso x t b c -> Iso s t a c
compose_iso o o' = withIso o $ \ sa bt -> withIso o' $ \ s'a' b't' -> iso sa b't'

--compose_lens :: ALens s y a b -> ALens x t b c -> Lens s t a c
--compose_lens o o' = withLens o $ \ sa sbt -> withLens o' $ \ s'a' s'b't' -> lens sa sb't'


instance (forall s . HasGetter (rs s) s) => HasGetter (PRefs Getting rt rs b a) a where

  get (PRefs o rs _) = liftIO $ view o <$> SV.get rs
  {-# INLINE get #-}

instance (forall s. HasGetter (rs s) s, forall t. HasSetter (rt t) t) => HasSetter (PRefs Mapping rt rs b a) b where

  (PRefs o rs rt) $= b = liftIO $ SV.get rs >>= \s -> rt $= over o (const b) s
  {-# INLINE ($=) #-}

instance (forall s. HasGetter (rs s) s, forall t. HasSetter (rt t) t) => HasUpdate (PRefs Mapping rt rs b a) a b where

  (PRefs o rs rt) $~ f  = liftIO $ SV.get rs >>= \s -> rt $= over o f s

  (PRefs o rs rt) $~! f = liftIO $ SV.get rs >>= \s -> rt $=! over o f s

-- | Unbox a 'Pxy' by providing an existentially quantified continuation.
withPRefs 
  :: PRefs c rt rs b a 
  -> (forall x y. Optical c x y a b -> rs x -> rt y -> r) 
  -> r
withPRefs (PRefs o sx ty) f = f o sx ty


{-

type PMVar c b a = PRefs c MVar MVar b a

type PInputStream c a = PRef c InputStream a

type POutputStream c b = PRef c OutputStream b

type PTChan c b a = PRefs c TChan TChan b a

type PTQueue c b a = PRefs c TQueue TQueue b a

type PTBQueue c b a = PRefs c TBQueue TBQueue b a


-}






--TODO : this is the key function. fills the (read-side) role of the lens in a Has type class
-- you can have your has-pattern using the raw accessor functions of your caps type,
-- or just use 'rs = id' if you want 'o' to be your accessor.  write this up.
has :: MonadReader r m => c (Star (Const a)) => PRefs c rt ((->) r) b a -> m a
has (PRefs o rs _) = view o <$> asks rs

contraview :: Optic (Costar (Const b)) s t a b -> (c <— t) -> c <— b
contraview = contra . review

gives :: MonadWriter w m => c (Costar (Const b)) => PRefs c (Op w) rs b a -> b -> m ()
gives (PRefs o _ rt) b = tells (runOp $ contraview o rt) b

tells :: MonadWriter w m => (a -> w) -> a -> m ()
tells f = tell . f


foox :: MonadIO m => PRefs c (Star m b) rs b a -> b -> m ()
foox (PRefs _ _ rt) b = runStar rt b >> return ()


-- TODO check dynamically whether a 'Show' instance is available, and supply a default if not.
--debug :: Show t => Optic (Star IO) s t a b -> (a -> b) -> s -> IO ()
--debug o = star (>>=print) o return


pstate 
  :: Optic (Star ((,) a)) s t a b
  -> (a -> (a, b)) -> s -> t
pstate o f = star o snd f id

pmaybe
  :: Optic (Costar Maybe) s t a b 
  -> a -> (a -> b) -> Maybe s -> t
pmaybe o a ab = costar' o ab (maybe a id)

--star' up down o f = outof runStar up (o . into Star down $ f)


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
