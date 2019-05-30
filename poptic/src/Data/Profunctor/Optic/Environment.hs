
module Data.Profunctor.Optic.Environment (
    module Data.Profunctor.Optic.Environment
  , module Export
  , Costar (..)
) where

import Data.Distributive
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Operator
import Data.Profunctor.Optic.Prelude

import Data.Profunctor.Closed as Export

import Control.Monad.IO.Unlift
import UnliftIO.Exception

--withRunInIO :: ((forall a. m a -> IO a) -> IO b) -> m b
environment :: (((s -> a) -> b) -> t) -> Env s t a b
environment f pab = dimap (flip ($)) f (closed pab)

environment' :: (s -> a) -> (b -> t) -> Env s t a b
environment' sa bt = environment $ envMod sa bt

unlifting :: MonadUnliftIO m => Env (m a) (m b) (IO a) (IO b)
unlifting = environment withRunInIO

masking :: MonadUnliftIO m => Env (m a) (m b) (m a) (m b)
masking = environment mask


---------------------------------------------------------------------
-- 
---------------------------------------------------------------------

-- | The 'EnvRep' profunctor precisely characterizes 'Env'.

newtype EnvRep a b s t = EnvRep { unEnvRep :: ((s -> a) -> b) -> t }

instance Profunctor (EnvRep a b) where
  dimap f g (EnvRep z) = EnvRep $ \d -> g (z $ \k -> d (k . f))

instance Closed (EnvRep a b) where
  -- closed :: p a b -> p (x -> a) (x -> b)
  closed (EnvRep z) = EnvRep $ \f x -> z $ \k -> f $ \g -> k (g x)

type AnEnv s t a b = Optic (EnvRep a b) s t a b

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

modEnv :: (((s -> a) -> b) -> t) -> (a -> b) -> s -> t
modEnv sabt ab s = sabt (\get -> ab (get s))

-- Every isomorphism is an environment.
envMod :: (s -> a) -> (b -> t) -> ((s -> a) -> b) -> t
envMod sa bt sab = bt (sab sa)

withEnv :: AnEnv s t a b -> ((s -> a) -> b) -> t
withEnv g = h where EnvRep h = (g (EnvRep $ \f -> f id))

cloneEnv :: AnEnv s t a b -> Env s t a b
cloneEnv g = environment (withEnv g)

cotraversed :: Distributive f => Env (f a) (f b) a b
cotraversed = environment $ \f -> cotraverse f id

cotraversing :: (Distributive f1, Functor f2) => (f2 a -> b) -> f2 (f1 a) -> f1 b
cotraversing = cotraverseOf cotraversed
