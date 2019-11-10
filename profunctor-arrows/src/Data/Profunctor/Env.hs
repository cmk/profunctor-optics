module Data.Profunctor.Env where

import Control.Arrow (Kleisli(..))
import Control.Category
import Control.Comonad (Comonad, Cokleisli(..))
import Control.Monad hiding (join)
import Data.Profunctor
import Data.Profunctor.Free
import Data.Profunctor.Misc

import Prelude

--IOEnv a a -> Acquire a, only works if au is a freeing function
--http://hackage.haskell.org/package/resourcet-1.2.2/docs/Data-Acquire.html
data Env m a b = Env (a -> m ()) (m b) 

type IOEnv = Env IO

instance Functor m => Functor (Env m a) where
  fmap f (Env amu mb) = Env amu (fmap f mb)

instance Functor m => Profunctor (Env m) where
  dimap f g (Env au b) = Env (au . f) (fmap g b) 

  lmap f (Env au b) = Env (au . f) b

  rmap = fmap

instance MonadPlus m => Category (Env m) where
  id = Env (const $ pure ()) mzero
  (.) (Env bu c) (Env au b) = Env (\a -> (au a >> b) >>= bu) c 
  -- couples all Envs in chain, using (Env au c) for impl would forget all but the last Env

readEnv :: Env m a b -> m b
readEnv (Env _ b) = b

writeEnv :: Env m a b -> a -> m ()
writeEnv (Env au _) a = au a

{-
import Data.IORef

--mkEnv :: IORef a -> IOEnv a a

mkEnvyo :: IORef a -> Yoneda IOEnv a a
mkEnvyo ref = Yoneda $ \f g -> dimap f g (mkEnv ref)

mkEnv ref = Env (writeIORef ref) (readIORef ref)

ref1 <- newIORef ("hi", 2)
ref2 <- newIORef ("ok", 3)

--foo :: IOEnv ([Char], Integer) ([Char], Integer)
foo = mkEnv ref1
bar = mkEnv ref2

foobar = foo . bar
readEnv foo
readEnv bar
readEnv foobar
writeEnv foobar ("yep",4)
readEnv foo
readEnv bar

λ> foo = mkEnv ref1
λ> bar = mkEnv ref2
λ> foobar = foo . bar
λ> readEnv foo
("hi",2)
λ> readEnv bar
("ok",3)
λ> readEnv foobar
("hi",2)
λ> writeEnv foobar ("yep",4)
λ> readEnv foobar
("yep",4)
λ> readEnv foo
("yep",4)
λ> readEnv bar
("yep",4)

-}


