{-# LANGUAGE TemplateHaskell, CPP #-}

module Data.Profunctor.Reference.PStream where

import Data.Profunctor.Optic
import Data.Profunctor.Reference.Types
import Data.Profunctor.Reference.Global

import Control.Monad.IO.Unlift
import System.IO.Streams (InputStream, OutputStream)
import qualified System.IO.Streams as S
import qualified System.IO.Streams.Combinators as SC



into :: ((a -> b) -> c) -> (r -> b) -> (a -> r) -> c
into up f = up . (f .)


outof :: (c -> a -> b) -> (b -> r) -> c -> a -> r
outof down g = (g .) . down


star
  :: (c -> f b)
  -> (f t -> d)
  -> Optic (Star f) s t a b 
  -> (a -> c)
  -> s
  -> d
star up down o f = outof runStar down (o . into Star up $ f)


costar
  :: (c -> b)
  -> (t -> d)
  -> Optic (Costar f) s t a b 
  -> (f a -> c)
  -> f s
  -> d
costar up down o f = outof runCostar down (o . into Costar up $ f)




neat
  :: Optic (Star Maybe) s t a b
  -> (a -> b) -> s -> Maybe t
neat o ab = (star Just . fmap) id o ab 

word
  :: Monoid a -- Default a
  => Optic (Costar Maybe) s t a b 
  -> (a -> b) -> Maybe s -> t
word o ab = costar ab id o (maybe mempty id)

--star' up down o f = outof runStar up (o . into Star down $ f)

baz
  :: Optic (Costar f) s t a b -> (f a -> b) -> f s -> Maybe t
baz = costar id Just

--data Pxy t s c b a = forall x y . Pxy (Optical c x y a b) !(s x) !(t y)

type PStream c b a = Pxy c OutputStream InputStream b a

type PInputStream c b a = Pxx c InputStream InputStream b a

--type PInputStream' c a = Px InputStream c a

type POutputStream c b = Px c OutputStream b

--type POutputStream' c b = Px OutputStream c b

-- | Read a value from a 'PStream' with profunctorial choice.
--
--  A return value of @'Nothing'@ indicates that either the underlying
-- 'InputStream' was empty, or that it was full and that the @a@ was not 
-- present.

previewPStream 
  :: MonadIO m 
  => c (Previewed a)
  => PStream c b a 
  -> m (Maybe a)
previewPStream (Pxy o rs _) = 
  liftIO (S.read rs) >>= return . (>>= preview o)

-- | Connects an 'InputStream' and 'OutputStream', supplying values from the
-- 'InputStream' to the 'OutputStream', and propagating the end-of-stream
-- message from the 'InputStream' through to the 'OutputStream'.
--
-- The connection ends when the 'InputStream' yields a 'Nothing'.

{-# INLINE connectPStream #-}

connectPStream
  :: MonadIO m 
  => c (->)
  => PStream c b a
  -> (a -> b)
  -> m ()
connectPStream (Pxy o rs rt) f = liftIO $ loop
  where
    loop = do
        ms <- S.read rs
        maybe (S.write Nothing rt)
              (\s -> S.write (Just $ over o f s) rt >> loop)
              ms



{-
-- | A variant of 'previewPStream' that writes the error value 't' to
-- 
-- the output stream whenever an 'a' is not available.

-- use this one to demo a server responding w/ an error 

matchPStream
  :: MonadIO m 
  => c (Matched a)
  => PStream c b a 
  -> m (Maybe a)
matchPStream (Pxy o rs rt) =



  do s <- readIORef rs
     case match o s of
       Left t -> 
         writeIORef rt t >> return Nothing
       Right a ->
         return $ Just a


-- | A variant of 'matchPStream' that additionally closes the output
-- 
-- stream once the input stream is no longer producing values.

matchPStream'
  :: MonadIO m 
  => c (Matched a)
  => PStream c b a 
  -> m (Maybe a)
matchPStream' (Pxy o rs rt) =


zipWith :: (a -> b -> c) -> InputStream a -> InputStream b -> IO (InputStream c)
zipWithOf :: Optic Zipped s t a b -> (a -> a -> b) -> s -> s -> t

zipWithPStream 
  :: c Zipped 
  => Pxx InputStream InputStream c b a
  -> (a -> a -> b) -> IO (Px InputStream c b)
zipWithPStream (Pxx o rs rs') f = 
  Px o <$> S.zipWith (zipWithOf o f) rs rs'


word
  :: Monoid a -- Default a
  => Optic (Costar Maybe) s t a b
  -> a -> (a -> b) -> Maybe s -> t
word o a ab = costar ab id o (maybe a id)

mapPStream
  :: (c (Forget a), MonadIO m) =>
     P rt InputStream c b a -> (a -> b2) -> m (InputStream b2)
mapPStream (Pxy o rs _) f = liftIO $ SC.map (f . view o) rs


mapPStream (Pxy o rs _) = liftIO $ SC.map (f . view o) rs


map :: MonadUnliftIO m => (a -> b) -> InputStream a -> m (InputStream b)
map f is = is

map :: (a -> b) -> InputStream a -> IO (InputStream b)
contramap :: (a -> b) -> OutputStream b -> IO (OutputStream a)



flushPStream' (P _ rt rs) = liftIO $ S.connect rs rt
connectPStream (Pxy o rs rt) = 


read :: MonadUnliftIO m => InputStream a -> m (Maybe a)
read as = liftIO $ S.read as
map :: MonadUnliftIO m => (a -> b) -> InputStream a -> m (InputStream b)
map f is = liftIO $ SC.map f is

modifyPRef 
  :: c (->)
  => PRef IORef c b a 
  -> (a -> b) 
  -> IO ()
modifyPRef (Pxy o rs rt) f = readIORef rs >>= writeIORef rt . over o f

-}

