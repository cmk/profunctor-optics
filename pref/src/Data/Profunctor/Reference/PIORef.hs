{-# LANGUAGE TemplateHaskell, CPP #-}

module Data.Profunctor.Reference.PIORef where

import Data.IORef
import Data.Monoid
import Data.Profunctor.Optic
import Data.Profunctor.Reference.PRef
import Data.Profunctor.Reference.Global
import Data.Profunctor.Reference.Types

import Data.Tuple (swap)
import Control.Category ((>>>),(<<<))
import Control.Monad.IO.Unlift

import Control.Monad.Trans.Reader


type PIORef c b a = PRef c X IORef b a

----------------------------------------------------------------
--  Creating 'PIORef's
---------------------------------------------------------------------

-- | Create a new 'PIORef' with purely local state.
--
-- The optic argument is exposed for completeness, but in most cases
-- should be set to 'id'.
newLocalPIORef 
  :: Optical c s s a b 
  -> s 
  -> IO (PIORef c b a)
newLocalPIORef o s = (PRef o) <$> newIORef s 


---------------------------------------------------------------------
--  Reading 'PIORef's
---------------------------------------------------------------------


-- | Read a value from a 'PIORef'.
--
--
readPIORef 
  :: c (Star (Const a)) 
  => PIORef c b a 
  -> IO a
readPIORef (PRef o rs) = view o <$> readIORef rs


-- | Read a value from a 'PIORef' with profunctorial choice.
previewPIORef 
  :: c (Star (Const (First a)))
  => PIORef c b a 
  -> IO (Maybe a)
previewPIORef (PRef o rs) = preview o <$> readIORef rs 


-- | A variant of 'previewPIORef' that updates the write ref on failure.
--
-- If the read and write refs are the same then this function reduces
-- to 'previewPIORef' with the overhead of an extra io operation.
matchPIORef
  :: c (Star (Either a))
  => PIORef c b a 
  -> IO (Maybe a)
matchPIORef (PRef o rs) =
  do s <- readIORef rs
     case match o s of
       Left t -> 
         writeIORef rs t >> return Nothing
       Right a ->
         return $ Just a


foldMapOfPIORef
  :: c (Star (Const r))
  => PIORef c b a 
  -> (a -> r)
  -> IO r
foldMapOfPIORef (PRef o rs) f = foldMapOf o f <$> readIORef rs 


-- sumPIORef?
sumOfPIORef :: c (Star (Const (Sum a))) => PIORef c b a -> IO a
sumOfPIORef r = getSum <$> foldMapOfPIORef r Sum



---------------------------------------------------------------------
--  Modifying 'PIORef's
---------------------------------------------------------------------

-- | Write operation that only opens the write ref.
--
-- Use this with 'Choice'-constrained optics.  Use 'modifyPIORef' with
-- a constant argument to modify lens-like optics.
writePIORef :: c (Costar (Const b)) => PIORef c b a -> b -> IO ()
writePIORef (PRef o rs) b = writeIORef rs . review o $ b


-- | Modify a 'PIORef'.
--
-- Note that this operation is lazy. Depending on use unevaluated 
-- expression thunks can pile up in memory resulting in a space leak. 
-- To update strictly use 'modifyPIORef''.
--
-- Lens example:
--
-- >>> s = ("hi!",2) :: (String, Int)
-- >>> t = (4,2)  :: (Int, Int)
-- >>> rs <- newRef @IO @IORef s
-- >>> rs <- newRef @IO @IORef t
-- >>> o :: PIORef Strong Int String = PRefs _1 rs rs
-- >>> o' :: PIORef Strong String String = PRefs _1 rs rs
--
-- >>> modifyPIORef o' tail >> readIORef rs 
-- ("i!",2)
-- >>> readIORef rs 
-- (4,2)
-- >>> modifyPIORef o length >> readIORef rs
-- ("i!",2)
-- >>> readIORef rs 
-- (2,2)
--
--
-- Prism example:
--
-- >>> s = Just "hi!" :: Maybe String
-- >>> t = Nothing  :: Maybe Int
-- >>> rs <- newRef @IO @IORef s
-- >>> rs <- newRef @IO @IORef t
-- >>> o :: PIORef Choice Int String = PRefs _Just rs rs
-- >>> o' :: PIORef Choice String String = PRefs _Just rs rs
-- >>> modifyPIORef o' tail >> readIORef rs
-- Just "i!"
-- >>> readIORef rs 
-- Nothing
-- >>> modifyPIORef o length >> readIORef rs
-- Just "i!"
-- >>> readIORef rs 
-- Just 2
--
--
-- Traversal example:
--
-- >>> s = ["hi", "there"] :: [String]
-- >>> t = fmap Sum [1..10] :: [Sum Int]
-- >>> rs <- newRef @IO @IORef s
-- >>> rs <- newRef @IO @IORef t
-- >>> o :: PIORef Traversing (Sum Int) String = PRefs traversed rs rs
-- >>> o' :: PIORef Traversing String String = PRefs traversed rs rs
-- >>> modifyPIORef o (Sum . length) >> readIORef rs
-- ["hi","there"]
-- >>> readIORef rs 
-- [Sum {getSum = 2},Sum {getSum = 5}]
-- >>> modifyPIORef o' ("oh" ++) >> readIORef rs
-- ["ohhi","ohthere"]
--
modifyPIORef 
  :: MonadIO m
  => c (->)
  => PIORef c b a 
  -> (a -> b) 
  -> m ()
modifyPIORef (PRef o rs) f = liftIO $ modifyIORef rs (over o f)


-- | Strict variant of 'modifyPIORef'. This forces both the value stored
--
-- as well as the value returned. This function is atomic when r is a 
-- TVar or TMVar.
modifyPIORef' :: c (->) => PIORef c b a -> (a -> b) -> IO ()
modifyPIORef' (PRef o rs) f = liftIO $ modifyIORef' rs (over o f)

{-
-- TODO more like foldState
atomicModifyPIORef'
  :: c (Star ((,) a))
  => PIORef c b a 
  -> (a -> (a, b))
  -> IO ()
atomicModifyPIORef' (PRef o rs) f = 
  do s <- readIORef rs
     let t = pstate o f s
     t `seq` writeIORef rs t

-}
