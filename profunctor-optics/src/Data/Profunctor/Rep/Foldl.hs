
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# OPTIONS_GHC -fno-warn-orphans      #-}

module Data.Profunctor.Rep.Foldl (
  -- * Foldl
    Foldl (..)
  , Unfoldl (..)
  , run
  , foldl
  , Data.Profunctor.Rep.Foldl.ofoldl
  , build
  , prefix
  , prescan
  , postscan
  , withFoldl
  -- * FoldlM
  , FoldlM (..)
  , UnfoldlM (..)
  , foldlM
  , buildM
  , premapM
  , withFoldlM
  -- * Folds
  , list
  , revList
  , mconcat
  , stepMay
  , stepDef
  , headDef
  , lastDef
  , maximumDef
  , maximumByDef
  , minimumDef
  , minimumByDef
  , generalize
  , sink
  , halt
  , halt_
  , skip
  , skip_
  -- * Unfolds
  , foldable
  , ofoldable
  , foldableM
  -- * Monomorphic folds
  , Data.Profunctor.Rep.Foldl.lazy
  , Data.Profunctor.Rep.Foldl.onull
  , Data.Profunctor.Rep.Foldl.ohead
  , Data.Profunctor.Rep.Foldl.olast
  , Data.Profunctor.Rep.Foldl.olength
  , Data.Profunctor.Rep.Foldl.oall
  , Data.Profunctor.Rep.Foldl.oany
  , Data.Profunctor.Rep.Foldl.oelem
  , Data.Profunctor.Rep.Foldl.onotElem
  , sfind
  ) where

import Control.Arrow (Kleisli(..),(***))
import Control.Applicative
import Control.Monad (MonadPlus(..), (>=>),ap, liftM)
import Control.Monad.Fix (MonadFix(..))
import Control.Monad.Reader (MonadReader(..))
import Control.Monad.Trans (MonadTrans(..))
import Data.Distributive (Distributive (..))
import Data.Functor.Rep as Functor (Representable (..), askRep, localRep, mfixRep)
import Data.Functor.Identity
import Data.List (mapAccumL)
import Data.Profunctor
import Data.Profunctor.Closed (Closed (..))
import Data.Profunctor.Rep as Profunctor (Corepresentable (..), unfirstCorep, unsecondCorep)
import Data.Profunctor.Sieve (Cosieve (..))
import Data.Strict.Tuple hiding (snd)
import Prelude as P hiding
  ( head, last, null, length, and, or, all, any, sum, product, maximum, 
    minimum, mconcat, elem, notElem, lookup, map, either, drop, 
    Fractional(..), foldl
  )
import qualified Data.Foldable as F
import qualified Data.Strict.Maybe as M'
import qualified Data.Strict.Either as E'

import Control.Exception (Exception (..), SomeException (..), IOException, SomeAsyncException (..))
import qualified Control.Exception as Ex

import Control.Monad.IO.Unlift
import Data.MonoTraversable (MonoFoldable(..), Element)
import Data.Sequences (SemiSequence, IsSequence, LazySequence, Index)
import qualified Data.Sequences as MS
import qualified Data.List.NonEmpty as NE
import qualified Data.MonoTraversable as MT
import System.IO (Handle, hIsEOF)





{-
import Data.IOData (IOData, hGetChunk, hGetLine, hPut, hPutStrLn)
import Data.List
import Data.Word (Word8)


import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC8

type DataModeIO m a = MonadIO m => ((Handle -> m a), (Handle -> a -> m ()))


type SinkIO m k = MonadIO m => forall a. ProcessT m k a
type SourceIO m a = MonadIO m => forall k. ListT m k a

type IODataMode a = ((Handle -> IO a), (Handle -> a -> IO ()))
type IOSink k = forall a. ProcessT IO k a
type IOSource a = forall k. ListT IO k a

byChar :: IODataMode Char
byChar = (\h -> BSC8.head <$> BSC8.hGet h 1, \h w -> BSC8.hPut h $ BSC8.pack [w])

byChunk ::  IOData a => IODataMode a
byChunk = (\h -> hGetChunk h, \h xs -> hPut h xs)

byChunkOf :: Int -> IODataMode BS.ByteString
byChunkOf n = (\h -> BS.hGet h n, \h xs -> BS.hPut h xs)

byWord8 :: IODataMode Word8
byWord8 = (\h -> BS.head <$> BS.hGet h 1, \h w -> BS.hPut h $ BS.pack [w])

byLine :: IOData a => DataModeIO m a
byLine = (hGetLine, hPutStrLn)

sourceIO :: IO a -> SourceIO m a
sourceIO f = repeatedly $ liftIO f >>= yield

sourceHandle :: DataModeIO m a -> Handle -> SourceIO m a
sourceHandle (r, _) = sourceHandleWith r

sourceIOWith :: m r -> (r -> m Bool) -> (r -> m a) -> SourceIO m a
sourceIOWith acquire release read' = ListT $ do
  r         <- acquire
  released  <- release r
  if released then
    return Stop
  else do
    x <- read' r
    return . Yield x $ sourceIOWith acquire release read'

sourceHandleWith :: (Handle -> m a) -> Handle -> SourceIO m a
sourceHandleWith f h = sourceIOWith (return h) (liftIO . hIsEOF) f

sinkIO :: (a -> IO ()) -> SinkIO m a
sinkIO f = repeatedly $ await >>= liftIO . f

sinkHandle :: IODataMode a -> Handle -> SinkIO m a
sinkHandle (_, w) h = repeatedly $ await >>= liftIO . w h

sinkHandleWith :: (Handle -> a -> IO ()) -> Handle -> SinkIO m a
sinkHandleWith f h = repeatedly $ await >>= liftIO . f h

filteredIO :: (a -> IO Bool) -> ProcessT IO a a
filteredIO p = repeatedly $ do
  i <- await
  x <- liftIO $ p i
  if x then yield i else return ()

printer :: Show a => SinkIO m a
printer = sinkIO $ liftIO . print
-}


---------------------------------------------------------------------
-- Foldl
---------------------------------------------------------------------

data Foldl a b = forall x. Foldl (x -> a -> x) x (x -> b)

newtype Unfoldl a = Unfoldl (forall x. (x -> a -> x) -> x -> x)


run :: Foldl a b -> a -> b
run (Foldl h z k) t = k (h z t)
{-# INLINABLE run #-}

foldl :: Foldable f => Foldl a b -> f a -> b
foldl (Foldl h z k) as = F.foldr cons k as z
  where
    cons a k x = k $! h x a
{-# INLINABLE foldl #-}

-- | Apply a strict left 'Fold' to a 'Data.MonoTraversable.MonoFoldable'.
--
ofoldl :: MonoFoldable a => Foldl (Element a) b -> a -> b
ofoldl (Foldl h z k) as =
    k (MT.ofoldl' h z as)
{-# INLINABLE ofoldl #-}

-- | A version of the /build/ function from < http://hackage.haskell.org/package/base-4.12.0.0/docs/src/GHC.Base.html#build base >.
--
build :: Foldl a b -> Unfoldl a -> b
build (Foldl h z k) (Unfoldl run) = k (run h z)
{-# INLINE build #-}

-- | TODO: Document
--
withFoldl :: Foldl a b -> (forall x. (x -> a -> x) -> x -> (x -> b) -> r) -> r
withFoldl (Foldl h z k) f = f h z k
{-# INLINABLE withFoldl #-}

prefix :: a -> Foldl a b -> Foldl a b
prefix a = flip run a . duplicate
{-# INLINABLE prefix #-}




{-

--
scan :: Foldl a b -> [a] -> [b]
scan (Foldl h z k) as = foldr cons nil as z
  where
    nil      x = k x:[]
    cons a k x = k x:(k $! h x a)
{-# INLINE scan #-}


-}

-- | Convert a `Foldl` into a prescan for any `Traversable` type
--
--  \"Prescan\" means that the lastDef element of the scan is not included
--
prescan :: Traversable f => Foldl a b -> f a -> f b
prescan (Foldl h z k) as = bs
  where
    h' x a = (x', b)
      where
        x' = h x a
        b  = k x
    (_, bs) = mapAccumL h' z as
{-# INLINE prescan #-}

-- | Convert a `Foldl` into a postscan for any `Traversable` type
--
--  \"Postscan\" means that the first element of the scan is not included
--
postscan :: Traversable f => Foldl a b -> f a -> f b
postscan (Foldl h z k) as = bs
  where
    h' x a = (x', b)
      where
        x' = h x a
        b  = k x'
    (_, bs) = mapAccumL h' z as
{-# INLINE postscan #-}

---------------------------------------------------------------------
-- FoldlM
---------------------------------------------------------------------

data FoldlM m a b = forall x . FoldlM (x -> a -> m x) (m x) (x -> m b)


{-|
A monadic variation of "DeferredFolds.Unfoldl"
-}
newtype UnfoldlM m a = UnfoldlM (forall x. (x -> a -> m x) -> x -> m x)

-- | Like 'fold', but monadic
foldlM :: (Foldable f, Monad m) => FoldlM m a b -> f a -> m b
foldlM (FoldlM h z k) as0 = do
    x0 <- z
    F.foldr h' k as0 $! x0
  where
    h' a k x = do
        x' <- h x a
        k $! x'
{-# INLINE foldlM #-}


{-

-- | Apply a strict monadic left 'FoldlM' to a lazy bytestring
--foldM :: Monad m => FoldlM m ByteString a -> Data.ByteString.Lazy.ByteString -> m a
ofoldM (FoldlM h z k) as = do
    x <- Data.ByteString.Lazy.Internal.foldlChunks h' z as
    k x
  where
    h' mx bs = do
      x <- mx
      x `seq` h x bs
{-# INLINABLE foldM #-}
-}

buildM :: Monad m => FoldlM m a b -> UnfoldlM m a -> m b
buildM (FoldlM h z k) (UnfoldlM run) =
  do
    s0 <- z
    sn <- run h s0
    k sn

withFoldlM :: FoldlM m a b -> (forall x. (x -> a -> m x) -> m x -> (x -> m b) -> r) -> r
withFoldlM (FoldlM h z k) f = f h z k

---------------------------------------------------------------------
-- Folds
---------------------------------------------------------------------

-- | Foldl all values into a list
list :: Foldl a [a]
list = Foldl (\x a -> x . (a:)) id ($ [])
{-# INLINABLE list #-}

-- | Foldl all values into a list, in reverse order
revList :: Foldl a [a]
revList = Foldl (\x a -> a:x) [] id
{-# INLINABLE revList #-}

-- | Convert a \"@mconcats@\" to a 'Fold'
mconcat :: Monoid m => (a -> m) -> (m -> b) -> Foldl a b
mconcat to = Foldl (\x a -> mappend x (to a)) mempty
{-# INLINABLE mconcat #-}

-- | Return the result of a step function.
--
-- Results in a 'Nothing' value for empty containers.
--
stepMay :: (a -> a -> a) -> Foldl a (Maybe a)
stepMay h = Foldl h_ M'.Nothing toLazy
  where
    h_ mx a = M'.Just (case mx of
        M'.Nothing -> a
        M'.Just x -> h x a)
{-# INLINABLE stepMay #-}

stepDef :: a -> (a -> a -> a) -> Foldl a a
stepDef a h = maybe a id <$> stepMay h
{-# INLINABLE stepDef #-}

-- | Return the first element of a collection.
--
-- Returns a default if the container is empty.
--
headDef :: a -> Foldl a a
headDef a = stepDef a const
{-# INLINABLE headDef #-}

-- | Return the last element of a collection.
--
-- Returns a default if the container is empty.
--
lastDef :: a -> Foldl a a
lastDef a = stepDef a (flip const)
{-# INLINABLE lastDef #-}

-- | Return the maximumDef element of a collection.
--
-- Returns a default if the container is empty.
--
maximumDef :: Ord a => a ->Foldl a a
maximumDef a = stepDef a max
{-# INLINABLE maximumDef #-}

-- | Return the maximumDef element of a collection wrt a comparator.
--
-- Returns a default if the container is empty.
--
maximumByDef :: (a -> a -> Ordering) -> a -> Foldl a a
maximumByDef cmp a = stepDef a max'
  where
    max' x y = case cmp x y of
        GT -> x
        _  -> y
{-# INLINABLE maximumByDef #-}

-- | Return the minimumDef element of a collection.
--
-- Returns a default if the container is empty.
--
minimumDef :: Ord a => a -> Foldl a a
minimumDef a = stepDef a min
{-# INLINABLE minimumDef #-}

-- | Return the minimumDef element of a collection wrt a comparator.
--
-- Returns a default if the container is empty.
--
minimumByDef :: (a -> a -> Ordering) -> a -> Foldl a a
minimumByDef cmp a = stepDef a min'
  where
    min' x y = case cmp x y of
        GT -> y
        _  -> x
{-# INLINABLE minimumByDef #-}

{-| Generalize a `Fold` to a `FoldlM`

> generalize (pure r) = pure r
>
> generalize (f <*> x) = generalize f <*> generalize x
-}
generalize :: Monad m => Foldl a b -> FoldlM m a b
generalize (Foldl h z k) = FoldlM h' z' k'
  where
    h' x a = return (h x a)
    z'    = return  z
    k' x   = return (k x)
{-# INLINABLE generalize #-}

premapM :: Monad m => (a -> m b) -> FoldlM m b r -> FoldlM m a r
premapM f (FoldlM h z k) = FoldlM h' z k
  where
    h' x a = f a >>= h x
{-# INLINABLE premapM #-}

-- | Converts an effectful function to a fold. Specialized version of 'sink'.
--maplM_ :: Monad m => (a -> m ()) -> FoldlM m a ()
--maplM_ = sink
--{-# INLINABLE maplM_ #-}


-- import qualified Control.Exception as Ex
-- >>> f x = if x < 10 then return x else Ex.throw Ex.Overflow
-- >>> exfold = premapM f (generalize list)
-- >>> xs = [1, 2, 500, 4] :: [Integer]
-- >>> foldlM (halt @Ex.ArithException exfold) xs
-- (Just arithmetic overflow,[1,2])
{-| Converts an effectful function to a fold

> sink (f <> g) = sink f <> sink g -- if `(<>)` is commutative
> sink mempty = mempty
-}



sink ::  (Monoid b, Monad m) => (a -> m b) -> FoldlM m a b
sink act = FoldlM h z k  where
  k = return
  z = return mempty
  h m a = do
    m' <- act a
    return $! mappend m m'
{-# INLINABLE sink #-}

halt_ :: MonadUnliftIO m => FoldlM m a b -> FoldlM m a b
halt_ f = fmap snd (halt @SomeException f)

{-
-- >>> import qualified Control.Exception as Ex
-- >>> f x = if x < 10 then return x else Ex.throw Ex.Overflow
-- >>> exfold = premapM f (generalize list)
-- >>> xs = [1, 2, 500, 4] :: [Integer]
-- >>> foldlM (halt @Ex.ArithException exfold) xs
-- (Just arithmetic overflow,[1,2])
-}

halt :: Exception e => MonadUnliftIO m => FoldlM m a b -> FoldlM m a (Maybe e, b)
halt (FoldlM h z k) = FoldlM h' z' k'
  where
    z' =
      do
        y <- z
        return (Nothing, y)

    h' x'@(Just _, _) _ = return x'
    h' (Nothing, x1) a =
      do
        x2Either <- flip catch (return . Left) . liftM Right $ h x1 a
        case x2Either of
            Left e   -> return (Just e, x1)
            Right x2 -> return (Nothing, x2)

    k' (eMaybe, x) =
      do
        b <- k x
        return (eMaybe, b)

skip_ :: MonadUnliftIO m => FoldlM m a b -> FoldlM m a b
skip_ f = fmap snd (skip @SomeException f)

skip :: Exception e => MonadUnliftIO m => FoldlM m a b -> FoldlM m a ([e], b)
skip (FoldlM h z k) = FoldlM h' z' k'
  where
    z' =
      do
        y <- z
        return (id, y)

    h' (es, x1) a =
      do
        x2Either <- flip catch (return . Left) . liftM Right $ h x1 a
        case x2Either of
            Left e   -> return (es . (e :), x1)
            Right x2 -> return (es, x2)

    k' (es, x) =
      do
        b <- k x
        return (es [], b)

---------------------------------------------------------------------
-- Monomorphic folds
---------------------------------------------------------------------

-- | Combine strict chunks to build a 'Data.Sequences.LazySequence'
--
lazy :: LazySequence l s => Foldl s l
lazy = fmap MS.fromChunks list

-- | Returns 'True' if the /a/ is empty, 'False' otherwise
--
onull :: MonoFoldable a => Foldl a Bool
onull = Foldl h True id
  where
    h isNull bs = isNull && MT.onull bs
{-# INLINABLE onull #-}

-- | Get the first byte of a byte stream or return 'Nothing' if the stream is empty
--
ohead :: MonoFoldable a => Foldl a (Maybe (Element a))
ohead = Foldl h M'.Nothing toLazy
  where
    h me bs =
        if MT.onull bs
        then me
        else case me of
            M'.Just _  -> me
            M'.Nothing -> toStrict $ MT.headMay bs
{-# INLINABLE ohead #-}

-- | Get the last byte of a byte stream or return 'Nothing' if the byte stream is empty
--
olast :: MonoFoldable a => Foldl a (Maybe (Element a))
olast = Foldl h M'.Nothing toLazy
  where
    h me bs =
        if MT.onull bs
        then me
        else case me of
            M'.Just _  -> me
            M'.Nothing -> toStrict $ MT.lastMay bs
{-# INLINABLE olast #-}

-- | Return the length of /a/ in bytes.
--
olength :: MonoFoldable a => Num n => Foldl a n
olength = Foldl h 0 id
  where
    h n bs = n + fromIntegral (MT.olength bs)
{-# INLINABLE olength #-}

-- | Return 'True' if all bytes satisfy the predicate, 'False' otherwise.
--
oall :: MonoFoldable a => (Element a -> Bool) -> Foldl a Bool
oall predicate = Foldl (\b bs -> b && MT.oall predicate bs) True id
{-# INLINABLE oall #-}

-- | Return 'True' if any byte satisfies the predicate, 'False' otherwise.
--
oany :: MonoFoldable a => (Element a -> Bool) -> Foldl a Bool
oany predicate = Foldl (\b bs -> b || MT.oany predicate bs) False id
{-# INLINABLE oany #-}

-- | @(elem e)@ returns 'True' if the byte stream has a byte equal to @e@, 'False' otherwise
--
oelem :: MonoFoldable a => Eq (Element a) => Element a -> Foldl a Bool
oelem e = Data.Profunctor.Rep.Foldl.oany (e ==)
{-# INLINABLE oelem #-}

-- | @(notElem e)@ returns 'False' if the byte stream has a byte equal to @e@, 'True' otherwise
--
onotElem :: MonoFoldable a => Eq (Element a) => Element a -> Foldl a Bool
onotElem e = Data.Profunctor.Rep.Foldl.oall (e /=)
{-# INLINABLE onotElem #-}

-- | Return the first element that satisfies the predicate or 'Nothing' otherwise.
--
sfind :: SemiSequence a => (Element a -> Bool) -> Foldl a (Maybe (Element a))
sfind predicate = Foldl h M'.Nothing toLazy 
  where
    h e bs = case e of
        M'.Nothing -> toStrict (MS.find predicate bs)
        M'.Just _  -> e
{-# INLINABLE sfind #-}



---------------------------------------------------------------------
-- Unfolds
---------------------------------------------------------------------

-- | Construct an 'Unfoldl' from a 'Data.Foldable'.
--
foldable :: Foldable f => f a -> Unfoldl a
foldable f = Unfoldl (\ h init -> F.foldl' h init f)
{-# INLINE foldable #-}

ofoldable :: MonoFoldable a => a -> Unfoldl (Element a)
ofoldable f = Unfoldl (\ h init -> MT.ofoldl' h init f)

{-| Construct from any foldable -}
foldableM :: Foldable f => Monad m => f a -> UnfoldlM m a
foldableM f = UnfoldlM (\ h init -> F.foldlM h init f)
{-# INLINE foldableM #-}

{-
{-| Lift a fold input mapping function into a mapping of unfolds -}
{-# INLINE mapFoldInput #-}
mapFoldInput :: (forall x. Fold b x -> Fold a x) -> Unfoldl a -> Unfoldl b
mapFoldInput newFold unfold = Unfoldl $ \ step init -> fold (newFold (Fold step init id)) unfold

{-| Construct from any foldable -}
{-# INLINE foldable #-}
foldable :: Foldable foldable => foldable a -> Unfoldl a
foldable foldable = Unfoldl (\ step init -> A.foldl' step init foldable)

{-| Filter the values given a predicate -}
{-# INLINE filter #-}
filter :: (a -> Bool) -> Unfoldl a -> Unfoldl a
filter test (Unfoldl run) = Unfoldl (\ step -> run (\ state element -> if test element then step state element else state))

{-| Ints in the specified inclusive range -}
{-# INLINE intsInRange #-}
intsInRange :: Int -> Int -> Unfoldl Int
intsInRange from to =
  Unfoldl $ \ step init ->
  let
    loop !state int =
      if int <= to
        then loop (step state int) (succ int)
        else state
    in loop init from

{-| Associations of a map -}
{-# INLINE mapAssocs #-}
mapAssocs :: Map key value -> Unfoldl (key, value)
mapAssocs map =
  Unfoldl (\ step init -> C.foldlWithKey' (\ state key value -> step state (key, value)) init map)

{-| Associations of an intmap -}
{-# INLINE intMapAssocs #-}
intMapAssocs :: IntMap value -> Unfoldl (Int, value)
intMapAssocs intMap =
  Unfoldl (\ step init -> D.foldlWithKey' (\ state key value -> step state (key, value)) init intMap)

{-| Bytes of a bytestring -}
{-# INLINE byteStringBytes #-}
byteStringBytes :: ByteString -> Unfoldl Word8
byteStringBytes bs = Unfoldl (\ step init -> ByteString.foldl' step init bs)

{-| Bytes of a short bytestring -}
{-# INLINE shortByteStringBytes #-}
shortByteStringBytes :: ShortByteString -> Unfoldl Word8
shortByteStringBytes (ShortByteString.SBS ba#) = primArray (PrimArray ba#)

{-| Elements of a prim array -}
{-# INLINE primArray #-}
primArray :: (Prim prim) => PrimArray prim -> Unfoldl prim
primArray ba = Unfoldl $ \ f z -> foldlPrimArray' f z ba

{-| Elements of a prim array coming paired with indices -}
{-# INLINE primArrayWithIndices #-}
primArrayWithIndices :: (Prim prim) => PrimArray prim -> Unfoldl (Int, prim)
primArrayWithIndices pa = Unfoldl $ \ step state -> let
  !size = sizeofPrimArray pa
  iterate index !state = if index < size
    then iterate (succ index) (step state (index, indexPrimArray pa index))
    else state
  in iterate 0 state



{-| Lift a fold input mapping function into a mapping of unfolds -}
{-# INLINE mapFoldMInput #-}
mapFoldMInput :: Monad m => (forall x. FoldM m b x -> FoldM m a x) -> UnfoldlM m a -> UnfoldlM m b
mapFoldMInput newFoldM unfoldM = UnfoldlM $ \ step init -> foldM (newFoldM (FoldM step (return init) return)) unfoldM

{-| Construct from any foldable -}
{-# INLINE foldable #-}
foldable :: (Monad m, Foldable foldable) => foldable a -> UnfoldlM m a
foldable foldable = UnfoldlM (\ step init -> A.foldlM step init foldable)

{-| Construct from a specification of how to execute a left-fold -}
{-# INLINE foldlRunner #-}
foldlRunner :: Monad m => (forall x. (x -> a -> x) -> x -> x) -> UnfoldlM m a
foldlRunner run = UnfoldlM (\ stepM state -> run (\ stateM a -> stateM >>= \state -> stepM state a) (return state))

{-| Construct from a specification of how to execute a right-fold -}
{-# INLINE foldrRunner #-}
foldrRunner :: Monad m => (forall x. (a -> x -> x) -> x -> x) -> UnfoldlM m a
foldrRunner run = UnfoldlM (\ stepM -> run (\ x k z -> stepM z x >>= k) return)

unfoldr :: Monad m => Unfoldr a -> UnfoldlM m a
unfoldr (Unfoldr unfoldr) = foldrRunner unfoldr

{-| Filter the values given a predicate -}
{-# INLINE filter #-}
filter :: Monad m => (a -> m Bool) -> UnfoldlM m a -> UnfoldlM m a
filter test (UnfoldlM run) = UnfoldlM (\ step -> run (\ state element -> test element >>= bool (return state) (step state element)))

{-| Ints in the specified inclusive range -}
{-# INLINE intsInRange #-}
intsInRange :: Monad m => Int -> Int -> UnfoldlM m Int
intsInRange from to =
  UnfoldlM $ \ step init ->
  let
    loop !state int =
      if int <= to
        then do
          newState <- step state int
          loop newState (succ int)
        else return state
    in loop init from

{-| TVar contents -}
{-# INLINE tVarValue #-}
tVarValue :: TVar a -> UnfoldlM STM a
tVarValue var = UnfoldlM $ \ step state -> do
  a <- readTVar var
  step state a

{-| Change the base monad using invariant natural transformations -}
{-# INLINE hoist #-}
hoist :: (forall a. m a -> n a) -> (forall a. n a -> m a) -> UnfoldlM m a -> UnfoldlM n a
hoist trans1 trans2 (UnfoldlM unfold) = UnfoldlM $ \ step init ->
  trans1 (unfold (\ a b -> trans2 (step a b)) init)

{-| Bytes of a bytestring -}
{-# INLINABLE byteStringBytes #-}
byteStringBytes :: ByteString -> UnfoldlM IO Word8
byteStringBytes (ByteString.PS fp off len) =
  UnfoldlM $ \ step init ->
  withForeignPtr fp $ \ ptr ->
  let
    endPtr = plusPtr ptr (off + len)
    iterate !state !ptr = if ptr == endPtr
      then return state
      else do
        x <- peek ptr
        newState <- step state x
        iterate newState (plusPtr ptr 1)
    in iterate init (plusPtr ptr off)

{-| Bytes of a short bytestring -}
{-# INLINE shortByteStringBytes #-}
shortByteStringBytes :: Monad m => ShortByteString -> UnfoldlM m Word8
shortByteStringBytes (ShortByteString.SBS ba#) = primArray (PrimArray ba#)

{-| Elements of a prim array -}
{-# INLINE primArray #-}
primArray :: (Monad m, Prim prim) => PrimArray prim -> UnfoldlM m prim
primArray pa = UnfoldlM $ \ f z -> foldlPrimArrayM' f z pa

{-| Elements of a prim array coming paired with indices -}
{-# INLINE primArrayWithIndices #-}
primArrayWithIndices :: (Monad m, Prim prim) => PrimArray prim -> UnfoldlM m (Int, prim)
primArrayWithIndices pa = UnfoldlM $ \ step state -> let
  !size = sizeofPrimArray pa
  iterate index !state = if index < size
    then do
      newState <- step state (index, indexPrimArray pa index)
      iterate (succ index) newState
    else return state
  in iterate 0 state
-}

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

catch :: (MonadUnliftIO m, Exception e) => m a -> (e -> m a) -> m a
catch f g = withRunInIO $ \run -> run f `Ex.catch` \e ->
  if isSyncException e
    then run (g e)
    -- intentionally rethrowing an async exception synchronously,
    -- since we want to preserve async behavior
    else Ex.throwIO e

isSyncException :: Exception e => e -> Bool
isSyncException e =
    case fromException (toException e) of
        Just (SomeAsyncException _) -> False
        Nothing -> True

-- | Convert 'Maybe'' to 'Maybe'
toLazy :: M'.Maybe a -> Maybe a
toLazy  M'.Nothing = Nothing
toLazy (M'.Just a) = Just a
{-# INLINABLE toLazy #-}

toStrict :: Maybe a -> M'.Maybe a
toStrict  Nothing = M'.Nothing
toStrict (Just a) = M'.Just a
{-# INLINABLE toStrict #-}

---------------------------------------------------------------------
-- Foldl instances
---------------------------------------------------------------------

-- Comonad instances

extract :: Foldl a b -> b
extract (Foldl _ z k) = k z

duplicate :: Foldl a b -> Foldl a (Foldl a b)
duplicate (Foldl h z k) = Foldl h z (flip (Foldl h) k)

--extend :: (Foldl a b -> c) -> Foldl a b -> Foldl a c
--extend f (Foldl h z k) = Foldl h z (f . flip (Foldl h) k)

instance Functor (Foldl a) where
    fmap f (Foldl h z k) = Foldl h z (f . k)
    {-# INLINE fmap #-}

instance Profunctor Foldl where
  rmap = fmap
  lmap f (Foldl h z k) = Foldl h' z k
    where
      h' x a = h x (f a)

instance Choice Foldl where
  right' (Foldl h z k) = Foldl (liftA2 h) (Right z) (fmap k)
  {-# INLINE right' #-}

{-
instance Comonad (Foldl a) where
    extract (Foldl _ z k) = k z
    {-#  INLINE extract #-}

    duplicate (Foldl h z k) = Foldl h z (\x -> Foldl h x k)
    {-#  INLINE duplicate #-}
-}

instance Applicative (Foldl a) where
    pure b    = Foldl (\() _ -> ()) () (\() -> b)
    {-# INLINE pure #-}

    (Foldl hL zL kL) <*> (Foldl hR zR kR) =
        let h (xL :!: xR) a = (hL xL a) :!: (hR xR a)
            z = zL :!: zR
            k (xL :!: xR) = kL xL (kR xR)
        in  Foldl h z k
    {-# INLINE (<*>) #-}

instance Distributive (Foldl a) where

  distribute z = Foldl (\fm a -> fmap (prefix a) fm) z (fmap extract)

instance Functor.Representable (Foldl a) where

  type Rep (Foldl a) = [a]

  index = cosieve

  tabulate = cotabulate

instance Cosieve Foldl [] where

  cosieve (Foldl k0 h0 z0) as0 = go k0 h0 z0 as0
    where
      go _ z k [] = k z
      go h z k (a : as) = go h (h z a) k as

instance Closed Foldl where

  closed (Foldl h z k) = Foldl (liftA2 h) (pure z) (\f x -> k (f x))

instance Costrong Foldl where

  unfirst = unfirstCorep

  unsecond = unsecondCorep

instance Corepresentable Foldl where

  type Corep Foldl = []

  cotabulate f = Foldl (flip (:)) [] (f . reverse)

instance Monad (Foldl a) where

  m >>= f = Foldl (flip (:)) [] (\xs -> flip foldl xs . f) <*> m

instance MonadReader [a] (Foldl a) where

  ask = askRep

  local = localRep

instance MonadFix (Foldl a) where
  mfix = mfixRep






---------------------------------------------------------------------
-- FoldlM instances
---------------------------------------------------------------------


instance Functor m => Functor (FoldlM m a) where
    fmap f (FoldlM h start k) = FoldlM h start k'
      where
        k' x = fmap f $! k x
    {-# INLINE fmap #-}

instance Applicative m => Applicative (FoldlM m a) where
    pure b = FoldlM (\() _ -> pure ()) (pure ()) (\() -> pure b)
    {-# INLINE pure #-}

    (FoldlM hL zL kL) <*> (FoldlM hR zR kR) =
        let h (xL :!: xR) a = (:!:) <$> hL xL a <*> hR xR a
            z = (:!:) <$> zL <*> zR
            k (xL :!: xR) = kL xL <*> kR xR
        in  FoldlM h z k
    {-# INLINE (<*>) #-}

instance Functor m => Profunctor (FoldlM m) where
    rmap = fmap
    lmap f (FoldlM h z k) = FoldlM h' z k
      where
        h' x a = h x (f a)

instance Monad m => Choice (FoldlM m) where
  right' (FoldlM h z k) =
    FoldlM ((.)(.)(.) sequence . liftA2 $ h)
           (fmap Right z)
           (runKleisli (right' $ Kleisli k))
  {-# INLINE right' #-}



-- instance Monad m => Closed (FoldlM m) where


{-
foo :: Monad m => (r -> a -> m r) -> r -> ListT m a -> m r
foo s r = uncons >=> maybe (return r) (\(h, t) -> s r h >>= \r' -> foo s r' t)

instance Monad m => Cosieve (FoldlM m) (ListT m) where

  cosieve (FoldlM h z k) l = z >>= (\o -> foo h o l) >>= k 



  closed (FoldlM h z k) = FoldlM undefined undefined (\f x -> k (f x)) -- (liftA2 h) (pure z) 

 z >>= (\z -> go h z l) >>= k where
    go s r = uncons >=> maybe (return r) (\(h, t) -> s r h >>= \r' -> go s r' t)

instance Closed Foldl where

  closed (Foldl h z k) = Foldl (liftA2 h) (pure z) (\f x -> k (f x))

instance Costrong Foldl where

  unfirst = unfirstCorep

  unsecond = unsecondCorep

instance Corepresentable Foldl where

  type Corep Foldl = []

  cotabulate f = Foldl (flip (:)) [] (f . reverse)
-}



---------------------------------------------------------------------
-- Unfoldl instances
---------------------------------------------------------------------

deriving instance Functor Unfoldl

instance Applicative Unfoldl where
  pure x =
    Unfoldl (\ step init -> step init x)
  (<*>) = ap

instance Alternative Unfoldl where
  empty =
    Unfoldl (const id)
  {-# INLINE (<|>) #-}
  (<|>) (Unfoldl left) (Unfoldl right) =
    Unfoldl (\ step init -> right step (left step init))

instance Monad Unfoldl where
  return = pure
  (>>=) (Unfoldl left) rightK =
    Unfoldl $ \ step init ->
    let
      newStep output x =
        case rightK x of
          Unfoldl right ->
            right step output
      in left newStep init

instance MonadPlus Unfoldl where
  mzero = empty
  mplus = (<|>)

instance Semigroup (Unfoldl a) where
  (<>) = (<|>)

instance Monoid (Unfoldl a) where
  mempty = empty
  mappend = (<>)

instance Foldable Unfoldl where
  {-# INLINE foldMap #-}
  foldMap inputMonoid = F.foldl' step mempty where
    step monoid input = mappend monoid (inputMonoid input)
  foldl = F.foldl'
  {-# INLINE foldl' #-}
  foldl' step init (Unfoldl run) = run step init

instance Eq a => Eq (Unfoldl a) where
  (==) left right = F.toList left == F.toList right

instance Show a => Show (Unfoldl a) where
  show = show . F.toList


---------------------------------------------------------------------
-- UnfoldlM instances
---------------------------------------------------------------------


deriving instance Functor m => Functor (UnfoldlM m)

instance Monad m => Applicative (UnfoldlM m) where
  pure x =
    UnfoldlM (\ step init -> step init x)
  (<*>) = ap

instance Monad m => Alternative (UnfoldlM m) where
  empty =
    UnfoldlM (const return)
  {-# INLINE (<|>) #-}
  (<|>) (UnfoldlM left) (UnfoldlM right) =
    UnfoldlM (\ h init -> left h init >>= right h)

instance Monad m => Monad (UnfoldlM m) where
  return = pure
  {-# INLINE (>>=) #-}
  (>>=) (UnfoldlM left) ext =
    UnfoldlM $ \ h z ->
    let
      h' output x =
        case ext x of
          UnfoldlM right ->
            right h output
      in left h' z

instance Monad m => MonadPlus (UnfoldlM m) where
  mzero = empty
  mplus = (<|>)

instance MonadTrans UnfoldlM where
  lift m = UnfoldlM (\ h z -> m >>= h z)

instance Monad m => Semigroup (UnfoldlM m a) where
  (<>) = (<|>)

instance Monad m => Monoid (UnfoldlM m a) where
  mempty = empty
  mappend = (<>)

instance Foldable (UnfoldlM Identity) where
  {-# INLINE foldMap #-}
  foldMap inputMonoid = F.foldl' h mempty where
    h monoid input = mappend monoid (inputMonoid input)
  foldl = F.foldl'
  {-# INLINE foldl' #-}
  foldl' h z (UnfoldlM run) =
    runIdentity (run identityStep z)
    where
      identityStep state input = return (h state input)

instance Eq a => Eq (UnfoldlM Identity a) where
  (==) left right = F.toList left == F.toList right

instance Show a => Show (UnfoldlM Identity a) where
  show = show . F.toList
