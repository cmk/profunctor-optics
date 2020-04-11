
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE MagicHash         #-}
module Data.Profunctor.Rep.Foldl (
  -- * Unfoldl
    Unfoldl (..)
  , foldable
  , ofoldable
  , prefilter
  -- * Foldl
  , Foldl (..)
  , foldl
  , ofoldl
  , foldsl
  , withFoldl
  , cons
  , filter
  , postscan
  , generalize
  -- * UnfoldlM
  , UnfoldlM (..)
  , foldableM
  , forM_
  , mapM_
  , prehoist
  , prefilterM
  , prefoldlM
  , prefoldrM
  -- * FoldlM
  , FoldlM (..)
  , runFoldlM
  , ofoldlM
  , unFoldlM
  , withFoldlM
  , filterM
  , hoist
  , lmapM
  , sink
  , halt
  , halt_
  , skip
  , skip_
  -- * Unfolds
  -- * Folds
  , list
  , revList
  , mconcat
  , hMay
  , hDef
  , headDef
  , lastDef
  , maximumDef
  , maximumByDef
  , minimumDef
  , minimumByDef
  -- * Monomorphic folds
  , lazy
  , onull
  , ohead
  , olast
  , olength
  , ofind
  , oall
  , oany
  , oelem
  , onotElem
  ) where

import Control.Arrow (Kleisli(..),(***))
import Control.Applicative
import Control.Monad (MonadPlus(..), (>=>),ap, liftM)
import Control.Monad.Fix (MonadFix(..))
import Control.Monad.Zip (MonadZip(..))
import Control.Monad.Reader (MonadReader(..))
import Control.Monad.Trans (MonadTrans(..))
import Data.Distributive (Distributive (..))
--import Data.Functor.Rep as Functor (Representable (..), askRep, localRep, mfixRep)
import Data.Functor.Identity
import Data.Bool (bool)
import Data.List (mapAccumL)
import Data.Profunctor
import Data.Profunctor.Closed (Closed (..))
import Data.Profunctor.Rep as Profunctor (Corepresentable (..), unfirstCorep, unsecondCorep)
import Data.Profunctor.Sieve (Cosieve (..))
import Prelude as P hiding
  ( head, last, null, length, and, or, all, any, sum, product, maximum, 
    minimum, mconcat, elem, notElem, lookup, map, either, drop, 
    Fractional(..), foldl, filter, mapM_
  )
import qualified Data.Foldable as F

import Control.Exception (Exception (..), SomeException (..), IOException, SomeAsyncException (..))
import qualified Control.Exception as Ex

import Control.Monad.IO.Unlift
import Data.MonoTraversable (MonoFoldable, Element)
import Data.Sequences (SemiSequence, IsSequence, LazySequence, Index)
import qualified Data.Sequences as MS
import qualified Data.List.NonEmpty as NE
import qualified Data.MonoTraversable as MT
import System.IO -- (Handle, hIsEOF)

import Foreign
  ( ForeignPtr, Ptr, plusPtr, peek)

import qualified Data.ByteString as B
import qualified Data.ByteString.Builder as B
import qualified Data.ByteString.Internal as B
import qualified Foreign.ForeignPtr as F
import Data.Word 
import Data.ByteString (ByteString)
import Data.Primitive 
import qualified Data.ByteString.Short.Internal as SB

import qualified Data.ByteString      as BS
import qualified Data.ByteString.Lazy as BL

chunks b = Unfoldl (\ h z -> BL.foldlChunks h z b)
bytes b = Unfoldl (\ h z -> BL.foldl h z b)

---------------------------------------------------------------------
-- Unfoldl
---------------------------------------------------------------------

newtype Unfoldl a = Unfoldl (forall x. (x -> a -> x) -> x -> x)

-- | A version of the /build/ function from < http://hackage.haskell.org/package/base-4.12.0.0/docs/src/GHC.Base.html#build base >.
--
build :: Unfoldl a -> [a]
build (Unfoldl u) = u (flip (:)) []

-- | Construct an 'Unfoldl' from a 'Data.Foldable.Foldable'.
--
foldable :: Foldable f => f a -> Unfoldl a
foldable f = Unfoldl (\ h z -> F.foldl' h z f)
{-# INLINE foldable #-}

-- | Construct an 'Unfoldl' from a 'Data.MonoTraversable.MonoFoldable'.
--
ofoldable :: MonoFoldable a => a -> Unfoldl (Element a)
ofoldable f = Unfoldl (\ h z -> MT.ofoldl' h z f)
{-# INLINE ofoldable #-}

{-| Lift a fold input mapping function into a mapping of unfolds -}
{-# INLINE premap #-}
premap :: (forall x. Foldl b x -> Foldl a x) -> Unfoldl a -> Unfoldl b
premap f u = Unfoldl $ \ h z -> foldl (f (Foldl h z id)) u

{-| Filter the values given a predicate -}
prefilter :: (a -> Bool) -> Unfoldl a -> Unfoldl a
prefilter test (Unfoldl u) = Unfoldl (\ h -> u (\ s elt -> if test elt then h s elt else s))
{-# INLINE prefilter #-}

---------------------------------------------------------------------
-- Foldl
---------------------------------------------------------------------

data Foldl a b = forall x. Foldl (x -> a -> x) x (x -> b)

run :: Foldl a b -> a -> b
run (Foldl h z k) t = k (h z t)
{-# INLINABLE run #-}

cons :: a -> Foldl a b -> Foldl a b
cons a = flip run a . duplicate
{-# INLINABLE cons #-}

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

foldsl :: Foldl a b -> Unfoldl a -> b
foldsl (Foldl h z k) (Unfoldl run) = k (run h z)
{-# INLINE foldsl #-}

-- | TODO: Document
--
withFoldl :: Foldl a b -> (forall x. (x -> a -> x) -> x -> (x -> b) -> r) -> r
withFoldl (Foldl h z k) f = f h z k
{-# INLINABLE withFoldl #-}


{-| @(filter f folder)@ returns a new 'Fold' where the folder's input is used
  only when the input satisfies a predicate f

  This can also be k with 'handles' (@handles (filtered f)@) but @filter@
  does not need you to depend on a lens library.

> fold (filter p folder) list = fold folder (filter p list)

>>> fold (filter (>5) Control.Foldl.sum) [1..10]
40

>>> fold Control.Foldl.sum (filter (>5) [1..10])
40
-}
filter :: (a -> Bool) -> Foldl a r -> Foldl a r
filter f (Foldl h z k) = Foldl h' z k
  where
    h' x a = if f a then h x a else x
{-# INLINABLE filter #-}

{-| Transforms a 'Fold' into one which ignores elts
    until they stop satisfying a predicate

> fold (dropWhile p folder) list = fold folder (dropWhile p list)

>>> fold (dropWhile (>5) Control.Foldl.sum) [10,9,5,9]
14
-}
dropWhile :: (a -> Bool) -> Foldl a r -> Foldl a r
dropWhile f (Foldl h z k) = Foldl h' z' k'
  where
    h' (Pair dropping x) a = if dropping && f a
      then Pair True x
      else Pair False (h x a)
    z' = Pair True z
    k' (Pair _ s) = k s
{-# INLINABLE dropWhile #-}

{-| Nest a fold in an applicative.
-}
apply :: Applicative f => Foldl a b -> Foldl (f a) (f b)
apply (Foldl s i e) =
    Foldl (\xs as -> liftA2 s xs as)
         (pure i)
         (\xs -> fmap e xs)
{-# INLINABLE apply #-}

{-

--
scan :: Foldl a b -> [a] -> [b]
scan (Foldl h z k) as = foldr cons nil as z
  where
    nil      x = k x:[]
    cons a k x = k x:(k $! h x a)
{-# INLINE scan #-}

-- | Convert a `Foldl` into a prescan for any `Traversable` type
--
--  \"Prescan\" means that the last elt of the scan is not included
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

-}

-- | Convert a `Foldl` into a postscan for any `Traversable` type
--
--  \"Postscan\" means that the first elt of the scan is not included
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

---------------------------------------------------------------------
-- UnfoldlM
---------------------------------------------------------------------


-- | A monadic version of 'Unfoldl'.
newtype UnfoldlM m a = UnfoldlM (forall x. (x -> a -> m x) -> x -> m x)


{-| Construct from any foldable -}
foldableM :: Foldable f => Monad m => f a -> UnfoldlM m a
foldableM f = UnfoldlM (\ h z -> F.foldlM h z f)
{-# INLINE foldableM #-}

{-| Lift a fold input mapping function into a mapping of unfolds -}
--{-# INLINE premapM #-}
premapM :: Monad m => (forall x. FoldlM m b x -> FoldlM m a x) -> UnfoldlM m a -> UnfoldlM m b
premapM f u = UnfoldlM $ \ h z -> unFoldlM (f (FoldlM h (return z) return)) u

{-| Filter the values given a predicate -}
prefilterM :: Monad m => (a -> m Bool) -> UnfoldlM m a -> UnfoldlM m a
prefilterM test (UnfoldlM run) = UnfoldlM (\ h -> run (\ s elt -> test elt >>= bool (return s) (h s elt)))
{-# INLINE prefilterM #-}

{-| Change the base monad using invariant natural transformations -}
prehoist :: (forall a. m a -> n a) -> (forall a. n a -> m a) -> UnfoldlM m a -> UnfoldlM n a
prehoist trans1 trans2 (UnfoldlM unfold) = UnfoldlM $ \ h z ->
  trans1 (unfold (\ a b -> trans2 (h a b)) z)
{-# INLINE prehoist #-}

{-| Construct from a specification of how to execute a left-fold -}
prefoldlM :: Monad m => (forall x. (x -> a -> x) -> x -> x) -> UnfoldlM m a
prefoldlM run = UnfoldlM (\ hM s -> run (\ sM a -> sM >>= \s -> hM s a) (return s))
{-# INLINE prefoldlM #-}

{-| Construct from a specification of how to execute a right-fold -}
prefoldrM :: Monad m => (forall x. (a -> x -> x) -> x -> x) -> UnfoldlM m a
prefoldrM run = UnfoldlM (\ hM -> run (\ x k z -> hM z x >>= k) return)
{-# INLINE prefoldrM #-}

{-| Check whether it's empty -}
isNullM :: Monad m => UnfoldlM m input -> m Bool
isNullM (UnfoldlM run) = run (\ _ _ -> return False) True
{-# INLINE isNullM #-}

{-| A more efficient implementation of mapM_ -}
mapM_ :: Monad m => (input -> m ()) -> UnfoldlM m input -> m ()
mapM_ h (UnfoldlM u) = u (const h) ()
{-# INLINE mapM_ #-}

{-| Same as 'mapM_' with arguments flipped -}
forM_ :: Monad m => UnfoldlM m input -> (input -> m ()) -> m ()
forM_ = flip Data.Profunctor.Rep.Foldl.mapM_
{-# INLINE forM_ #-}

---------------------------------------------------------------------
-- FoldlM
---------------------------------------------------------------------

data FoldlM m a b = forall x . FoldlM (x -> a -> m x) (m x) (x -> m b)

-- | Variant of 'foldlM' without the 'Data.Foldable.Foldable' constraint.
--
unFoldlM :: Monad m => FoldlM m a b -> UnfoldlM m a -> m b
unFoldlM (FoldlM h z k) (UnfoldlM u) = z >>= u h >>= k

-- | Monadic variant of 'foldl'.
--
-- @ 'runFoldlM' f = 'unFoldlM' f . 'foldableM' @
--
runFoldlM :: Foldable f => Monad m => FoldlM m a b -> f a -> m b
runFoldlM (FoldlM h z k) as0 = do
    x0 <- z
    F.foldr h' k as0 $! x0
  where
    h' a k x = do
        x' <- h x a
        k $! x'
{-# INLINE runFoldlM #-}

withFoldlM :: FoldlM m a b -> (forall x. (x -> a -> m x) -> m x -> (x -> m b) -> r) -> r
withFoldlM (FoldlM h z k) f = f h z k

-- | Apply a strict monadic left 'FoldlM' to a lazy bytestring
--foldM :: Monad m => FoldlM m ByteString a -> Data.ByteString.Lazy.ByteString -> m a
ofoldlM (FoldlM h z k) as = do
    x <- MT.ofoldl' h' z as
    k x
  where
    h' mx bs = do
      x <- mx
      x `seq` h x bs
{-# INLINABLE ofoldlM #-}

{- | Shift a 'FoldlM' from one monad to another with a morphism such as 'lift' or 'liftIO';
     the effect is the same as 'Control.Monad.Morph.hoist'.
-}
hoist :: (forall x . m x -> n x) -> FoldlM m a b -> FoldlM n a b
hoist phi (FoldlM h z k) = FoldlM (\a b -> phi (h a b)) (phi z) (phi . k)
{-# INLINABLE hoist #-}




lmapM :: Monad m => (a -> m b) -> FoldlM m b r -> FoldlM m a r
lmapM f (FoldlM h z k) = FoldlM h' z k
  where
    h' x a = f a >>= h x
{-# INLINABLE lmapM #-}




{-| @(filterM f folder)@ returns a new 'FoldM' where the folder's input is used
  only when the input satisfies a monadic predicate f.

> foldM (filterM p folder) list = foldM folder (filter p list)
-}
filterM :: (Monad m) => (a -> m Bool) -> FoldlM m a r -> FoldlM m a r
filterM f (FoldlM h z k) = FoldlM h' z k
  where
    h' x a = do
      use <- f a
      if use then h x a else return x
{-# INLINABLE filterM #-}



{-
{-| Combine two folds into a fold over inputs for either of them.
-}
either :: Foldl a1 b1 -> Foldl a2 b2 -> Foldl (Either a1 a2) (b1, b2)
either l r = (,) <$> left' `id` l <*> right' `id` r
{-# INLINABLE either #-}

{-| Combine two monadic folds into a fold over inputs for either of them.
-}
eitherM :: Monad m => FoldlM m a1 b1 -> FoldlM m a2 b2 -> FoldlM m (Either a1 a2) (b1, b2)
eitherM l r = (,) <$> left' `id` l <*> right' `id` r
{-# INLINABLE eitherM #-}
-}




halt_ :: MonadUnliftIO m => FoldlM m a b -> FoldlM m a b
halt_ f = fmap snd (halt @SomeException f)

{-
-- >>> import qualified Control.Exception as Ex
-- >>> f x = if x < 10 then return x else Ex.throw Ex.Overflow
-- >>> exfold = lmapM f (generalize list)
-- >>> xs = [1, 2, 500, 4] :: [Integer]
-- >>> runFoldlM (halt @Ex.ArithException exfold) xs
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


{-
import Data.IOData (IOData, hGetChunk, hGetLine, hPut, hPutStrLn)
import Data.List
import Data.Word (Word8)


import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC8

type DataMode m a = MonadIO m => ((Handle -> m a), (Handle -> a -> m ()))
type Sink m k = MonadIO m => forall a. ProcessT m k a
type Source m a = MonadIO m => forall k. ListT m k a


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


 
{-
import qualified Data.ByteString as B
import qualified Data.ByteString.Builder as B
import Control.Monad.IO.Class
import System.IO
import Data.ByteString.Lazy.Internal (defaultChunkSize)
type AFoldlM m s t a b = Optic (L.FoldlM m) s t a b


driveHandle :: MonadIO m => AFoldlM m B.ByteString t a b -> Int -> Handle -> L.FoldlM m a b -> m t
driveHandle o chunkSize handle = consume chunkSize handle . o

-}


{-
-- adapted from foldM in Pipes.Prelude
consume :: MonadIO m => Int -> Handle -> FoldlM m B.ByteString b -> m b
consume chunkSize handle (FoldlM h z k) = do
    x0 <- z
    loop x0
      where
	loop x = do
	    atEOF <- liftIO $ hIsEOF handle
	    if atEOF 
	       then k x 
	       else do
		   chunk <- liftIO $ B.hGetSome handle chunkSize
		   x' <- h x chunk
		   loop $! x'

-}
-- adapted from foldM in Pipes.Prelude
consume :: MonadIO m => Int -> Handle -> FoldlM m B.ByteString b -> m b
consume chunkSize handle (FoldlM h z k) = do
    x0 <- z
    loop x0
      where
	loop x = do
	    atEOF <- liftIO $ hIsEOF handle
	    if atEOF 
	       then k x 
	       else do
		   chunk <- liftIO $ B.hGetSome handle chunkSize
		   x' <- h x chunk
		   loop $! x'

toHandle :: (MonadIO m) => Handle -> FoldlM m B.ByteString ()
toHandle handle = 
    FoldlM 
    (\_ b -> liftIO (B.hPut handle b))  
    (return ()) 
    (\_ -> return ())

toHandleBuilder :: (MonadIO m) => Handle -> FoldlM m B.Builder ()
toHandleBuilder handle = 
    FoldlM
    (\_ b -> liftIO (B.hPutBuilder handle b)) 
    (return ()) 
    (\_ -> return ())

---------------------------------------------------------------------
-- Unfolds
---------------------------------------------------------------------



{-| Ints in the specified inclusive range -}
{-# INLINE intsInRange #-}
intsInRange :: Int -> Int -> Unfoldl Int
intsInRange from to =
  Unfoldl $ \ h z ->
  let
    loop !s int =
      if int <= to
        then loop (h s int) (succ int)
        else s
    in loop z from



{-| Bytes of a bytestring -}
{-# INLINABLE byteStringBytes #-}
byteStringBytes :: MonadUnliftIO m => ByteString -> UnfoldlM m Word8
byteStringBytes (B.PS fp off len) =
  UnfoldlM $ \ h z ->
  withForeignPtr fp $ \ ptr ->
  let
    endPtr = plusPtr ptr (off + len)
    --x -> Ptr b -> m x
    iterate !s !ptr = if ptr == endPtr
      then return s
      else do
        x <- liftIO $ peek ptr
        newState <- h s x
        iterate newState (plusPtr ptr 1)
    in iterate z (plusPtr ptr off)

{-
{-| Elements of a prim array -}
{-# INLINE primArray #-}
primArray :: (Prim prim) => PrimArray prim -> Unfoldl prim
primArray ba = Unfoldl $ \ f z -> foldlPrimArray f z ba

{-| Bytes of a short bytestring -}
{-# INLINE shortByteStringBytes #-}
shortByteStringBytes :: (Prim prim) => SB.ShortByteString -> Unfoldl prim
shortByteStringBytes (SB.SBS ba#) = primArray (PrimArray ba#)
-}

{-| Bytes of a short bytestring -}
{-# INLINE shortByteStringBytes #-}
shortByteStringBytes :: Monad m => SB.ShortByteString -> UnfoldlM m Word8
shortByteStringBytes (SB.SBS ba#) = primArray (PrimArray ba#)

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

-- | Return the result of a h function.
--
-- Results in a 'Nothing' value for empty containers.
--
hMay :: (a -> a -> a) -> Foldl a (Maybe a)
hMay h = Foldl h_ Nothing' toLazy
  where
    h_ mx a = Just' (case mx of
        Nothing' -> a
        Just' x -> h x a)
{-# INLINABLE hMay #-}

hDef :: a -> (a -> a -> a) -> Foldl a a
hDef a h = maybe a id <$> hMay h
{-# INLINABLE hDef #-}

-- | Return the first elt of a collection.
--
-- Returns a default if the container is empty.
--
headDef :: a -> Foldl a a
headDef a = hDef a const
{-# INLINABLE headDef #-}

-- | Return the last elt of a collection.
--
-- Returns a default if the container is empty.
--
lastDef :: a -> Foldl a a
lastDef a = hDef a (flip const)
{-# INLINABLE lastDef #-}

-- | Return the maximumDef elt of a collection.
--
-- Returns a default if the container is empty.
--
maximumDef :: Ord a => a ->Foldl a a
maximumDef a = hDef a max
{-# INLINABLE maximumDef #-}

-- | Return the maximumDef elt of a collection wrt a comparator.
--
-- Returns a default if the container is empty.
--
maximumByDef :: (a -> a -> Ordering) -> a -> Foldl a a
maximumByDef cmp a = hDef a max'
  where
    max' x y = case cmp x y of
        GT -> x
        _  -> y
{-# INLINABLE maximumByDef #-}

-- | Return the minimumDef elt of a collection.
--
-- Returns a default if the container is empty.
--
minimumDef :: Ord a => a -> Foldl a a
minimumDef a = hDef a min
{-# INLINABLE minimumDef #-}

-- | Return the minimumDef elt of a collection wrt a comparator.
--
-- Returns a default if the container is empty.
--
minimumByDef :: (a -> a -> Ordering) -> a -> Foldl a a
minimumByDef cmp a = hDef a min'
  where
    min' x y = case cmp x y of
        GT -> y
        _  -> x
{-# INLINABLE minimumByDef #-}


{-| Convert an effectful function to a fold

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
ohead = Foldl h Nothing' toLazy
  where
    h me bs =
        if MT.onull bs
        then me
        else case me of
            Just' _  -> me
            Nothing' -> toStrict $ MT.headMay bs
{-# INLINABLE ohead #-}

-- | Get the last byte of a byte stream or return 'Nothing' if the byte stream is empty
--
olast :: MonoFoldable a => Foldl a (Maybe (Element a))
olast = Foldl h Nothing' toLazy
  where
    h me bs =
        if MT.onull bs
        then me
        else case me of
            Just' _  -> me
            Nothing' -> toStrict $ MT.lastMay bs
{-# INLINABLE olast #-}

-- | Return the length of /a/ in bytes.
--
olength :: MonoFoldable a => Num n => Foldl a n
olength = Foldl h 0 id
  where
    h n bs = n + fromIntegral (MT.olength bs)
{-# INLINABLE olength #-}

-- | Return the first element that satisfies the predicate or 'Nothing' otherwise.
--
ofind :: SemiSequence a => (Element a -> Bool) -> Foldl a (Maybe (Element a))
ofind predicate = Foldl h Nothing' toLazy 
  where
    h e bs = case e of
        Nothing' -> toStrict (MS.find predicate bs)
        Just' _  -> e
{-# INLINABLE ofind #-}

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

{-# INLINE withForeignPtr #-}
withForeignPtr :: MonadUnliftIO m => ForeignPtr a -> (Ptr a -> m b) -> m b
withForeignPtr fo io = withRunInIO (\u -> F.withForeignPtr fo (u . io))

-- | A strict 'Maybe'
data Maybe' a = Just' !a | Nothing'

-- | Convert 'Maybe'' to 'Maybe'
toLazy :: Maybe' a -> Maybe a
toLazy  Nothing' = Nothing
toLazy (Just' a) = Just a
{-# INLINABLE toLazy #-}

-- | Convert 'Maybe' to 'Maybe''
toStrict :: Maybe a -> Maybe' a
toStrict  Nothing  = Nothing'
toStrict (Just a ) = Just' a
{-# INLINABLE toStrict #-}

-- | A strict 'Either'
data Either' a b = Left' !a | Right' !b

-- | Convert 'Either'' to 'Maybe'
hush :: Either' a b -> Maybe b
hush (Left'  _) = Nothing
hush (Right' b) = Just b
{-# INLINABLE hush #-}

data Pair a b = Pair !a !b

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
        let h (xL `Pair` xR) a = (hL xL a) `Pair` (hR xR a)
            z = zL `Pair` zR
            k (xL `Pair` xR) = kL xL (kR xR)
        in  Foldl h z k
    {-# INLINE (<*>) #-}

instance Distributive (Foldl a) where

  distribute z = Foldl (\fm a -> fmap (cons a) fm) z (fmap extract)



{-
instance Functor.Representable (Foldl a) where

  type Rep (Foldl a) = [a]

  index = cosieve

  tabulate = cotabulate
-}

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

  ask = cotabulate id

  local f m = cotabulate (cosieve m . f)

instance MonadFix (Foldl a) where

  mfix = cotabulate . mfix . fmap cosieve

instance MonadZip (Foldl a) where

  --mzipWith f as bs = cotabulate $ \k -> f (cosieve as k) (cosieve bs k)
  mzipWith = liftA2


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
        let h (xL `Pair` xR) a = Pair <$> hL xL a <*> hR xR a
            z = Pair <$> zL <*> zR
            k (xL `Pair` xR) = kL xL <*> kR xR
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
    Unfoldl (\ h z -> h z x)
  (<*>) = ap

instance Alternative Unfoldl where
  empty =
    Unfoldl (const id)
  {-# INLINE (<|>) #-}
  (<|>) (Unfoldl left) (Unfoldl right) =
    Unfoldl (\ h z -> right h (left h z))

instance Monad Unfoldl where
  return = pure
  (>>=) (Unfoldl left) rightK =
    Unfoldl $ \ h z ->
    let
      newStep output x =
        case rightK x of
          Unfoldl right ->
            right h output
      in left newStep z

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
  foldMap inputMonoid = F.foldl' h mempty where
    h monoid input = mappend monoid (inputMonoid input)
  foldl = F.foldl'
  {-# INLINE foldl' #-}
  foldl' h z (Unfoldl run) = run h z

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
    UnfoldlM (\ h z -> h z x)
  (<*>) = ap

instance Monad m => Alternative (UnfoldlM m) where
  empty =
    UnfoldlM (const return)
  {-# INLINE (<|>) #-}
  (<|>) (UnfoldlM left) (UnfoldlM right) =
    UnfoldlM (\ h z -> left h z >>= right h)

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
      identityStep s input = return (h s input)

instance Eq a => Eq (UnfoldlM Identity a) where
  (==) left right = F.toList left == F.toList right

instance Show a => Show (UnfoldlM Identity a) where
  show = show . F.toList
