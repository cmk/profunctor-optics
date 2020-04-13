
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE MagicHash         #-}
module Data.Profunctor.Rep.Fold where
{-(
  -- * Unfold
    Unfold (..)
  , backwards
  , forwards
  , cons
  , snoc
  , over
  , filter
  -- * UnfoldM
  , UnfoldM (..)
  , backwardsM
  , forwardsM
  , uforM_
  , umapM_
  , invhoist
  , overM
  , filterM
  , forwardsM
  , backwardsM
  -- * Fold
  , L
  , Fold (..)
  , foldl
  , foldsl
  , withFold
  , prefilter
  , prepend
  , postscan
  , generalize
  -- * FoldM
  , LM
  , FoldM (..)
  , foldlM
  , foldslM
  , withFoldM
  , premapM
  , prefilterM
  , duplicateM
  , hoist
  , sink
  , halt
  , halt_
  , skip
  , skip_
  -- * Unfolds
  , enumsFrom
  , enumsRange
  , unsetBitIndices
  -- * Folds
  , mconcats
  , stepMay
  , stepDef
{-
  , list
  , revList
  , headDef
  , lastDef
  , maximumDef
  , maximumByDef
  , minimumDef
  , minimumByDef
-}
  , enumsRange'
  ) where
-}

import Control.Foldl (Fold(..), FoldM(..))
import qualified Control.Foldl as L

import Control.Arrow (Kleisli(..),(***))
import Control.Applicative
import Data.Functor.Coapply
import Control.Monad (MonadPlus(..), (>=>),ap, liftM)
import Control.Monad.Fix (MonadFix(..))
import Control.Monad.Zip (MonadZip(..))
import Control.Monad.Reader (MonadReader(..))
import Control.Monad.Trans (MonadTrans(..))
import Data.Distributive (Distributive (..))
import Data.Functor.Apply
--import Data.Functor.Rep as Functor (Representable (..), askRep, localRep, mfixRep)
import Data.Functor.Identity
import Data.Bool (bool)
import Data.List (mapAccumL)
import Data.Profunctor
import qualified Data.Bifunctor as B
import Data.Profunctor.Closed (Closed (..))
import Data.Profunctor.Rep as Profunctor (Corepresentable (..), unfirstCorep, unsecondCorep)
import Data.Profunctor.Sieve (Cosieve (..))
import Prelude as P hiding
  ( head, last, null, length, and, or, all, any, sum, product, maximum, 
    minimum, mconcat, elem, notElem, lookup, map, either, drop, 
    Fractional(..), foldl, filter, mapM_
  )
import qualified Data.Foldable as F

import Control.Exception (Exception (..), SomeException (..), SomeAsyncException (..))
import qualified Control.Exception as Ex

import Control.Monad.IO.Unlift
import Data.MonoTraversable (MonoFoldable, Element)
import Data.Sequences (SemiSequence, IsSequence, LazySequence, Index)
import qualified Data.Sequences as MS
import qualified Data.List.NonEmpty as NE
import qualified Data.MonoTraversable as MT
import System.IO -- (Handle, hIsEOF)

import Foreign
  ( ForeignPtr, Ptr, plusPtr, peek, testBit, FiniteBits(..))

import qualified Data.ByteString as B
import qualified Data.ByteString.Builder as B
import qualified Data.ByteString.Internal as B
import qualified Foreign.ForeignPtr as F
import Data.Word 
import Data.ByteString (ByteString)
import Data.Primitive 

import qualified GHC.Exts as Exts

import qualified Data.ByteString as ByteString
import qualified Data.ByteString.Short.Internal as ShortByteString




-- unfolds package
-- transformers, monad-loops, bytestring, text, unlift-io-core, io-streams?
-- transformers
-------------------------
import Control.Monad.Trans.Class as Exports

-- bytestring
-------------------------
import qualified Data.ByteString      as BS
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Char8      as CS
import qualified Data.ByteString.Lazy.Char8 as CL

import qualified Data.ByteString.Short.Internal as SB

-- primitive
-------------------------
import Data.Primitive as Exports --TODO remove?


import qualified Control.Monad.Loops as ML

---------------------------------------------------------------------
-- Unfold
---------------------------------------------------------------------

{-

>list :: [a] -> Unfoldl a
>list list = Unfoldl (\ step init -> foldl' step init list)

We can do the same with say "Data.Text.Text":

>text :: Text -> Unfoldl Char
>text text = Unfoldl (\ step init -> Data.Text.foldl' step init text)

And then we can use those both to concatenate with just an @O(1)@ cost:

>abcdef :: Unfoldl Char
>abcdef = list ['a', 'b', 'c'] <> text "def"
-}

-- | A continuation of a left fold.
--
-- Useful for unifying both 'Data.Foldable.Foldable' and non-foldable
-- types (e.g. /ByteString/s) in one interface.
--
-- Concatentaion (`<>`) has complexity of @O(1)@.
--
-- >>> :set -XOverloadedLists 
-- >>> [1..3] <> [4..6] :: Unfold Int
-- [1,2,3,4,5,6]
--
newtype Unfold a = Unfold ( forall x. (x -> a -> x) -> x -> x )

withUnfold :: Unfold a -> (x -> a -> x) -> x -> x
withUnfold (Unfold u) h z = u h z

-- | Construct a strict 'Unfold' from a 'Data.Foldable.Foldable'.
--
-- >>> F.foldr (:) [] $ forwards [0..4]
-- [0,1,2,3,4]
-- >>> F.foldl (flip (:)) [] $ forwards [0..4]
-- [4,3,2,1,0]
--
forwards :: Foldable f => f a -> Unfold a
forwards f = Unfold (\ h z -> F.foldl' h z f)
{-# INLINE forwards #-}

-- | Construct a strict 'Unfold' from a 'Data.Foldable.Foldable'.
--
-- >>> F.foldr (:) [] $ backwards [0..4]
-- [4,3,2,1,0]
-- >>> F.foldl (flip (:)) [] $ backwards [0..4]
-- [0,1,2,3,4]
--
backwards :: Foldable f => f a -> Unfold a
backwards f = Unfold (\ h z -> F.foldr' (flip h) z f)
{-# INLINE backwards #-}

snoc :: a -> Unfold a -> Unfold a
snoc a (Unfold u) = Unfold $ \ h z -> h (u h z) a

cons :: Unfold a -> a -> Unfold a
cons (Unfold u) a = Unfold $ \ h z -> u h (h z a)

{-| Lift a foldl input mapping function into a mapping of withUnfolds -}
{-# INLINE over #-}
over :: (forall x. Fold b x -> Fold a x) -> Unfold a -> Unfold b
over f u = Unfold $ \ h z -> L.fold (f (Fold h z id)) u

{-| Filter the values given a pred -}
filter :: (a -> Bool) -> Unfold a -> Unfold a
filter test (Unfold u) = Unfold (\ h -> u (\ s elt -> if test elt then h s elt else s))
{-# INLINE filter #-}

take :: Int -> Unfold a -> Unfold a
take i (Unfold u) = Unfold $ \ h z -> u
  (\ nxt a idx -> if idx < i
    then h (nxt (succ idx)) a
    else z)
  (const z)
  0

takeWhile :: (a -> Bool) -> Unfold a -> Unfold a
takeWhile pred (Unfold u) = Unfold $ \ h z -> u
  (\ nxt a -> if pred a
    then h nxt a
    else z)
  z


{-|
Reverse the order.

Use with care, because it requires to allocate all elements.
-}
reverse :: Unfold a -> Unfold a
reverse (Unfold u) = Unfold $ \ h -> u (\ f a -> f . flip h a) id

{-|
Lift into an withUnfold, which produces pairs with index.
-}
zipWithIndex :: Unfold a -> Unfold (Int, a)
zipWithIndex (Unfold u) = Unfold $ \ indexedStep indexedState -> u
  (\ nxtByIndex a index -> indexedStep (nxtByIndex (succ index)) (index, a))
  (const indexedState)
  0

headMay :: Unfold a -> Maybe a
headMay (Unfold u) = u (\x a -> x <|> Just a) Nothing

lastMay :: Unfold a -> Maybe a
lastMay (Unfold u) = u (\x a -> Just a <|> x) Nothing

headDef :: a -> Unfold a -> a
headDef a (Unfold u) = u const a

lastDef :: a -> Unfold a -> a
lastDef a (Unfold u) = u (flip const) a

---------------------------------------------------------------------
-- UnfoldM
---------------------------------------------------------------------

type UnfoldIO = UnfoldM IO

-- | A continuation of a left effectful fold.
--
-- >>> :set -XOverloadedLists 
-- >>> [1..3] <> [4..6] :: UnfoldM Identity Int
-- [1,2,3,4,5,6]
--
newtype UnfoldM m a = UnfoldM ( forall x. (x -> a -> m x) -> m x -> m x )

-- F.foldlM h z u = withUnfoldM u h z
withUnfoldM :: UnfoldM m a -> (x -> a -> m x) -> m x -> m x
withUnfoldM (UnfoldM u) h z = u h z

withUnfoldIO :: MonadUnliftIO m => UnfoldIO a -> (x -> a -> m x) -> m x -> m x
withUnfoldIO (UnfoldM u) h z = withRunInIO $ \io -> u (\x a -> io $ h x a) (io z)

{-# INLINE unfoldlM #-}
{-| Construct from a specification of how to execute a left-fold -}
unfoldlM :: Monad m => (forall x. (x -> a -> x) -> x -> x) -> UnfoldM m a
unfoldlM u = UnfoldM (\ hM s -> u (\ sM a -> sM >>= \s -> hM s a) s)

{-# INLINE unfoldrM #-}
{-| Construct from a specification of how to execute a right-fold -}
unfoldrM :: Monad m => (forall x. (a -> x -> x) -> x -> x) -> UnfoldM m a
unfoldrM u = UnfoldM (\ hM z -> z >>= u (\ a xmx x -> hM x a >>= xmx) return)

-- | Construct an 'UnfoldM' from a 'Data.Foldable.Foldable'.
--
-- >>> F.foldr (:) [] $ forwardsM @Identity [0..4]
-- [0,1,2,3,4]
-- >>> F.foldl (flip (:)) [] $ forwardsM @Identity [0..4]
-- [4,3,2,1,0]
--
forwardsM :: Monad m => Foldable f => f a -> UnfoldM m a
forwardsM f = UnfoldM (\ h z -> z >>= flip (F.foldlM h) f)
{-# INLINE forwardsM #-}

-- | Construct an 'UnfoldM' from a 'Data.Foldable.Foldable'.
--
-- >>> F.foldr (:) [] $ backwardsM @Identity [0..4]
-- [4,3,2,1,0]
-- >>> F.foldl (flip (:)) [] $ backwardsM @Identity [0..4]
-- [0,1,2,3,4]
--
backwardsM :: Monad m => Foldable f => f a -> UnfoldM m a
backwardsM f = UnfoldM (\ h z -> z >>= flip (F.foldlM h) f)
{-# INLINE backwardsM #-}

{-| Lift a foldl input mapping function into a mapping of withUnfolds -}
{-# INLINE overM #-}
overM :: Monad m => (forall x. FoldM m b x -> FoldM m a x) -> UnfoldM m a -> UnfoldM m b
overM f u = UnfoldM $ \ h z -> foldsM (f (FoldM h z return)) u

{-| Filter the values given a pred -}
filterM :: Monad m => (a -> m Bool) -> UnfoldM m a -> UnfoldM m a
filterM test (UnfoldM u) = UnfoldM (\ h -> u (\ s elt -> test elt >>= bool (return s) (h s elt)))
{-# INLINE filterM #-}

{-| Change the base monad using an invariant natural transformation -}
invhoist :: (forall a. m a -> n a) -> (forall a. n a -> m a) -> UnfoldM m a -> UnfoldM n a
invhoist t1 t2 (UnfoldM u) = UnfoldM $ \ h z -> t1 $ u (\ a b -> t2 $ h a b) (t2 z)
{-# INLINE invhoist #-}


{-

{-| Check whether it's empty -}
isNullM :: Monad m => UnfoldM m input -> m Bool
isNullM (UnfoldM u) = u (\ _ _ -> return False) $ pure True
{-# INLINE isNullM #-}

{-| A more efficient implementation of mapM_ -}
umapM_ :: Monad m => (input -> m ()) -> UnfoldM m input -> m ()
umapM_ h (UnfoldM u) = u (const h) ()
{-# INLINE umapM_ #-}

{-| Same as 'mapM_' with arguments flipped -}
uforM_ :: Monad m => UnfoldM m input -> (input -> m ()) -> m ()
uforM_ = flip umapM_
{-# INLINE uforM_ #-}
-}
---------------------------------------------------------------------
-- Fold
---------------------------------------------------------------------


--moore :: (s -> (b, a -> s)) -> s -> Fold a b

-- | Provided for symmetry w/ 'foldsM'.
--
-- @ 'folds' f u = 'Control.Foldl.fold' f u @
--
folds :: Fold a b -> Unfold a -> b
folds (Fold h z k) (Unfold u) = k (u h z)

prepend :: a -> Fold a b -> Fold a b
prepend a = run a . duplicate where
  run a (Fold h z k) = k (h z a)
{-# INLINABLE prepend #-}

---------------------------------------------------------------------
-- FoldM
---------------------------------------------------------------------

--data FoldM m a b = forall x . FoldM (x -> a -> m x) (m x) (x -> m b)

-- | Variant of 'foldlM' without the 'Data.Foldable.Foldable' constraint.
--
foldsM :: Monad m => FoldM m a b -> UnfoldM m a -> m b
foldsM (FoldM h z k) (UnfoldM u) = u h z >>= k -- z >>= u h >>= k

---------------------------------------------------------------------
-- Unfolds
---------------------------------------------------------------------

-- | Elements of a prim array.
--
prim :: (Prim prim) => PrimArray prim -> Unfold prim
prim ba = Unfold $ \ f z -> foldlPrimArray f z ba
{-# INLINE prim #-}

-- | Bytes of a short bytestring.
--
short :: (Prim prim) => SB.ShortByteString -> Unfold prim
short (SB.SBS ba#) = prim (PrimArray ba#)
{-# INLINE short #-}

-- | Bytes of a lazy bytestring
--
-- >>> toList $ bytes "foo"
-- [102,111,111]
--
bytes :: BL.ByteString -> Unfold Word8
bytes b = Unfold (\ h z -> BL.foldl h z b)

-- | Chars of a lazy bytestring
--
-- >>> toList $ chars "foo"
-- "foo"
--
chars :: BL.ByteString -> Unfold Char
chars b = Unfold (\ h z -> CL.foldl h z b)

-- | Bytes of a strict bytestring
--
bytes' :: BS.ByteString -> Unfold Word8
bytes' bs = Unfold (\ h z -> BS.foldl h z bs)
{-# INLINE bytes' #-}

-- | Chars of a strict bytestring
--
chars' :: BS.ByteString -> Unfold Char
chars' bs = Unfold (\ h z -> CS.foldl h z bs)
{-# INLINE chars' #-}

-- | Chunks of a lazy bytestring
--
chunks :: BL.ByteString -> Unfold BS.ByteString
chunks b = Unfold (\ h z -> BL.foldlChunks h z b)

-- | Digits of a non-negative number in numeral system based on the specified radix.
--
-- >>> digits 2 7 :: Unfold Int
-- [1,1,1]
-- >>> digits 2 8 :: Unfold Int
-- [1,0,0,0]
-- >>> digits 2 16 :: Unfold Int
-- [1,0,0,0,0]
--
digits :: Integral a => a -> a -> Unfold a
digits rad a = Unfold $ \ h z -> let
  loop a = case divMod a rad of
    (d, m) -> h (if d <= 0 then z else loop d) m
  in loop a

{-| Ascending stream of enumss starting from the one specified -}
{-# INLINE enumsFrom #-}
enumsFrom :: (Enum a) => a -> Unfold a
enumsFrom from = Unfold $ \ h z -> let
  loop i = h (loop $ succ i) i
  in loop from

{-| Enums in the specified inclusive range -}
{-# INLINE enumsRange #-}
enumsRange :: (Enum a, Ord a) => a -> a -> Unfold a
enumsRange from to =
  Unfold $ \ h z ->
  let
    loop i =
      if i <= to
        then h (loop $ succ i) i
        else z
    in loop from


{-

{-| Elements of a vector -}
{-# INLINE vector #-}
--
--
vector :: GenericVector.Vector vector a => vector a -> Unfold a
vector vector = Unfold $ \ h s -> GenericVector.withUnfoldr h s vector

{-| Elements of a vector coming paired with indices -}
{-# INLINE vectorWithIndex #-}
--
vectorWithIndex :: GenericVector.Vector vector a => vector a -> Unfold (Int, a)
vectorWithIndex vector = Unfold $ \ h s -> GenericVector.iunfoldr (\ index a -> h (index, a)) s vector

takeBytes :: Int64                        -- ^ maximum number of bytes to read
          -> InputStream ByteString       -- ^ input stream to wrap
          -> IO (InputStream ByteString)
takeBytes k0 = takeBytes' k0 (return Nothing)
{-# INLINE takeBytes #-}


------------------------------------------------------------------------------
-- | Like @Streams.'takeBytes'@, but throws 'ReadTooShortException' when
-- there aren't enough bytes present on the source.
takeExactly :: Int64                        -- ^ number of bytes to read
            -> InputStream ByteString       -- ^ input stream to wrap
            -> IO (InputStream ByteString)
takeExactly k0 = takeBytes' k0 (throwIO $ ReadTooShortException k0)

import qualified Data.ByteString.Char8             as S
import qualified Data.ByteString.Lazy.Char8        as L
import qualified Data.ByteString.Unsafe            as S
-- lines
-- words = splitOn isSpace >=> filterM (return . not . S.all isSpace)
lines = splitOn (== '\n')

-}




iterateUntil :: Monad m => (a -> Bool) -> (a -> m a) -> a -> UnfoldM m a
iterateUntil p f a0 = UnfoldM $ \h z ->
  let loop a x = do
        a' <- f a
        if p a' 
          then return x 
          else h x a' >>= loop a'
   in z >>= loop a0

 
whileJust :: Monad m => m (Maybe a) -> UnfoldM m a
whileJust p = UnfoldM $ \h z -> 
  let loop x = do
        a <- p
        case a of
          Nothing -> return x
          Just a  -> h x a >>= loop   
   in z >>= loop

fromHandle :: MonadIO m => Int -> Handle -> UnfoldM m BS.ByteString
fromHandle chunkSize handle = UnfoldM $ \h z ->
  let loop x = do 
	    atEOF <- liftIO $ hIsEOF handle
	    if atEOF 
	       then return x 
	       else do
		   chunk <- liftIO $ B.hGetSome handle chunkSize
		   x' <- h x chunk
		   loop $! x'
   in z >>= loop



--fromFile :: MonadIO m => Int64 -> FilePath -> UnfoldM m BS.ByteString
--System.Process
--fromProcess
{-
--unfoldM :: MonadUnliftIO m => (b -> m (Maybe (a, b))) -> b -> m [a]
unfoldM f s =
  withRunInIO $ \io ->
    ML.unfoldM (io . f) s

unfoldrM :: (Monad m) => (a -> m (Maybe (b,a))) -> a -> m [b]

--mapM :: (a -> IO b) -> InputStream a -> IO (InputStream b) 
--unfoldM :: (b -> IO (Maybe (a, b))) -> b -> IO (InputStream a) 

mapM :: MonadUnliftIO m => (a -> m b) -> InputStream a -> m (InputStream b)
mapM f is =
  withRunInIO $ \io ->
    SC.mapM (io . f) is

{-# INLINE unfoldM #-}



import  System.IO (BufferMode (NoBuffering), IOMode (ReadMode, WriteMode), SeekMode (AbsoluteSeek), hSeek, hSetBuffering, withBinaryFile)


withBinaryFile :: FilePath -> IOMode -> (Handle -> IO r) -> IO r 
withFile :: FilePath -> IOMode -> (Handle -> IO r) -> IO r 

withFileAsInput = withFileAsInputStartingAt 0


import           Control.Concurrent         (forkIO)
import           Control.Concurrent.Chan    (Chan, newChan, readChan, writeChan)
import           Control.Concurrent.MVar    (modifyMVar, newEmptyMVar, newMVar, putMVar, takeMVar)
--
chanToInput :: Chan (Maybe a) -> IO (InputStream a)
chanToInput ch = makeInputStream $! readChan ch


------------------------------------------------------------------------------
-- | Like 'withFileAsInput', but seeks to the specified byte offset before
-- attaching the given file descriptor to the 'InputStream'.
withFileAsInputStartingAt
    :: Int64                             -- ^ starting index to seek to
    -> FilePath                          -- ^ file to open
    -> (InputStream ByteString -> IO a)  -- ^ function to run
    -> IO a
withFileAsInputStartingAt idx fp m = withBinaryFile fp ReadMode go
  where
    go h = do
        unless (idx == 0) $ hSeek h AbsoluteSeek $ toInteger idx
        handleToInputStream h >>= m

{-# INLINE withFileAsInput #-}
withFileAsInput :: (MonadUnliftIO m) => FilePath -> (InputStream ByteString -> m a) -> m a
withFileAsInput fp m =
  withRunInIO $ \io ->
    SF.withFileAsInput fp (io . m)

whileJust_ :: (Monad m) => m (Maybe a) -> (a -> m b) -> m ()
whileJust_ p f = go
    where go = do
            x <- p
            case x of
                Nothing -> return ()
                Just x  -> do
                        f x
                        go

iterateUntilM :: (Monad m) => (a -> Bool) -> (a -> m a) -> a -> m a
iterateUntilM p f v 
    | p v       = return v
    | otherwise = f v >>= iterateUntilM p f

iterateWhile :: Monad m => (a -> Bool) -> m a -> m a 

iterateUntil :: Monad m => (a -> Bool) -> m a -> m a 
iterateUntilM :: Monad m => (a -> Bool) -> (a -> m a) -> a -> m a 

newtype UnfoldM m a = UnfoldM { withUnfoldM :: forall x. (x -> a -> m x) -> m x -> m x }


foldM
    :: Monad m
    => (x -> a -> m x) -> m x -> (x -> m b) -> Producer a m () -> m b
foldM step begin done p0 = do
    x0 <- begin
    go p0 x0
  where
    go p x = case p of
        Request v  _  -> closed v
        Respond a  fu -> do
            x' <- step x a
            go (fu ()) $! x'
        M          m  -> m >>= \p' -> go p' x
        Pure    _     -> done x
-}


---------------------------------------------------------------------
-- Folds
---------------------------------------------------------------------

-- | Return the result of a h function.
--
-- Results in a 'Nothing' value for empty containers.
--
stepMay :: (a -> a -> a) -> Fold a (Maybe a)
stepMay h = Fold h_ Nothing' toLazy
  where
    h_ mx a = Just' (case mx of
        Nothing' -> a
        Just' x -> h x a)
{-# INLINABLE stepMay #-}

stepDef :: a -> (a -> a -> a) -> Fold a a
stepDef a h = maybe a id <$> stepMay h
{-# INLINABLE stepDef #-}



halt_ :: MonadUnliftIO m => FoldM m a b -> FoldM m a b
halt_ f = fmap snd (halt @SomeException f)

{-
-- >>> import qualified Control.Exception as Ex
-- >>> f x = if x < 10 then return x else Ex.throw Ex.Overflow
-- >>> exfoldl = lmapM f (generalize list)
-- >>> xs = [1, 2, 500, 4] :: [Integer]
-- >>> foldlM (halt @Ex.ArithException exfold) xs
-- (Just arithmetic overflow,[1,2])
-}

halt :: Exception e => MonadUnliftIO m => FoldM m a b -> FoldM m a (Maybe e, b)
halt (FoldM h z k) = FoldM h' z' k'
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

skip_ :: MonadUnliftIO m => FoldM m a b -> FoldM m a b
skip_ f = fmap snd (skip @SomeException f)

skip :: Exception e => MonadUnliftIO m => FoldM m a b -> FoldM m a ([e], b)
skip (FoldM h z k) = FoldM h' z' k'
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

toHandle :: MonadIO m => Handle -> FoldM m B.ByteString ()
toHandle handle = 
    FoldM 
    (\_ b -> liftIO (B.hPut handle b))  
    (return ()) 
    (\_ -> return ())

toHandleBuilder :: MonadIO m => Handle -> FoldM m B.Builder ()
toHandleBuilder handle = 
    FoldM
    (\_ b -> liftIO (B.hPutBuilder handle b)) 
    (return ()) 
    (\_ -> return ())

---------------------------------------------------------------------
-- Unfold instances
---------------------------------------------------------------------

deriving instance Functor Unfold

instance Apply Unfold where
  (<.>) = ap 

instance Coapply Unfold where
  coapply = B.bimap forwards forwards . coapply . F.toList --TODO improve

instance Applicative Unfold where
  pure x = Unfold (\h z -> h z x)
  (<*>) = ap

instance Alternative Unfold where
  empty = Unfold (flip const)
  (<|>) (Unfold l) (Unfold r) = Unfold (\h z -> r h (l h z))
  {-# INLINE (<|>) #-}

instance Monad Unfold where
  return = pure

  (>>=) (Unfold u) f = Unfold $
    \ h z -> let h' x a = withUnfold (f a) h x in u h' z

instance MonadPlus Unfold where
  mzero = empty
  mplus = (<|>)

instance Semigroup (Unfold a) where
  (<>) = (<|>)

instance Monoid (Unfold a) where
  mempty = empty
  mappend = (<>)

instance Foldable Unfold where
  foldMap f = F.foldl' (\m a -> m <> f a) mempty
  {-# INLINE foldMap #-}
  foldl = F.foldl'
  foldl' h z (Unfold u) = u h z
  {-# INLINE foldl' #-}
  --toList t = build (\ c n -> F.foldr c n t)
  --toList = F.foldl (flip (:)) []

instance Eq a => Eq (Unfold a) where
  (==) left right = F.toList left == F.toList right

instance Show a => Show (Unfold a) where
  show = show . F.toList


instance Exts.IsList (Unfold a) where
  type Item (Unfold a) = a
  fromList = forwards
  toList = F.toList
  --toList = F.foldr (:) []
  --toList t = build (\ c n -> F.foldr c n t)

{-
:set -XNoOverloadedLists 
:set -XOverloadedLists 
λ> [1..3] <> [4..6] :: Unfold Int
[1,2,3,4,5,6]

λ> [1..3] <> [4..6] :: Unfold Int
[6,5,4,3,2,1]
λ> [1..3] <> [4..6] :: UnfoldM Identity Int
[1,2,3,4,5,6]

λ> runIdentity $ F.foldrM (\s a -> return $ s : a) [] [1..10]
[1,2,3,4,5,6,7,8,9,10]
λ> runIdentity $ F.foldlM (\s a -> return $ a : s) [] [1..10]
[10,9,8,7,6,5,4,3,2,1]

--λ> F.toList $ enumsRange 1 10
[10,9,8,7,6,5,4,3,2,1]
--λ> F.toList $ enumsRange' 1 10
[1,2,3,4,5,6,7,8,9,10]

-}

---------------------------------------------------------------------
-- UnfoldM instances
---------------------------------------------------------------------

deriving instance Functor m => Functor (UnfoldM m)

instance Monad m => Applicative (UnfoldM m) where
  pure x = UnfoldM (\ h z -> z >>= flip h x)
  (<*>) = ap

instance Monad m => Alternative (UnfoldM m) where
  empty = UnfoldM (const id)
  {-# INLINE (<|>) #-}
  (<|>) (UnfoldM l) (UnfoldM r) = UnfoldM (\ h z -> l h z >>= r h . pure)
  --(<|>) (UnfoldM l) (UnfoldM r) = UnfoldM (\ h z -> l h z <|> r h z)

instance Monad m => Monad (UnfoldM m) where
  return = pure
  {-# INLINE (>>=) #-}
  (>>=) (UnfoldM u) f = UnfoldM $ \ h z ->
    let h' x a = withUnfoldM (f a) h (pure x) in u h' z

instance Monad m => MonadPlus (UnfoldM m) where
  mzero = empty
  mplus = (<|>)

instance MonadTrans UnfoldM where
  lift m = UnfoldM (\ h z -> z >>= \z0 -> m >>= h z0)

instance Monad m => Semigroup (UnfoldM m a) where
  (<>) = (<|>)

instance Monad m => Monoid (UnfoldM m a) where
  mempty = empty
  mappend = (<>)

instance Foldable (UnfoldM Identity) where
  {-# INLINE foldMap #-}
  foldMap f = F.foldl' (\m a -> m <> f a) mempty
  foldl = F.foldl'
  {-# INLINE foldl' #-}
  foldl' h z (UnfoldM u) = runIdentity $ u (\s a -> return $ h s a) (Identity z)

{-
import Data.Profunctor.Rep.Fold
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic
λ> F.foldl (flip (:)) [] $ backwards [0..4]

<interactive>:4:1: error:
    Not in scope: ‘F.foldl’
    No module named ‘F’ is imported.
λ> import qualified Data.Foldable as F
-}
enumsRange' :: Int -> Int -> UnfoldM Identity Int
enumsRange' from to =
  UnfoldM $ \ step init ->
  let
    loop !state int =
      if int <= to
        then do
          newState <- step state int
          loop newState (succ int)
        else return state
    in init >>= flip loop from

instance Eq a => Eq (UnfoldM Identity a) where
  (==) left right = F.toList left == F.toList right

instance Show a => Show (UnfoldM Identity a) where
  show = show . F.toList

instance Exts.IsList (UnfoldM Identity a) where
  type Item (UnfoldM Identity a) = a
  fromList = forwardsM
  toList = F.toList -- F.foldr (:) []

---------------------------------------------------------------------
-- Fold instances
---------------------------------------------------------------------

---------------------------------------------------------------------
-- Orphan Fold & Scan instances
---------------------------------------------------------------------

-- Comonad instances

extract :: Fold a b -> b
extract (Fold _ z k) = k z

duplicate :: Fold a b -> Fold a (Fold a b)
duplicate (Fold h z k) = Fold h z (flip (Fold h) k)


instance Distributive (Fold a) where

  distribute z = Fold (\fm a -> fmap (prepend a) fm) z (fmap extract)

instance Cosieve Fold [] where

  cosieve (Fold k0 h0 z0) as0 = go k0 h0 z0 as0
    where
      go _ z k [] = k z
      go h z k (a : as) = go h (h z a) k as

instance Closed Fold where

  closed (Fold h z k) = Fold (liftA2 h) (pure z) (\f x -> k (f x))

instance Costrong Fold where

  unfirst = unfirstCorep

  unsecond = unsecondCorep

instance Corepresentable Fold where

  type Corep Fold = []

  cotabulate f = Fold (flip (:)) [] (f . P.reverse)

instance Monad (Fold a) where
  --m >>= f = cotabulate $ \a -> cosieve (f (cosieve m a)) a
  m >>= f = Fold (flip (:)) [] (\xs -> flip L.fold xs . f) <*> m

instance MonadFix (Fold a) where

  mfix = cotabulate . mfix . fmap cosieve

{-
-- Comonad instances

extract :: Fold a b -> b
extract (Fold _ z k) = k z

duplicate :: Fold a b -> Fold a (Fold a b)
duplicate (Fold h z k) = Fold h z (flip (Fold h) k)

--extend :: (Fold a b -> c) -> Fold a b -> Fold a c
--extend f (Fold h z k) = Fold h z (f . flip (Fold h) k)

instance Functor (Fold a) where
    fmap f (Fold h z k) = Fold h z (f . k)
    {-# INLINE fmap #-}

instance Profunctor Fold where
  rmap = fmap
  lmap f (Fold h z k) = Fold h' z k
    where
      h' x a = h x (f a)

instance Choice Fold where
  right' (Fold h z k) = Fold (liftA2 h) (Right z) (fmap k)
  {-# INLINE right' #-}

{-
instance Comonad (Fold a) where
    extract (Fold _ z k) = k z
    {-#  INLINE extract #-}

    duplicate (Fold h z k) = Fold h z (\x -> Fold h x k)
    {-#  INLINE duplicate #-}
-}

instance Applicative (Fold a) where
    pure b    = Fold (\() _ -> ()) () (\() -> b)
    {-# INLINE pure #-}

    (Fold hL zL kL) <*> (Fold hR zR kR) =
        let h (xL `Pair` xR) a = (hL xL a) `Pair` (hR xR a)
            z = zL `Pair` zR
            k (xL `Pair` xR) = kL xL (kR xR)
        in  Fold h z k
    {-# INLINE (<*>) #-}

instance Distributive (Fold a) where

  distribute z = Fold (\fm a -> fmap (prepend a) fm) z (fmap extract)

instance Cosieve Fold [] where

  cosieve (Fold k0 h0 z0) as0 = go k0 h0 z0 as0
    where
      go _ z k [] = k z
      go h z k (a : as) = go h (h z a) k as

instance Closed Fold where

  closed (Fold h z k) = Fold (liftA2 h) (pure z) (\f x -> k (f x))

instance Costrong Fold where

  unfirst = unfirstCorep

  unsecond = unsecondCorep

instance Corepresentable Fold where

  type Corep Fold = []

  cotabulate f = Fold (flip (:)) [] (f . P.reverse)

instance Monad (Fold a) where

  m >>= f = Fold (flip (:)) [] (\xs -> flip foldl xs . f) <*> m

instance MonadReader [a] (Fold a) where

  ask = cotabulate id

  local f m = cotabulate (cosieve m . f)

instance MonadFix (Fold a) where

  mfix = cotabulate . mfix . fmap cosieve

instance MonadZip (Fold a) where

  mzipWith = liftA2

-}
---------------------------------------------------------------------
-- FoldM instances
---------------------------------------------------------------------
{-
instance Functor m => Functor (FoldM m a) where
    fmap f (FoldM h start k) = FoldM h start k'
      where
        k' x = fmap f $! k x
    {-# INLINE fmap #-}

instance Applicative m => Applicative (FoldM m a) where
    pure b = FoldM (\() _ -> pure ()) (pure ()) (\() -> pure b)
    {-# INLINE pure #-}

    (FoldM hL zL kL) <*> (FoldM hR zR kR) =
        let h (xL `Pair` xR) a = Pair <$> hL xL a <*> hR xR a
            z = Pair <$> zL <*> zR
            k (xL `Pair` xR) = kL xL <*> kR xR
        in  FoldM h z k
    {-# INLINE (<*>) #-}

instance Functor m => Profunctor (FoldM m) where
    rmap = fmap
    lmap f (FoldM h z k) = FoldM h' z k
      where
        h' x a = h x (f a)
-}

instance Monad m => Choice (FoldM m) where
  right' (FoldM h z k) =
    FoldM ((.)(.)(.) sequence . liftA2 $ h)
           (fmap Right z)
           (runKleisli (right' $ Kleisli k))
  {-# INLINE right' #-}





{-

foo :: Monad m => (r -> a -> m r) -> r -> ListT m a -> m r
foo s r = uncons >=> maybe (return r) (\(h, t) -> s r h >>= \r' -> foo s r' t)

instance Monad m => Cosieve (FoldM m) (ListT m) where

  cosieve (FoldM h z k) l = z >>= (\o -> foo h o l) >>= k 



  closed (FoldM h z k) = FoldM undefined undefined (\f x -> k (f x)) -- (liftA2 h) (pure z) 

 z >>= (\z -> go h z l) >>= k where
    go s r = uncons >=> maybe (return r) (\(h, t) -> s r h >>= \r' -> go s r' t)

instance Closed Fold where

  closed (Fold h z k) = Fold (liftA2 h) (pure z) (\f x -> k (f x))

instance Costrong Fold where

  unfirst = unfirstCorep

  unsecond = unsecondCorep

instance Corepresentable Fold where

  type Corep Fold = []

  cotabulate f = Fold (flip (:)) [] (f . reverse)
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
