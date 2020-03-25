
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE MagicHash         #-}
{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE PatternSynonyms       #-}
module Data.Profunctor.Rep.Fold where
{-(
  -- * Free

    Free (..)
  , liftr
 
  ) where
-}

import Control.Applicative
import Control.Arrow (Kleisli(..),(&&&),(***))
import Control.Exception (Exception (..), SomeException (..), SomeAsyncException (..))
import Control.Foldl (Fold(..), FoldM(..))
import Control.Monad (MonadPlus(..), (>=>),ap, liftM)
import Control.Monad.Fix (MonadFix(..))
import Control.Monad.IO.Unlift
import Control.Monad.Reader (MonadReader(..))
import Control.Monad.State.Strict -- (MonadState(..))
import Control.Monad.Trans (MonadTrans(..))
import Control.Monad.Trans.Class as Exports
import Control.Monad.Zip (MonadZip(..))
import Data.Bool (bool)
import Data.ByteString (ByteString)
import Data.Distributive (Distributive (..))
import Data.Function ((&))
import Data.Functor.Apply
import Data.Functor.Coapply
import Data.Functor.Identity
import Data.List (mapAccumL)
import Data.Profunctor
import Data.Profunctor.Closed (Closed (..))
import Data.Profunctor.Rep as Profunctor (Corepresentable (..), unfirstCorep, unsecondCorep)
import Data.Profunctor.Sieve (Cosieve (..))
import Data.Word 
import Foreign ( ForeignPtr, Ptr, plusPtr, peek, testBit, FiniteBits(..))
import System.IO -- (Handle, hIsEOF)
import qualified Control.Exception as Ex
import qualified Control.Foldl as L


import qualified Data.Bifunctor as B
import qualified Data.ByteString      as BS
import qualified Data.ByteString as B
import qualified Data.ByteString as ByteString
import qualified Data.ByteString.Builder as B
import qualified Data.ByteString.Char8      as CS
import qualified Data.ByteString.Internal as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Lazy.Char8 as CL
import qualified Data.ByteString.Short.Internal as SB
import qualified Data.ByteString.Short.Internal as ShortByteString

import qualified Data.Foldable as F
import qualified Data.List.NonEmpty as NE
import qualified Foreign.ForeignPtr as F
import qualified GHC.Exts as Exts

--import qualified Data.Map.Strict as Map
--import qualified Data.IntMap.Strict as IntMap
--import qualified Data.HashMap.Strict as HashMap

import  System.IO as IO
 (BufferMode (NoBuffering), IOMode (ReadMode, WriteMode), SeekMode (AbsoluteSeek), hSeek, hSetBuffering, withBinaryFile)

import Prelude as P hiding
  ( head, last, null, length, and, or, all, any, sum, product, maximum, 
    minimum, mconcat, elem, notElem, lookup, map, drop, 
    Fractional(..), foldl, filter, mapM_, iterate, repeat, span, break,
    take, drop, takeWhile, dropWhile, reverse
  )

---------------------------------------------------------------------
-- Types
---------------------------------------------------------------------

-- Inspired by Nikita Volkov's /deferred-folds/.
-- Type variables that don't appear in the return type are existentially quantified:
-- Type variables that only appear in the return type are universally quantified:
-- > foldr :: (a -> x -> x) -> x -> f a -> x
-- > \h z -> flip (foldr h z) :: f a -> (forall x. (a -> x -> x) -> x -> x)

-- | A continuation of a fold.
--
-- > Free a ~ forall x . Cont (Endo x) a
-- 
-- 'Free's may be used as a non-classy replacement for 'Data.MonoTraversable.MonoFoldable',
-- i.e. for unifying both 'Data.Foldable.Foldable' and analagous non-foldable types 
-- (e.g. /ByteString/s) in one interface.
--
type Free = FreeM Identity

pattern Free :: (forall x. (a -> x -> x) -> x -> x) -> Free a
pattern Free a <- (retractr -> a) where Free a = free a

-- | A continuation of an effectful left fold.
--
-- >>> :set -XOverloadedLists 
-- >>> [1..3] <> [4..6] :: FreeM Identity Int
-- [1,2,3,4,5,6]
--
newtype FreeM m a = FreeM ( forall x. (a -> x -> m x) -> m x -> m x )

---------------------------------------------------------------------
-- Introduction
---------------------------------------------------------------------

-- | Obtain an 'Free' from a left-folding continuation.
--
free :: (forall x. (a -> x -> x) -> x -> x) -> Free a
free f = FreeM $ \h z -> Identity $ f (\a x -> runIdentity $! h a x) (runIdentity z)

-- | Obtain an 'Free' using a 'Data.Foldable.foldl''.
--
-- >>> F.foldr (flip (:)) [] $ liftl [0..4]
-- [4,3,2,1,0]
-- >>> F.foldl' (:) [] $ liftl [0..4]
-- [0,1,2,3,4]
--
liftl :: Foldable f => f a -> Free a
liftl f = free (\ h z -> F.foldl' (flip h) z f)
{-# INLINE liftl #-}

-- | Obtain an 'Free' using a 'Data.Foldable.foldr'.
--
-- >>> F.foldr (:) [] $ liftr [0..4]
-- [0,1,2,3,4]
-- >>> F.foldl' (flip (:)) [] $ liftr [0..4]
-- [4,3,2,1,0]
--
liftr :: Foldable f => f a -> Free a
liftr f = free (\ h z -> F.foldr h z f)
{-# INLINE liftr #-}

-- | Obtain an 'FreeM' from a 'Data.Foldable.Foldable'.
--
-- >>> F.foldr (:) [] $ liftlM @Identity [0..4]
-- [4,3,2,1,0]
-- >>> F.foldl' (flip (:)) [] $ liftlM @Identity [0..4]
-- [0,1,2,3,4]
--
liftlM :: Monad m => Foldable f => f a -> FreeM m a
liftlM f = FreeM (\ h z -> z >>= flip (F.foldlM $ flip h) f)
{-# INLINE liftlM #-}

-- | Obtain an 'FreeM' from a 'Data.Foldable.Foldable', reversing the order of the elements.
--
-- >>> F.foldr (:) [] $ liftrM @Identity [0..4]
-- [0,1,2,3,4]
-- >>> F.foldl' (flip (:)) [] $ liftrM @Identity [0..4]
-- [4,3,2,1,0]
--
liftrM :: Monad m => Foldable f => f a -> FreeM m a
liftrM f = FreeM (\ h z -> z >>= flip (F.foldrM h) f)
{-# INLINE liftrM #-}

{-
--improve :: (forall f. Foldable f => m a) -> FreeM m a 

-- | Lift an 'Free' into an 'FreeM' forwards.
--
-- >>> F.toList . forwards @Identity $ liftr [1..5]
-- [1,2,3,4,5]
-- >>> F.toList . backwards @Identity $ liftl [1..5]
-- [5,4,3,2,1]
--
forwards :: Monad m => Free a -> FreeM m a
forwards (Free u) = FreeM (\ h z -> u (\ a sM -> sM >>= \s -> h a s) z)
{-# INLINE forwards #-}

-- | Lift an 'Free' into an 'FreeM' backwards.
--
-- >>> F.toList . backwards @Identity $ liftr [1..5]
-- [5,4,3,2,1]
-- >>> F.toList . backwards @Identity $ liftl [1..5]
-- [1,2,3,4,5]
--
backwards :: Monad m => Free a -> FreeM m a
backwards (Free u) = FreeM (\ h z -> z >>= u (\ a f x -> h a x >>= f) pure)
{-# INLINE backwards #-}
-}

---------------------------------------------------------------------
-- Elimination
---------------------------------------------------------------------

-- | Run an 'Free'.
--
-- >>> retractr (liftl [0..4]) (flip (:)) []
-- [4,3,2,1,0]
--
retractr :: Free a -> (forall x . (a -> x -> x) -> x -> x)
retractr (FreeM u) h z = runIdentity $ u (\a x -> Identity $! h a x) (Identity z)

-- | Run an 'Free' from the right.
--
-- >>> retractl' (liftl [0..4]) (:) []
-- [0,1,2,3,4]
--
retractl' :: Free a -> (x -> a -> x) -> x -> x
retractl' (Free u) f z0 = u f' id z0 where f' x k z = k $! f z x

-- | Run an 'FreeM'.
--
retractM :: FreeM m a -> (a -> x -> m x) -> m x -> m x
retractM (FreeM u) h z = u h z

-- | Run an 'FreeM IO' inside 'Control.Monad.IO.Unlift.UnliftIO'.
--
retractIO :: MonadUnliftIO m => FreeM IO a -> (a -> x -> m x) -> m x -> m x
retractIO (FreeM u) h z = withRunInIO $ \io -> u (\a x -> io $ h a x) (io z)

-- | Run an 'Free' with a continuation function.
--
-- @ \u -> 'withFree' u 'Control.Foldl.purely_' :: 'Free' a -> 'Control.Foldl.Fold' a b -> b @
--
withFree :: Free a -> ((forall x . (a -> x -> x) -> x -> x) -> r) -> r
withFree u f = f $ retractr u

-- | Run an 'FreeM' with a continuation function.
--
-- @ \u -> 'withFreeM' u 'Control.Foldl.impurely_' :: 'FreeM' m a -> 'Control.Foldl.FoldM' m a b -> m b @
--
withFreeM :: FreeM m a -> ((forall x . (a -> x -> m x) -> m x -> m x) -> r) -> r
withFreeM u f = f $ retractM u

---------------------------------------------------------------------
-- Basic Interface
---------------------------------------------------------------------

infixr 5 `cons` -- (:)

-- | Prepend a value to an 'Free'.
--
cons :: a -> Free a -> Free a
cons a (Free u) = free $ \ h z -> h a (u h z)

infixl 5 `snoc`

-- | Append a value to an 'Free'.
--
snoc :: Free a -> a -> Free a
snoc (Free u) a = free $ \ h z -> u h (h a z)

infixr 6 `append` -- (<>)

-- | Append two 'Free's.
--
-- Prefer to /<>/ for 'Free's.
--
append :: Free a -> Free a -> Free a
append u1 u2 = retractr u1 cons u2

-- | Retrieve the first element of an 'Free'.
--
head :: Free a -> Maybe a
head (Free u) = u (\a x -> x <|> Just a) Nothing

-- | Retrieve the first element of an 'Free', with a default.
--
headDef :: a -> Free a -> a
headDef a = maybe a id . head

-- | Retrieve the last element of an 'Free'.
--
-- > maybe a id $ last u = retractr u (flip const) a
--
last :: Free a -> Maybe a
last (Free u) = u (\a x -> Just a <|> x) Nothing

-- | Retrieve the last element of an 'Free', with a default.
--
lastDef :: a -> Free a -> a
lastDef a = maybe a id . last

-- | Check whether an 'Free' is empty.
--
-- > null u = retractr u (\_ _ -> False) True
--
null :: Free a -> Bool
null = runIdentity . nullM

-- | Check whether an 'FreeM' is empty.
--
nullM :: Monad m => FreeM m a -> m Bool
nullM (FreeM u) = u (\ _ _ -> pure False) $ pure True
{-# INLINE nullM #-}

-- | Right-handed monadic free to a list.
--
-- >>> listM $ liftr [1..5]
-- Identity [1,2,3,4,5]
--
listM :: Monad m => FreeM m a -> m [a]
listM (FreeM u) = u (\a x -> pure $ a : x) $ pure []

-- | Free a pure effect with an 'FreeM'.
--
-- > liftMapM_ print :: Show a => FreeM IO a -> IO ()
--
-- This is more efficient implementation of /mapM_/.
--
liftMapM_ :: Monad m => (a -> m ()) -> FreeM m a -> m ()
liftMapM_ f (FreeM u) = u (const . f) $ pure ()
{-# INLINE liftMapM_ #-}

---------------------------------------------------------------------
-- Indexing lifts
---------------------------------------------------------------------

-- | TODO: Document
--
-- >>> index (liftl [0..9]) 3
-- Just 3
--
index :: Free a -> Int -> Maybe a
index (Free u) i = either (const Nothing) Just $ u h (Left 0)
  where
    h a x = case x of
      Left j -> if i == j then Right a else Left (j + 1)
      _       -> x

-- | Return the index of the first element equal to a given element, in ascending order.
--
-- >>> elemIndex 'o' (liftl "foobar")
-- Just 1
--
elemIndex :: Eq a => a -> Free a -> Maybe Int
elemIndex a = findIndex (== a)

-- | Return the index of the first element satisfying a predicate, in ascending order.
--
findIndex :: (a -> Bool) -> Free a -> Maybe Int
findIndex p (Free u) = either (const Nothing) Just $ u h (Left 0)
  where
    h a x = case x of
      Left j -> if p a then Right j else Left (j + 1)
      _       -> x

-- | Return the indices of all elements equal to a given element, in descending order.
--
-- >>> elemIndices 'o' (liftl "foobar")
-- [2,1]
--
elemIndices :: Eq a => a -> Free a -> [Int]
elemIndices a = findIndices (==a)

-- | Return the indices of all elements satisfying a predicate, in descending order.
--
findIndices :: (a -> Bool) -> Free a -> [Int]
findIndices p (Free u) = fst' $ u h (Pair [] 0)
  where
    h a (Pair js j) = if p a then Pair (j:js) (j+1) else Pair js (j+1) 

---------------------------------------------------------------------
-- Transformation
---------------------------------------------------------------------

-- | Reverse an 'Free'.
--
reverse :: Free a -> Free a
reverse (Free u) = free $ \ h -> u (\ a f -> f . h a) id

-- | Take the first /n/ values from an 'Free'.
--
-- >>> F.toList . take 2 $ liftr [1..10]
-- [1,2]
--
take :: Int -> Free a -> Free a
take i0 (Free u) = free $ \ h z -> u
  (\ a ix i -> if i < i0 then h a (ix $ succ i) else z)
  (const z)
  0

-- | Drop the last /n/ values from an 'Free'.
--
-- >>> dropEnd 2 $ liftr [1..10]
-- [1,2,3,4,5,6,7,8]
--
dropEnd :: Int -> Free a -> Free a
dropEnd = dropM

-- | Drop the last /n/ values from an 'FreeM'.
--
dropM :: Monad m => Int -> FreeM m a -> FreeM m a
dropM i0 = transduceM $ predropM i0 where
  predropM n (FoldM h z k) = FoldM h' z' k'
    where
      z'              = Pair n <$> z
      h' (Pair 0 s) x = Pair 0 <$> h s x
      h' (Pair i s) _ = pure $ Pair (i - 1) s
      k' = k . snd'

-- | Take values from an 'Free' while a predicate holds.
--
-- >>> takeWhile (<= 5) $ liftr [1..10]
-- [1,2,3,4,5]
--
takeWhile :: (a -> Bool) -> Free a -> Free a
takeWhile p (Free u) = free $ \ h -> u (\ a f -> if p a then h a . f else id) id 

-- | Drop the last /n/ values from an 'Free' for which a predicate holds.
--
-- > dropWhileEnd isSpace (chars "foo\n" <> undefined) == chars "foo" <> undefined
--
-- >>> dropWhileEnd (> 5) $ liftr [1..10]
-- [1,2,3,4,5]
-- >>> dropWhileEnd isSpace $ chars "foo\n"
-- "foo"
-- >>> dropWhileEnd isSpace $ chars "foo bar"
-- "foo bar"
--
dropWhileEnd :: (a -> Bool) -> Free a -> Free a
dropWhileEnd p = F.foldr (\x xs -> if p x && null xs then mempty else x `cons` xs) mempty

-- | Filter values with a predicate.
--
filter :: (a -> Bool) -> Free a -> Free a
filter p (Free u) = free (\ h -> u (\ elt s -> if p elt then h elt s else s))
{-# INLINE filter #-}

-- | Filter values in an 'FreeM' with an effectful predicate.
--
filterM :: Monad m => (a -> m Bool) -> FreeM m a -> FreeM m a
filterM test (FreeM u) = FreeM (\ h -> u (\ elt s -> test elt >>= bool (pure s) (h elt s)))
{-# INLINE filterM #-}

-- | Partition values with a predicate.
--
-- > partition p u = (filter p u, filter (not . p) u)
--
partition :: (a -> Bool) -> Free a -> (Free a, Free a)
partition p = filter p &&& filter (not . p)

-- | Zip two lifts together.
--
zip :: Free a -> Free b -> Free (a, b)
zip = Data.Profunctor.Rep.Fold.zipWith (,)

-- | Zip two lifts together with a function.
--
zipWith :: (a -> b -> c) -> Free a -> Free b -> Free c
zipWith = mzipWith

-- | Lift an index counter into an 'Free'.
--
zipWithIndex :: Free a -> Free (Int, a)
zipWithIndex (Free u) = free $ \ istep istate -> u
  (\a ia i -> istep (i, a) (ia $ succ i))
  (const istate)
  0

-- | Change the base monad using an invariant natural transformation.
--
invhoist :: (forall a. m a -> n a) -> (forall a. n a -> m a) -> FreeM m a -> FreeM n a
invhoist t1 t2 (FreeM u) = FreeM $ \ h z -> t1 $ u (\ a b -> t2 $ h a b) (t2 z)
{-# INLINE invhoist #-}

-- | A variant of 'Control.Monad.Trans.Cont.callCC' for lifts.
--
-- >>> try5 x ex = if x == 5 then pure (x*3) else ex 0
-- >>> cont = pure >=> backtrack . try5 >=> pure . (+1) :: Int -> Free Int
-- >>> cont 5
-- [16]
-- >>> cont 4
-- [1]
--
-- See also < https://wiki.haskell.org/MonadCont_under_the_hood#MonadCont_and_callCC >
--
backtrack :: Monad m => ((a -> FreeM m a) -> FreeM m b) -> FreeM m b
backtrack f = let back a = FreeM $ \ h z -> z >>= h a in FreeM $ \ c -> retractM (f back) c
{-# INLINE backtrack #-}

-- | Lift a 'Control.Foldl.Fold' input mapping function into a mapping of 'Free's.
--
-- Useable in conjuction with the combinators from 'Control.Foldl':
--
-- @
-- 'transduce' $ 'Control.Foldl.handles' 'Control.Foldl.folded' :: 'Data.Foldable' f => 'Free' (f b) -> 'Free' b
-- 'transduce' $ 'Control.Foldl.handles' 'Data.Traversable.traverse' :: 'Data.Traversable' t => 'Free' (t b) -> 'Free' b
-- @
--
-- >>> transduce (FL.prefilter (<=2)) $ liftr [1..5]
-- [1,2]
--
-- See also /foldl-transduce/.
--
transduce :: (forall x. Fold b x -> Fold a x) -> Free a -> Free b
transduce f (Free u) = free $ \ h z -> L.purely_ (u . flip) (f $ Fold (flip h) z id)
{-# INLINE transduce #-}

-- | Lift a 'Control.Foldl.FoldM' input mapping function into a mapping of 'FreeM's.
--
transduceM :: Monad m => (forall x. FoldM m b x -> FoldM m a x) -> FreeM m a -> FreeM m b
transduceM f (FreeM u) = FreeM $ \ h z -> L.impurely_ (u . flip) (f $ FoldM (flip h) z pure)
{-# INLINE transduceM #-}

---------------------------------------------------------------------
-- Generating and lifting
---------------------------------------------------------------------

-- | Left lifting anamorphism.
--
-- > ana f (retractr u h z) == u
--
-- if the following holds:
--
-- > f (h x y) = Just (x,y)
-- > f z       = Nothing
--
-- >>> F.toList $ ana (\b -> if b > 10 then Nothing else Just (b, b+1)) 1
-- [1,2,3,4,5,6,7,8,9,10]
--
ana :: (r -> Maybe (a, r)) -> r -> Free a
ana f r0 = free $ \h z ->
  let loop r = 
        case f r of
	    Nothing      -> z
	    Just (a, r') -> loop r' & h a
   in loop r0
{-# INLINE ana #-}

-- | Monadic variant of 'ana'.
--
anaM :: Monad m => (r -> m (Maybe (a, r))) -> r -> FreeM m a
anaM f r0 = FreeM $ \h z ->
  let loop r x = do
	mr <- f r
	case mr of
	    Nothing      -> pure x
	    Just (a, r') -> loop r' x >>= h a
   in z >>= loop r0

-- | Repeat a value ad infinitum.
--
repeat :: a -> Free a
repeat a = iterate id a

-- | Create an 'Free' of length n with x the value of every element.
--
replicate :: Int -> a -> Free a
replicate i = take i . ana (\a -> Just (a,a))

-- | Apply a function ad infinitum.
--
iterate :: (a -> a) -> a -> Free a
iterate f = ana (\x -> Just (x, f x))

-- | Apply a monadic function ad infinitum.
--
iterateM :: Monad m => (a -> m a) -> a -> FreeM m a
iterateM = iterateWhileM (const False)

-- | Execute a monadic action repeatedly until the result fails to satisfy a predicate.
--
iterateWhile :: Monad m => (a -> Bool) -> m a -> FreeM m a 
iterateWhile p ma = FreeM $ \h z ->
  let loop x = do
        a <- ma 
        if not $ p a 
          then pure x 
          else h a x >>= loop
   in z >>= loop

-- | Apply a monadic function repeatedly until the result fails to satisfy a predicate
--
-- This is a monadic analogue of @('Prelude.until')@.
--
-- >>> F.toList $ iterateWhileM (> 0) (Identity . pred) 11
-- [1,2,3,4,5,6,7,8,9,10]
--
iterateWhileM :: Monad m => (a -> Bool) -> (a -> m a) -> a -> FreeM m a
iterateWhileM p f a0 = FreeM $ \h z ->
  let loop a x = do
        a' <- f a
        if not $ p a' 
          then pure x 
          else h a' x >>= loop a'
   in z >>= loop a0

-- | Execute a monadic action repeatedly as long as the given boolean expression pures /True/.
--
-- The condition is evaluated before the recursive step.
--
whileM :: Monad m => m Bool -> (a -> m a) -> a -> FreeM m a
whileM mb f a0 = FreeM $ \h z ->
  let loop a x = do
	b <- mb
	if b
          then f a >>= flip h x 
	  else pure x
   in z >>= loop a0

-- | Execute a monadic action repeatedly until the result pures /Nothing/.
--
whileJust :: Monad m => m (Maybe a) -> FreeM m a
whileJust ma = FreeM $ \h z -> 
  let loop x = do
        a <- ma
        case a of
          Nothing -> pure x
          Just a  -> h a x >>= loop   
   in z >>= loop

---------------------------------------------------------------------
-- Frees
---------------------------------------------------------------------

-- | The empty lift.
--
empty :: FreeM m a
empty = FreeM $ const id

-- | Ascending stream of enumss starting from the one specified.
--
enumsFrom :: (Enum a) => a -> Free a
enumsFrom a = free $ \ h z ->
  let loop i = h i (loop $ succ i) in loop a
{-# INLINE enumsFrom #-}

-- | Enums in the specified inclusive range.
--
enumsRange :: (Enum a, Ord a) => a -> a -> Free a
enumsRange a0 a1 = free $ \ h z ->
  let loop i =
        if i <= a1
	  then h i (loop $ succ i)
	  else z
   in loop a0
{-# INLINE enumsRange #-}

-- | Bytes of a lazy bytestring
--
-- >>> toList $ bytes "foo"
-- [102,111,111]
--
-- Essentially a version of < http://hackage.haskell.org/package/bytestring-0.10.10.0/docs/src/Data.ByteString.html#unpackFoldr /unpackFoldr/ >.
--
bytes :: BL.ByteString -> Free Word8
bytes b = free $ \ h z -> BL.foldr h z b
{-# INLINE [0] bytes #-}

-- | Reversed bytes of a lazy bytestring
--
-- > bytesRev b = free $ \ h z -> BL.foldl' (flip h) z b
--
-- >>> toList $ bytesRev "foo"
-- [111,111,102]
--
bytesRev :: BL.ByteString -> Free Word8
bytesRev b = free $ \ h z -> BL.foldl' (flip h) z b

-- | Chars of a lazy bytestring
--
-- >>> toList $ chars "foo"
-- "foo"
--
chars :: BL.ByteString -> Free Char
chars b = free $ \ h z -> CL.foldr h z b

-- | Reversed chars of a lazy bytestring
--
-- > charsRev b = free $ \ h z -> CL.foldl' (flip h) z b
--
-- >>> toList $ charsRev "foo"
-- "oof"
--
charsRev :: BL.ByteString -> Free Char
charsRev b = free $ \ h z -> CL.foldl' (flip h) z b

-- | Bytes of a strict bytestring
--
bytes' :: BS.ByteString -> Free Word8
bytes' bs = free $ \ h z -> BS.foldr h z bs
{-# INLINE bytes' #-}

-- | Reversed bytes of a strict bytestring
--
-- > bytesRev' bs = free $ \ h z -> BS.foldl' (flip h) z bs
--
bytesRev' :: BS.ByteString -> Free Word8
bytesRev' bs = free $ \ h z -> BS.foldl' (flip h) z bs
{-# INLINE bytesRev' #-}

-- | Chars of a strict bytestring
--
chars' :: BS.ByteString -> Free Char
chars' bs = free $ \ h z -> CS.foldr h z bs
{-# INLINE chars' #-}

-- | Reversed chars of a strict charstring
--
-- > charsRev' bs = free $ \ h z -> CS.foldl' (flip h) z bs
--
charsRev' :: BS.ByteString -> Free Char
charsRev' bs = free $ \ h z -> CS.foldl' (flip h) z bs
{-# INLINE charsRev' #-}

-- | Chunks of a lazy bytestring
--
chunks :: BL.ByteString -> Free BS.ByteString
chunks b = free $ \ h z -> BL.foldrChunks h z b

-- | Reversed chunks of a lazy bytestring
--
-- > chunksRev b = free $ \ h z -> BL.foldlChunks (flip h) z b
--
chunksRev :: BL.ByteString -> Free BS.ByteString
chunksRev b = free $ \ h z -> BL.foldlChunks (flip h) z b

-- | Free a bytestring from a handle, line by line.
--
liftLine :: MonadIO m => Handle -> FreeM m BS.ByteString
liftLine handle = FreeM $ \h z ->
  let loop x = do 
	atEOF <- liftIO $ hIsEOF handle
	if atEOF 
	   then pure x 
	   else do
	       a <- liftIO $ B.hGetLine handle
	       x' <- h a x
	       loop $! x'
   in z >>= loop

-- | Free a bytestring from a handle.
--
liftSome :: MonadIO m => Int -> Handle -> FreeM m BS.ByteString
liftSome chunk handle = FreeM $ \h z ->
  let loop x = do 
	atEOF <- liftIO $ hIsEOF handle
	if atEOF 
	   then pure x 
	   else do
	       a <- liftIO $ B.hGetSome handle chunk
	       x' <- h a x
	       loop $! x'
   in z >>= loop

-- | Free a bytestring from a handle, without blocking.
--
-- Similar to 'liftSome', except that it will never block waiting for data to become available, 
-- instead pureing only what data is available.
--
-- If there is no data available to be read, 'liftGetNonBlocking' pures the empty bytestring.
-- 
liftNonBlocking :: MonadIO m => Int -> Handle -> FreeM m BL.ByteString
liftNonBlocking chunk handle = FreeM $ \h z ->
  let loop x = do 
	atEOF <- liftIO $ hIsEOF handle
	if atEOF 
	   then pure x 
	   else do
	       a <- liftIO $ BL.hGetNonBlocking handle chunk
	       x' <- h a x
	       loop $! x'
   in z >>= loop

---------------------------------------------------------------------
-- Folds
---------------------------------------------------------------------

prepend :: a -> Fold a b -> Fold a b
prepend a = run a . duplicate where run a (Fold h z k) = k (h z a)
{-# INLINABLE prepend #-}

stepDef :: a -> (a -> a -> a) -> Fold a a
stepDef a h = maybe a id <$> L._Fold1 h
{-# INLINABLE stepDef #-}

halt_ :: MonadUnliftIO m => FoldM m a b -> FoldM m a b
halt_ f = fmap snd (halt @SomeException f)

{-
-- >>> import qualified Control.Exception as Ex
-- >>> f x = if x < 10 then pure x else Ex.throw Ex.Overflow
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
        pure (Nothing, y)

    h' x'@(Just _, _) _ = pure x'
    h' (Nothing, x1) a =
      do
        x2Either <- flip catch (pure . Left) . liftM Right $ h x1 a
        case x2Either of
            Left e   -> pure (Just e, x1)
            Right x2 -> pure (Nothing, x2)

    k' (eMaybe, x) =
      do
        b <- k x
        pure (eMaybe, b)

skip_ :: MonadUnliftIO m => FoldM m a b -> FoldM m a b
skip_ f = fmap snd (skip @SomeException f)

skip :: Exception e => MonadUnliftIO m => FoldM m a b -> FoldM m a ([e], b)
skip (FoldM h z k) = FoldM h' z' k'
  where
    z' =
      do
        y <- z
        pure (id, y)

    h' (es, x1) a =
      do
        x2Either <- flip catch (pure . Left) . liftM Right $ h x1 a
        case x2Either of
            Left e   -> pure (es . (e :), x1)
            Right x2 -> pure (es, x2)

    k' (es, x) =
      do
        b <- k x
        pure (es [], b)

toHandle :: MonadIO m => Handle -> FoldM m B.ByteString ()
toHandle handle = 
    FoldM 
    (\_ b -> liftIO (B.hPut handle b))  
    (pure ()) 
    (\_ -> pure ())

toHandleBuilder :: MonadIO m => Handle -> FoldM m B.Builder ()
toHandleBuilder handle = 
    FoldM
    (\_ b -> liftIO (B.hPutBuilder handle b)) 
    (pure ()) 
    (\_ -> pure ())

---------------------------------------------------------------------
-- ZipFold
---------------------------------------------------------------------

newtype ZipFold a = ZipFold { getZipFold :: Free a } deriving (Functor, Show)

instance Applicative ZipFold where
  pure = ZipFold . repeat
  -- |
  -- >>> getZipFold $ (,) <$> ZipFold (liftr [1..4]) <*> ZipFold (liftr [1..4])
  -- [(1,1),(2,2),(3,3),(4,4)]
  liftA2 f (ZipFold u1) (ZipFold u2) = ZipFold $ mzipWith f u1 u2

---------------------------------------------------------------------
-- FreeM instances
---------------------------------------------------------------------


deriving instance Functor m => Functor (FreeM m)

instance Foldable Free where
  
  foldr h z u = retractr u h z
  {-# INLINE foldr #-}

  foldl' h z u = retractl' u h z
  {-# INLINE foldl' #-}

instance Monad m => Applicative (FreeM m) where
  pure x = FreeM (\ h z -> z >>= h x)
  (<*>) = ap

instance Monad m => Alternative (FreeM m) where
  -- >>> F.toList (empty :: Free Int)
  -- []
  empty = Data.Profunctor.Rep.Fold.empty

  (<|>) (FreeM l) (FreeM r) = FreeM (\ h z -> l h z >>= r h . pure)
  {-# INLINE (<|>) #-}

--TODO improve
instance Coapply Free where 
  coapply = B.bimap liftr liftr . coapply . F.toList

--TODO improve
instance Traversable Free where
  -- |
  -- >>> traverse pure $ liftr [1..5]
  -- [1,2,3,4,5]
  traverse f = fmap liftr . traverse f . F.toList 

instance Monad m => Monad (FreeM m) where
  (>>=) (FreeM u) f = FreeM $ \ h z ->
    let h' a x = retractM (f a) h (pure x) in u h' z
  {-# INLINE (>>=) #-}

instance Monad m => MonadPlus (FreeM m) where
  mzero = Data.Profunctor.Rep.Fold.empty
  mplus = (<|>)

instance MonadTrans FreeM where
  lift m = FreeM (\ h z -> z >>= \z0 -> m >>= flip h z0)

--TODO improve
instance MonadZip Free where
  mzipWith f u1 u2 = liftr $ P.zipWith f (F.toList u1) (F.toList u2)

instance Monad m => Semigroup (FreeM m a) where
  (<>) = (<|>)

instance Monad m => Monoid (FreeM m a) where
  mempty = Data.Profunctor.Rep.Fold.empty
  mappend = (<>)


instance Eq a => Eq (Free a) where
  (==) left right = F.toList left == F.toList right

instance Show a => Show (Free a) where
  show = show . F.toList

instance Exts.IsList (Free a) where
  type Item (FreeM Identity a) = a
  fromList = liftr
  toList = F.toList

instance Exts.IsString (Free Char) where
  fromString = liftr

---------------------------------------------------------------------
-- Orphan Fold & FoldM instances
---------------------------------------------------------------------

-- Comonad instances

extract :: Fold a b -> b
extract (Fold _ z k) = k z

duplicate :: Fold a b -> Fold a (Fold a b)
duplicate (Fold h z k) = Fold h z (flip (Fold h) k)

instance Distributive (Fold a) where

  distribute z = Fold (\fm a -> fmap (prepend a) fm) z (fmap extract)

instance Closed Fold where

  closed (Fold h z k) = Fold (liftA2 h) (pure z) (\f x -> k (f x))

instance Costrong Fold where

  unfirst = unfirstCorep

  unsecond = unsecondCorep

{- TODO a/b test
instance Cosieve Fold [] where

  cosieve (Fold k0 h0 z0) as0 = go k0 h0 z0 as0
    where
      go _ z k [] = k z
      go h z k (a : as) = go h (h z a) k as

instance Corepresentable Fold where

  type Corep Fold = []

  cotabulate f = Fold (flip (:)) [] (f . P.reverse)

instance Monad (Fold a) where
  --m >>= f = cotabulate $ \a -> cosieve (f (cosieve m a)) a
  m >>= f = Fold (flip (:)) [] (\xs -> flip L.fold xs . f) <*> m
-}

instance Cosieve Fold Free where

  cosieve = L.fold -- (Fold h z k) (Free u) = k $ u h z

instance Corepresentable Fold where

  type Corep Fold = Free

  --cotabulate f = Fold (flip cons) mempty (f . reverse) -- TODO a/b test
  cotabulate f = Fold snoc mempty f

instance Monad (Fold a) where
  --m >>= f = cotabulate $ \a -> cosieve (f (cosieve m a)) a  -- TODO a/b test
  m >>= f = Fold (flip (:)) [] (\xs -> flip L.fold xs . f) <*> m

instance MonadFix (Fold a) where

  mfix = cotabulate . mfix . fmap cosieve

instance Monad m => Choice (FoldM m) where
  right' (FoldM h z k) =
    FoldM ((.)(.)(.) sequence . liftA2 $ h)
           (fmap Right z)
           (runKleisli (right' $ Kleisli k))
  {-# INLINE right' #-}

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

try :: (MonadUnliftIO m, Exception e) => m a -> m (Either e a)
try f = catch (liftM Right f) (pure . Left)

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

fst' (Pair a b) = a
snd' (Pair a b) = b

