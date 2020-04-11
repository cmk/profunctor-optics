
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE MagicHash         #-}

module Data.Profunctor.Rep.Foldr where


import Control.Arrow (Kleisli(..),(***))
import Control.Applicative
import Control.Monad (MonadPlus(..), (>=>),ap, liftM)
import Control.Monad.Fix (MonadFix(..))
import Control.Monad.Zip (MonadZip(..))
import Control.Monad.Reader (MonadReader(..))
import Control.Monad.Trans (MonadTrans(..))
import Data.Distributive (Distributive (..))
import Data.Functor.Identity
import Data.Functor.Apply
import Data.Bool (bool)
import Data.List (mapAccumL)
import Data.Profunctor
import Data.Profunctor.Closed (Closed (..))
import Data.Profunctor.Rep as Profunctor (Corepresentable (..), unfirstCorep, unsecondCorep)
import Data.Profunctor.Sieve (Cosieve (..))
import qualified Data.Foldable as F

import Control.Exception (Exception (..), SomeException (..), IOException, SomeAsyncException (..))
import qualified Control.Exception as Ex

import Control.Monad.IO.Unlift
import Data.MonoTraversable (MonoFoldable(..), Element)
import Data.Sequences (SemiSequence, IsSequence, LazySequence, Index)
import qualified Data.Sequences as MS
import qualified Data.List.NonEmpty as NE
import qualified Data.MonoTraversable as MT
import System.IO (Handle, hIsEOF)


import qualified Data.Map.Strict as Map
import qualified Data.IntMap.Strict as IntMap
import qualified Data.HashMap.Strict as HashMap
import qualified Data.ByteString as ByteString
import qualified Data.ByteString.Short.Internal as ShortByteString
--import qualified Data.Vector.Generic as GenericVector

import Control.Applicative as Exports
import Control.Arrow as Exports
import Control.Category as Exports
import Control.Concurrent as Exports
import Control.Exception as Exports
import Control.Monad as Exports hiding (mapM_, sequence_, forM_, msum, mapM, sequence, forM)
import Control.Monad.IO.Class as Exports
import Control.Monad.Fix as Exports hiding (fix)
import Control.Monad.ST as Exports
import Data.Bits as Exports
import Data.Bool as Exports
import Data.Char as Exports
import Data.Coerce as Exports
import Data.Complex as Exports
import Data.Data as Exports
import Data.Dynamic as Exports
import Data.Either as Exports
import Data.Fixed as Exports
import Data.Function as Exports hiding (id, (.))
import Data.Functor as Exports
import Data.Functor.Identity as Exports
import Data.Int as Exports
import Data.IORef as Exports
import Data.Ix as Exports
import Data.List as Exports hiding (foldr, reverse,sortOn, isSubsequenceOf, uncons, concat, runFoldr, foldl1, maximum, minimum, product, sum, all, and, any, concatMap, elem, foldl, runFoldr1, notElem, or, find, maximumBy, minimumBy, mapAccumL, mapAccumR, foldl', traverse_, sequence_, asum)
import Data.Maybe as Exports
import Data.Monoid as Exports -- hiding (Last(..), First(..), (<>))
import Data.Ord as Exports
import Data.Proxy as Exports
import Data.Ratio as Exports
import Data.Semigroup as Exports hiding (Last(..), First(..))
import Data.STRef as Exports
import Data.String as Exports
import Data.Traversable as Exports
import Data.Tuple as Exports
import Data.Unique as Exports
import Data.Version as Exports
import Data.Word as Exports
import Debug.Trace as Exports
import Foreign.ForeignPtr as Exports
import Foreign.Ptr as Exports
import Foreign.StablePtr as Exports
import Foreign.Storable as Exports hiding (sizeOf, alignment)
import GHC.Conc as Exports hiding (withMVar, threadWaitWriteSTM, threadWaitWrite, threadWaitReadSTM, threadWaitRead)
import GHC.Exts as Exports (lazy, inline, sortWith, groupWith, IsList)
import qualified GHC.Exts as Exts

import GHC.Generics as Exports (Generic)
import GHC.IO.Exception as Exports
import Numeric as Exports
import Prelude as Exports hiding (concat, runFoldr, mapM_, sequence_, foldl1, maximum, minimum, product, sum, all, and, any, concatMap, elem, foldl, foldr, foldr1, notElem, or, mapM, sequence, id, (.), reverse, foldMap)
import System.Environment as Exports
import System.Exit as Exports
import System.IO as Exports
import System.IO.Error as Exports
import System.IO.Unsafe as Exports
import System.Mem as Exports
import System.Mem.StableName as Exports
import System.Timeout as Exports
import Text.ParserCombinators.ReadP as Exports (ReadP, ReadS, readP_to_S, readS_to_P)
import Text.ParserCombinators.ReadPrec as Exports (ReadPrec, readPrec_to_P, readP_to_Prec, readPrec_to_S, readS_to_Prec)
import Text.Printf as Exports (printf, hPrintf)
import Text.Read as Exports (Read(..), readMaybe, readEither)

import Data.Profunctor.Rep.Foldl (Foldl(..), FoldlM(..), UnfoldlM, prefoldrM)
import Data.Profunctor.Unsafe
import Unsafe.Coerce

import qualified Prelude as P

-- containers
-------------------------
import Data.IntMap.Strict as Exports (IntMap)
import Data.Map.Strict as Exports (Map)
import Data.IntSet as Exports (IntSet)
import Data.Set as Exports (Set)
import Data.Sequence as Exports (Seq)

-- transformers
-------------------------
import Control.Monad.Trans.Class as Exports

-- bytestring
-------------------------
import Data.ByteString as Exports (ByteString)
import Data.ByteString.Short as Exports (ShortByteString)

-- primitive
-------------------------
import Data.Primitive as Exports

-- unordered-containers
-------------------------
import Data.HashMap.Strict as Exports (HashMap)

-- hashable
-------------------------
import Data.Hashable as Exports (Hashable)



--import qualified Data.Text      as TS
--import qualified Data.Text.Lazy as TL
import qualified Data.ByteString      as BS
import qualified Data.ByteString.Lazy as BL


{-|
A projection on data, which only knows how to execute a right-fold.

It is a monad and a monoid, and is very useful for
efficiently aggregating the projections on data intended for right-folding,
since its concatenation (`<>`) has complexity of @O(1)@.

[Intuition]

The intuition of what this abstraction is all about can be derived from lists.

Let's consider the `Data.List.runFoldr` function for lists:

>runFoldr :: (a -> b -> b) -> b -> [a] -> b

If we reverse its parameters we get

>runFoldr :: [a] -> (a -> b -> b) -> b -> b

Which in Haskell is essentially the same as

>runFoldr :: [a] -> (forall b. (a -> b -> b) -> b -> b)

We can isolate that part into an abstraction:

>newtype Unfoldr a = Unfoldr (forall b. (a -> b -> b) -> b -> b)

Then we get to this simple morphism:

>list :: [a] -> Unfoldr a
>list list = Unfoldr (\ h z -> runFoldr h z list)

We can do the same with say "Data.Text.Text":

>text :: Text -> Unfoldr Char
>text text = Unfoldr (\ h z -> Data.Text.runFoldr h z text)

And then we can use those both to concatenate with just an @O(1)@ cost:

>abcdef :: Unfoldr Char
>abcdef = list ['a', 'b', 'c'] <> text "def"

Please notice that up until this moment no actual data materialization has happened and
hence no traversals have appeared.
All that we've done is just composed a function,
which only specifies which parts of data structures to traverse to perform a right-fold.
Only at the moment where the actual folding will happen will we actually traverse the source data.
E.g., using the "fold" function:

>abcdefLength :: Int
>abcdefLength = fold Control.Foldl.length abcdef
-}

---------------------------------------------------------------------
-- Unfoldr
---------------------------------------------------------------------

newtype Unfoldr a = Unfoldr (forall x. (a -> x -> x) -> x -> x)

{-
kan extensions?

unrunFoldr' :: (forall x. (a -> Endo x) -> Endo x) -> Unfoldr a
unrunFoldr' f = Unfoldr $ \axx -> appEndo (f $ Endo . axx)

newtype UnfoldrM m a = UnfoldrM (forall x. (a -> x -> m x) -> x -> m x)

unrunFoldrM :: Monad m => Unfoldr a -> UnfoldrM m a
unrunFoldrM (Unfoldr u) = UnfoldrM $ \ hM -> let
  h a act s = hM a s >>= act
  in u h return

unfoldlM :: Monad m => Unfoldr a -> UnfoldlM m a
unfoldlM (Unfoldr u) = prerunFoldrM u

fromList list = foldable list
-}



{-| Apply a Gonzalez fold -}
{-# INLINE fold #-}
fold :: Foldl a b -> Unfoldr a -> b
fold (Foldl h z k) = k . F.foldl' h z

{-| Apply a monadic Gonzalez fold -}
{-# INLINE foldM #-}
foldM :: Monad m => FoldlM m a b -> Unfoldr a -> m b
foldM (FoldlM h z k) (Unfoldr u) =
  z >>= u (\ a next s -> h s a >>= next) return >>= k

{-| Construct from any foldable -}
{-# INLINE foldable #-}
foldable :: Foldable f => f a -> Unfoldr a
foldable f = Unfoldr (\ h z -> P.foldr h z f)

{-| Filter the values given a predicate -}
{-# INLINE filter #-}
filter :: (a -> Bool) -> Unfoldr a -> Unfoldr a
filter test (Unfoldr u) = Unfoldr (\ h -> u (\ element s -> if test element then h element s else s))


-- | A version of the /toList/ function from < http://hackage.haskell.org/package/base-4.12.0.0/docs/src/GHC.Base.html#toList base >.
--
build :: ((a -> [a] -> [a]) -> [b] -> t) -> t
build u = u (:) []

foldr :: (a -> b -> b) -> b -> Unfoldr a -> b
foldr h z (Unfoldr u) = u h z

foldMap :: Monoid m => (a -> m) -> Unfoldr a -> m
foldMap f (Unfoldr u) = u (mappend . f) mempty

traverse_ :: Applicative f => (a -> f b) -> Unfoldr a -> f ()
traverse_ f (Unfoldr u) = u ((*>) . f) (pure ())

{-# INLINE for_ #-}
for_ :: Applicative f => Unfoldr a -> (a -> f b) -> f ()
for_ = flip traverse_

sequence_ :: Applicative f => Unfoldr (f a) -> f ()
sequence_ (Unfoldr u) = u (*>) (pure ())

asum :: Alternative f => Unfoldr (f a) -> f a
asum (Unfoldr u) = u (<|>) empty
{-# INLINE asum #-}

-- | List of elements of a structure, from left to right.
toList :: Unfoldr a -> [a]
toList t = build $ \ c n -> foldr c n t

-- | The concatenation of all the elements of a container of lists.
--concat :: Foldable t => t [a] -> [a]
concat :: Unfoldr (Unfoldr a) -> [a]
concat u = build $ \c n -> foldr (\x y -> foldr c y x) n u
--{-# INLINE concat #-}

-- | Map a function over all the elements of a container and concatenate
-- the resulting lists.
concatMap :: (a -> [b]) -> Unfoldr a -> [b]
concatMap f u = build $ \c n -> foldr (\x b -> foldr c b (foldable $ f x)) n u
{-# INLINE concatMap #-}

-- | 'and' returns the conjunction of a container of Bools.  For the
-- result to be 'True', the container must be finite; 'False', however,
-- results from a 'False' value finitely far from the left end.
and :: Unfoldr Bool -> Bool
and = getAll #. foldMap All

-- | 'or' returns the disjunction of a container of Bools.  For the
-- result to be 'False', the container must be finite; 'True', however,
-- results from a 'True' value finitely far from the left end.
or :: Unfoldr Bool -> Bool
or = getAny #. foldMap Any

-- | Determines whether any element of the structure satisfies the predicate.
any :: (a -> Bool) -> Unfoldr a -> Bool
any p = getAny #. foldMap (Any #. p)

-- | Determines whether all elements of the structure satisfy the predicate.
all :: (a -> Bool) -> Unfoldr a -> Bool
all p = getAll #. foldMap (All #. p)

-- | The 'find' function takes a predicate and a structure and returns
-- the leftmost element of the structure matching the predicate, or
-- 'Nothing' if there is no such element.
find :: (a -> Bool) -> Unfoldr a -> Maybe a
find p = getFirst . foldMap (\ x -> First (if p x then Just x else Nothing))

-- | Test whether the structure is empty.
null :: Unfoldr a -> Bool
null = foldr (\_ _ -> False) True

-- | Returns the size/length of a finite structure as an 'Int'.
length :: Unfoldr a -> Int
length = foldl' (\c _ -> c+1) 0

-- | Does the element occur in the structure?
elem :: Eq a => a -> Unfoldr a -> Bool
elem = any . (==)

notElem :: Eq a => a -> Unfoldr a -> Bool
notElem x = not . elem x

foldl :: (b -> a -> b) -> b -> Unfoldr a -> b
foldl f z t = appEndo (getDual (foldMap (Dual . Endo . flip f) t)) z

foldl' :: (b -> a -> b) -> b -> Unfoldr a -> b
foldl' f z0 xs = foldr f' id xs z0 where f' x k z = k $! f z x

{-
-- | The largest element of a non-empty structure with respect to the
-- given comparison function.

-- See Note [maximumBy/minimumBy space usage]
maximumBy :: Foldable t => (a -> a -> Ordering) -> t a -> a
maximumBy cmp = foldl1 max'
  where max' x y = case cmp x y of
                        GT -> x
                        _  -> y

-- | The least element of a non-empty structure with respect to the
-- given comparison function.
-- See Note [maximumBy/minimumBy space usage]
minimumBy :: Foldable t => (a -> a -> Ordering) -> t a -> a
minimumBy cmp = foldl1 min'
  where min' x y = case cmp x y of
                        GT -> y
                        _  -> x
-}

---------------------------------------------------------------------
-- Foldr
---------------------------------------------------------------------

data Foldr a b = forall r. Foldr (a -> r -> r) r (r -> b)

run :: a -> Foldr a b -> b
run a (Foldr h z k)    = k (h a z)

runFoldr :: Foldable f => Foldr a b -> f a -> b
runFoldr (Foldr h z k) t = k (P.foldr h z t)

postfix :: Foldable (Foldr a) => Foldr a b1 -> Foldr (Foldr a b1) b2 -> b2
postfix t s = runFoldr s (duplicate t)

prefix1 :: a -> Foldr a b -> Foldr a b
prefix1 a = extend (run a)
{-
instance Scan Foldr where
  postfix1 t a        = run1 a (duplicate t)
  interspersing a (Foldr h z k) = Foldr (maybe' (k z) k) h' Nothing' where
    h' b Nothing'  = Just' (h b z)
    h' b (Just' x) = Just' (h b (h a x))
  {-# INLINE run1 #-}
  {-# INLINE prefix1 #-}
  {-# INLINE postfix1 #-}
  {-# INLINE interspersing #-}

-- | leaky 'prefix', efficient 'postfix'
instance Folding Foldr where
  runOf l s (Foldr h z k) = k (runFoldrOf l h z s)
  prefix s            = extend (runFoldr s)
  prefixOf l s        = extend (runOf l s)
  postfixOf l t s     = runOf l s (duplicate t)
  filtering p (Foldr h z k) = Foldr k (\a r -> if p a then h a r else r) z
  {-# INLINE run #-}
  {-# INLINE runOf #-}
  {-# INLINE prefix #-}
  {-# INLINE prefixOf #-}
  {-# INLINE postfix #-}
  {-# INLINE postfixOf #-}
  {-# INLINE filtering #-}
-}

apply :: Applicative f => Foldr a b -> Foldr (f a) (f b)
apply (Foldr h z k) = Foldr (liftA2 h) (pure z) (fmap k)
{-# INLINABLE apply #-}

---------------------------------------------------------------------
-- Unfolds
---------------------------------------------------------------------

bytes :: BL.ByteString -> Unfoldr Word8
bytes b = Unfoldr (\ h z -> BL.foldr h z b)

bytes' :: BS.ByteString -> Unfoldr Word8
bytes' b = Unfoldr (\ h z -> BS.foldr h z b)

chunks :: BL.ByteString -> Unfoldr BS.ByteString
chunks b = Unfoldr (\ h z -> BL.foldrChunks h z b)

--text :: TL.Text -> Unfoldr Char
--text b = Unfoldr (\ h z -> TL.runFoldr h z b)

--text' :: TS.Text -> Unfoldr Char
--text' b = Unfoldr (\ h z -> TS.runFoldr h z b)

-- replace w/ Ix?
{-| Ascending infze stream of enums starting from the one specified -}
{-# INLINE enumsFrom #-}
enumsFrom :: (Enum a) => a -> Unfoldr a
enumsFrom from = Unfoldr $ \ h z -> let
  loop int = h int (loop (succ int))
  in loop from

{-| Enums in the specified inclusive range -}
{-# INLINE enumsInRange #-}
enumsInRange :: (Enum a, Ord a) => a -> a -> Unfoldr a
enumsInRange from to =
  Unfoldr $ \ h z ->
  let
    loop int =
      if int <= to
        then h int (loop (succ int))
        else z
    in loop from

{-| Ascending infze stream of ints starting from the one specified -}
{-# INLINE intsFrom #-}
intsFrom :: Int -> Unfoldr Int
intsFrom = enumsFrom

{-| Ints in the specified inclusive range -}
{-# INLINE intsInRange #-}
intsInRange :: Int -> Int -> Unfoldr Int
intsInRange = enumsInRange

{-| Associations of a map -}
{-# INLINE mapAssocs #-}
mapAssocs :: Map k a -> Unfoldr (k, a)
mapAssocs map =
  Unfoldr (\ h z -> Map.foldrWithKey (\ k a s -> h (k, a) s) z map)

{-| Associations of an intmap -}
{-# INLINE intMapAssocs #-}
intMapAssocs :: IntMap a -> Unfoldr (Int, a)
intMapAssocs intMap =
  Unfoldr (\ h z -> IntMap.foldrWithKey (\ k a s -> h (k, a) s) z intMap)

{-| Associations of a hash-map -}
{-# INLINE hashMapAssocs #-}
hashMapAssocs :: HashMap k a -> Unfoldr (k, a)
hashMapAssocs hashMap =
  Unfoldr (\ h z -> HashMap.foldrWithKey (\ k a s -> h (k, a) s) z hashMap)

{-| Value of a hash-map by k -}
{-# INLINE hashMapAt #-}
hashMapAt :: (Hashable k, Eq k) => HashMap k a -> k -> Unfoldr a
hashMapAt hashMap k = foldable (HashMap.lookup k hashMap)

{-| Value of a hash-map by k -}
{-# INLINE hashMapValue #-}
{-# DEPRECATED hashMapValue "Use 'hashMapAt' instead" #-}
hashMapValue :: (Hashable k, Eq k) => k -> HashMap k a -> Unfoldr a
hashMapValue k = foldable . HashMap.lookup k

{-| Values of a hash-map by their ks -}
{-# INLINE hashMapValues #-}
hashMapValues :: (Hashable k, Eq k) => HashMap k a -> Unfoldr k -> Unfoldr a
hashMapValues hashMap ks = ks >>= flip hashMapValue hashMap

{-| Bytes of a bytestring -}
{-# INLINE byteStringBytes #-}
byteStringBytes :: ByteString -> Unfoldr Word8
byteStringBytes bs = Unfoldr (\ h z -> ByteString.foldr h z bs)

{-| Bytes of a short bytestring -}
{-# INLINE shortByteStringBytes #-}
shortByteStringBytes :: ShortByteString -> Unfoldr Word8
shortByteStringBytes (ShortByteString.SBS ba#) = primArray (PrimArray ba#)

{-| Elements of a prim array -}
{-# INLINE primArray #-}
primArray :: (Prim prim) => PrimArray prim -> Unfoldr prim
primArray ba = Unfoldr $ \ f z -> foldrPrimArray f z ba

{-| Elements of a prim array coming paired with indices -}
{-# INLINE primArrayWithIndices #-}
primArrayWithIndices :: (Prim prim) => PrimArray prim -> Unfoldr (Int, prim)
primArrayWithIndices pa = Unfoldr $ \ h s -> let
  !size = sizeofPrimArray pa
  loop index = if index < size
    then h (index, indexPrimArray pa index) (loop (succ index))
    else s
  in loop 0

{-
{-| Elements of a vector -}
{-# INLINE vector #-}
vector :: GenericVector.Vector vector a => vector a -> Unfoldr a
vector vector = Unfoldr $ \ h s -> GenericVector.runFoldr h s vector

{-| Elements of a vector coming paired with indices -}
{-# INLINE vectorWithIndices #-}
vectorWithIndices :: GenericVector.Vector vector a => vector a -> Unfoldr (Int, a)
vectorWithIndices vector = Unfoldr $ \ h s -> GenericVector.irunFoldr (\ index a -> h (index, a)) s vector
-}

{-|
Binary digits of a non-negative integral number.
-}
binaryDigits :: Integral a => a -> Unfoldr a
binaryDigits = reverse . reverseBinaryDigits

{-|
Binary digits of a non-negative integral number in reverse order.
-}
reverseBinaryDigits :: Integral a => a -> Unfoldr a
reverseBinaryDigits = reverseDigits 2

{-|
Octal digits of a non-negative integral number.
-}
octalDigits :: Integral a => a -> Unfoldr a
octalDigits = reverse . reverseOctalDigits

{-|
Octal digits of a non-negative integral number in reverse order.
-}
reverseOctalDigits :: Integral a => a -> Unfoldr a
reverseOctalDigits = reverseDigits 8

{-|
Decimal digits of a non-negative integral number.
-}
decimalDigits :: Integral a => a -> Unfoldr a
decimalDigits = reverse . reverseDecimalDigits

{-|
Decimal digits of a non-negative integral number in reverse order.
More efficient than 'decimalDigits'.
-}
reverseDecimalDigits :: Integral a => a -> Unfoldr a
reverseDecimalDigits = reverseDigits 10

{-|
Hexadecimal digits of a non-negative number.
-}
hexadecimalDigits :: Integral a => a -> Unfoldr a
hexadecimalDigits = reverse . reverseHexadecimalDigits

{-|
Hexadecimal digits of a non-negative number in reverse order.
-}
reverseHexadecimalDigits :: Integral a => a -> Unfoldr a
reverseHexadecimalDigits = reverseDigits 16

{-|
Digits of a non-negative number in numeral system based on the specified radix.
The digits come in reverse order.

E.g., here's how an unfold of binary digits in proper order looks:

@
binaryDigits :: Integral a => a -> Unfoldr a
binaryDigits = 'reverse' . 'reverseDigits' 2
@
-}
reverseDigits :: Integral a => a {-^ Radix -} -> a {-^ Number -} -> Unfoldr a
reverseDigits radix x = Unfoldr $ \ h z -> let
  loop x = case divMod x radix of
    (next, digit) -> h digit (if next <= 0 then z else loop next)
  in loop x

{-|
Reverse the order.

Use with care, because it requires to allocate all elements.
-}
reverse :: Unfoldr a -> Unfoldr a
reverse (Unfoldr u) = Unfoldr $ \ h -> u (\ a f -> f . h a) id

{-|
Lift into an unfold, which produces pairs with index.
-}
zipWithIndex :: Unfoldr a -> Unfoldr (Int, a)
zipWithIndex (Unfoldr u) = Unfoldr $ \ indexedStep indexedState -> u
  (\ a nextStateByIndex index -> indexedStep (index, a) (nextStateByIndex (succ index)))
  (const indexedState)
  0

{-|
Lift into an unfold, which produces pairs with right-associative index.
-}
{-# DEPRECATED zipWithReverseIndex "This function toLists up stack. Use 'zipWithIndex' instead." #-}
zipWithReverseIndex :: Unfoldr a -> Unfoldr (Int, a)
zipWithReverseIndex (Unfoldr u) = Unfoldr $ \ h z -> snd $ u
  (\ a (index, s) -> (succ index, h (index, a) s))
  (0, z)

{-
{-|
Indices of set bits.
-}
setBitIndices :: FiniteBits a => a -> Unfoldr Int
setBitIndices a = let
  !size = fzeBitSize a
  in Unfoldr $ \ h s -> let
    loop !index = if index < size
      then if testBit a index
        then h index (loop (succ index))
        else loop (succ index)
      else s
    in loop 0

{-|
Indices of unset bits.
-}
unsetBitIndices :: FiniteBits a => a -> Unfoldr Int
unsetBitIndices a = let
  !size = fzeBitSize a
  in Unfoldr $ \ h s -> let
    loop !index = if index < size
      then if testBit a index
        then loop (succ index)
        else h index (loop (succ index))
      else s
    in loop 0
-}

take :: Int -> Unfoldr a -> Unfoldr a
take amount (Unfoldr u) = Unfoldr $ \ h z -> u
  (\ a nextState index -> if index < amount
    then h a (nextState (succ index))
    else z)
  (const z)
  0

takeWhile :: (a -> Bool) -> Unfoldr a -> Unfoldr a
takeWhile predicate (Unfoldr u) = Unfoldr $ \ h z -> u
  (\ a nextState -> if predicate a
    then h a nextState
    else z)
  z

cons :: a -> Unfoldr a -> Unfoldr a
cons a (Unfoldr u) = Unfoldr $ \ h z -> h a (u h z)

snoc :: a -> Unfoldr a -> Unfoldr a
snoc a (Unfoldr u) = Unfoldr $ \ h z -> u h (h a z)


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
-- Unfoldr instances
---------------------------------------------------------------------

deriving instance Functor Unfoldr

instance Applicative Unfoldr where
  pure x = Unfoldr (\ h -> h x)
  (<*>) = ap

instance Alternative Unfoldr where
  empty = Unfoldr (const id)
  {-# INLINE (<|>) #-}
  (<|>) (Unfoldr left) (Unfoldr right) = Unfoldr (\ h z -> left h (right h z))

instance Monad Unfoldr where
  return = pure
  {-# INLINE (>>=) #-}
  (>>=) (Unfoldr left) rightK =
    Unfoldr $ \ h -> left $ \ a -> case rightK a of Unfoldr right -> right h

instance MonadPlus Unfoldr where
  mzero = empty
  mplus = (<|>)

instance Semigroup (Unfoldr a) where
  (<>) = (<|>)

instance Monoid (Unfoldr a) where
  mempty = empty
  mappend = (<>)

instance Foldable Unfoldr where
  {-# INLINE foldMap #-}
  foldMap fn (Unfoldr u) = u (mappend . fn) mempty
  {-# INLINE foldr #-}
  foldr h s (Unfoldr u) = u h s
  foldl = F.foldl'
  {-# INLINE foldl' #-}
  foldl' leftStep s (Unfoldr u) = u rightStep id s where
    rightStep element k s = k $! leftStep s element

instance Eq a => Eq (Unfoldr a) where
  (==) left right = toList left == toList right

instance Show a => Show (Unfoldr a) where
  show = show . toList

instance IsList (Unfoldr a) where
  type Item (Unfoldr a) = a
  fromList = foldable
  toList = toList

---------------------------------------------------------------------
-- Foldr instances
---------------------------------------------------------------------

data Pair a b = Pair !a !b


instance Profunctor Foldr where
  dimap f g (Foldr h z k) = Foldr (h.f) z (g.k)
  {-# INLINE dimap #-}
  rmap g (Foldr h z k) = Foldr h z (g.k)
  {-# INLINE rmap #-}
  lmap f (Foldr h z k) = Foldr (h.f) z k
  {-# INLINE lmap #-}
  (#.) _ = unsafeCoerce
  {-# INLINE (#.) #-}
  x .# _ = unsafeCoerce x
  {-# INLINE (.#) #-}

instance Choice Foldr where
  left' (Foldr h z k) = Foldr h1 (Left z) (left' `id` k) where
    h1 (Left x) (Left y) = Left (h x y)
    h1 (Right c) _ = Right c
    h1 _ (Right c) = Right c
  {-# INLINE left' #-}

  right' (Foldr h z k) = Foldr h1 (Right z) (right' `id` k) where
    h1 (Right x) (Right y) = Right (h x y)
    h1 (Left c) _ = Left c
    h1 _ (Left c) = Left c
  {-# INLINE right' #-}

instance Functor (Foldr a) where
  fmap f (Foldr h z k) = Foldr h z (f.k)
  {-# INLINE fmap #-}

  (<$) b = \_ -> pure b
  {-# INLINE (<$) #-}

extract (Foldr _ z k) = k z
{-# INLINE extract #-}

duplicate (Foldr h z k) = Foldr h z (flip (Foldr h) k)
{-# INLINE duplicate #-}

extend f (Foldr h z k)  = Foldr h z (f . flip (Foldr h) k)
{-# INLINE extend #-}
{-
instance Comonad (Foldr a) where
  extract (Foldr k _ z) = k z
  {-# INLINE extract #-}

  duplicate (Foldr h z k) = Foldr (Foldr k h) h z
  {-# INLINE duplicate #-}

  extend f (Foldr h z k)  = Foldr (f . Foldr k h) h z
  {-# INLINE extend #-}
-}

instance Monad (Foldr a) where
  return = pure
  {-# INLINE return #-}
  --m >>= f = Foldl (flip (:)) [] (\xs -> flip foldl xs . f) <*> m
  m >>= f = Foldr (:) [] (\xs a -> flip runFoldr xs (f a)) <*> m
  {-# INLINE (>>=) #-}

  (>>) = (*>)
  {-# INLINE (>>) #-}

instance MonadZip (Foldr a) where
  mzipWith = liftA2
  {-# INLINE mzipWith #-}

instance Applicative (Foldr a) where
  pure b = Foldr (\_ () -> ()) () (\() -> b)
  {-# INLINE pure #-}

  Foldr bxx xz xf <*> Foldr byy yz ya = Foldr
    (\b ~(Pair x y) -> Pair (bxx b x) (byy b y))
    (Pair xz yz)
    (\(Pair x y) -> xf x $ ya y)
  {-# INLINE (<*>) #-}

  (<*) m = \_ -> m
  {-# INLINE (<*) #-}

  _ *> m = m
  {-# INLINE (*>) #-}

instance Apply (Foldr a) where
  (<.>) = (<*>)
  {-# INLINE (<.>) #-}

  (<.) m = \_ -> m
  {-# INLINE (<.) #-}

  _ .> m = m
  {-# INLINE (.>) #-}


instance Distributive (Foldr a) where
  distribute z = Foldr (fmap . prefix1) z (fmap extract)
  {-# INLINE distribute #-}

instance Costrong Foldr where
  unfirst = unfirstCorep
  unsecond = unsecondCorep

instance Profunctor.Corepresentable Foldr where
  type Corep Foldr = []
  cotabulate f = Foldr (:) [] (f . P.reverse)--improve?
  {-# INLINE cotabulate #-}

instance Cosieve Foldr [] where
  cosieve (Foldr h0 z0 k0) as0 = go h0 z0 k0 as0 where
    go _ z k [] = k z
    go h z k (a:as) = go h (h a z) k as
  {-# INLINE cosieve #-}

instance Closed Foldr where

  closed (Foldr h z k) = Foldr (liftA2 h) (pure z) (\f x -> k (f x))

instance MonadReader [a] (Foldr a) where

  ask = cotabulate id

  local f m = cotabulate (cosieve m . f)

instance MonadFix (Foldr a) where

  mfix = cotabulate . mfix . fmap cosieve


