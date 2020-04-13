{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}

module Data.ByteString.Optic where

{-
  , built
  , built'
  , unpacked
  , unpacked'
  , unpackedBytes
  , unpackedBytes'
  , unpackedChars
  , unpackedChars'

  , utf8
  , utf8'
-}

{-
import Data.ByteString.Optic                  as Words
utf8
utf8'
built
built'
unpacked
unpacked'
unpackedBytes
unpackedBytes'
unpackedChars
unpackedChars'
-}


{-
  ( packedBytes, unpackedBytes, bytes
  , packedChars, unpackedChars, chars
  , pattern Bytes
  , pattern Chars
  )
-}

import Data.ByteString.Lazy       as Words
import Data.ByteString.Lazy.Char8 as Char8
import Data.Int (Int64)
import Data.Word (Word8)

import Data.Profunctor.Optic
import Data.Profunctor.Optic.Import

import Data.ByteString (ByteString)

--import qualified Data.ByteString.Words.Internal
--import qualified Data.ByteString.Unsafe
{-
import Data.Word
import qualified Control.Category as C
import qualified Control.Foldl.ByteString as B
import qualified Control.Foldl.Text as T
import qualified Data.ByteString as Words'
import qualified Data.ByteString.Char8 as Char8'
import qualified Data.ByteString.Lazy as Words
import qualified Data.ByteString.Lazy.Char8 as Char8
import qualified Data.List as L
import qualified Data.Profunctor.Optic.Fold as FO
import qualified Data.Profunctor.Optic.Types as T (Fold, Fold1)

import qualified Data.Text as Text'
import qualified Data.Text.Lazy as Text
-}

import qualified Data.ByteString.Lazy as Words

import qualified Data.ByteString.Lazy.Char8 as Char8
import qualified Data.ByteString as Words'
import qualified Data.ByteString.Char8 as Char8'



import qualified Data.ByteString.Lazy       as Words
import qualified Data.ByteString.Lazy.Char8 as Char8
import qualified Data.ByteString       as Words'
import qualified Data.ByteString.Char8 as Char8'
import Data.Int
import Data.Word

{-
import qualified Data.Text.Lazy as Text
import qualified Data.Text as Text'
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.Encoding as Enc
import qualified Data.Text as Text'
import qualified Data.Text.Encoding as Enc'
import qualified Data.Text.Lazy as Text
import Data.Text.Lazy.Builder
-}

abytestring :: ACofold a Words.ByteString (Maybe (Word8, a))
abytestring = acofold Words.unfoldr

---------------------------------------------------------------------
-- ByteString
---------------------------------------------------------------------


--- 




{-
-- | Traverse each 'Word8' in a 'ByteString'.
--
-- This 'Traversal' walks the 'ByteString' in a tree-like fashion enable zippers
-- to seek to locations in logarithmic time and accelerating many monoidal
-- queries, but up to associativity (and constant factors) it is equivalent to
-- the much slower:
--
-- @
-- 'bytes' ≡ 'unpackedBytes' '%' 'traversed'
-- @
--
-- >>> anyOf bytes (== 0x80) (Char8.pack "hello")
-- False
--
-- Note that when just using this as a 'Setter', @'sets' 'Data.ByteString.map'@
-- can be more efficient.
bytes :: IxTraversal' Int64 ByteString Word8
bytes = traversedStrictTree
{-# INLINE bytes #-}

-- | TODO: Document
--
packing :: (Word8 -> a) -> (ByteString -> b -> t) -> Rescan Word8 t a b
packing sa sbt = moore sa $ sbt . Words'.pack . F.toList
{-# INLINEABLE packing #-}

-- | TODO: Document
--
chunking :: (ByteString -> a) -> (Words.ByteString -> b -> t) -> Rescan ByteString t a b
chunking sa sbt = moore sa $ sbt . Words.fromChunks . F.toList
{-# INLINEABLE chunking #-}




aggregateWith :: Functor f => (f Float -> Float) -> AList1' [] Features Float
aggregateWith aggregator p = Costar (fmap (cosieve p) . L.transpose)

-- >>> ["foo", "foobar"] & partitioned (<) /~ 8
partitioned :: (Word8 -> Word8 -> Bool) -> Rescan Words'.ByteString (Words.ByteString,Words.ByteString) Words'.ByteString Word8
partitioned f = moore id $ \as ref -> bimap id id $ --TODO clean up
  ( Words.filter (\x -> False == f ref x) (Words.fromChunks $ F.toList as)
  , Words.filter (\x -> True == f ref x) (Words.fromChunks $ F.toList as)
  )

partitionedWith :: (Word8 -> Word8 -> Bool) -> Rescan Words'.ByteString (Words.ByteString,Words.ByteString) Word8 Word8
partitionedWith f = chunked undefined  $ \bs w -> Words.partition (f w) bs
{-# INLINE partitionedWith #-}

{-
λ> foldsRepFoldl (partitioned' (\_ _ -> True)) F.mconcat ["foo","bar"] 
([],["foo","bar"])
λ> foldsRepFoldl (partitioned' (\_ _ -> False)) F.mconcat ["foo","bar"]
(["foo","bar"],[])
λ> foldsRepFoldl (partitioned' (>=)) F.sum [1..10] ["foo","foo"]

-}

ge :: Ord a => List a ([a],[a]) a a
ge = partitioned (>=)

partitioned' :: (a -> a -> Bool) -> Rescan a ([a],[a]) a a
partitioned' f = listed id $ \xs ref ->
  ( Ls.filter (\x -> False == f ref x) (F.toList xs)
  , Ls.filter (\x -> True == f ref x) (F.toList xs)
  )

--concatenated :: Rescan' Words.ByteString Words.ByteString
--concatenated = list id $ \s _ -> Words.concat s
{-
partitioned :: (Word8 -> Word8 -> Bool) -> Rescan Word8 (Words.ByteString,Words.ByteString) Word8 Word8
partitioned f = moore id $ \as ref -> bimap undefined undefined $
  ( Words'.filter (\x -> False == f ref x) (Words.fromChunks $ F.toList as)
  , Words'.filter (\x -> True == f ref x) (Words.fromChunks $ F.toList as)
  )

partitioned :: (Word8 -> Bool) -> Rescan Words'.ByteString (Words.ByteString,Words.ByteString) Words'.ByteString  Words'.ByteString
partitioned f = chunked id  $ \bs _ -> Words.partition f bs
{-# INLINE partitioned #-}

{-# INLINE partitioned #-}

partition :: (a -> Bool) -> Map k a -> (Map k a, Map k a) 

padded :: a -> Rescan [a] [[a]] Int Int
padded a = list L.length $ \as n -> fmap (\s -> L.take n $ s <> L.repeat a) as
-- | TODO: Document
--
{-# INLINE partitioned #-}
-}



-- | TODO: Document
--
-- >>> ["foo", "foobar"] & padded 42 /~ 8
-- ["foo*****","foobar**"]
-- >>> ["foo", "foobar"] & padded 42 //~ maximum
-- ["foo***","foobar"]
--
padded :: Word8 -> Rescan Words.ByteString [Words.ByteString] Int64 Int64
padded w = listed Words.length $ \bs n -> fmap (\s -> Words.take n $ s `Words.append` Words.repeat w) bs
{-# INLINE padded #-}

-- | TODO: Document
--
padded' :: Word8 -> Rescan ByteString Words.ByteString Int Int
padded' w = moore Words'.length $ \bs n -> Words.fromChunks $
  fmap (\s -> Words'.take n $ s `Words'.append` Words'.replicate n w) $ F.toList bs
{-# INLINE padded' #-}


-- | Apply a strict left 'Fold' to a lazy bytestring
chunksl :: ARescan Words'.ByteString r a b -> (x -> a -> x) -> x -> (x -> b) -> Words.ByteString -> r
chunksl o h z k s = flip B.fold s . o $ M.Fold h z k
{-# INLINE chunksl #-}

-- >>> ["a", "hello", "yo"] & padLength //~ maximum
-- ["a    ","hello","yo   "]
-- >>> ["a", "hello", "yo"] & padLength //~ minimum
-- ["a","h","y"]

--TODO how is /~ using the feedback mechanism exactly
-- >>> ["a", "hello", "yo"] & pad /~ 6
-- ["a     ","hello ","yo    "]
-- >>> ["a", "hello", "yo"] & pad /~ 2
-- ["a ","he","yo"]
-- >>> ["a", "hello", "yo"] & pad //~ maximum . fmap length
-- ["a    ","hello","yo   "]
-- >>> ["a", "hello", "yo"] & pad //~ minimum . fmap length
-- ["a","h","y"]


pad :: Rescan String [String] String Int
pad = listing id padder
  where
    padder :: [String] -> Int -> [String]
    padder xs n = fmap (\s -> Ls.take n $ s <> Ls.repeat ' ') xs

padLength :: Rescan String [String] Int Int
padLength = listing Ls.length padder
  where
    padder :: [String] -> Int -> [String]
    padder xs n = fmap (\s -> Ls.take n $ s <> Ls.repeat ' ') xs

---------------------------------------------------------------------
-- Char8
---------------------------------------------------------------------


-- | TODO: Document
--
padded :: Char -> Rescan Char8.ByteString [Char8.ByteString] Int64 Int64
padded w = listed Char8.length $ \as n -> fmap (\s -> Char8.take n $ s `Char8.append` Char8.repeat w) as
{-# INLINE padded #-}

-- | TODO: Document
--
paddedChars' :: Char -> Rescan ByteString Char8.ByteString Int Int
paddedChars' w = moore Char8'.length $ \bs n -> Char8.fromChunks $
  fmap (\s -> Char8'.take n $ s `Char8'.append` Char8'.replicate n w) $ F.toList bs
{-# INLINE paddedChars' #-}

-}



{-
singleton :: Word8 -> ByteString
unsnoc :: ByteString -> Maybe (ByteString, Word8)
uncons :: ByteString -> Maybe (Word8, ByteString)
map :: (Word8 -> Word8) -> ByteString -> ByteString
reverse :: ByteString -> ByteString

-- | /O(log n)/. Affine traversal into the value at a key of a 'Map.Map'.
--
at :: Ord k => k -> Traversal0' (Map.Map k a) a
at k = traversal0' (Map.lookup k) (flip $ Map.insert k)
{-# INLINE at #-}

-- | /O(log n)/. Affine traversal into the value at a key of a 'Map.Map''.
--
at' :: Ord k => k -> Traversal0' (Map'.Map k a) a
at' k = traversal0' (Map'.lookup k) (flip $ Map'.insert k)
{-# INLINE at' #-}
-}

-- see also http://hackage.haskell.org/package/lens-4.18.1/docs/src/Control.Lens.Internal.ByteString.html



{-
-- | Traverse the individual bytes in a 'ByteString'.
--
-- This 'Traversal' walks each strict 'ByteString' chunk in a tree-like fashion
-- enable zippers to seek to locations more quickly and accelerate many monoidal
-- queries, but up to associativity (and constant factors) it is equivalent to
-- the much slower:
--
-- @
-- 'bytes' ≡ 'unpackedBytes' '.' 'traversed'
-- @
--
-- >>> anyOf bytes (== 0x80) (Char8.pack "hello")
-- False
--
-- Note that when just using this as a 'Setter', @'sets'
-- 'Data.ByteString.Lazy.map'@ can be more efficient.
bytes :: Ixtraversal' Int64 ByteString Word8
bytes = traversedLazy
{-# INLINE bytes #-}

-- | Traverse the individual bytes in a 'ByteString' as characters.
--
-- When writing back to the 'ByteString' it is assumed that every 'Char' lies
-- between @'\x00'@ and @'\xff'@.
--
-- This 'Traversal' walks each strict 'ByteString' chunk in a tree-like fashion
-- enable zippers to seek to locations more quickly and accelerate many monoidal
-- queries, but up to associativity (and constant factors) it is equivalent to:
--
-- @
-- 'chars' = 'unpackedChars' '%' 'traversed'
-- @
--
-- >>> anyOf chars (== 'h') $ Char8.pack "hello"
-- True
chars :: Ixtraversal' Int64 ByteString Char
chars = traversedLazy8
{-# INLINE chars #-}
-}

{-
-- | Traverse the individual bytes in a 'ByteString' as characters.
--
-- When writing back to the 'ByteString' it is assumed that every 'Char' lies
-- between @'\x00'@ and @'\xff'@.
--
-- This 'Traversal' walks the 'ByteString' in a tree-like fashion enable zippers
-- to seek to locations in logarithmic time and accelerating many monoidal
-- queries, but up to associativity (and constant factors) it is equivalent to
-- the much slower:
--
-- @
-- 'chars' = 'unpackedChars' '%' 'traversed'
-- @
--
-- >>> anyOf chars (== 'h') $ Char8.pack "hello"
-- True
chars' :: IxTraversal' Int64 ByteString Char
chars' = traversedStrictTree8
{-# INLINE chars' #-}
-}



{-

-- $setup
-- >>> import Data.Profunctor.Optic


packing :: (Word8 -> a) -> (BL.ByteString -> b -> t) -> List Word8 t a b
packing sa sbt = list sa $ sbt . BL.pack . F.toList
{-# INLINEABLE packing #-}

-- | TODO: Document
--
-- @since 0.0.3
packing' :: (Word8 -> a) -> (BS.ByteString -> b -> t) -> List Word8 t a b
packing' sa sbt = list sa $ sbt . BS.pack . F.toList
{-# INLINEABLE packing' #-}

chunking :: (BS.ByteString -> a) -> (BL.ByteString -> b -> t) -> List BS.ByteString t a b
chunking sa sbt = list sa $ sbt . BL.fromChunks . F.toList
{-# INLINEABLE chunking #-}

---------------------------------------------------------------------
-- Sequential optics
---------------------------------------------------------------------

-- | TODO: Document
--
-- @since 0.0.3
packed :: IsSequence s => Lens s t a b -> List (Element s) t a b
packed o = withLens o $ \sa sbt -> packing (sa . MT.opoint) sbt

-- | TODO: Document
--
-- @since 0.0.3
packed' :: LazySequence l s => Lens l t a b -> List s t a b
packed' o = withLens o $ \la lbt -> chunking (la . MS.fromStrict) lbt
{-# INLINE packed' #-}

-- | TODO: Document
--
-- >>> "foobar" & taken id /~ 3 :: String
-- "foo"
-- >>> listl (taken $ const 3) "foobar" :: String
-- "foo"
--
-- @since 0.0.3
taken :: IsSequence s => (b -> Index s) -> List (Element s) s (Element s) b
taken f = packing id $ \s b -> MS.take (f b) s

-- | TODO: Document
--
-- >>> CL.unpack $ listl (taken' $ const 9) $ fmap C.pack ["foo","bar","baz","bip"]
-- "foobarbaz"
-- >>> CL.unpack $ fmap C.pack ["foo","bar","baz","bip"] & taken' fromIntegral /~ 9
-- "foobarbaz"
-- >>> CL.unpack $ fmap C.pack ["foo","bar","baz","bip"] & taken' fromIntegral //~ (3 *) . head 
-- "foobarbaz"
-- >>> fmap CL.unpack $ (fmap.fmap) C.pack [(0,"zero"),(1,"one"),(2,"two")] & maximizedDef (0,mempty) second . taken' fromIntegral //~ maximum
-- (2,"zero")
--
-- @since 0.0.3
taken' :: LazySequence l s => (b -> Index l) -> List s l (Index s) b
taken' f = chunking MS.lengthIndex $ \s b -> MS.take (f b) s
{-# INLINE taken' #-}

-- | TODO: Document
--
-- @since 0.0.3
padded :: IsSequence s => Element s -> List s [s] (Index s) (Index s)
padded w = listing MS.lengthIndex $ \s b -> fmap (\x -> MS.take b (x <> MS.replicate b w)) s
{-# INLINE padded #-}

-- | TODO: Document
--
-- >>> ["foo","barbaz","bippy"] & padded ' ' /~ 4
-- ["foo ","barb","bipp"]
-- >>> ["foo","barbaz","bippy"] & padded ' ' //~ maximum
-- ["foo   ","barbaz","bippy "]
--
-- @since 0.0.3
padded' :: LazySequence l s => Element s -> List s l (Index s) (Index s)
padded' w = list MS.lengthIndex $ \bs n -> MS.fromChunks $
  fmap (\s -> MS.take n $ s <> MS.replicate n w) $ F.toList bs
{-# INLINE padded' #-}

-- | TODO: Document
--
-- >>> listl (takenWhile id $ const . isAlpha) "foo2bar" :: String
-- "foo"
-- >>> [(1,"one"),(0,"zero"),(2,"two")] & minimizedDef (0,[]) second . takenWhile id (/=) /~ "two" :: (Int,[String])
-- (0,["one","zero"])
-- >>> [(1,"one"),(0,"zero"),(2,"two")] & maximizedDef (0,[]) second . takenWhile id (/=) //~ maximum :: (Int,[String])
-- (2,["one"])
--
-- @since 0.0.3
takenWhile :: IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> List (Element s) s a b
takenWhile sa sbt = packing sa $ \s b -> MS.takeWhile (flip sbt b) s
{-# INLINE takenWhile #-}

-- | TODO: Document
--
-- >>> CL.unpack $ listl (takenWhile' id $ const . isAlpha . chr . fromIntegral) $ fmap C.pack ["foo","bar","2baz"]
-- "foobar"
--
-- @since 0.0.3
takenWhile' :: LazySequence l s => (s -> a) -> (Element l -> b -> Bool) -> List s l a b
takenWhile' sa sbt = chunking sa $ \s b -> MS.takeWhile (flip sbt b) s
{-# INLINE takenWhile' #-}

-- | TODO: Document
--
-- @since 0.0.3
droppedWhile :: IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> List (Element s) s a b
droppedWhile sa sbt = packing sa $ \s b -> MS.dropWhile (flip sbt b) s
{-# INLINE droppedWhile #-}

-- | TODO: Document
--
-- @since 0.0.3
droppedWhile' :: LazySequence l s => (s -> a) -> (Element l -> b -> Bool) -> List s l a b
droppedWhile' sa sbt = chunking sa $ \s b -> MS.dropWhile (flip sbt b) s
{-# INLINE droppedWhile' #-}

-- | Filter a sequence of elements using a List machine. 
--
-- >>> "foobar" & filteredBy id (==) /~ 'b' :: String
-- "b"
-- >>> "foobar" & filteredBy id (\c i -> ord c /= i) /~ 111 :: String
-- "fbar"
-- >>> "fizbuz" & filteredBy ord (\c i -> ord c /= i) //~ maximum :: String
-- "fibu"
-- >>> ["bob","oob","baz"] & filteredBy head (==) //~ reverse :: [String]
-- ["bob"]
-- >>> ["bob","bob","baz"] & filteredBy head (==) //~ reverse :: [String]
-- []
--
-- Take all strings @s@ that pass the following test:
--
-- * @s@ must not include a /z/
--
-- * @s@ must be equal to the concatenation of the first characters in each string in the remaining list
--
-- >>> ["z","obb","bob","baz"] & (filteredBy head (==) . filteredBy id (/=)) /~ 'z' :: [String]
-- ["obb"]
--
-- @since 0.0.3
filteredBy :: IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> List (Element s) s a b
filteredBy sa sbt = packing sa $ \s b -> MS.filter (flip sbt b) s
{-# INLINE filteredBy #-}

-- | Filter a chunked sequence of elements using a List machine. 
--
-- >>> CL.unpack $ fmap C.pack ["foo","bar"] & filteredBy' (ord . C.head) (/=) /~ 111 
-- "fbar"
-- >>> CL.unpack $ fmap C.pack ["f","i","z","b","u","z"] & filteredBy' (ord . C.head) (\e b -> fromIntegral e /= b) //~ maximum
-- "fibu"
-- >>> CL.unpack $ fmap C.pack ["fizbuz"] & filteredBy' (ord . C.head) (\e b -> fromIntegral e /= b) //~ maximum 
-- "izbuz"
--
-- @since 0.0.3
filteredBy' :: LazySequence l s => (s -> a) -> (Element l -> b -> Bool) -> List s l a b
filteredBy' sa sbt = chunking sa $ \s b -> MS.filter (flip sbt b) s
{-# INLINE filteredBy' #-}

-- | TODO: Document
--
-- @since 0.0.3
filteredBy1 :: IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> List1 (Element s) s a b
filteredBy1 sa sbt = packing1 sa $ \s b -> NN.nfilter (flip sbt b) s
{-# INLINE filteredBy1 #-}

-- | TODO: Document
--
-- @since 0.0.3
broken :: IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> List (Element s) (s, s) a b
broken sa sbt = packing sa $ \s b -> MS.break (flip sbt b) s
{-# INLINE broken #-}

-- | TODO: Document
--
-- @since 0.0.3
spanned :: IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> List (Element s) (s, s) a b
spanned sa sbt = packing sa $ \s b -> MS.span (flip sbt b) s
{-# INLINE spanned #-}

-- | TODO: Document
--
-- >>> listl (partitioned id $ const . odd) [1..10] :: ([Int],[Int])
-- ([1,3,5,7,9],[2,4,6,8,10])
-- >>> [1..10] & partitioned id (>=) //~ (!! 5) :: ([Int],[Int])
-- ([6,7,8,9,10],[1,2,3,4,5])
-- >>> [1..10] & partitioned id (<) /~ 6 :: ([Int],[Int])
-- ([1,2,3,4,5],[6,7,8,9,10])
-- >>> [1..10] & partitioned id (==) /~ 6 :: (B.ByteString, B.ByteString)
-- ("\ACK","\SOH\STX\ETX\EOT\ENQ\a\b\t\n")
--
-- @since 0.0.3
partitioned :: IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> List (Element s) (s, s) a b
partitioned sa sbt = packing sa $ \s b -> MS.partition (flip sbt b) s
{-# INLINE partitioned #-}

-- | TODO: Document
--
-- @since 0.0.3
partitioned' :: LazySequence l s => (s -> a) -> (Element l -> b -> Bool) -> List s (l, l) a b
partitioned' sa sbt = chunking sa $ \s b -> MS.partition (flip sbt b) s
{-# INLINE partitioned' #-}

-- | TODO: Document
--
-- >>> "Mississippi" & groupedAllOn id (==) /~ 'i' :: [String]
-- ["Msssspp","iiii"]
-- >>> listl (minimizedDef (' ',0) first . groupedAllOn id (const . (== 'i'))) [('H',1),('a',2),('w',3),('a',4),('i',5),('i',6)] :: ([String],Int)
-- (["Hawa","ii"],1)
--
-- @since 0.0.3
groupedAllOn :: IsSequence s => Eq r => (Element s -> a) -> (Element s -> b -> r) -> List (Element s) [s] a b
groupedAllOn sa sbt = packing sa $ \s b -> MS.groupAllOn (flip sbt b) s
{-# INLINE groupedAllOn #-}

-- | TODO: Document
--
-- @since 0.0.3
splitWhen :: IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> List (Element s) [s] a b 
splitWhen sa sbt = packing sa $ \s b -> MS.splitWhen (flip sbt b) s 
{-# INLINE splitWhen #-}

-- | TODO: Document
--
-- @since 0.0.3
splitFirst :: IsSequence s => (Element s -> a) -> ((Element s, s) -> b -> t) -> List1 (Element s) t a b 
splitFirst sa sbt = packing1 sa $ sbt . NN.splitFirst
{-# INLINE splitFirst #-}








-- | TODO: Document
--
-- >>> ["foo","barbaz","bippy"] & padded (c2w ' ') /~ 4
-- ["foo ","barb","bipp"]
-- >>> ["foo","barbaz","bippy"] & padded (c2w ' ') //~ maximum
-- ["foo   ","barbaz","bippy "]
--
-- @since 0.0.3
padded :: Word8 -> List BL.ByteString (Unfold BL.ByteString) Int64 Int64
padded w = unfolding BL.length $ \as n -> fmap (\s -> BL.take n $ s `BL.append` BL.repeat w) as
{-# INLINE padded #-}

-- | TODO: Document
--
-- >>> "foobar" & taken id B.char8 id /~ 3
-- "foo"
-- >>> lists (taken id B.char8 $ const 3) "foobar"
-- "foo"
--
-- @since 0.0.3
taken :: (s -> a) -> (s -> B.Builder) -> (b -> Int64) -> List s BL.ByteString a b 
taken sa bld g = building sa bld $ \s b -> BL.take (g b) s

-- | TODO: Document
--
-- >>> lists (takenWhile id B.char8 $ const . isAlpha . w2c) "foo2bar"
-- "foo"
-- >>> P.zip [0..] "foobar" & maximizedDef (0,' ') second . takenWhile ord B.char8 (/=) /~ c2w 'b' 
-- (5,"foo")
--
-- @since 0.0.3
takenWhile :: (s -> a) -> (s -> B.Builder) -> (Word8 -> b -> Bool) -> List s BL.ByteString a b
takenWhile sa bld sbt = building sa bld $ \s b -> BL.takeWhile (flip sbt b) s
{-# INLINE takenWhile #-}

-- | TODO: Document
--
-- @since 0.0.3
droppedWhile :: (s -> a) -> (s -> B.Builder) -> (Word8 -> b -> Bool) -> List s BL.ByteString a b
droppedWhile sa bld sbt = building sa bld $ \s b -> BL.dropWhile (flip sbt b) s
{-# INLINE droppedWhile #-}

-- | Filter a sequence of elements using a Rescan machine. 
--
-- >>> "foobar" & filteredOn id (==) /~ 'b'
-- "b"
-- >>> L.chars "foobar" & filteredOn id (/=) /~ 'o'
-- "fbar"
-- >>> L.chars "fizbuz" & filteredOn id (/=) //~ F.maximum
-- "fibu"
--
-- >>> l = unfoldl (fmap L.chars ["bob","oob","baz"]) :: Unfold (Unfold Char)
-- >>> safeHead = maybe '_' id . L.head
-- >>> l & filteredOn safeHead (==) //~ L.reverse
-- ["bob"]
--
-- Somewhat arbitrary demonstration of nesting: take all strings /s/ that pass the following test
--
-- * @s@ must not include a /z/
--
-- * @s@ must be equal to the concatenation of the first characters in each string in the remaining list
--
-- >>> L.chars "z" `L.cons` l & (filteredOn safeHead (==) . filteredOn id (/=)) /~ 'z'
-- ["bob"]
--
-- @since 0.0.3
filteredOn :: (s -> a) -> (s -> b -> Bool) -> List s (Unfold s) a b
filteredOn sa sbt = unfolding sa $ \s b -> L.filter (flip sbt b) s
{-# INLINE filteredOn #-}

-- | TODO: Document
--
-- @since 0.0.3
broken :: (s -> a) -> (s -> B.Builder) -> (Word8 -> b -> Bool) -> List s (BL.ByteString, BL.ByteString) a b
broken sa bld sbt = building sa bld $ \s b -> BL.break (flip sbt b) s
{-# INLINE broken #-}

-- | TODO: Document
--
-- @since 0.0.3
spanned :: (s -> a) -> (s -> B.Builder) -> (Word8 -> b -> Bool) -> List s (BL.ByteString, BL.ByteString) a b
spanned sa bld sbt = building sa bld $ \s b -> BL.span (flip sbt b) s
{-# INLINE spanned #-}

-- | TODO: Document
--
-- >>> "foobar" & partitioned id B.char8 (/=) /~ 111
-- ("fbar","oo")
-- >>> lists (partitioned id B.intDec $ const . odd) [0..9]
-- ("13579","02468")
--
-- @since 0.0.3
partitioned :: (s -> a) -> (s -> B.Builder) -> (Word8 -> b -> Bool) -> List s (BL.ByteString, BL.ByteString) a b
partitioned sa bld sbt = building sa bld $ \s b -> BL.partition (flip sbt b) s
{-# INLINE partitioned #-}
-}
