{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}

-- | Left and right carriers are characterized by their representation
-- functors ('Rep' and 'Corep'). 'Iso' sits at the top where both
-- are trivial ('Identity'). 'Adjoint' sits at the bottom where they
-- form a full adjunction (@'Corep' p ⊣ 'Rep' p@). A left-indexed
-- ('Ix') optic threads an index through the left adjoint functor
-- @(,) k@, while a right-indexed ('Cx') optic threads a coindex
-- through the right adjoint functor @(->) k@.
--
-- Profunctor optics for 'ByteString'.
--
-- @
-- \-\- convert strict ByteString to ShortByteString
-- view short myBS
--
-- \-\- round-trip
-- review short (view short myBS) == myBS
-- @
module Data.ByteString.Optic (
    -- * Optics
    -- ** Iso
    short,
    lazy,
    packed,
    reversed,
    lined,
    worded,
    splitOn,

    -- ** Prism
    consed,
    snoced,
    prefixed,
    suffixed,

    -- ** Traversal0
    at,
    found,

    -- ** Traversal
    bytes,

    -- ** Fold0
    headed,
    lasted,
    foundIndex,
    elemIndexed,

    -- ** Fold
    folded,

    -- ** Setter
    mapped,
    sorted,

    -- ** Adjoint
    filtered,

    -- * Indexed Optics
    -- ** Ixtraversal
    ixat,
    ixtraversed,

    -- ** Ixfold
    ixfolded,

    -- ** Ixsetter
    ixmapped,

    -- * Coindexed Optics
    -- ** Cxtraversal
    cxtraversed,

    -- ** Cxfold
    cxfolded,

    -- ** Cxsetter
    cxmapped,
    cxfiltered,

    -- * Dual Optics
    -- ** Cotraversal
    zippedBS,

    -- * Operators
    -- ** Sort-based
    sortingBS,
) where

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as B8
import qualified Data.ByteString.Lazy as BL
import Data.Map.Optic (Map)
import Data.ByteString.Short (ShortByteString)
import qualified Data.ByteString.Short as SBS
import Data.Monoid (Sum(..))
import Data.Profunctor.Optic hiding (folded, prefixed, filtered)
import Data.Word (Word8)

-- | Iso between strict 'ByteString' and 'ShortByteString'.
--
-- 'ShortByteString' is backed by unpinned @ByteArray#@ — better
-- for GC when storing many small strings.
short :: Iso' ByteString ShortByteString
short = iso SBS.toShort SBS.fromShort

-- | Iso between strict and lazy 'ByteString'.
lazy :: Iso' ByteString BL.ByteString
lazy = iso BL.fromStrict BL.toStrict

-- | Iso between @[Word8]@ and strict 'ByteString'.
packed :: Iso' [Word8] ByteString
packed = iso BS.pack BS.unpack

-- | Split on newlines.
--
-- >>> view lined "hello\nworld"
-- ["hello","world"]
-- >>> review lined ["hello","world"]
-- "hello\nworld"
lined :: Iso' ByteString [ByteString]
lined = iso B8.lines (B8.intercalate "\n")

-- | Split on spaces.
--
-- >>> view worded "hello world"
-- ["hello","world"]
-- >>> review worded ["hello","world"]
-- "hello world"
worded :: Iso' ByteString [ByteString]
worded = iso B8.words (B8.intercalate " ")

-- | Split on an arbitrary delimiter.
--
-- >>> view (splitOn ",") "a,b,c"
-- ["a","b","c"]
-- >>> review (splitOn ",") ["a","b","c"]
-- "a,b,c"
splitOn :: ByteString -> Iso' ByteString [ByteString]
splitOn delim = iso (split delim) (BS.intercalate delim)
  where
    split d s
        | BS.null s = []
        | otherwise = case BS.breakSubstring d s of
            (pre, rest)
                | BS.null rest -> [pre]
                | otherwise -> pre : split d (BS.drop (BS.length d) rest)

-- | 'ByteString' is reversible.
reversed :: Iso' ByteString ByteString
reversed = iso BS.reverse BS.reverse

---------------------------------------------------------------------
-- Prisms
---------------------------------------------------------------------

-- | Prism for cons-cell view of 'ByteString'.
consed :: Prism' ByteString (Word8, ByteString)
consed = prism' BS.uncons (uncurry BS.cons)

-- | Prism for snoc-cell view of 'ByteString'.
snoced :: Prism' ByteString (ByteString, Word8)
snoced = prism' BS.unsnoc (uncurry BS.snoc)

-- | Prism matching a prefix.
prefixed :: ByteString -> Prism' ByteString ByteString
prefixed p = prism' (BS.stripPrefix p) (p <>)

-- | Prism matching a suffix.
suffixed :: ByteString -> Prism' ByteString ByteString
suffixed s = prism' (BS.stripSuffix s) (<> s)

---------------------------------------------------------------------
-- Traversal0, Fold0
---------------------------------------------------------------------

-- | /O(1)/. Affine traversal into the byte at a position.
at :: Int -> Traversal0' ByteString Word8
at i = traversal0' sa sbt
  where
    sa bs = if i >= 0 && i < BS.length bs then Just (BS.index bs i) else Nothing
    sbt bs w = let (l, r) = BS.splitAt i bs
               in  if BS.null r then bs else l <> BS.singleton w <> BS.tail r

-- | Affine traversal into the first byte matching a predicate.
found :: (Word8 -> Bool) -> Traversal0' ByteString Word8
found p = traversal0' (BS.find p) (\bs w -> BS.map (\x -> if p x then w else x) bs)

-- | First byte, if non-empty.
headed :: Fold0 ByteString Word8
headed = fold0 (\bs -> if BS.null bs then Nothing else Just (BS.head bs))

-- | Last byte, if non-empty.
lasted :: Fold0 ByteString Word8
lasted = fold0 (\bs -> if BS.null bs then Nothing else Just (BS.last bs))

-- | Index of the first byte matching a predicate.
foundIndex :: (Word8 -> Bool) -> Fold0 ByteString (Sum Int)
foundIndex p = fold0 (fmap Sum . BS.findIndex p)

-- | Index of the first occurrence of a byte.
elemIndexed :: Word8 -> Fold0 ByteString (Sum Int)
elemIndexed w = fold0 (fmap Sum . BS.elemIndex w)

---------------------------------------------------------------------
-- Indexed optics
---------------------------------------------------------------------

-- | Indexed affine traversal at the incoming index.
ixat :: Ixtraversal0' (Sum Int) ByteString Word8
ixat = ixtraversalVl0 $ \point f k bs ->
  let i = getSum k
  in  if i >= 0 && i < BS.length bs
      then fmap (\w -> let (l, r) = BS.splitAt i bs
                       in  l <> BS.singleton w <> BS.tail r) (f k (BS.index bs i))
      else point bs

-- | Indexed traversal over bytes with positional index.
ixtraversed :: Ixtraversal (Sum Int) ByteString ByteString Word8 Word8
ixtraversed = ixtraversalVl $ \f k bs ->
  BS.pack <$> traverse (\(i, w) -> f (k <> Sum i) w) (zip [0..] (BS.unpack bs))

-- | Indexed fold over bytes with positional index.
ixfolded :: Ixfold (Sum Int) ByteString Word8
ixfolded = ixfoldVl $ \f k bs ->
  traverse (\(i, w) -> f (k <> Sum i) w) (zip [0..] (BS.unpack bs))

-- | Indexed setter over bytes with positional index.
ixmapped :: Ixsetter (Sum Int) ByteString ByteString Word8 Word8
ixmapped = ixsetter $ \f k bs ->
  BS.pack $ zipWith (\i w -> f (k <> Sum i) w) [0..] (BS.unpack bs)

---------------------------------------------------------------------
-- Setters / Adjoints
---------------------------------------------------------------------

-- | Sort bytes in ascending order.
sorted :: Setter' ByteString ByteString
sorted = setter $ \f -> f . BS.sort

-- | Filter bytes by predicate.
filtered :: Adjoint ByteString ByteString Word8 Bool
filtered = adjoint BS.filter

-- | Traversal over individual bytes.
--
-- @bytes = re packed . traversed@
--
-- >>> over bytes (+1) "abc"
-- "bcd"
bytes :: Traversal' ByteString Word8
bytes = re packed . traversed

-- | Fold over individual bytes.
--
folded :: Fold ByteString Word8
folded = fold_ BS.unpack
{-# INLINE folded #-}

-- | Setter over individual bytes.
--
-- @over mapped f = BS.map f@
mapped :: Setter' ByteString Word8
mapped = setter BS.map
{-# INLINE mapped #-}

---------------------------------------------------------------------
-- Coindexed optics
---------------------------------------------------------------------

-- | Coindexed traversal over bytes with positional coindex.
cxtraversed :: Cxtraversal (Sum Int) ByteString ByteString Word8 Word8
cxtraversed = cxtraversalVl $ \fakb k fs ->
  let bs0 = copure fs
  in  BS.pack $ zipWith (\i w -> fakb (fmap (\bs -> if i < BS.length bs then BS.index bs i else w) fs) (k <> Sum i))
        [0..] (BS.unpack bs0)
{-# INLINE cxtraversed #-}

-- | Coindexed fold over bytes with positional coindex.
cxfolded :: Cxfold (Sum Int) ByteString Word8
cxfolded = cxfoldVl $ \fakb k fs ->
  let bs0 = copure fs
  in  BS.pack $ zipWith (\i w -> fakb (fmap (\bs -> if i < BS.length bs then BS.index bs i else w) fs) (k <> Sum i))
        [0..] (BS.unpack bs0)
{-# INLINE cxfolded #-}

-- | Coindexed setter over bytes with positional coindex.
cxmapped :: Cxsetter (Sum Int) ByteString ByteString Word8 Word8
cxmapped = cxsetter $ \f k bs ->
  BS.pack $ zipWith (\i w -> f (k <> Sum i) w) [0..] (BS.unpack bs)
{-# INLINE cxmapped #-}

-- | Coindexed filter over bytes with positional coindex.
cxfiltered :: Cxsetter (Sum Int) ByteString ByteString Word8 Bool
cxfiltered = cxsetter $ \f k bs ->
  BS.pack [w | (i, w) <- zip [0..] (BS.unpack bs), f (k <> Sum i) w]
{-# INLINE cxfiltered #-}

---------------------------------------------------------------------
-- Dual optics
---------------------------------------------------------------------

-- | Pointwise 'Cotraversal' over bytes of two 'ByteString' values.
--
-- @'BS.packZipWith' :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString -> ByteString@
--
-- Truncates to the shorter bytestring, like 'ZipList'.
--
zippedBS :: Cotraversal ByteString ByteString Word8 Word8
zippedBS = cotraversalVl $ \fab fs ->
  let t = copure fs
      n = BS.length t
  in  BS.pack [ fab (fmap (\t' -> BS.index t' i) fs) | i <- [0..n-1] ]
{-# INLINE zippedBS #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Sort a 'ByteString' by a key on each byte.
--
sortingBS :: Ord k => (Word8 -> k) -> ByteString -> Map k ByteString
sortingBS = sortingRep BS.length BS.index BS.pack
{-# INLINE sortingBS #-}
