{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}

-- | Profunctor optics for lazy 'ByteString'.
--
-- See "Data.ByteString.Optic" for the strict variant.
module Data.ByteString.Lazy.Optic (
    -- * Optics
    -- ** Iso
    strict,
    packed,
    reversed,
    chunked,
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
    zipped,

    -- * Operators
    -- ** Sort-based
    sortingBS,
) where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as B
import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy.Char8 as B8
import Data.Int (Int64)
import Data.Map.Optic (Map)
import Data.Monoid (Sum(..))
import Data.Profunctor.Optic hiding (folded, prefixed, filtered, zipped)
import Data.Word (Word8)

-- | Iso between lazy and strict 'ByteString'.
strict :: Iso' ByteString BS.ByteString
strict = iso B.toStrict B.fromStrict

-- | Iso between @[Word8]@ and lazy 'ByteString'.
packed :: Iso' [Word8] ByteString
packed = iso B.pack B.unpack

-- | Lazy 'ByteString' is reversible.
reversed :: Iso' ByteString ByteString
reversed = iso B.reverse B.reverse

-- | Iso between lazy 'ByteString' and its strict chunks.
chunked :: Iso' ByteString [BS.ByteString]
chunked = iso B.toChunks B.fromChunks

-- | Split on newlines.
lined :: Iso' ByteString [ByteString]
lined = iso B8.lines (B8.intercalate "\n")

-- | Split on spaces.
worded :: Iso' ByteString [ByteString]
worded = iso B8.words (B8.intercalate " ")

-- | Split on an arbitrary delimiter.
splitOn :: ByteString -> Iso' ByteString [ByteString]
splitOn delim = iso (split delim) (B.intercalate delim)
  where
    dlen = B.length delim
    split d s
        | B.null s = []
        | B.null d = [s]
        | otherwise = go s
    go s = case BS.breakSubstring (B.toStrict delim) (B.toStrict s) of
             (pre, rest)
               | BS.null rest -> [B.fromStrict pre]
               | otherwise -> B.fromStrict pre : go (B.fromStrict (BS.drop (fromIntegral dlen) rest))

---------------------------------------------------------------------
-- Prisms
---------------------------------------------------------------------

-- | Prism for cons-cell view of lazy 'ByteString'.
consed :: Prism' ByteString (Word8, ByteString)
consed = prism' B.uncons (uncurry B.cons)

-- | Prism for snoc-cell view of lazy 'ByteString'.
snoced :: Prism' ByteString (ByteString, Word8)
snoced = prism' B.unsnoc (uncurry B.snoc)

-- | Prism matching a prefix.
prefixed :: ByteString -> Prism' ByteString ByteString
prefixed p = prism' (B.stripPrefix p) (p <>)

-- | Prism matching a suffix.
suffixed :: ByteString -> Prism' ByteString ByteString
suffixed s = prism' (B.stripSuffix s) (<> s)

---------------------------------------------------------------------
-- Traversal0, Fold0
---------------------------------------------------------------------

-- | /O(n)/. Affine traversal into the byte at a position.
at :: Int64 -> Traversal0' ByteString Word8
at i = traversal0' sa sbt
  where
    sa bs = if i >= 0 && i < B.length bs then Just (B.index bs i) else Nothing
    sbt bs w = let (l, r) = B.splitAt i bs
               in  if B.null r then bs else l <> B.singleton w <> B.tail r

-- | Affine traversal into the first byte matching a predicate.
found :: (Word8 -> Bool) -> Traversal0' ByteString Word8
found p = traversal0' (B.find p) (\bs w -> B.map (\x -> if p x then w else x) bs)

-- | First byte, if non-empty.
headed :: Fold0 ByteString Word8
headed = fold0 (\bs -> if B.null bs then Nothing else Just (B.head bs))

-- | Last byte, if non-empty.
lasted :: Fold0 ByteString Word8
lasted = fold0 (\bs -> if B.null bs then Nothing else Just (B.last bs))

-- | Index of the first byte matching a predicate.
foundIndex :: (Word8 -> Bool) -> Fold0 ByteString (Sum Int64)
foundIndex p = fold0 (fmap Sum . B.findIndex p)

-- | Index of the first occurrence of a byte.
elemIndexed :: Word8 -> Fold0 ByteString (Sum Int64)
elemIndexed w = fold0 (fmap Sum . B.elemIndex w)

---------------------------------------------------------------------
-- Indexed optics
---------------------------------------------------------------------

-- | Indexed affine traversal at the incoming index.
ixat :: Ixtraversal0' (Sum Int64) ByteString Word8
ixat = ixtraversalVl0 $ \point f k bs ->
  let i = getSum k
  in  if i >= 0 && i < B.length bs
      then fmap (\w -> let (l, r) = B.splitAt i bs
                       in  l <> B.singleton w <> B.tail r) (f k (B.index bs i))
      else point bs

-- | Indexed traversal over bytes with positional index.
ixtraversed :: Ixtraversal (Sum Int64) ByteString ByteString Word8 Word8
ixtraversed = ixtraversalVl $ \f k bs ->
  B.pack <$> traverse (\(i, w) -> f (k <> Sum i) w) (zip [0..] (B.unpack bs))

-- | Indexed fold over bytes with positional index.
ixfolded :: Ixfold (Sum Int64) ByteString Word8
ixfolded = ixfoldVl $ \f k bs ->
  traverse (\(i, w) -> f (k <> Sum i) w) (zip [0..] (B.unpack bs))

-- | Indexed setter over bytes with positional index.
ixmapped :: Ixsetter (Sum Int64) ByteString ByteString Word8 Word8
ixmapped = ixsetter $ \f k bs ->
  B.pack $ zipWith (\i w -> f (k <> Sum i) w) [0..] (B.unpack bs)

---------------------------------------------------------------------
-- Setters / Adjoints
---------------------------------------------------------------------

-- | Filter bytes by predicate.
filtered :: Adjoint ByteString ByteString Word8 Bool
filtered = adjoint B.filter

-- | Traversal over individual bytes.
bytes :: Traversal' ByteString Word8
bytes = re packed . traversed

-- | Fold over individual bytes.
folded :: Fold ByteString Word8
folded = fold_ B.unpack

-- | Setter over individual bytes.
mapped :: Setter' ByteString Word8
mapped = setter B.map

---------------------------------------------------------------------
-- Coindexed optics
---------------------------------------------------------------------

-- | Coindexed traversal over bytes with positional coindex.
cxtraversed :: Cxtraversal (Sum Int64) ByteString ByteString Word8 Word8
cxtraversed = cxtraversalVl $ \fakb k fs ->
  let bs0 = copure fs
  in  B.pack $ zipWith (\i w -> fakb (fmap (\bs -> if i < B.length bs then B.index bs i else w) fs) (k <> Sum i))
        [0..] (B.unpack bs0)
{-# INLINE cxtraversed #-}

-- | Coindexed fold over bytes with positional coindex.
cxfolded :: Cxfold (Sum Int64) ByteString Word8
cxfolded = cxfoldVl $ \fakb k fs ->
  let bs0 = copure fs
  in  B.pack $ zipWith (\i w -> fakb (fmap (\bs -> if i < B.length bs then B.index bs i else w) fs) (k <> Sum i))
        [0..] (B.unpack bs0)
{-# INLINE cxfolded #-}

-- | Coindexed setter over bytes with positional coindex.
cxmapped :: Cxsetter (Sum Int64) ByteString ByteString Word8 Word8
cxmapped = cxsetter $ \f k bs ->
  B.pack $ zipWith (\i w -> f (k <> Sum i) w) [0..] (B.unpack bs)
{-# INLINE cxmapped #-}

-- | Coindexed filter over bytes with positional coindex.
cxfiltered :: Cxsetter (Sum Int64) ByteString ByteString Word8 Bool
cxfiltered = cxsetter $ \f k bs ->
  B.pack [w | (i, w) <- zip [0..] (B.unpack bs), f (k <> Sum i) w]
{-# INLINE cxfiltered #-}

---------------------------------------------------------------------
-- Dual optics
---------------------------------------------------------------------

-- | Pointwise 'Cotraversal' over bytes of two lazy 'ByteString' values.
zipped :: Cotraversal ByteString ByteString Word8 Word8
zipped = cotraversalVl $ \fab fs ->
  let bs = copure fs
      n = B.length bs
  in  B.pack [ fab (fmap (\bs' -> B.index bs' i) fs) | i <- [0..n-1] ]
{-# INLINE zipped #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Sort a lazy 'ByteString' by a key on each byte.
sortingBS :: Ord k => (Word8 -> k) -> ByteString -> Map k BS.ByteString
sortingBS f = sortingRep BS.length BS.index BS.pack f . B.toStrict
{-# INLINE sortingBS #-}
