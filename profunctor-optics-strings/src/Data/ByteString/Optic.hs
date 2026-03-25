{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}

-- | Profunctor optics for 'ByteString'.
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
    lined,
    worded,
    splitOn,

    -- ** Traversal
    bytes,

    -- ** Fold
    folded,

    -- ** Setter
    mapped,

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
import Data.Map.Optic (Map(..))
import Data.ByteString.Short (ShortByteString)
import qualified Data.ByteString.Short as SBS
import Data.Profunctor.Optic hiding (folded)
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
