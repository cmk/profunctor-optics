{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

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
    -- * Short iso
    short,

    -- * Lazy\/strict iso
    lazy,

    -- * Packing
    packed,

    -- * Splitting
    lined,
    worded,
    splitOn,

    -- * Element traversal
    bytes,
) where

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as B8
import qualified Data.ByteString.Lazy as BL
import Data.ByteString.Short (ShortByteString)
import qualified Data.ByteString.Short as SBS
import Data.Profunctor.Optic
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
