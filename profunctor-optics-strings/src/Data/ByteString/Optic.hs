{-# LANGUAGE FlexibleContexts #-}

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
) where

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
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
