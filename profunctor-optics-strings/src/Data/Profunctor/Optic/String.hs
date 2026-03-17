{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

-- | Cotraversal-based string operations via profunctor optics.
--
-- == Fixed-size types (cotraversals)
--
-- Fixed-size types like 'Word8' are isomorphic to functions from
-- a finite index type: @Word8 ≅ I8 -> Bool@ (8 bits). Since
-- @(->) I8@ is 'Distributive', this gives cotraversals for free:
--
-- @
-- bits8  :: Cotraversal Word8 Word8 Bool Bool
-- bits16 :: Cotraversal Word16 Word16 Bool Bool
-- @
--
-- These compose with other optics:
--
-- @
-- \-\- flip all bits in a Word8
-- over bits8 not myByte
-- @
--
-- == Short ByteString iso
--
-- 'short' connects strict 'ByteString' to 'ShortByteString'
-- (pinned vs unpinned memory).
module Data.Profunctor.Optic.String (
    -- * Bit-level cotraversals
    bits8,
    bits16,
    bits32,
    bits64,

    -- * Byte-level grate
    grate8,

    -- * Short iso
    short,

    -- * Re-exports
    module Data.Functor.Index,
) where

import Data.ByteString (ByteString)
import Data.ByteString.Short (ShortByteString)
import qualified Data.ByteString.Short as SBS
import Data.Functor.Index
import Data.Profunctor.Optic
import Data.Word (Word8, Word16, Word32, Word64)

---------------------------------------------------------------------
-- Bit-level cotraversals
--
-- WordN ≅ (IN -> Bool), so (->) IN is the Distributive functor
-- and cotraversed gives us the cotraversal. We compose with the
-- iso to get cotraversals on the Word types directly.
---------------------------------------------------------------------

-- | Cotraversal over the 8 bits of a 'Word8'.
--
-- @bits8 = iso toBits8 fromBits8 . cotraversed@
bits8 :: Cotraversal Word8 Word8 Bool Bool
bits8 = iso toBits8 fromBits8 . cotraversed

-- | Cotraversal over the 16 bits of a 'Word16'.
bits16 :: Cotraversal Word16 Word16 Bool Bool
bits16 = iso toBits16 fromBits16 . cotraversed

-- | Cotraversal over the 32 bits of a 'Word32'.
bits32 :: Cotraversal Word32 Word32 Bool Bool
bits32 = iso toBits32 fromBits32 . cotraversed

-- | Cotraversal over the 64 bits of a 'Word64'.
bits64 :: Cotraversal Word64 Word64 Bool Bool
bits64 = iso toBits64 fromBits64 . cotraversed

---------------------------------------------------------------------
-- Byte-level grate
---------------------------------------------------------------------

-- | Grate viewing a 'Word8' through its bit representation.
--
-- @grate8 = grate (\\f -> fromBits8 (f . toBits8))@
grate8 :: Colens Word8 Word8 (I8 -> Bool) (I8 -> Bool)
grate8 = grate $ \f -> fromBits8 (f toBits8)

---------------------------------------------------------------------
-- Short iso
---------------------------------------------------------------------

-- | Iso between strict 'ByteString' and 'ShortByteString'.
--
-- 'ShortByteString' is backed by unpinned @ByteArray#@ — better
-- for GC when storing many small strings.
short :: Iso' ByteString ShortByteString
short = iso SBS.toShort SBS.fromShort
