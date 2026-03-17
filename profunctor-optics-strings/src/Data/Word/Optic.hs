{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

-- | Bit-level cotraversals and grates for 'Word' types.
--
-- Each 'Word' type is isomorphic to a function from a finite
-- index type: @Word8 ≅ I8 -> Bool@. Since @(->) I8@ is
-- 'Distributive', 'cotraversed' gives cotraversals for free.
--
-- @
-- \-\- flip all bits
-- over bits8 not 0xFF  ==  0
--
-- \-\- identity
-- over bits8 id 42  ==  42
-- @
module Data.Word.Optic (
    -- * Bit-level cotraversals
    bits8,
    bits16,
    bits32,
    bits64,

    -- * Byte-level grate
    grate8,

    -- * Re-exports
    module Data.Functor.Index,
) where

import Data.Functor.Index
import Data.Profunctor.Optic
import Data.Word (Word8, Word16, Word32, Word64)

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

-- | Grate viewing a 'Word8' through its bit representation.
--
-- @grate8 = grate (\\f -> fromBits8 (f . toBits8))@
grate8 :: Colens Word8 Word8 (I8 -> Bool) (I8 -> Bool)
grate8 = grate $ \f -> fromBits8 (f toBits8)
