{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

-- | Left and right carriers are characterized by their representation
-- functors ('Rep' and 'Corep'). 'Iso' sits at the top where both
-- are trivial ('Identity'). 'Adjoint' sits at the bottom where they
-- form a full adjunction (@'Corep' p ⊣ 'Rep' p@). A left-indexed
-- ('Ix') optic threads an index through the left adjoint functor
-- @(,) k@, while a right-indexed ('Cx') optic threads a coindex
-- through the right adjoint functor @(->) k@.
--
-- Bit-level cotraversals and grates for 'Word' types.
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
--
-- \-\- indexed: flip only even-positioned bits
-- cxover ibits8 (\\i b -> if even (fromEnum i) then not b else b) 0xFF
-- @
module Data.Word.Optic (
    -- * Bit-level cotraversals
    bits8,
    bits16,
    bits32,
    bits64,

    -- * Indexed bit-level cotraversals
    ibits8,
    ibits16,
    ibits32,
    ibits64,

    -- * Byte-level grates
    grate8,
    grate16,
    grate32,
    grate64,

    -- * Re-exports
    module Data.Functor.Index,
) where

import Data.Functor.Index
import Data.Profunctor.Optic
import Data.Word (Word8, Word16, Word32, Word64)

-- | Cotraversal over the 8 bits of a 'Word8'.
--
-- ~44 ns\/bit. Prefer 'ibits8' (~7 ns\/bit) when the index is available.
-- See the Benchmarks section of the README for details.
--
-- @bits8 = iso toBits8 fromBits8 . cotraversed@
bits8 :: Cotraversal Word8 Word8 Bool Bool
bits8 = iso toBits8 fromBits8 . cotraversed

-- | Cotraversal over the 16 bits of a 'Word16'.
--
-- ~44 ns\/bit. Prefer 'ibits16' (~7 ns\/bit). See README.
bits16 :: Cotraversal Word16 Word16 Bool Bool
bits16 = iso toBits16 fromBits16 . cotraversed

-- | Cotraversal over the 32 bits of a 'Word32'.
--
-- ~44 ns\/bit. Prefer 'ibits32' (~7 ns\/bit). See README.
bits32 :: Cotraversal Word32 Word32 Bool Bool
bits32 = iso toBits32 fromBits32 . cotraversed

-- | Cotraversal over the 64 bits of a 'Word64'.
--
-- ~44 ns\/bit. Prefer 'ibits64' (~7 ns\/bit). See README.
bits64 :: Cotraversal Word64 Word64 Bool Bool
bits64 = iso toBits64 fromBits64 . cotraversed

-- | Indexed cotraversal over the 8 bits of a 'Word8'.
--
-- The index is the bit position ('I8'). ~7 ns\/bit — 6-7x faster
-- than 'bits8'. Preferred for all use cases where the index is
-- available. See README.
ibits8 :: Cxlens I8 Word8 Word8 Bool Bool
ibits8 = cxlens $ \f -> fromBits8 (\i -> f (\w -> toBits8 w i) i)

-- | Indexed cotraversal over the 16 bits of a 'Word16'. ~7 ns\/bit. See README.
ibits16 :: Cxlens I16 Word16 Word16 Bool Bool
ibits16 = cxlens $ \f -> fromBits16 (\i -> f (\w -> toBits16 w i) i)

-- | Indexed cotraversal over the 32 bits of a 'Word32'. ~7 ns\/bit. See README.
ibits32 :: Cxlens I32 Word32 Word32 Bool Bool
ibits32 = cxlens $ \f -> fromBits32 (\i -> f (\w -> toBits32 w i) i)

-- | Indexed cotraversal over the 64 bits of a 'Word64'. ~7 ns\/bit. See README.
ibits64 :: Cxlens I64 Word64 Word64 Bool Bool
ibits64 = cxlens $ \f -> fromBits64 (\i -> f (\w -> toBits64 w i) i)

-- | Grate viewing a 'Word8' through its bit representation.
--
-- ~21 ns\/bit. Faster than 'bits8' (~44 ns\/bit), slower than 'ibits8' (~7 ns\/bit).
-- Use when you need 'Closed' but not the coindex. See README.
--
-- @grate8 = grate (\\f -> fromBits8 (f . toBits8))@
grate8 :: Colens Word8 Word8 (I8 -> Bool) (I8 -> Bool)
grate8 = grate $ \f -> fromBits8 (f toBits8)

-- | Grate viewing a 'Word16' through its bit representation.
grate16 :: Colens Word16 Word16 (I16 -> Bool) (I16 -> Bool)
grate16 = grate $ \f -> fromBits16 (f toBits16)

-- | Grate viewing a 'Word32' through its bit representation.
grate32 :: Colens Word32 Word32 (I32 -> Bool) (I32 -> Bool)
grate32 = grate $ \f -> fromBits32 (f toBits32)

-- | Grate viewing a 'Word64' through its bit representation.
grate64 :: Colens Word64 Word64 (I64 -> Bool) (I64 -> Bool)
grate64 = grate $ \f -> fromBits64 (f toBits64)
