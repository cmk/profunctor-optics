module Numeric.Optic.Word (
  -- * Word8
    w08i08
  , w08w16
  , w08w32
  , w08w64
  , w08nat
  -- * Word16
  , w16i16
  , w16w32
  , w16w64
  , w16nat
  -- * Word32
  , w32i32
  , w32w64
  , w32nat
  -- * Word64
  , w64i64
  , w64nat
) where

import Data.Int
import Data.Word
import Data.Profunctor.Optic.Grate 
import Numeric.Natural
import qualified Data.Connection.Word as W

-- >>> constOf w08i08 0
-- 128
-- >>> zipWithOf w08i08 (+) 0 0
-- 128
--
w08i08 :: Grate' Word8 Int8
w08i08 = connected W.w08i08

-- >>> constOf w08w16 0
-- 0
-- >>> zipWithOf w08w16 (+) 16 7
-- 23
--
w08w16 :: Grate' Word8 Word16
w08w16 = connected W.w08w16 

w08w32 :: Grate' Word8 Word32
w08w32 = connected W.w08w32

w08w64 :: Grate' Word8 Word64
w08w64 = connected W.w08w64

w08nat :: Grate' Word8 Natural
w08nat = connected W.w08nat

w16i16 :: Grate' Word16 Int16
w16i16 = connected W.w16i16

w16w32 :: Grate' Word16 Word32
w16w32 = connected W.w16w32

w16w64 :: Grate' Word16 Word64
w16w64 = connected W.w16w64

w16nat :: Grate' Word16 Natural
w16nat = connected W.w16nat

w32i32 :: Grate' Word32 Int32
w32i32 = connected W.w32i32

w32w64 :: Grate' Word32 Word64
w32w64 = connected W.w32w64

w32nat :: Grate' Word32 Natural
w32nat = connected W.w32nat

w64i64 :: Grate' Word64 Int64
w64i64 = connected W.w64i64

w64nat :: Grate' Word64 Natural
w64nat = connected W.w64nat
