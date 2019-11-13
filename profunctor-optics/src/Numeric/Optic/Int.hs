module Numeric.Optic.Int (
  -- * Int8
    i08w08
  , i08w08'
  , i08i16
  , i08i32
  , i08i64
  -- * Int16
  , i16w16
  , i16w16'
  , i16i32
  , i16i64
  -- * Int32
  , i32w32
  , i32w32'
  , i32i64
  -- * Int64
  , i64w64
  , i64w64'
  -- * Integer
  , intnat
) where

import Data.Int
import Data.Word
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Grate
import Numeric.Natural
import qualified Data.Connection.Int as I

i08w08 :: Grate' Int8 Word8
i08w08 = connected I.i08w08

i08w08' :: Grate' Int8 Word8
i08w08' = connected I.i08w08'

-- >>> (127 :: Int8) + 3
-- -126
-- >>> zipWithOf i08i16 (+) 127 3
-- 127
i08i16 :: Grate' Int8 Int16
i08i16 = connected I.i08i16

i08i32 :: Grate' Int8 Int32
i08i32 = connected I.i08i32

i08i64 :: Grate' Int8 Int64
i08i64 = connected I.i08i64

i16w16 :: Grate' Int16 Word16
i16w16 = connected I.i16w16

i16w16' :: Grate' Int16 Word16
i16w16' = connected I.i16w16'

i16i32 :: Grate' Int16 Int32
i16i32 = connected I.i16i32

i16i64 :: Grate' Int16 Int64
i16i64 = connected I.i16i64

i32w32 :: Grate' Int32 Word32
i32w32 = connected I.i32w32

i32w32' :: Grate' Int32 Word32
i32w32' = connected I.i32w32'

i32i64 :: Grate' Int32 Int64
i32i64 = connected I.i32i64

i64w64 :: Grate' Int64 Word64
i64w64 = connected I.i64w64

i64w64' :: Grate' Int64 Word64
i64w64' = connected I.i64w64'

intnat :: Grate' Integer Natural
intnat = connected I.intnat 
