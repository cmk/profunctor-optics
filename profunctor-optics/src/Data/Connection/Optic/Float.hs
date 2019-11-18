module Data.Connection.Optic.Float (
    f32u32
  , u32f32
  , u32w64
  , f32i64
  , i64f32
) where

import Data.Connection.Float (Ulp32)
import Data.Int
import Data.Prd.Nan (Nan)
import Data.Profunctor.Optic.Grate
import Data.Profunctor.Optic.Import
import Data.Word
import qualified Data.Connection.Float as F

-- >>> constOf f32u32 (Ulp32 0)
-- 0.0
-- >>> constOf f32u32 (Ulp32 1)
-- 1.0e-45
f32u32 :: Grate' Float Ulp32
f32u32 = connected F.f32u32

u32f32 :: Grate' Ulp32 Float
u32f32 = connected F.u32f32

u32w64 :: Grate' Ulp32 (Nan Word64)
u32w64 = connected F.u32w64

-- >>> constOf f32i64 Nan
-- NaN
-- >>> zipWithOf i64f32 (/) (Def 0) (Def 0)
-- Nan
f32i64 :: Grate' Float (Nan Int64)
f32i64 = connected F.f32i64
  
i64f32 :: Grate' (Nan Int64) Float
i64f32 = connected F.i64f32
