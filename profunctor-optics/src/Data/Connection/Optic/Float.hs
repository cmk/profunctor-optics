module Data.Connection.Optic.Float (
    f32u32
  , u32f32
) where

import Data.Connection.Float (Ulp32)
import Data.Int
import Data.Prd.Nan (Nan)
import Data.Profunctor.Optic.Grate
import Data.Profunctor.Optic.Import
import Data.Word
import qualified Data.Connection.Float as F

-- >>> coview f32u32 (Ulp32 0)
-- 0.0
-- >>> coview f32u32 (Ulp32 1)
-- 1.0e-45
f32u32 :: Grate' Float Ulp32
f32u32 = connected F.f32u32

u32f32 :: Grate' Ulp32 Float
u32f32 = connected F.u32f32

{-
-- >>> coview f32i32 Nan
-- NaN
-- >>> zipsWith i32f32 (/) (Def 0) (Def 0)
-- Nan
f32i32 :: Grate' Float (Nan Int64)
f32i32 = connected F.f32i32
  
i32f32 :: Grate' (Nan Int64) Float
i32f32 = connected F.i32f32
-}
