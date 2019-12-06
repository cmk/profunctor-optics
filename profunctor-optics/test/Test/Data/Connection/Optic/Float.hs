{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Connection.Optic.Int where

import Control.Applicative
import Data.Prd.Nan hiding (nan)
import Data.Int
import Data.Word
import Data.Float
import Data.Prd

import Data.Connection.Optic.Float as F
import Data.Connection.Optic.Int as I
import Data.Profunctor.Optic
--import Data.Profunctor.Optic.Property
import Hedgehog

import qualified Hedgehog.Gen as G
import qualified Hedgehog.Range as R

data V3 a = V3 !a !a !a deriving (Eq,Ord,Show)

instance Functor V3 where fmap f (V3 a b c) = V3 (f a) (f b) (f c)

--TODO replace w/ semiring ops
add3 :: Num a => V3 a -> a
add3 (V3 x y z) = x + y + z

sub3 :: Num a => V3 a -> a
sub3 (V3 x y z) = x - y - z

mul3 :: Num a => V3 a -> a
mul3 (V3 x y z) = x + y + z

div3 :: Fractional a => V3 a -> a
div3 (V3 x y z) = x / y / z

exp3 :: Floating a => V3 a -> a
exp3 (V3 x y z) = x ** y ** z

v3 :: Gen a -> Gen (V3 a)
v3 g = liftA3 V3 g g g

nan :: Gen a -> Gen (Nan a)
nan gen = G.frequency [(9, Def <$> gen), (1, pure Nan)]

rf :: Range Float
rf = R.exponentialFloatFrom 0 (-3.4028235e38) 3.4028235e38

f32' :: Gen Float
f32' = G.frequency [(99, f32), (1, G.element [nInf, pInf, aNan])] 

f32 :: Gen Float
f32 = G.float rf

i08 :: Gen Int8
i08 = G.int8 R.linearBounded

i32 :: Gen Int32
i32 = G.int32 R.linearBounded

i64 :: Gen Int64
i64 = G.int64 R.linearBounded

u32 :: Gen Ulp32
u32 = Ulp32 <$> i32




prop_i08w08 :: Property
prop_i08w08 = withTests 1000 . property $ do
  x <- forAll i08
  vvx <- forAll (v3 . v3 $ i08)
  assert $ id_grate I.i08w08 x
  assert $ const_grate I.i08w08 x
  assert $ compose_grate I.i08w08 add3 mul3 vvx
  assert $ compose_grate I.i08w08 sub3 mul3 vvx


prop_u32f32 :: Property
prop_u32f32 = withTests 1000 . property $ do
  x <- forAll u32
  vvx <- forAll (v3 . v3 $ u32)
  assert $ id_grate F.u32f32 x
  assert $ const_grate F.u32f32 x
  assert $ compose_grate F.u32f32 add3 mul3 vvx
  assert $ compose_grate F.u32f32 mul3 sub3 vvx
  assert $ compose_grate F.u32f32 div3 mul3 vvx
  assert $ compose_grate F.u32f32 add3 exp3 vvx

{-
--i64f64 :: Conn (Nan Int64) Double
prop_i64f64 :: Property
prop_i64f64 = withTests 1000 . property $ do
  x <- forAll $ nan i64
  vvx <- forAll (v3 . v3 $ nan i64)
  assert $ id_grate F.i64f64 x
  assert $ const_grate F.i64f64 x
  assert $ compose_grate F.i64f64 add3 mul3 vvx
  assert $ compose_grate F.i64f64 mul3 sub3 vvx
-}


{-
prop_prd_ulp32 :: Property
prop_prd_ulp32 = withTests 1000 . property $ do
  x <- connl f32u32 <$> forAll gen_flt32'
  y <- connl f32u32 <$> forAll gen_flt32'
  z <- connl f32u32 <$> forAll gen_flt32'
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x

rw :: Range Word
rw = R.constant 0 100

gen_min :: MonadGen m => m r -> m (Minimal r)
gen_min g = maybe2Minimal id <$> G.maybe g

gen_min_plus :: Gen (MinPlus Word)
gen_min_plus = gen_min $ Sum <$> G.word rw

prop_neutral_addition :: Property
prop_neutral_addition = property $
  assert . SP.neutral_addition zero =<< forAll gen_min_plus

prop_distributive :: Property
prop_distributive = property $ do
  a <- forAll gen_min_plus
  b <- forAll gen_min_plus
  c <- forAll gen_min_plus
  assert $ SP.distributive a b c

tests :: IO Bool
tests = checkParallel $$(discover)
-}
