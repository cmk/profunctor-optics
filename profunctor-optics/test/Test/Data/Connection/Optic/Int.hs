{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Connection.Optic.Int where

import Control.Applicative
import Data.Int
import Data.Word
import Data.Prd

import Data.Connection.Optic.Int as I
import Data.Profunctor.Optic

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

v3 :: Gen a -> Gen (V3 a)
v3 g = liftA3 V3 g g g

i08 :: Gen Int8
i08 = G.int8 R.linearBounded

i32 :: Gen Int32
i32 = G.int32 R.linearBounded

i64 :: Gen Int64
i64 = G.int64 R.linearBounded

prop_i08w08 :: Property
prop_i08w08 = withTests 1000 . property $ do
  x <- forAll i08
  vvx <- forAll (v3 . v3 $ i08)
  assert $ id_grate I.i08w08 x
  assert $ const_grate I.i08w08 x
  assert $ compose_grate I.i08w08 add3 mul3 vvx
  assert $ compose_grate I.i08w08 sub3 mul3 vvx
