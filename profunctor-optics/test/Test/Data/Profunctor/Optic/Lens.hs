{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Profunctor.Optic.Lens where

import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Carrier (withIxlens, AIxlens)
import Data.Profunctor.Optic.Property as Prop
import Data.Profunctor.Optic.Lens (ixlens, ixfirst, ixsecond, cloneIxlens)
import Hedgehog
import qualified Hedgehog.Gen as G
import qualified Hedgehog.Range as R

---------------------------------------------------------------------
-- Generators
---------------------------------------------------------------------

ri :: Range Int
ri = R.linearFrom 0 (-1000) 1000

int :: Gen Int
int = G.int ri

char :: Gen Char
char = G.alpha

gen_pair :: Gen a -> Gen b -> Gen (a, b)
gen_pair ga gb = (,) <$> ga <*> gb

---------------------------------------------------------------------
-- Non-Monoid index type (the whole point of this module)
---------------------------------------------------------------------

-- | A newtype with no Monoid instance, used to verify that
-- withIxlens's lazy knot-tying genuinely avoids the constraint.
newtype Tag = Tag Int
  deriving (Eq, Show)

-- An Ixlens that tags the focus with a constant Tag derived from the source.
tagged_fst :: Ixlens' Tag (Int, Char) Int
tagged_fst = ixlens (\(a, _) -> (Tag a, a)) (\(_, b) a -> (a, b))

---------------------------------------------------------------------
-- withIxlens laws at a non-Monoid index
---------------------------------------------------------------------

-- | tofrom: sbt s (snd (ska s)) == s
prop_ixlens_nonmonoid_tofrom :: Property
prop_ixlens_nonmonoid_tofrom = withTests 200 . property $ do
  s <- forAll $ gen_pair int char
  assert $ Prop.tofrom_ixlens tagged_fst s

-- | fromto: snd (ska (sbt s a)) == a
prop_ixlens_nonmonoid_fromto :: Property
prop_ixlens_nonmonoid_fromto = withTests 200 . property $ do
  s <- forAll $ gen_pair int char
  a <- forAll int
  assert $ Prop.fromto_ixlens tagged_fst s a

-- | idempotent: sbt (sbt s a1) a2 == sbt s a2
prop_ixlens_nonmonoid_idempotent :: Property
prop_ixlens_nonmonoid_idempotent = withTests 200 . property $ do
  s <- forAll $ gen_pair int char
  a1 <- forAll int
  a2 <- forAll int
  assert $ Prop.idempotent_ixlens tagged_fst s a1 a2

---------------------------------------------------------------------
-- withIxlens: getter preserves the index
---------------------------------------------------------------------

-- | The index produced by withIxlens's getter must agree with the
-- original ixlens's getter. This catches any corruption from the
-- lazy knot (e.g. if the "fed-back" key leaked into the output).
prop_ixlens_nonmonoid_index_preserved :: Property
prop_ixlens_nonmonoid_index_preserved = withTests 200 . property $ do
  s@(a, _) <- forAll $ gen_pair int char
  withIxlens tagged_fst $ \ska _sbt ->
    fst (ska s) === Tag a

---------------------------------------------------------------------
-- withIxlens: setter ignores the index
---------------------------------------------------------------------

-- | The setter from withIxlens must produce the same result
-- regardless of what index the getter reports.
prop_ixlens_nonmonoid_setter_independent :: Property
prop_ixlens_nonmonoid_setter_independent = withTests 200 . property $ do
  s <- forAll $ gen_pair int char
  b <- forAll int
  withIxlens tagged_fst $ \_ sbt ->
    sbt s b === (b, snd s)

---------------------------------------------------------------------
-- ixfirst / ixsecond at non-Monoid index
---------------------------------------------------------------------

-- | ixfirst at Tag (no Monoid instance).
-- The index threads via lmap assocl, but withIxlens should still
-- work because the knot-tied value is never forced.
prop_ixfirst_nonmonoid_tofrom :: Property
prop_ixfirst_nonmonoid_tofrom = withTests 200 . property $ do
  s <- forAll $ gen_pair int char
  assert $ Prop.tofrom_ixlens (ixfirst :: Ixlens' Tag (Int, Char) Int) s

prop_ixsecond_nonmonoid_tofrom :: Property
prop_ixsecond_nonmonoid_tofrom = withTests 200 . property $ do
  s <- forAll $ gen_pair int char
  assert $ Prop.tofrom_ixlens (ixsecond :: Ixlens' Tag (Int, Char) Char) s

---------------------------------------------------------------------
-- cloneIxlens round-trip at non-Monoid index
---------------------------------------------------------------------

-- | Clone an Ixlens at a non-Monoid index and verify laws still hold.
prop_cloneIxlens_nonmonoid_tofrom :: Property
prop_cloneIxlens_nonmonoid_tofrom = withTests 200 . property $ do
  s <- forAll $ gen_pair int char
  assert $ Prop.tofrom_ixlens (cloneIxlens tagged_fst) s

prop_cloneIxlens_nonmonoid_fromto :: Property
prop_cloneIxlens_nonmonoid_fromto = withTests 200 . property $ do
  s <- forAll $ gen_pair int char
  a <- forAll int
  assert $ Prop.fromto_ixlens (cloneIxlens tagged_fst) s a

---------------------------------------------------------------------
-- cloneIxlens preserves index
---------------------------------------------------------------------

-- | After cloning, the getter must still produce the correct index.
prop_cloneIxlens_nonmonoid_index :: Property
prop_cloneIxlens_nonmonoid_index = withTests 200 . property $ do
  s@(a, _) <- forAll $ gen_pair int char
  withIxlens (cloneIxlens tagged_fst) $ \ska _sbt ->
    fst (ska s) === Tag a

tests :: IO Bool
tests = checkSequential $$(discover)
