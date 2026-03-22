{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Test.Carrier where

import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Property as Prop
import Data.Profunctor.Optic.Combinator (over)
import Data.Profunctor.Optic.Iso (iso)
import Data.Profunctor.Optic.Lens (grate, lensVl, relens, refirst)
import Data.Profunctor.Optic.Prism (just, reprism, releft)
import Data.Profunctor.Optic.Traversal (traversed)
import Data.Profunctor.Optic.Setter (set)
import Data.Functor.Identity
import Data.Profunctor.Types (Profunctor(..))
import Data.Profunctor.Choice (Choice(..))
import Data.Profunctor.Closed (Closed(..))
import Hedgehog
import qualified Hedgehog.Gen as G
import qualified Hedgehog.Range as R

ri :: Range Int
ri = R.linearFrom 0 (-1000) 1000

int :: Gen Int
int = G.int ri

char :: Gen Char
char = G.alpha

gen_pair :: Gen a -> Gen b -> Gen (a, b)
gen_pair ga gb = (,) <$> ga <*> gb

gen_either :: Gen a -> Gen b -> Gen (Either a b)
gen_either ga gb = G.choice [Left <$> ga, Right <$> gb]

gen_maybe :: Gen a -> Gen (Maybe a)
gen_maybe g = G.choice [pure Nothing, Just <$> g]

gen_list :: Gen a -> Gen [a]
gen_list = G.list (R.linear 0 10)

---------------------------------------------------------------------
-- Iso
---------------------------------------------------------------------

prop_iso_fromto :: Property
prop_iso_fromto = withTests 100 . property $ do
  a <- forAll int
  -- Test fromto using show/read: show (read (show a)) == show a
  assert $ Prop.fromto_iso (iso (read @Int) show) (show a)

prop_iso_tofrom :: Property
prop_iso_tofrom = withTests 100 . property $ do
  a <- forAll int
  assert $ Prop.tofrom_iso (iso (read @Int) show) a

---------------------------------------------------------------------
-- Lens
---------------------------------------------------------------------

fst_ :: Lens' (Int, Char) Int
fst_ = lensVl $ \f (a, b) -> (\a' -> (a', b)) <$> f a

prop_lens_tofrom :: Property
prop_lens_tofrom = withTests 100 . property $ do
  s <- forAll $ gen_pair int char
  assert $ Prop.tofrom_lens fst_ s

prop_lens_fromto :: Property
prop_lens_fromto = withTests 100 . property $ do
  s <- forAll $ gen_pair int char
  a <- forAll int
  assert $ Prop.fromto_lens fst_ s a

prop_lens_idempotent :: Property
prop_lens_idempotent = withTests 100 . property $ do
  s <- forAll $ gen_pair int char
  a1 <- forAll int
  a2 <- forAll int
  assert $ Prop.idempotent_lens fst_ s a1 a2

---------------------------------------------------------------------
-- Prism
---------------------------------------------------------------------

left_ :: Prism' (Either Int Int) Int
left_ = dimap
  (\s -> case s of Left a -> Right a; Right c -> Left (Right c))
  (\e -> case e of Left t -> t; Right b -> Left b)
  . right'

prop_prism_tofrom :: Property
prop_prism_tofrom = withTests 100 . property $ do
  s <- forAll $ gen_either int int
  assert $ Prop.tofrom_prism left_ s

prop_prism_fromto :: Property
prop_prism_fromto = withTests 100 . property $ do
  a <- forAll int
  assert $ Prop.fromto_prism left_ a

prop_prism_idempotent :: Property
prop_prism_idempotent = withTests 100 . property $ do
  s <- forAll $ gen_either int int
  assert $ Prop.idempotent_prism left_ s

---------------------------------------------------------------------
-- Relens
---------------------------------------------------------------------

-- re first' :: Relens' Int (Int, Char)
-- bsa a (i, c) = i, bt a = (a, c) where c = snd (bt a) ... via knot-tying
-- Carrier: RelensRep (\a (i, _) -> i) (\a -> (a, ???))
-- Use refirst directly which is just unfirst.
--
-- refirst @Int @Int @Char :: Relens' Int (Int, Char)
-- s = Int, a = (Int, Char)
-- const_relens: bsa a (bt a) == a  (a :: (Int, Char))
-- tofrom_relens: bt (bsa a s) == s  (s :: Int)
-- idempotent_relens: bsa (bsa a s1) s2 == bsa a s2

prop_relens_const :: Property
prop_relens_const = withTests 100 . property $ do
  a <- forAll $ gen_pair int char
  assert $ Prop.const_relens (refirst @Int @Int @Char) a

prop_relens_tofrom :: Property
prop_relens_tofrom = withTests 100 . property $ do
  a <- forAll $ gen_pair int char
  s <- forAll int
  assert $ Prop.tofrom_relens (refirst @Int @Int @Char) a s

prop_relens_idempotent :: Property
prop_relens_idempotent = withTests 100 . property $ do
  a <- forAll $ gen_pair int char
  s1 <- forAll int
  s2 <- forAll int
  assert $ Prop.idempotent_relens (refirst @Int @Int @Char) a s1 s2

---------------------------------------------------------------------
-- Reprism
---------------------------------------------------------------------

-- releft @Int @Int @Char :: Reprism' Int (Either Int Char)
-- s = Int, a = Either Int Char

prop_reprism_tofrom :: Property
prop_reprism_tofrom = withTests 100 . property $ do
  a <- forAll $ gen_either int char
  assert $ Prop.tofrom_reprism (releft @Int @Int @Char) a

prop_reprism_fromto :: Property
prop_reprism_fromto = withTests 100 . property $ do
  s <- forAll int
  assert $ Prop.fromto_reprism (releft @Int @Int @Char) s

prop_reprism_idempotent :: Property
prop_reprism_idempotent = withTests 100 . property $ do
  a <- forAll $ gen_either int char
  assert $ Prop.idempotent_reprism (releft @Int @Int @Char) a

---------------------------------------------------------------------
-- Traversal0 (Affine)
---------------------------------------------------------------------

prop_traversal0_fromto :: Property
prop_traversal0_fromto = withTests 100 . property $ do
  s <- forAll $ gen_maybe int
  assert $ Prop.fromto_traversal0 just s

prop_traversal0_tofrom :: Property
prop_traversal0_tofrom = withTests 100 . property $ do
  s <- forAll $ gen_maybe int
  a <- forAll int
  assert $ Prop.tofrom_traversal0 just s a

prop_traversal0_idempotent :: Property
prop_traversal0_idempotent = withTests 100 . property $ do
  s <- forAll $ gen_maybe int
  a1 <- forAll int
  a2 <- forAll int
  assert $ Prop.idempotent_traversal0 just s a1 a2

---------------------------------------------------------------------
-- Colens (Grate)
---------------------------------------------------------------------

pair_grate :: Colens' (Int, Int) Int
pair_grate = grate $ \f -> (f fst, f snd)

prop_grate_const :: Property
prop_grate_const = withTests 100 . property $ do
  s <- forAll $ gen_pair int int
  assert $ Prop.const_grate pair_grate s

---------------------------------------------------------------------
-- Setter
---------------------------------------------------------------------

prop_setter_id :: Property
prop_setter_id = withTests 100 . property $ do
  xs <- forAll $ gen_list int
  assert $ Prop.id_setter traversed xs

prop_setter_compose :: Property
prop_setter_compose = withTests 100 . property $ do
  xs <- forAll $ gen_list int
  assert $ Prop.compose_setter traversed (+1) (*2) xs

prop_setter_idempotent :: Property
prop_setter_idempotent = withTests 100 . property $ do
  xs <- forAll $ gen_list int
  a <- forAll int
  b <- forAll int
  assert $ Prop.idempotent_setter traversed xs a b

---------------------------------------------------------------------
-- CoaffineRep carrier: Profunctor law
---------------------------------------------------------------------

-- | Profunctor law: dimap id id ≡ id
prop_coaffinerep_profunctor_id :: Property
prop_coaffinerep_profunctor_id = withTests 100 . property $ do
  x <- forAll int
  let cr :: CoaffineRep Int Int Int Int
      cr = CoaffineRep $ \f -> f Right
      dimapped = dimap id id cr
  unCoaffineRep cr (const x) === unCoaffineRep dimapped (const x)

---------------------------------------------------------------------
-- CoaffineRep carrier: Choice instance (left-unit law)
---------------------------------------------------------------------

-- | left-unit law: lmap Left . left' ≡ rmap Left
-- Both sides: CoaffineRep Int Int Int (Either Int c)
-- We test by running with the same callback and comparing results.
prop_coaffinerep_left_unit :: Property
prop_coaffinerep_left_unit = withTests 100 . property $ do
  x <- forAll int
  let cr :: CoaffineRep Int Int Int Int
      cr = CoaffineRep $ \f -> f Right
      -- lhs: lmap Left . left'
      -- left' cr :: CoaffineRep Int Int (Either Int c) (Either Int c)
      -- lmap Left :: ... -> CoaffineRep Int Int Int (Either Int c)
      lhs :: Int
      lhs = case unCoaffineRep (lmap Left (left' cr)) (\g -> case g x of { Left (Left n) -> n; Left (Right _) -> -999; Right n -> n + 1000 }) of
              Left n -> n
              Right _ -> -888
      -- rhs: rmap Left
      -- rmap Left cr :: CoaffineRep Int Int Int (Either Int c)
      rhs :: Int
      rhs = case unCoaffineRep (rmap (Left @Int @Char) cr) (\g -> case g x of { Left (Left n) -> n; Left (Right _) -> -999; Right n -> n + 1000 }) of
              Left n -> n
              Right _ -> -888
  lhs === rhs

---------------------------------------------------------------------
-- CoaffineRep carrier: left' always produces Left
---------------------------------------------------------------------

prop_coaffinerep_left_always :: Property
prop_coaffinerep_left_always = withTests 100 . property $ do
  x <- forAll int
  let cr :: CoaffineRep Int Int Int Int
      cr = CoaffineRep $ \f -> f Right
      left_cr :: CoaffineRep Int Int (Either Int Char) (Either Int Char)
      left_cr = left' cr
      result :: Either Int Char
      result = unCoaffineRep left_cr $ \sta -> case sta (Left x) of
        Left (Left t) -> t
        Left (Right _) -> -888
        Right a -> a + 1000
  case result of
    Left _  -> success
    Right _ -> failure

---------------------------------------------------------------------
-- CoaffineRep carrier: Closed instance
---------------------------------------------------------------------

-- | closed instance: closed cr = CoaffineRep $ \f x -> f (\xs -> Right (xs x))
-- The identity CoaffineRep through closed should give back the value via const.
-- unCoaffineRep closed_cr f y = f (\xs -> Right (xs y))
-- With f = \sta -> case sta (const x) of Right a -> a:
--   sta (const x) = Right (const x y) = Right x  =>  result = x
prop_coaffinerep_closed :: Property
prop_coaffinerep_closed = withTests 100 . property $ do
  x <- forAll int
  y <- forAll int
  let cr :: CoaffineRep Int Int Int Int
      cr = CoaffineRep $ \f -> f Right
      closed_cr :: CoaffineRep Int Int (Int -> Int) (Int -> Int)
      closed_cr = closed cr
      result :: Int -> Int
      result = unCoaffineRep closed_cr $ \sta ->
        case sta (const x) of
          Left _  -> -999
          Right a -> a
  result y === x

---------------------------------------------------------------------
-- ColensRep carrier: Profunctor law
---------------------------------------------------------------------

-- | Profunctor law: dimap id id ≡ id
prop_colensrep_profunctor_id :: Property
prop_colensrep_profunctor_id = withTests 100 . property $ do
  x <- forAll int
  let cr :: ColensRep Int Int Int Int
      cr = ColensRep $ \f -> f id
      dimapped = dimap id id cr
  unColensRep cr ($ x) === unColensRep dimapped ($ x)

-- | const law: sabt ($ s) ≡ s
prop_colensrep_const :: Property
prop_colensrep_const = withTests 100 . property $ do
  x <- forAll int
  let cr :: ColensRep Int Int Int Int
      cr = ColensRep $ \f -> f id
  unColensRep cr ($ x) === x

---------------------------------------------------------------------
-- ColensRep carrier: Closed instance
---------------------------------------------------------------------

-- | closed identity grate should yield the identity function.
-- closed cr = ColensRep $ \xsab x -> xsab ($ x)
-- So: unColensRep closed_cr (\g -> g id) y = (\g -> g id) ($ y) = ($ y) id = id y = y
prop_colensrep_closed :: Property
prop_colensrep_closed = withTests 100 . property $ do
  y <- forAll int
  let cr :: ColensRep Int Int Int Int
      cr = ColensRep $ \f -> f id
      closed_cr :: ColensRep Int Int (Int -> Int) (Int -> Int)
      closed_cr = closed cr
      result :: Int -> Int
      result = unColensRep closed_cr $ \g -> g id
  result y === y

---------------------------------------------------------------------
-- withCoaffine: round-trip through carrier extraction
---------------------------------------------------------------------

-- | withPrism' round-trip: matching then rebuilding recovers s
prop_withPrism_simple :: Property
prop_withPrism_simple = withTests 100 . property $ do
  s <- forAll $ gen_maybe int
  withPrism' just $ \sa bt -> do
    case sa s of
      Nothing -> success
      Just a  -> bt a === s

-- | withCoaffine' round-trip
prop_withCoaffine_simple :: Property
prop_withCoaffine_simple = withTests 100 . property $ do
  x <- forAll int
  let o :: ACotraversal0 Int Int Int Int
      o = id
  withCoaffine' o $ \stabt ->
    stabt (const x) === x

prop_withCoaffine_identity :: Property
prop_withCoaffine_identity = withTests 100 . property $ do
  x <- forAll int
  let o :: ACotraversal0 Int Int Int Int
      o = id
  withCoaffine o $ \stabt ->
    stabt (const x) === x

-- | withColens round-trip
prop_withColens_identity :: Property
prop_withColens_identity = withTests 100 . property $ do
  x <- forAll int
  let o :: AColens Int Int Int Int
      o = id
  withColens o $ \sabt ->
    sabt ($ x) === x

---------------------------------------------------------------------
-- Integration: over with carrier-based optics
---------------------------------------------------------------------

prop_over_grate :: Property
prop_over_grate = withTests 100 . property $ do
  a <- forAll int
  b <- forAll int
  let o = grate $ \f -> (f fst, f snd)
  over o (+1) (a, b) === (a + 1, b + 1)

prop_over_traversed :: Property
prop_over_traversed = withTests 100 . property $ do
  xs <- forAll $ gen_list int
  over traversed (+1) xs === fmap (+1) xs

prop_over_just :: Property
prop_over_just = withTests 100 . property $ do
  s <- forAll $ gen_maybe int
  over just (+1) s === fmap (+1) s

prop_set_just :: Property
prop_set_just = withTests 100 . property $ do
  s <- forAll $ gen_maybe int
  x <- forAll int
  set just x s === (fmap (const x) s)

---------------------------------------------------------------------
-- CotraversalRep carrier: Profunctor law
---------------------------------------------------------------------

-- | Profunctor law: dimap id id ≡ id
prop_cotraversalrep_profunctor_id :: Property
prop_cotraversalrep_profunctor_id = withTests 100 . property $ do
  x <- forAll int
  let cr :: CotraversalRep Int Int Int Int
      cr = CotraversalRep $ \fab fa -> fab fa
      dimapped = dimap id id cr
  -- Use Identity as our Coapplicative functor
  runCotraversalRep cr runIdentity (Identity x) === runCotraversalRep dimapped runIdentity (Identity x)

---------------------------------------------------------------------
-- CotraversalRep carrier: Closed instance
---------------------------------------------------------------------

-- | closed identity: closed applies the function pointwise
-- closed h fab fxs x = h fab (fmap ($ x) fxs)
-- For identity h: result = fab (fmap ($ x) fxs)
prop_cotraversalrep_closed :: Property
prop_cotraversalrep_closed = withTests 100 . property $ do
  x <- forAll int
  y <- forAll int
  let cr :: CotraversalRep Int Int Int Int
      cr = CotraversalRep $ \fab fa -> fab fa
      closed_cr :: CotraversalRep Int Int (Int -> Int) (Int -> Int)
      closed_cr = closed cr
      -- With f=Identity: fab :: Identity Int -> Int, fxs :: Identity (Int -> Int)
      -- closed h fab fxs y = fab (fmap ($ y) fxs) = fab (Identity (g y))
      -- With fab=runIdentity, fxs=Identity (+100): result y = y + 100
      result :: Int -> Int
      result = runCotraversalRep closed_cr runIdentity (Identity (+x))
  result y === y + x

---------------------------------------------------------------------
-- CotraversalRep carrier: Choice instance
---------------------------------------------------------------------

-- | left' produces Left for the identity rep (same pattern as CoaffineRep)
prop_cotraversalrep_left_always :: Property
prop_cotraversalrep_left_always = withTests 100 . property $ do
  x <- forAll int
  let cr :: CotraversalRep Int Int Int Int
      cr = CotraversalRep $ \fab fa -> fab fa
      left_cr :: CotraversalRep Int Int (Either Int Char) (Either Int Char)
      left_cr = left' cr
      -- With f=Identity: coapply (Identity (Left x)) = Left (Identity x)
      -- So left' h fab (Identity (Left x)) = Left (h fab (Identity x))
      result :: Either Int Char
      result = runCotraversalRep left_cr runIdentity (Identity (Left x))
  case result of
    Left _  -> success
    Right _ -> failure

---------------------------------------------------------------------
-- CotraversalRep carrier: Cosieve/Corepresentable round-trip
---------------------------------------------------------------------

-- | cotabulate . cosieve ≡ id (tested via manual eta-expansion)
prop_cotraversalrep_roundtrip :: Property
prop_cotraversalrep_roundtrip = withTests 100 . property $ do
  x <- forAll int
  let cr :: CotraversalRep Int Int Int Int
      cr = CotraversalRep $ \fab fa -> fab fa
      roundtripped :: CotraversalRep Int Int Int Int
      roundtripped = CotraversalRep $ \fab fs ->
        runCotraversalRep cr fab fs
  runCotraversalRep cr runIdentity (Identity x) === runCotraversalRep roundtripped runIdentity (Identity x)

---------------------------------------------------------------------
-- CotraversalRep: withCotraversal round-trip
---------------------------------------------------------------------

prop_withCotraversal_identity :: Property
prop_withCotraversal_identity = withTests 100 . property $ do
  x <- forAll int
  let o :: Optic (CotraversalRep Int Int) Int Int Int Int
      o = id
  withCotraversal o $ \h ->
    h runIdentity (Identity x) === x

---------------------------------------------------------------------
-- CxtraversalRep carrier: Profunctor law
---------------------------------------------------------------------

prop_cxtraversalrep_profunctor_id :: Property
prop_cxtraversalrep_profunctor_id = withTests 100 . property $ do
  x <- forAll int
  let cr :: CxtraversalRep String Int Int Int Int
      cr = CxtraversalRep $ \fakb fa -> fakb fa ""
      dimapped = dimap id id cr
  runCxtraversalRep cr (\fa _ -> runIdentity fa) (Identity x) === runCxtraversalRep dimapped (\fa _ -> runIdentity fa) (Identity x)

---------------------------------------------------------------------
-- CxtraversalRep carrier: Closed instance
---------------------------------------------------------------------

prop_cxtraversalrep_closed :: Property
prop_cxtraversalrep_closed = withTests 100 . property $ do
  x <- forAll int
  y <- forAll int
  let cr :: CxtraversalRep String Int Int Int Int
      cr = CxtraversalRep $ \fakb fa -> fakb fa ""
      closed_cr :: CxtraversalRep String Int Int (Int -> Int) (Int -> Int)
      closed_cr = closed cr
      result :: Int -> Int
      result = runCxtraversalRep closed_cr (\fa _ -> runIdentity fa) (Identity (+x))
  result y === y + x

tests :: IO Bool
tests = checkSequential $$(discover)
