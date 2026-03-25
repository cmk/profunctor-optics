{-# LANGUAGE FlexibleContexts    #-}
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
import Data.Profunctor.Optic.Index (cxix, ixcx)
import Data.Profunctor.Optic.Lens (grate, lensVl, ixlens, relens, refirst)
import Data.Profunctor.Optic.Prism (just, reprism, releft, ixjust)
import Data.Profunctor.Optic.Traversal (traversed, ix, cotraverseOf, cloneCotraversal0)
import Data.Monoid (Sum(..))
import Data.Profunctor.Optic.Setter (set, adjoint, ixadjoint, cosets)
import Data.Profunctor.Optic.Fold (acofold, cofoldMapOf)
import Data.Map.Optic as MapO
import Data.IntMap.Optic as IMO
import Data.Sequence.Optic as SeqO
import qualified Data.Map.Strict as Map
import qualified Data.IntMap.Strict as IM
import qualified Data.Sequence as Seq
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
-- Ixlens
---------------------------------------------------------------------

prop_ixlens_tofrom :: Property
prop_ixlens_tofrom = withTests 100 . property $ do
  s <- forAll $ gen_pair int char
  assert $ Prop.tofrom_ixlens (ixlens (\(a,b) -> ((), a)) (\(_,b) a -> (a,b))) s

prop_ixlens_fromto :: Property
prop_ixlens_fromto = withTests 100 . property $ do
  s <- forAll $ gen_pair int char
  a <- forAll int
  assert $ Prop.fromto_ixlens (ixlens (\(a,b) -> ((), a)) (\(_,b) a -> (a,b))) s a

prop_ixlens_idempotent :: Property
prop_ixlens_idempotent = withTests 100 . property $ do
  s <- forAll $ gen_pair int char
  a1 <- forAll int
  a2 <- forAll int
  assert $ Prop.idempotent_ixlens (ixlens (\(a,b) -> ((), a)) (\(_,b) a -> (a,b))) s a1 a2

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

-- Identity reprism: reprism id Right :: Reprism' Int Int
-- The simplest lawful Reprism'. releft/reright diverge at simple
-- types because forgetr loops on values outside the matched branch.

prop_reprism_tofrom :: Property
prop_reprism_tofrom = withTests 100 . property $ do
  a <- forAll int
  assert $ Prop.tofrom_reprism (reprism id Right :: Reprism' Int Int) a

prop_reprism_fromto :: Property
prop_reprism_fromto = withTests 100 . property $ do
  s <- forAll int
  assert $ Prop.fromto_reprism (reprism id Right :: Reprism' Int Int) s

prop_reprism_idempotent :: Property
prop_reprism_idempotent = withTests 100 . property $ do
  a <- forAll int
  assert $ Prop.idempotent_reprism (reprism id Right :: Reprism' Int Int) a

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
-- Traversal
---------------------------------------------------------------------

prop_traversal_id :: Property
prop_traversal_id = withTests 100 . property $ do
  xs <- forAll $ gen_list int
  assert $ Prop.id_traversal traversed xs

prop_traversal_compose :: Property
prop_traversal_compose = withTests 100 . property $ do
  xs <- forAll $ gen_list int
  assert $ Prop.compose_traversal traversed (Identity . (+1)) (Identity . (*2)) xs

---------------------------------------------------------------------
-- Ixtraversal
---------------------------------------------------------------------

prop_ixtraversal_id :: Property
prop_ixtraversal_id = withTests 100 . property $ do
  xs <- forAll $ gen_list int
  assert $ Prop.id_ixtraversal (ix (Sum 1) traversed) xs

---------------------------------------------------------------------
-- Cosetter
---------------------------------------------------------------------

prop_cosetter_id :: Property
prop_cosetter_id = withTests 100 . property $ do
  s <- forAll $ gen_pair int int
  assert $ Prop.id_cosetter (grate $ \f -> (f fst, f snd)) s

prop_cosetter_compose :: Property
prop_cosetter_compose = withTests 100 . property $ do
  s <- forAll $ gen_pair int int
  assert $ Prop.compose_cosetter (grate $ \f -> (f fst, f snd)) (+1) (*2) s

---------------------------------------------------------------------
-- Cotraversal0Rep carrier: Profunctor law
---------------------------------------------------------------------

-- | Profunctor law: dimap id id ≡ id
prop_coaffinerep_profunctor_id :: Property
prop_coaffinerep_profunctor_id = withTests 100 . property $ do
  x <- forAll int
  let cr :: Cotraversal0Rep Int Int Int Int
      cr = Cotraversal0Rep $ \f -> f Right
      dimapped = dimap id id cr
  unCotraversal0Rep cr (const x) === unCotraversal0Rep dimapped (const x)

---------------------------------------------------------------------
-- Cotraversal0Rep carrier: Choice instance (left-unit law)
---------------------------------------------------------------------

-- | left-unit law: lmap Left . left' ≡ rmap Left
-- Both sides: Cotraversal0Rep Int Int Int (Either Int c)
-- We test by running with the same callback and comparing results.
prop_coaffinerep_left_unit :: Property
prop_coaffinerep_left_unit = withTests 100 . property $ do
  x <- forAll int
  let cr :: Cotraversal0Rep Int Int Int Int
      cr = Cotraversal0Rep $ \f -> f Right
      -- lhs: lmap Left . left'
      -- left' cr :: Cotraversal0Rep Int Int (Either Int c) (Either Int c)
      -- lmap Left :: ... -> Cotraversal0Rep Int Int Int (Either Int c)
      lhs :: Int
      lhs = case unCotraversal0Rep (lmap Left (left' cr)) (\g -> case g x of { Left (Left n) -> n; Left (Right _) -> -999; Right n -> n + 1000 }) of
              Left n -> n
              Right _ -> -888
      -- rhs: rmap Left
      -- rmap Left cr :: Cotraversal0Rep Int Int Int (Either Int c)
      rhs :: Int
      rhs = case unCotraversal0Rep (rmap (Left @Int @Char) cr) (\g -> case g x of { Left (Left n) -> n; Left (Right _) -> -999; Right n -> n + 1000 }) of
              Left n -> n
              Right _ -> -888
  lhs === rhs

---------------------------------------------------------------------
-- Cotraversal0Rep carrier: left' always produces Left
---------------------------------------------------------------------

prop_coaffinerep_left_always :: Property
prop_coaffinerep_left_always = withTests 100 . property $ do
  x <- forAll int
  let cr :: Cotraversal0Rep Int Int Int Int
      cr = Cotraversal0Rep $ \f -> f Right
      left_cr :: Cotraversal0Rep Int Int (Either Int Char) (Either Int Char)
      left_cr = left' cr
      result :: Either Int Char
      result = unCotraversal0Rep left_cr $ \sta -> case sta (Left x) of
        Left (Left t) -> t
        Left (Right _) -> -888
        Right a -> a + 1000
  case result of
    Left _  -> success
    Right _ -> failure

---------------------------------------------------------------------
-- Cotraversal0Rep carrier: Closed instance
---------------------------------------------------------------------

-- | closed instance: closed cr = Cotraversal0Rep $ \f x -> f (\xs -> Right (xs x))
-- The identity Cotraversal0Rep through closed should give back the value via const.
-- unCotraversal0Rep closed_cr f y = f (\xs -> Right (xs y))
-- With f = \sta -> case sta (const x) of Right a -> a:
--   sta (const x) = Right (const x y) = Right x  =>  result = x
prop_coaffinerep_closed :: Property
prop_coaffinerep_closed = withTests 100 . property $ do
  x <- forAll int
  y <- forAll int
  let cr :: Cotraversal0Rep Int Int Int Int
      cr = Cotraversal0Rep $ \f -> f Right
      closed_cr :: Cotraversal0Rep Int Int (Int -> Int) (Int -> Int)
      closed_cr = closed cr
      result :: Int -> Int
      result = unCotraversal0Rep closed_cr $ \sta ->
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
-- withCotraversal0: round-trip through carrier extraction
---------------------------------------------------------------------

-- | withPrism' round-trip: matching then rebuilding recovers s
prop_withPrism_simple :: Property
prop_withPrism_simple = withTests 100 . property $ do
  s <- forAll $ gen_maybe int
  withPrism' just $ \sa bt -> do
    case sa s of
      Nothing -> success
      Just a  -> bt a === s

-- | withCotraversal0' round-trip
prop_withCotraversal0_simple :: Property
prop_withCotraversal0_simple = withTests 100 . property $ do
  x <- forAll int
  let o :: ACotraversal0 Int Int Int Int
      o = id
  withCotraversal0' o $ \stabt ->
    stabt (const x) === x

prop_withCotraversal0_identity :: Property
prop_withCotraversal0_identity = withTests 100 . property $ do
  x <- forAll int
  let o :: ACotraversal0 Int Int Int Int
      o = id
  withCotraversal0 o $ \stabt ->
    stabt (const x) === x

-- | cloneCotraversal0 round-trip: clone then run should give same result
prop_cloneCotraversal0_roundtrip :: Property
prop_cloneCotraversal0_roundtrip = withTests 100 . property $ do
  x <- forAll int
  let o :: ACotraversal0 Int Int Int Int
      o = id
      cloned = cloneCotraversal0 o
  withCotraversal0 cloned $ \stabt ->
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

-- | left' produces Left for the identity rep (same pattern as Cotraversal0Rep)
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
-- CotraversalRep: withCotraversalVl round-trip
---------------------------------------------------------------------

prop_withCotraversalVl_identity :: Property
prop_withCotraversalVl_identity = withTests 100 . property $ do
  x <- forAll int
  let o :: Optic (CotraversalRep Int Int) Int Int Int Int
      o = id
  withCotraversalVl o $ \h ->
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

---------------------------------------------------------------------
-- Cofold: validates Coaffine (Closed + Choice) constraint fix
---------------------------------------------------------------------

-- | cofoldMapOf identity law.
-- Uses acofold (concrete carrier) to exercise the Cofold path.
prop_cofold_id :: Property
prop_cofold_id = withTests 100 . property $ do
  x <- forAll int
  let o :: ACofold Int Int Int
      o = acofold id
  Prop.id_cofold o x === True

-- | cofoldMapOf composition law.
prop_cofold_compose :: Property
prop_cofold_compose = withTests 100 . property $ do
  x <- forAll int
  let o :: ACofold Int Int Int
      o = acofold id
  Prop.compose_cofold o (+1) (*2) x === True

---------------------------------------------------------------------
-- Re/Co duality
---------------------------------------------------------------------

-- | re . re ≡ id on an Iso
prop_re_involutive :: Property
prop_re_involutive = withTests 100 . property $ do
  s <- forAll int
  a <- forAll int
  let o :: Iso' Int Int
      o = iso (+1) (subtract 1)
  assert $ Prop.involutive_re o s a

-- | cxjoin . cxreturn ≡ id
prop_cxreturn_cxjoin :: Property
prop_cxreturn_cxjoin = withTests 100 . property $ do
  a <- forAll int
  assert $ Prop.cxreturn_cxjoin (+1) a

-- | cxunit . cxreturn ≡ id
prop_cxreturn_cxunit :: Property
prop_cxreturn_cxunit = withTests 100 . property $ do
  a <- forAll int
  assert $ Prop.cxreturn_cxunit (+1) a

-- | ixcx . cxix ≡ id on an Iso-like Cxoptic at (->)
prop_roundtrip_ixcx :: Property
prop_roundtrip_ixcx = withTests 100 . property $ do
  s <- forAll int
  k <- forAll char
  -- A simple Cxoptic at (->): maps over values, ignoring coindex
  let o :: Cxoptic (->) Char Int Int Int Int
      o akb s k1 = akb (s + 1) k1 - 1
  assert $ Prop.roundtrip_ixcx o (\a _k -> a * 2) s k

-- | cxix . ixcx ≡ id on an Iso-like Ixoptic at (->)
prop_roundtrip_cxix :: Property
prop_roundtrip_cxix = withTests 100 . property $ do
  s <- forAll int
  k <- forAll char
  -- A simple Ixoptic at (->): maps over values, ignoring index
  let o :: Ixoptic (->) Char Int Int Int Int
      o kab (k1, s) = kab (k1, s + 1) - 1
  assert $ Prop.roundtrip_cxix o (\(_k, a) -> a * 2) (k, s)

---------------------------------------------------------------------
-- Ixprism properties
---------------------------------------------------------------------

prop_ixprism_tofrom :: Property
prop_ixprism_tofrom = withTests 100 . property $ do
  s <- forAll (gen_maybe int)
  assert $ Prop.tofrom_ixprism (ixjust @(Sum Int)) s

prop_ixprism_fromto :: Property
prop_ixprism_fromto = withTests 100 . property $ do
  a <- forAll int
  assert $ Prop.fromto_ixprism (ixjust @(Sum Int)) a

prop_ixprism_idempotent :: Property
prop_ixprism_idempotent = withTests 100 . property $ do
  s <- forAll (gen_maybe int)
  assert $ Prop.idempotent_ixprism (ixjust @(Sum Int)) s

---------------------------------------------------------------------
-- Adjoint properties
---------------------------------------------------------------------

-- A simple Adjoint: fmapped, which is an Adjoint for any Functor
-- (satisfies Adjoining at Conjoin and (->)).
-- We use it on pairs since (,) c is a Functor.
adj_snd :: Adjoint' (Int, Int) Int
adj_snd = adjoint fmap

prop_adjoint_id :: Property
prop_adjoint_id = withTests 100 . property $ do
  s <- forAll $ gen_pair int int
  assert $ Prop.id_adjoint adj_snd s

prop_adjoint_compose :: Property
prop_adjoint_compose = withTests 100 . property $ do
  s <- forAll $ gen_pair int int
  assert $ Prop.compose_adjoint adj_snd (+1) (*2) s

prop_adjoint_idempotent :: Property
prop_adjoint_idempotent = withTests 100 . property $ do
  s <- forAll $ gen_pair int int
  a <- forAll int
  b <- forAll int
  assert $ Prop.idempotent_adjoint adj_snd s a b

prop_adjoined_id :: Property
prop_adjoined_id = withTests 100 . property $ do
  a <- forAll int
  assert $ Prop.id_adjoined (+1) a

---------------------------------------------------------------------
-- Adjoint Ix/Cx duality
---------------------------------------------------------------------

prop_roundtrip_ixadjoining :: Property
prop_roundtrip_ixadjoining = withTests 100 . property $ do
  s <- forAll int
  k <- forAll char
  -- A Cxoptic at Conjoin (): \akb s k -> akb (s+1) k - 1
  let o :: Cxoptic (Conjoin ()) Char Int Int Int Int
      o (Conjoin f) = Conjoin $ \() s k -> f () (s + 1) k - 1
  assert $ Prop.roundtrip_ixadjoining o (\a _k -> a * 2) s k

prop_roundtrip_cxadjoining :: Property
prop_roundtrip_cxadjoining = withTests 100 . property $ do
  s <- forAll int
  k <- forAll char
  -- An Ixoptic at Conjoin (): \kab (k,s) -> kab (k, s+1) - 1
  let o :: Ixoptic (Conjoin ()) Char Int Int Int Int
      o (Conjoin f) = Conjoin $ \() (k1, s) -> f () (k1, s + 1) - 1
  assert $ Prop.roundtrip_cxadjoining o (\(_k, a) -> a * 2) (k, s)

---------------------------------------------------------------------
-- Sort-Conjoin bridge
---------------------------------------------------------------------

prop_retract_embedSort :: Property
prop_retract_embedSort = withTests 100 . property $ do
  k <- forAll char
  a <- forAll int
  let c :: Conjoin Char Int Int
      c = Conjoin $ \k1 n -> n + fromEnum k1
  assert $ Prop.retract_embedSort c k a

---------------------------------------------------------------------
-- Container Cx optic properties (S21.19–S21.21)
---------------------------------------------------------------------

gen_map :: Gen (Map.Map (Sum Int) Int)
gen_map = Map.fromList <$> G.list (R.linear 0 10) ((,) <$> (Sum <$> int) <*> int)

gen_intmap :: Gen (IM.IntMap Int)
gen_intmap = IM.fromList <$> G.list (R.linear 0 10) ((,) <$> int <*> int)

gen_seq :: Gen (Seq.Seq Int)
gen_seq = Seq.fromList <$> G.list (R.linear 0 10) int

-- Map Cxsetter
prop_map_cxmapped_id :: Property
prop_map_cxmapped_id = withTests 100 . property $ do
  m <- forAll gen_map
  assert $ Prop.id_cxsetter MapO.cxmapped m

prop_map_cxmapped_compose :: Property
prop_map_cxmapped_compose = withTests 100 . property $ do
  m <- forAll gen_map
  assert $ Prop.compose_cxsetter MapO.cxmapped (+1) (*2) m

-- IntMap Cxsetter (cosets on Cxsetter gives (a -> k -> b) -> s -> k -> t,
-- so we use const to ignore the key and evaluate at 0)
prop_intmap_cxmapped_id :: Property
prop_intmap_cxmapped_id = withTests 100 . property $ do
  m <- forAll gen_intmap
  cosets IMO.cxmapped (const . id) m 0 === m

prop_intmap_cxmapped_compose :: Property
prop_intmap_cxmapped_compose = withTests 100 . property $ do
  m <- forAll gen_intmap
  ((\s -> cosets IMO.cxmapped (const . (+1)) s 0) . (\s -> cosets IMO.cxmapped (const . (*2)) s 0)) m
    === cosets IMO.cxmapped (const . ((+1) . (*2))) m 0

-- Seq Cxsetter
prop_seq_cxmapped_id :: Property
prop_seq_cxmapped_id = withTests 100 . property $ do
  s <- forAll gen_seq
  cosets SeqO.cxmapped (const . id) s 0 === s

prop_seq_cxmapped_compose :: Property
prop_seq_cxmapped_compose = withTests 100 . property $ do
  s <- forAll gen_seq
  ((\q -> cosets SeqO.cxmapped (const . (+1)) q 0) . (\q -> cosets SeqO.cxmapped (const . (*2)) q 0)) s
    === cosets SeqO.cxmapped (const . ((+1) . (*2))) s 0

-- Map Cxsetter via cosets (ignoring key, same as Cosetter id law)
prop_map_cxmapped_cosets_id :: Property
prop_map_cxmapped_cosets_id = withTests 100 . property $ do
  m <- forAll gen_map
  cosets MapO.cxmapped (const . id) m (Sum 0) === m

tests :: IO Bool
tests = checkSequential $$(discover)
