{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}

-- | Left and right carriers are characterized by their representation
-- functors ('Rep' and 'Corep'). 'Iso' sits at the top where both
-- are trivial ('Identity'). 'Adjoint' sits at the bottom where they
-- form a full adjunction (@'Corep' p ⊣ 'Rep' p@). A left-indexed
-- ('Ix') optic threads an index through the left adjoint functor
-- @(,) k@, while a right-indexed ('Cx') optic threads a coindex
-- through the right adjoint functor @(->) k@.
module Data.Profunctor.Optic.Index (
    -- * Constructors
    -- ** Main
    ixmap
  , representing
  , ixrepresenting
    -- ** Dual
  , cxmap
  , corepresenting
  , cxrepresenting
    -- * Transforms
    -- ** Main
  , (%)
  , cxix
  , reix
  , ixsum
  , ixany
  , ixhead
  , ixlast
    -- ** Dual
  , (#)
  , ixcx
  , recx
  , cxsum
    -- ** Cx algebra
  , cxjoin
  , cxreturn
  , cxunit
  , cxstrength
  , cxpastro
    -- * Operators
    -- ** Main
  , ixover
  , reps
  , ixreps
    -- ** Dual
  , cxover
  , coreps
  , cxreps
) where


import Data.Profunctor.Strong (Pastro(..))
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Import
import qualified Data.Bifunctor as B
import qualified Data.Semigroup as S

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XRankNTypes
-- >>> import Data.Char
-- >>> import Data.Function ((&))
-- >>> import Data.Semigroup
-- >>> import qualified Data.Bifunctor as B
-- >>> import qualified Data.Map.Lazy as Map
-- >>> :load Data.Profunctor.Optic
-- >>> import Prelude

---------------------------------------------------------------------
-- Constructors
---------------------------------------------------------------------

-- ** Main

-- | 'dimap' for indexed optics. Maps over the outer types of an
-- 'Ixoptic' without affecting the index.
--
-- @since 0.0.3
ixmap :: Profunctor p => (s -> a) -> (b -> t) -> Ixoptic p k s t a b
ixmap sa bt = dimap (fmap sa) bt
{-# INLINE ixmap #-}

-- | TODO: Document
--
representing :: Representable p => ((a -> Rep p b) -> s -> Rep p t) -> Optic p s t a b
representing f = tabulate . f . sieve
{-# INLINE representing #-}

-- | TODO: Document
--
-- @since 0.0.3
ixrepresenting :: Representable p => ((i -> a -> Rep p b) -> s -> Rep p t) -> Ixoptic p i s t a b
ixrepresenting f = representing $ \ab -> f (curry ab) . snd
{-# INLINE ixrepresenting #-}

-- ** Dual

-- | 'dimap' for coindexed optics. Maps over the outer types of a
-- 'Cxoptic' without affecting the coindex.
--
-- @since 0.0.3
cxmap :: Profunctor p => (s -> a) -> (b -> t) -> Cxoptic p k s t a b
cxmap sa bt = dimap sa (fmap bt)
{-# INLINE cxmap #-}

-- | TODO: Document
--
corepresenting :: Corepresentable p => ((Corep p a -> b) -> Corep p s -> t) -> Optic p s t a b
corepresenting f = cotabulate . f . cosieve
{-# INLINE corepresenting #-}

-- | TODO: Document
--
-- @since 0.0.3
cxrepresenting :: Corepresentable p => ((i -> Corep p a -> b) -> Corep p s -> t) -> Cxoptic p i s t a b
cxrepresenting f = corepresenting $ \ab -> const . f (flip ab)
{-# INLINE cxrepresenting #-}

---------------------------------------------------------------------
-- Transforms
---------------------------------------------------------------------


-- ** Main

infixr 8 %

-- | Monoidally combine indices between subsequent levels of optic.
--
-- Its precedence is one lower than that of function composition, which allows /./ to be nested in /%/.
--
-- If you only need the final index then use /./.
--
-- >>> ixtoListOf (ix "*" traversed . ix "+" traversed) ["foo", "bar"]
-- [("",'f'),("+",'o'),("++",'o'),("",'b'),("+",'a'),("++",'r')]
-- >>> ixtoListOf (ix "*" traversed % ix "+" traversed) ["foo", "bar"]
-- [("",'f'),("+",'o'),("++",'o'),("*",'b'),("*+",'a'),("*++",'r')]
--
-- @since 0.0.3
(%) :: Monoid i => Representable p => Ixoptic p i c1 c2 b1 b2 -> Ixoptic p i b1 b2 a1 a2 -> Ixoptic p i c1 c2 a1 a2
f % g = ixrepresenting . runCoindex $ (Coindex . ixreps) f <<<< (Coindex . ixreps) g
{-# INLINE (%) #-}
{-
f % g = representing $ \ia1a2 (ic,c1) ->
          (fmap flip . flip . ixrepn) f ic c1 $ \ib b1 ->
            (fmap flip . flip . ixrepn) g ib b1 $ \ia a1 -> ia1a2 (ib <> ia, a1)
  where ixrepn o h = curry $ reps o $ uncurry h
-}

-- | Convert a coindexed optic to an indexed optic by uncurrying
-- the coindex.
--
-- @
-- 'Cx' p k a b  =  p a (k -> b)     — function coindex on the right
-- 'Ix' p k a b  =  p (k, a) b       — product index on the left
-- @
--
-- Requires both 'Closed' (to curry the input) and 'Strong' (to
-- uncurry the output). This means 'cxix' and 'ixcx' are only
-- usable with optics that are both 'Strong' and 'Closed' (e.g.
-- 'Iso'), reflecting the fact that currying and uncurrying are
-- inverse operations that each require one half of the duality.
--
cxix :: Strong p => Closed p => Cxoptic p k s t a b -> Ixoptic p k s t a b
cxix o pka_b =
  let pa_kb   = lmap (\a k -> (k, a)) (closed pka_b)   -- p (k,a) b  →  p a (k->b)
      ps_kt   = o pa_kb                                  -- p a (k->b) →  p s (k->t)
      psk_ktk = first' ps_kt                             -- p s (k->t) →  p (s,k) (k->t, k)
  in  dimap swap (\(f, k) -> f k) psk_ktk                -- p (s,k) (k->t, k) →  p (k,s) t
{-# INLINE cxix #-}

-- | Map over the indices of an indexed optic.
--
-- See also 'Data.Profunctor.Optic.Iso.reixed'.
--
-- @since 0.0.3
reix :: Profunctor p => (k1 -> k2) -> (k2 -> k1) -> Ixoptic p k1 s t a b -> Ixoptic p k2 s t a b
reix kl lk = (. lmap (first' kl)) . (lmap (first' lk) .)
{-# INLINE reix #-}

-- | Lift a numeric index into a sum monoid.
--
-- @since 0.0.3
ixsum :: Profunctor p => Ixoptic p k s t a b -> Ixoptic p (Sum k) s t a b
ixsum = reix Sum getSum
{-# INLINE ixsum #-}

-- | TODO: Document
--
ixany :: Profunctor p => Ixoptic p Bool s t a b -> Ixoptic p Any s t a b
ixany = reix Any getAny
{-# INLINE ixany #-}

-- | TODO: Document
--
-- @since 0.0.3
ixhead :: Profunctor p => Ixoptic p i s t a b -> Ixoptic p (S.First i) s t a b
ixhead = reix S.First S.getFirst

-- | TODO: Document
--
-- @since 0.0.3
ixlast :: Profunctor p => Ixoptic p i s t a b -> Ixoptic p (S.Last i) s t a b
ixlast = reix S.Last S.getLast

-- ** Dual

infixr 8 #

-- | Compose two coindexed traversals, combining indices.
--
-- Its precedence is one lower than that of function composition, which allows /./ to be nested in /#/.
--
-- If you only need the final index then use /./.
--
-- >>> cxfoldMapOf (cxfrom Map.mapWithKey # cxfrom Map.mapWithKey) (\k r a -> Map.singleton k (a + r)) 1.0 $ Map.fromList [("k",Map.fromList [("l",2.0)])]
-- fromList [("k",fromList [("l",fromList [("kl",3.0)])])]
--
-- @since 0.0.3
(#) :: Monoid i => Corepresentable p => Cxoptic p i c1 c2 b1 b2 -> Cxoptic p i b1 b2 a1 a2 -> Cxoptic p i c1 c2 a1 a2
f # g = cxrepresenting . runCoindex $ (Coindex . cxreps) f <<<< (Coindex . cxreps) g
{-
f # g = corepresenting $ \a1ka2 c1 kc ->
          (fmap flip . flip . cxrepn) f kc c1 $ \kb b1 ->
            (fmap flip . flip . cxrepn) g kb b1 $ \ka a1 -> a1ka2 a1 (kb <> ka)
  where cxrepn o f = flip $ coreps o $ flip f
{-# INLINE (#) #-}
-}

-- | Convert an indexed optic to a coindexed optic by currying
-- the index.
--
-- @
-- 'ixcx' :: ('Closed' p, 'Strong' p) => 'Ixoptic' p k s t a b -> 'Cxoptic' p k s t a b
-- @
--
-- 'ixcx' requires 'Closed' on @p@ to introduce the function space
-- @(k -> b)@ from the product @(k, a)@, and 'Strong' for the
-- reverse direction on the input. These are the Ix\/Cx analogues
-- of 'co' and 're' at the index level — currying and uncurrying
-- move the index between a product on the left and a function on
-- the right.
--
-- Note: both 'cxix' and 'ixcx' require /both/ 'Strong' and 'Closed',
-- because each must convert in both directions (once for the input,
-- once for the output of the optic). This means they are only usable
-- with optics that are both 'Strong' and 'Closed' — i.e., 'Iso'-like
-- optics. This is a genuine limitation: you cannot curry an 'Ixlens'
-- into a 'Cxlens' because 'Ixlens' requires 'Strong' but not 'Closed'.
--
ixcx :: Strong p => Closed p => Ixoptic p k s t a b -> Cxoptic p k s t a b
ixcx o pa_kb =
  let pka_b   = dimap swap (\(f, k) -> f k) (first' pa_kb)  -- p a (k->b)  →  p (k,a) b
      pks_t   = o pka_b                                       -- p (k,a) b   →  p (k,s) t
      ps_kt   = lmap (\s k -> (k, s)) (closed pks_t)          -- p (k,s) t   →  p s (k->t)
  in  ps_kt
{-# INLINE ixcx #-}

-- | Map over the indices of a coindexed optic.
--
-- See also 'Data.Profunctor.Optic.Iso.recxed'.
--
-- @since 0.0.3
recx :: Profunctor p => (k1 -> k2) -> (k2 -> k1) -> Cxoptic p k1 s t a b -> Cxoptic p k2 s t a b
recx kl lk = (. rmap (. kl)) . (rmap (. lk) .)
{-# INLINE recx #-}

-- | Lift a numeric co-index into a sum monoid.
--
-- @since 0.0.3
cxsum :: Profunctor p => Cxoptic p k s t a b -> Cxoptic p (Sum k) s t a b
cxsum = recx Sum getSum
{-# INLINE cxsum #-}

-- | Collapse a coindexed profunctor where the coindex matches the focus.
--
-- @'cxjoin' ≡ 'dimap' 'fork' 'apply' '.' 'first''@
--
cxjoin :: Strong p => Cx p a a b -> p a b
cxjoin = dimap fork apply . first'

-- | Lift a profunctor into a coindexed profunctor by ignoring the coindex.
--
cxreturn :: Profunctor p => p a b -> Cx p k a b
cxreturn = rmap const

-- | Extract a profunctor from a self-coindexed profunctor.
--
-- @'cxjoin' '.' 'cxunit' ≡ 'id'@
--
cxunit :: Strong p => Cx' p a b -> p a b
cxunit p = dimap fork apply (first' p)

-- | 'Cx'' is freely 'Strong'.
--
-- See <https://r6research.livejournal.com/27858.html>.
--
cxstrength :: Profunctor p => Cx' p a b -> Cx' p (a, c) (b, c)
cxstrength = dimap fst (B.first @(,))

-- | Witness that self-coindexing is isomorphic to freely adjoining 'Strong'.
--
-- @
-- 'Cx'' p a b = p a (a -> b)     — self-coindexed profunctor
-- 'Pastro' p a b                 — free 'Strong' on p
-- @
--
-- The forward direction packs @p a (a -> b)@ into @Pastro apply p fork@.
-- The backward direction unpacks @Pastro l m r@ by composing with the
-- projections.
--
-- This iso witnesses a deep connection between the index\/coindex
-- layer and the Strong\/Closed duality: 'Cx'' is the function-space
-- presentation of the same structure that 'Pastro' presents via
-- products. See also "Data.Profunctor.Optic.Dual" for the 'Co' type,
-- which is the analogous free 'Closed' construction.
--
cxpastro :: Profunctor p => Iso (Cx' p a b) (Cx' p c d) (Pastro p a b) (Pastro p c d)
cxpastro = dimap (\p -> Pastro apply p fork) (\(Pastro l m r) -> dimap (fst . r) (\y a -> l (y, (snd (r a)))) m)

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- ** Main

-- | Indexed 'over': apply a key-dependent function through an indexed optic.
--
-- Routes through 'Conjoin' wrapping internally.
--
-- /Benchmark: 1.08x vs direct mapWithKey (Conjoin overhead negligible). See "Data.Profunctor.Optic.Bench"./
--
-- @since 0.0.3
ixover :: Monoid i => Ixoptic (->) i s t a b -> (i -> a -> b) -> s -> t
ixover o f = (unConjoin #. corepresenting o .# Conjoin) f mempty
{-# INLINE ixover #-}

-- | TODO: Document
--
reps :: Representable p => Optic p s t a b -> ((a -> Rep p b) -> s -> Rep p t)
reps o = sieve . o . tabulate
{-# INLINE reps #-}

-- | TODO: Document
--
-- @since 0.0.3
ixreps :: Representable p => Monoid i => Ixoptic p i s t a b -> (i -> a -> Rep p b) -> s -> Rep p t
ixreps o f = curry (reps o $ uncurry f) mempty
{-# INLINE ixreps #-}

-- ** Dual

-- | Coindexed 'over': apply a coindex-dependent function through a coindexed optic.
--
-- Routes through 'Conjoin' wrapping internally (dual of 'overWithKey').
--
-- /Benchmark: ~1.08x overhead (same Conjoin path as 'overWithKey'). See "Data.Profunctor.Optic.Bench"./
--
-- @since 0.0.3
cxover :: Monoid i => Cxoptic (->) i s t a b -> (i -> a -> b) -> s -> t
cxover o f = (unConjoin #. representing o .# Conjoin) f mempty
{-# INLINE cxover #-}

-- | TODO: Document
--
coreps :: Corepresentable p => Optic p s t a b -> ((Corep p a -> b) -> Corep p s -> t)
coreps o = cosieve . o . cotabulate
{-# INLINE coreps #-}

-- | TODO: Document
--
-- @since 0.0.3
cxreps :: Corepresentable p => Monoid i => Cxoptic p i s t a b -> (i -> Corep p a -> b) -> Corep p s -> t
cxreps o f = flip (coreps o $ flip f) mempty
{-# INLINE cxreps #-}
