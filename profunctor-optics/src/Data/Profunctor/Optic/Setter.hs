{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
module Data.Profunctor.Optic.Setter (
    -- * Constructors
    -- ** Setter, Ixsetter
    Setter, Setter'
  , Ixsetter, Ixsetter'
  , setter
  , ixsetter
  , closing
  , cloneSetter
  , cloneIxsetter
    -- ** Setter1, Ixsetter1
  , Setter1, Setter1'
  , Ixsetter1, Ixsetter1'
  , setter1
  , ixsetter1
    -- * Adjoint Constructors
    -- ** Adjoint, Ixadjoint, Cxadjoint
  , Adjoint, Adjoint'
  , Ixadjoint, Ixadjoint'
  , Cxadjoint, Cxadjoint'
  , adjoint
  , ixadjoint
  , adjointl
  , adjointr
    -- * Dual Constructors
    -- ** Cosetter, Cxsetter
  , Cosetter, Cosetter'
  , Cxsetter, Cxsetter'
  , cosetter
  , cxsetter
  , cloneCosetter
  , cloneCxsetter
    -- ** Cosetter1, Cxsetter1
  , Cosetter1, Cosetter1'
  , Cxsetter1, Cxsetter1'
  , cosetter1
  , cxsetter1
    -- * Optics
    -- ** Setter, Ixsetter
  , fmapped
  , contramapped
  , imappedRep
  , domain
  , codomain
  , liftedM
  , liftedA
  , forwarded
  , censored
  , zipped
  , modded
  , conditioned
    -- ** Setter1, Ixsetter1
    -- * Adjoint Optics
  , adjoined
  , mappedException
    -- * Adjoint Operators
  , lifts
  , lowers
  , alower
  , aupper
    -- * Ix\/Cx adjunction transforms
  , ixadjoining
  , cxadjoining
    -- * Sort-Conjoin bridge
  , absorbSort
  , embedSort
  , sortCosort
    -- * Dual Optics
    -- ** Cosetter, Cxsetter
    -- ** Cosetter1, Cxsetter1
  , coliftedA
  , coliftedF
  , zipListed
    -- * Operators
    -- ** Setter, Ixsetter
  , set
  , ixset
  , sets
  , ixsets
  , over
  , ixover
    -- ** Setter1, Ixsetter1
    -- * Dual Operators
    -- ** Cosetter, Cxsetter
  , coset
  , cxset
  , cosets
  , cxsets
  , cxover
    -- ** Cosetter1, Cxsetter1
    -- * MTL
  , assigns
  , ixassigns
  , modifies
  , ixmodifies
  , localizes
  , tells
    -- * Re-exports
) where

import Control.Applicative (liftA,ZipList(..))
import Control.Exception (Exception)
import Control.Monad.Reader as Reader
import Control.Monad.State as State
import Control.Monad.Writer as Writer
import Data.Functor.Adjunction
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Sort (Sort(..), Cosort(..))
import Data.Profunctor.Optic.Import hiding ((&&&))
import Data.Profunctor.Optic.Index
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Iso (indexing,coindexing)
import Data.Profunctor.Optic.Traversal
import qualified Control.Exception as Ex
import qualified Data.Functor.Rep as F

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XRankNTypes
-- >>> import Control.Category ((>>>))
-- >>> import Control.Arrow (Kleisli(..))
-- >>> import Control.Monad.State
-- >>> import Control.Monad.Reader
-- >>> import Control.Monad.Writer
-- >>> import Data.Bool (bool)
-- >>> import Data.Complex
-- >>> import Data.Function ((&))
-- >>> import Data.Functor.Rep
-- >>> import Data.Functor.Identity
-- >>> import Data.Functor.Contravariant
-- >>> import Data.Semigroup
-- >>> import Data.Tuple (swap)
-- >>> :load Data.Profunctor.Optic
-- >>> import Prelude

---------------------------------------------------------------------
-- Constructors
---------------------------------------------------------------------

-- | Obtain a 'Setter' from a <http://conal.net/blog/posts/semantic-editor-combinators SEC>.
--
-- To demote an optic to a semantic edit combinator, use the section @(l ..~)@ or @over l@.
--
-- >>> [("The",0),("quick",1),("brown",1),("fox",2)] & setter fmap . first' ..~ Prelude.length
-- [(3,0),(5,1),(5,1),(3,2)]
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input function satisfies the following
-- properties:
--
-- * @abst id ≡ id@
--
-- * @abst f . abst g ≡ abst (f . g)@
--
-- More generally, a profunctor optic must be monoidal as a natural
-- transformation:
--
-- * @o id ≡ id@
--
-- * @o ('Data.Profunctor.Composition.Procompose' p q) ≡ 'Data.Profunctor.Composition.Procompose' (o p) (o q)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
setter :: ((a -> b) -> s -> t) -> Setter s t a b
setter abst = indexing abst . representing (\f -> distribute . fmap f)
{-# INLINE setter #-}

-- | Build an 'Ixsetter' from an indexed function.
--
-- @
-- 'ixsetter' '.' 'ixsets' ≡ 'id'
-- 'ixsets' '.' 'ixsetter' ≡ 'id'
-- @
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @iabst (const id) ≡ id@
--
-- * @fmap (iabst $ const f) . (iabst $ const g) ≡ iabst (const $ f . g)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- @since 0.0.3
ixsetter :: ((i -> a -> b) -> s -> t) -> Ixsetter i s t a b
ixsetter f = setter $ \iab -> f (curry iab) . snd
{-# INLINE ixsetter #-}

-- | Every valid 'Colens' is a 'Setter'.
--
closing :: (((s -> a) -> b) -> t) -> Setter s t a b
closing sabt = setter $ \ab s -> sabt $ \sa -> ab (sa s)
{-# INLINE closing #-}

-- | Clone a 'Setter'.
--
cloneSetter :: ASetter s t a b -> Setter s t a b
cloneSetter o = setter (sets o)
{-# INLINE cloneSetter #-}

-- | Clone an 'Ixsetter'.
--
cloneIxsetter :: Monoid k => AIxsetter k s t a b -> Ixsetter k s t a b
cloneIxsetter o = ixsetter (ixsets o)
{-# INLINE cloneIxsetter #-}

---------------------------------------------------------------------
-- Setter1
---------------------------------------------------------------------

-- | TODO: Document
--
-- @since 0.0.3
setter1 :: ((a -> b) -> a -> t) -> Setter1 a t a b
setter1 abst = indexing abst . representing (\f -> distribute1 . fmap f)
{-# INLINE setter1 #-}

-- | Build an 'Ixsetter1' from an indexed function.
--
-- @since 0.0.3
ixsetter1 :: ((i -> a -> b) -> a -> t) -> Ixsetter1 i a t a b
ixsetter1 f = setter1 $ \iab -> f (curry iab) . snd
{-# INLINE ixsetter1 #-}

---------------------------------------------------------------------
-- Adjoint Constructors
---------------------------------------------------------------------

-- | Obtain an 'Adjoint' from a
-- <http://conal.net/blog/posts/semantic-editor-combinators SEC>.
--
-- @
-- 'adjoint' abst ≡ 'adjointl' ('Data.Functor.Adjunction.rightAdjunct' abst)
-- 'adjoint' abst ≡ 'adjointr' ('Data.Functor.Adjunction.leftAdjunct' abst)
-- @
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input function satisfies the following
-- properties:
--
-- * @abst id ≡ id@
--
-- * @abst f . abst g ≡ abst (f . g)@
--
adjoint :: ((a -> b) -> s -> t) -> Adjoint s t a b
adjoint abst = indexing abst . representing (\f -> distribute . fmap f)
{-# INLINE adjoint #-}

-- | Build an 'Ixadjoint' from an indexed function.
--
-- @
-- 'ixadjoint' '.' 'ixsets' ≡ 'id'
-- 'ixsets' '.' 'ixadjoint' ≡ 'id'
-- @
--
ixadjoint :: ((i -> a -> b) -> s -> t) -> Ixadjoint i s t a b
ixadjoint f = adjoint $ \iab -> f (curry iab) . snd
{-# INLINE ixadjoint #-}

-- | Construct an 'Adjoint' from a Costar-side Van Laarhoven function.
--
-- @
-- 'adjointl' f = 'corepresenting' (f '.' 'leftAdjunct')
-- @
--
-- For each 'Adjoining' profunctor @p@ with @'Corep' p = l@ and
-- @'Rep' p = u@, the input is instantiated at the adjunction
-- @l ⊣ u@.
--
adjointl :: (forall l u. Adjunction l u => (a -> u b) -> l s -> t) -> Adjoint s t a b
adjointl f = corepresenting $ f . leftAdjunct
{-# INLINE adjointl #-}

-- | Construct an 'Adjoint' from a Star-side Van Laarhoven function.
--
-- @
-- 'adjointr' f = 'representing' (f '.' 'rightAdjunct')
-- @
--
-- For each 'Adjoining' profunctor @p@ with @'Corep' p = l@ and
-- @'Rep' p = u@, the input is instantiated at the adjunction
-- @l ⊣ u@.
--
adjointr :: (forall l u. Adjunction l u => (l a -> b) -> s -> u t) -> Adjoint s t a b
adjointr f = representing $ f . rightAdjunct
{-# INLINE adjointr #-}

---------------------------------------------------------------------
-- Dual Constructors
---------------------------------------------------------------------

-- | Obtain a 'Cosetter' from a <http://conal.net/blog/posts/semantic-editor-combinators SEC>.
--
-- The construction uses 'copure' to extract the focal element and
-- @'fmap' ('const' a)@ to build a constant container, avoiding the
-- @'Applicative' ('Coindex' t b)@ constraint that would force
-- @b = t@.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input function satisfies the following
-- properties:
--
-- * @abst id ≡ id@
--
-- * @abst f . abst g ≡ abst (f . g)@
--
cosetter :: ((a -> b) -> s -> t) -> Cosetter s t a b
cosetter abst = corepresenting $ \fab fs ->
  abst (\a -> fab (fmap (const a) fs)) (copure fs)
{-# INLINE cosetter #-}

-- | Clone a 'Cosetter'.
--
cloneCosetter :: ACosetter s t a b -> Cosetter s t a b
cloneCosetter o = cosetter (cosets o)
{-# INLINE cloneCosetter #-}

-- | Obtain a 'Cxsetter' from a coindexed SEC.
--
-- The coindex @i@ threads through the right side of the profunctor
-- via @'Cxoptic' p i s t a b = p a (i -> b) -> p s (i -> t)@, which
-- is equivalent to @'Cosetter' s (i -> t) a (i -> b)@. The
-- constructor delegates to 'cosetter' on these function-wrapped types.
--
-- @
-- 'cxsets' '.' 'cxsetter' ≡ 'id'
-- 'cxsetter' '.' 'cxsets' ≡ 'id'
-- @
--
cxsetter :: ((i -> a -> b) -> s -> t) -> Cxsetter i s t a b
cxsetter f = cosetter $ \aib s -> const $ f (\i a -> aib a i) s
{-# INLINE cxsetter #-}

-- | Clone a 'Cxsetter'.
--
cloneCxsetter :: Monoid i => ACxsetter i s t a b -> Cxsetter i s t a b
cloneCxsetter o = cxsetter (cxsets o)
{-# INLINE cloneCxsetter #-}

---------------------------------------------------------------------
-- Cosetter1
---------------------------------------------------------------------

-- | TODO: Document
--
-- @since 0.0.3
cosetter1 :: ((a -> t) -> s -> t) -> Cosetter1 s t a t
cosetter1 abst = coindexing abst . corepresenting (\f -> fmap f . sequence1)
{-# INLINE cosetter1 #-}

-- | Obtain a 'Cxsetter1' from a coindexed SEC.
--
-- Non-empty variant of 'cxsetter'.
--
cxsetter1 :: ((i -> a -> t) -> s -> t) -> Cxsetter1 i s t a t
cxsetter1 f = cosetter1 $ \ait s -> const $ f (\i a -> ait a i) s
{-# INLINE cxsetter1 #-}

---------------------------------------------------------------------
-- Optics
---------------------------------------------------------------------

-- | 'Setter' on each value of a functor.
--
fmapped :: Functor f => Setter (f a) (f b) a b
fmapped = setter fmap
{-# INLINE fmapped #-}

-- | 'Setter' on each value of a contravariant functor.
--
-- @
-- 'Data.Functor.Contravariant.contramap' ≡ 'over' 'contramapped'
-- @
--
-- >>> getPredicate (over contramapped (*2) (Predicate even)) 5
-- True
-- >>> getOp (over contramapped (*5) (Op show)) 100
-- "500"
--
contramapped :: Contravariant f => Setter (f b) (f a) a b
contramapped = setter contramap
{-# INLINE contramapped #-}

-- | 'Ixsetter' on each value of a representable functor.
--
-- >>> 1 :+ 2 & ixany imappedRep %~ bool 20 10 . getAny
-- 20 :+ 10
--
imappedRep :: F.Representable f => Ixsetter (F.Rep f) (f a) (f b) a b
imappedRep = ixsetter F.imapRep
{-# INLINE imappedRep #-}

-- | Map contravariantly over the input of a profunctor.
--
-- The most common profunctor to use this with is @(->)@.
--
-- @
-- ('domain' '..~' f) g x ≡ g (f x)
-- @
--
-- >>> (domain ..~ show) length [1,2,3]
-- 7
--
domain :: Profunctor p => Setter (p b r) (p a r) a b
domain = setter lmap
{-# INLINE domain #-}

-- | Map covariantly over the output of a profunctor.
--
-- The most common profunctor to use this with is @(->)@.
--
-- @
-- (codomain ..~ f) g x ≡ f (g x)
-- codomain @(->) ≡ 'Data.Profunctor.Optic.Lens.withColens' 'Data.Profunctor.Closed.closed' 'Data.Profunctor.Optic.Setter.closing'
-- @
--
-- >>> (codomain ..~ show) length [1,2,3]
-- "3"
--
codomain :: Profunctor p => Setter (p r a) (p r b) a b
codomain = setter rmap
{-# INLINE codomain #-}

-- | 'Setter' on each value of a monad.
--
liftedM :: Monad m => Setter (m a) (m b) a b
liftedM = setter liftM
{-# INLINE liftedM #-}

-- | 'Setter' on each value of an applicative.
--
-- @
-- 'Control.Applicative.liftA' ≡ 'setter' 'liftedA'
-- @
--
-- >>> setter liftedA Identity [1,2,3]
-- [Identity 1,Identity 2,Identity 3]
-- >>> set liftedA 2 (Just 1)
-- Just 2
--
liftedA :: Applicative f => Setter (f a) (f b) a b
liftedA = setter liftA
{-# INLINE liftedA #-}

-- | 'Setter' on the local environment of a 'Reader'.
--
-- Use to lift reader actions into a larger environment:
--
-- >>> runReader (ask & forwarded ..~ fst) (1,2)
-- 1
--
forwarded :: Setter (ReaderT r2 m a) (ReaderT r1 m a) r1 r2
forwarded = setter withReaderT
{-# INLINE forwarded #-}

-- | TODO: Document
--
censored :: Writer.MonadWriter w m => Setter' (m a) w
censored = setter Writer.censor
{-# INLINE censored #-}

-- | 'Setter' on the codomain of a zipping function.
--
-- >>> ((,) & zipped ..~ swap) 1 2
-- (2,1)
--
zipped :: Setter (u -> v -> a) (u -> v -> b) a b
zipped = setter ((.)(.)(.))
{-# INLINE zipped #-}

-- | TODO: Document
--
modded :: (a -> Bool) -> Setter' (a -> b) b
modded p = setter $ \mods f a -> if p a then mods (f a) else f a
{-# INLINE modded #-}

-- | Apply a function only when the given condition holds.
--
-- See also 'Data.Profunctor.Optic.Traversal0.predicated' & 'Data.Profunctor.Optic.Prism.filtered'.
--
conditioned :: (a -> Bool) -> Setter' a a
conditioned p = setter $ \f a -> if p a then f a else a
{-# INLINE conditioned #-}

---------------------------------------------------------------------
-- Adjoint Optics
---------------------------------------------------------------------

-- | The identity for 'Adjoint' optics.
--
-- @
-- 'adjoined' = 'adjointl' 'rightAdjunct'
-- 'adjoined' = 'adjointr' 'leftAdjunct'
-- @
--
adjoined :: Adjoint a b a b
adjoined = adjointl rightAdjunct
{-# INLINE adjoined #-}

-- | Map one exception into another as proposed in
-- /"A semantics for imprecise exceptions"/.
--
-- @
-- 'mappedException' :: ('Exception' e1, 'Exception' e2) => 'Adjoint' s s e1 e2
-- @
--
mappedException :: (Exception e1, Exception e2) => Adjoint s s e1 e2
mappedException = adjoint Ex.mapException
{-# INLINE mappedException #-}

---------------------------------------------------------------------
-- Adjoint Operators
---------------------------------------------------------------------

-- | Lift a Costar-side (co-Van Laarhoven) traversal through an
-- adjunction to obtain a Star-side result.
--
-- @
-- 'lifts' o f = 'leftAdjunct' ('cotraverseOf' o f)
-- @
--
lifts :: Adjunction l u => ACotraversal l s t a b -> (l a -> b) -> s -> u t
lifts o f = leftAdjunct $ cotraverseOf o f
{-# INLINE lifts #-}

-- | Lower a Star-side (Van Laarhoven) traversal through an
-- adjunction to obtain a Costar-side result.
--
-- @
-- 'lowers' o f = 'rightAdjunct' ('traverseOf' o f)
-- @
--
lowers :: Adjunction l u => ATraversal u s t a b -> (a -> u b) -> l s -> t
lowers o f = rightAdjunct $ traverseOf o f
{-# INLINE lowers #-}

-- | Convert a Star-side traversal to the Costar side through an
-- adjunction, applied to an SEC.
--
-- @
-- 'alower' abst = over 'Data.Profunctor.Optic.Iso.adjuncted' ('aupper' abst)
-- @
--
alower :: Adjunction l u => ((a -> b) -> s -> t) -> (l a -> b) -> l s -> t
alower abst f = rightAdjunct $ aupper abst (leftAdjunct f)
{-# INLINE alower #-}

-- | Convert an SEC to a Star-side (Van Laarhoven) form.
--
-- For each index @i@ of the representable functor @u@, the SEC
-- @abst@ is applied to the @i@-th component extracted from
-- @a -> u b@.
--
aupper :: F.Representable u => ((a -> b) -> s -> t) -> (a -> u b) -> s -> u t
aupper abst afb s = F.tabulate $ \i -> abst (flip F.index i . afb) s
{-# INLINE aupper #-}

---------------------------------------------------------------------
-- Ix/Cx adjunction transforms
---------------------------------------------------------------------

-- | Convert an indexed 'Adjoint' optic to a coindexed one via the
-- adjunction on the profunctor's representation functors.
--
-- 'Ix' @p k a b = p (k, a) b@ threads the index as a product on the
-- left — the 'Corep' (left adjoint) side. 'Cx' @p k a b = p a (k -> b)@
-- threads the index as a function on the right — the 'Rep' (right
-- adjoint) side. For an 'Adjoining' profunctor, these are isomorphic
-- because the adjunction @'Corep' p ⊣ 'Rep' p@ relates products and
-- functions.
--
-- The conversion factors into three steps:
--
-- @
-- p (k, a) b
--   ─── 'cosieve' ──────> Corep p (k, a) -> b       (enter Corep)
--   ─── 'leftAdjunct' ──> (k, a) -> Rep p b          (cross via adjunction)
--   ─── curry/distribute > a -> Rep p (k -> b)        (rearrange k)
--   ─── 'tabulate' ─────> p a (k -> b)               (exit Rep)
-- @
--
-- Compare 'Data.Profunctor.Optic.Index.ixcx', which achieves the
-- same isomorphism using 'Strong' + 'Closed' via a mechanical
-- shuffle through 'first'' and 'closed'. Here, the adjunction
-- makes the structure explicit: Ix threads through the left adjoint,
-- Cx through the right, and 'leftAdjunct'\/'rightAdjunct' is the
-- bridge.
--
-- @
-- 'ixadjoining' '.' 'cxadjoining' ≡ 'id'
-- 'cxadjoining' '.' 'ixadjoining' ≡ 'id'
-- @
--
ixadjoining :: Adjoining p => Ixoptic p k s t a b -> Cxoptic p k s t a b
ixadjoining o p_a_kb = p_s_kt
  where
    -- Cx → Ix: sieve, uncurry k, rightAdjunct, cotabulate
    p_ka_b = cotabulate $ rightAdjunct $ \(k, a) ->
      fmap ($ k) (sieve p_a_kb a)

    -- Apply the indexed optic
    p_ks_t = o p_ka_b

    -- Ix → Cx: cosieve, leftAdjunct, curry k + distribute, tabulate
    p_s_kt = tabulate $ \s -> distribute $ \k ->
      leftAdjunct (cosieve p_ks_t) (k, s)
{-# INLINE ixadjoining #-}

-- | Convert a coindexed 'Adjoint' optic to an indexed one via the
-- adjunction. The inverse of 'ixadjoining'.
--
-- The conversion factors into the reverse three steps:
--
-- @
-- p a (k -> b)
--   ─── 'sieve' ────────> a -> Rep p (k -> b)        (enter Rep)
--   ─── undistribute/fmap > (k, a) -> Rep p b          (rearrange k)
--   ─── 'rightAdjunct' ──> Corep p (k, a) -> b        (cross via adjunction)
--   ─── 'cotabulate' ───> p (k, a) b                  (exit Corep)
-- @
--
-- @
-- 'cxadjoining' '.' 'ixadjoining' ≡ 'id'
-- 'ixadjoining' '.' 'cxadjoining' ≡ 'id'
-- @
--
cxadjoining :: Adjoining p => Cxoptic p k s t a b -> Ixoptic p k s t a b
cxadjoining o p_ka_b = p_ks_t
  where
    -- Ix → Cx: cosieve, leftAdjunct, curry k + distribute, tabulate
    p_a_kb = tabulate $ \a -> distribute $ \k ->
      leftAdjunct (cosieve p_ka_b) (k, a)

    -- Apply the coindexed optic
    p_s_kt = o p_a_kb

    -- Cx → Ix: sieve, uncurry k, rightAdjunct, cotabulate
    p_ks_t = cotabulate $ rightAdjunct $ \(k, s) ->
      fmap ($ k) (sieve p_s_kt s)
{-# INLINE cxadjoining #-}

---------------------------------------------------------------------
-- Sort-Conjoin-Adjoint bridge
---------------------------------------------------------------------

-- | Absorb a 'Sort' to 'Conjoin' by evaluating at 'mempty'.
--
-- 'Conjoin' is the 'Adjoining' profunctor at the currying adjunction
-- @(,) k ⊣ (->) k@. This collapses Sort's multi-index structure
-- into a single key-value function.
--
-- @
-- 'absorbSort' '.' 'embedSort' ≡ 'id'
-- @
--
absorbSort :: Monoid i => Sort i k a b -> Conjoin k a b
absorbSort (Sort f) = Conjoin $ \k a -> f (const (k, a))
{-# INLINE absorbSort #-}

-- | Embed 'Conjoin' into 'Sort' at a trivial index.
--
-- This is a section of 'absorbSort':
--
-- @
-- 'absorbSort' '.' 'embedSort' ≡ 'id'
-- @
--
-- but NOT a retraction:
--
-- @
-- 'embedSort' '.' 'absorbSort' ≢ 'id'    (loses multi-index structure)
-- @
--
embedSort :: Conjoin k a b -> Sort () k a b
embedSort (Conjoin f) = Sort $ \inp -> uncurry f (inp ())
{-# INLINE embedSort #-}

-- | Cross from the Costar side ('Sort') to the Star side ('Cosort')
-- by absorbing through 'Conjoin' and using the currying adjunction.
--
-- 'Sort' is Costar-only (no 'Rep'). 'Cosort' is Star-only (no
-- 'Corep'). There is no direct adjunction between them — Sort\'s
-- Corep mixes a right adjoint @(->) i@ with a left adjoint @(,) k@,
-- blocking the composed adjunction theorem.
--
-- However, 'Conjoin' @k@ sits at the currying adjunction
-- @(,) k ⊣ (->) k@ and is simultaneously 'Representable' and
-- 'Corepresentable' — the unique 'Adjoining' profunctor connecting
-- the two sides. The bridge is:
--
-- @
-- Sort i k ──('absorbSort')──> Conjoin k ──(currying adjunction)──> Cosort () k
-- @
--
-- The first step ('absorbSort') collapses Sort\'s multi-index
-- structure by evaluating at @const@, which is lossy — the
-- function @i -> k@ that assigns different keys to different
-- indices is frozen. The second step uses @(,) k ⊣ (->) k@ to
-- flip @(k, a) -> b@ into @a -> k -> b@, crossing from Costar
-- to Star.
--
-- This pattern generalises: any Costar-only profunctor can reach
-- the Star side by retracting to an 'Adjoining' mediator and
-- then applying 'Data.Profunctor.Optic.Iso.adjuncted'. The cost
-- is always the retraction — the structure that exceeds the
-- mediator is lost.
--
sortCosort :: Monoid i => Sort i k a b -> Cosort () k a b
sortCosort (Sort f) = Cosort $ \a k -> ((), f (const (k, a)))
{-# INLINE sortCosort #-}

-- | Lift a 'Sort'-based operation across the currying adjunction.
--
-- Given a Costar-side operation using @(,) k@ (e.g. one built
-- from 'Conjoin'), 'lifts' converts it to the Star side via
-- the adjunction @(,) k ⊣ (->) k@:
--
-- @
-- 'lifts' o :: ((k, a) -> b) -> s -> (k -> t)
-- @
--
-- This is how Sort-based sorting can feed into Star-side (e.g.
-- 'Cosort'-shaped) operations.
--
-- Example:
--
-- @
-- 'lifts' myColens :: Adjunction ((,) k) ((->) k) => ((k, a) -> b) -> s -> (k -> t)
-- @
--

---------------------------------------------------------------------
-- Dual Optics
---------------------------------------------------------------------

-- | TODO: Document
--
coliftedA :: Applicative f => Cosetter (f a) (f b) a b
coliftedA p = cotabulate $ fmap (cosieve p) . sequenceA
{-# INLINE coliftedA #-}

-- | TODO: Document
--
-- @since 0.0.3
coliftedF :: Apply f => Cosetter1 (f a) (f b) a b
coliftedF p = cotabulate $ fmap (cosieve p) . sequence1
{-# INLINE coliftedF #-}

-- | Variant of 'coliftedA' specialized to zip-toListOf.
--
-- Useful because toListOf are not 'Control.Coapplicative.Coapplicative'.
--
-- @since 0.0.3
zipListed :: Cosetter [a] [b] a b
zipListed = dimap ZipList getZipList . coliftedA
{-# INLINE zipListed #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Set the focus of a 'Setter'.
--
-- @
-- 'set' o y ('set' o x a) ≡ 'set' o y a
-- 'set' o b = 'Data.Functor.runIdentity' . (o *~ 'Data.Functor.Identity' b)
-- @
--
set :: ASetter s t a b -> b -> s -> t
set o b = sets o $ const b
{-# INLINE set #-}

-- | Set the focus of a 'Ixsetter'.
--
-- Equivalent to 'ixsets' with the current value ignored.
--
-- @
-- 'set' o ≡ 'ixset' o '.' 'const'
-- @
--
-- @since 0.0.3
ixset :: Monoid i => AIxsetter i s t a b -> (i -> b) -> s -> t
ixset o = ixsets o . (const .)
{-# INLINE ixset #-}

-- | Set the focus of a 'Setter'.
--
sets ::  ASetter s t a b -> (a -> b) -> s -> t
sets o = (runIdentity #.) #. traverseOf o .# (Identity #.)
{-# INLINE sets #-}

-- | Set the focus of a 'Ixsetter'.
--
-- @since 0.0.3
ixsets :: Monoid i => AIxsetter i s t a b -> (i -> a -> b) -> s -> t
ixsets o f = curry (sets o $ uncurry f) mempty
{-# INLINE ixsets #-}

---------------------------------------------------------------------
-- Dual Operators
---------------------------------------------------------------------

-- | Set the focus of a 'Cosetter'.
--
-- @
-- 'coset' o b = (o '/~' b) . 'Data.Functor.Identity'
-- @
--
coset :: ACosetter s t a b -> b -> s -> t
coset o b = cosets o $ const b

-- | Set the focus of a 'Cxsetter'.
--
-- Equivalent to 'cxsets' with the current value ignored.
--
-- @since 0.0.3
cxset :: Monoid i => ACxsetter i s t a b -> (i -> b) -> s -> t
cxset o ib = cxsets o $ flip (const ib)
{-# INLINE cxset #-}

-- | Set the focus of a 'Cosetter'.
--
cosets :: ACosetter s t a b -> (a -> b) -> s -> t
cosets o = (.# Identity) #. cotraverseOf o .# (.# runIdentity)
{-# INLINE cosets #-}

-- | Set the focus of a 'Cxsetter'.
--
-- @since 0.0.3
cxsets :: Monoid i => ACxsetter i s t a b -> (i -> a -> b) -> s -> t
cxsets o f = flip (cosets o $ flip f) mempty
{-# INLINE cxsets #-}

---------------------------------------------------------------------
-- MonadState / MonadReader / MonadWriter
---------------------------------------------------------------------

-- | Replace the target(s) of a settable in a monadic state.
--
assigns :: MonadState s m => Optic (->) s s a b -> b -> m ()
assigns o b = State.modify (o (const b))
{-# INLINE assigns #-}

-- | Map over the target(s) of a 'Setter' in a monadic state.
--
modifies :: MonadState s m => Optic (->) s s a b -> (a -> b) -> m ()
modifies o f = State.modify (o f)
{-# INLINE modifies #-}

-- | Indexed 'assigns': replace the target(s) of an indexed settable
-- in a monadic state.
--
-- @since 0.0.3
ixassigns :: MonadState s m => Monoid i => Ixoptic (->) i s s a b -> (i -> b) -> m ()
ixassigns o f = State.modify (ixover o (const . f))
{-# INLINE ixassigns #-}

-- | Indexed 'modifies': map over the target(s) of an indexed settable
-- in a monadic state.
--
-- @since 0.0.3
ixmodifies :: MonadState s m => Monoid i => Ixoptic (->) i s s a b -> (i -> a -> b) -> m ()
ixmodifies o f = State.modify (ixover o f)
{-# INLINE ixmodifies #-}

-- | Modify the value of a 'Reader' environment.
--
-- @
-- 'localizes' l 'id' a ≡ a
-- 'localizes' l f '.' localizes l g ≡ 'localizes' l (f '.' g)
-- @
--
-- >>> (1,1) & localizes first' (+1) (uncurry (+))
-- 3
-- >>> "," & localizes (setter ($)) ("Hello" <>) (<> " world!")
-- "Hello, world!"
--
-- Compare 'forwarded'.
--
localizes :: MonadReader s m => Optic (->) s s a b -> (a -> b) -> m r -> m r
localizes o f = Reader.local (o f)
{-# INLINE localizes #-}

-- | Write to a fragment of a larger 'Writer' format.
--
tells :: MonadWriter w m => Monoid s => Optic (->) s w a b -> b -> m ()
tells o b = Writer.tell (o (const b) mempty)
{-# INLINE tells #-}
