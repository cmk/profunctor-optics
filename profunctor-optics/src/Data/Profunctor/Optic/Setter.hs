{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

-- | Left and right carriers are characterized by their representation
-- functors ('Rep' and 'Corep'). 'Iso' sits at the top where both
-- are trivial ('Identity'). 'Adjoint' sits at the bottom where they
-- form a full adjunction (@'Corep' p ⊣ 'Rep' p@). A left-indexed
-- ('Ix') optic threads an index through the left adjoint functor
-- @(,) k@, while a right-indexed ('Cx') optic threads a coindex
-- through the right adjoint functor @(->) k@.
module Data.Profunctor.Optic.Setter (
    -- * Left Adjoint Constructors
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
    -- * Right Adjoint Constructors
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
    -- * Adjoint Constructors
  , Adjoint, Adjoint'
  , Ixadjoint, Ixadjoint'
  , Cxadjoint, Cxadjoint'
  , adjoint
  , ixadjoint
  , cxadjoint
  , adjointl
  , adjointr
  , adjointlVl
  , adjointrVl
  , ixadjoining
  , cxadjoining
    -- * Left Adjoint Optics
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
    -- * Right Adjoint Optics
    -- ** Cosetter, Cxsetter
    -- ** Cosetter1, Cxsetter1
  , coliftedA
  , zipListed
    -- * Adjoint Optics
  , adjoined
  , mappedException
    -- * Left Adjoint Operators
    -- ** Setter, Ixsetter
  , set
  , ixset
  , sets
  , ixsets
  , over
  , ixover
    -- ** Setter1, Ixsetter1
    -- * Right Adjoint Operators
    -- ** Cosetter, Cxsetter
  , coset
  , cxset
  , cosets
  , cxsets
  , cxover
    -- ** Cosetter1, Cxsetter1
    -- * Adjoint Operators
  , lifts
  , lowers
  , alower
  , aupper
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
import Data.Profunctor.Optic.Import hiding ((&&&))
import Data.Profunctor.Optic.Index
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Iso (indexing)
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
-- Left Adjoint Constructors
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
-- Right Adjoint Constructors
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

-- | Clone a 'Cosetter'.
--
cloneCosetter :: ACosetter s t a b -> Cosetter s t a b
cloneCosetter o = cosetter (cosets o)
{-# INLINE cloneCosetter #-}

-- | Clone a 'Cxsetter'.
--
cloneCxsetter :: Monoid i => ACxsetter i s t a b -> Cxsetter i s t a b
cloneCxsetter o = cxsetter (cxsets o)
{-# INLINE cloneCxsetter #-}

---------------------------------------------------------------------
-- Adjoint Constructors
---------------------------------------------------------------------

-- | Obtain an 'Adjoint' from a
-- <http://conal.net/blog/posts/semantic-editor-combinators SEC>.
--
-- @
-- 'adjoint' abst ≡ 'adjointlVl' ('Data.Functor.Adjunction.rightAdjunct' abst)
-- 'adjoint' abst ≡ 'adjointrVl' ('Data.Functor.Adjunction.leftAdjunct' abst)
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

-- | Build a 'Cxadjoint' from a coindexed function.
--
-- The coindex @i@ threads through the right side of the profunctor.
-- Same implementation as 'cxsetter' but returns 'Cxadjoint'
-- (requires 'Adjoining').
--
cxadjoint :: ((i -> a -> b) -> s -> t) -> Cxadjoint i s t a b
cxadjoint f = adjoint $ \aib s -> const $ f (\i a -> aib a i) s
{-# INLINE cxadjoint #-}

-- | Construct an 'Adjoint' from a getter and a setter (lens-like).
--
-- This is the 'Adjoint' analogue of
-- 'Data.Profunctor.Optic.Lens.lensVl'. The getter extracts the
-- focus; the setter rebuilds the structure with a new focus. The
-- adjunction threads the representation functors through
-- 'zapWithAdjunction'.
--
-- At @(->)@ this reduces to the standard lens SEC:
--
-- @
-- 'over' ('adjointl' sa sbt) f s ≡ sbt s (f (sa s))
-- @
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @sbt s (sa s) ≡ s@ (GetPut)
--
-- * @sa (sbt s b) ≡ b@ (PutGet)
--
-- * @sbt (sbt s b1) b2 ≡ sbt s b2@ (PutPut)
--
adjointl :: (s -> a) -> (s -> b -> t) -> Adjoint s t a b
adjointl sa sbt = adjointlVl $ \ab s -> zapWithAdjunction (flip sbt) (ab . sa $ extractL s) s
{-# INLINE adjointl #-}

-- | Construct an 'Adjoint' from a matching function and a review
-- (prism-like).
--
-- This is the 'Adjoint' analogue of
-- 'Data.Profunctor.Optic.Prism.handling'. The matching function
-- decomposes @s@ into either @t@ (failure) or @a@ (success); the
-- review rebuilds @t@ from @b@. On success, 'leftAdjunct' lifts
-- the left-adjoint map @l a -> b@ into the right adjoint @a -> u b@,
-- then 'fmap' applies the review. On failure, @'leftAdjunct'
-- 'extractL'@ embeds @t@ into @u t@ (the \"pure\" of the
-- adjunction-induced monad).
--
-- At @(->)@ this reduces to the standard prism SEC:
--
-- @
-- 'over' ('adjointr' sta bt) f s ≡ either id (bt . f) (sta s)
-- @
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @sta (bt b) ≡ Right b@ (PutGet)
--
-- * @either id bt (sta s) ≡ s@ when @sta s ≡ Left t@ (GetPut)
--
-- * @left' sta (sta s) ≡ left' Left (sta s)@ (Idempotence)
--
adjointr :: (s -> t + a) -> (b -> t) -> Adjoint s t a b
adjointr sta bt = adjointrVl $ \lab s ->
  either (leftAdjunct extractL) (fmap bt . leftAdjunct lab) (sta s)
{-# INLINE adjointr #-}

-- | Construct an 'Adjoint' from a Costar-side Van Laarhoven function.
--
-- @
-- 'adjointlVl' f = 'corepresenting' (f '.' 'leftAdjunct')
-- @
--
-- For each 'Adjoining' profunctor @p@ with @'Corep' p = l@ and
-- @'Rep' p = u@, the input is instantiated at the adjunction
-- @l ⊣ u@.
--
adjointlVl :: (forall l u. Adjunction l u => (a -> u b) -> l s -> t) -> Adjoint s t a b
adjointlVl f = corepresenting $ f . leftAdjunct
{-# INLINE adjointlVl #-}

-- | Construct an 'Adjoint' from a Star-side Van Laarhoven function.
--
-- @
-- 'adjointrVl' f = 'representing' (f '.' 'rightAdjunct')
-- @
--
-- For each 'Adjoining' profunctor @p@ with @'Corep' p = l@ and
-- @'Rep' p = u@, the input is instantiated at the adjunction
-- @l ⊣ u@.
--
adjointrVl :: (forall l u. Adjunction l u => (l a -> b) -> s -> u t) -> Adjoint s t a b
adjointrVl f = representing $ f . rightAdjunct
{-# INLINE adjointrVl #-}


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
-- Left Adjoint Optics
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
-- Right Adjoint Optics
---------------------------------------------------------------------

-- | TODO: Document
--
coliftedA :: Applicative f => Cosetter (f a) (f b) a b
coliftedA p = cotabulate $ fmap (cosieve p) . sequenceA
{-# INLINE coliftedA #-}

-- | Variant of 'coliftedA' specialized to zip-toListOf.
--
-- Useful because toListOf are not 'Control.Coapplicative.Coapplicative'.
--
-- @since 0.0.3
zipListed :: Cosetter [a] [b] a b
zipListed = dimap ZipList getZipList . coliftedA
{-# INLINE zipListed #-}

---------------------------------------------------------------------
-- Adjoint Optics
---------------------------------------------------------------------

-- | The identity for 'Adjoint' optics.
--
-- @
-- 'adjoined' = 'adjointlVl' 'rightAdjunct'
-- 'adjoined' = 'adjointrVl' 'leftAdjunct'
-- @
--
adjoined :: Adjoint a b a b
adjoined = adjointlVl rightAdjunct
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
-- Left Adjoint Operators
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
-- Right Adjoint Operators
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
