module Data.Profunctor.Optic.Property where

import Control.Applicative
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Iso
--import Data.Profunctor.Optic.View
import Data.Profunctor.Optic.Setter
import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.Prism
import Data.Profunctor.Optic.Grate
--import Data.Profunctor.Optic.Fold
import Data.Profunctor.Optic.Traversal

---------------------------------------------------------------------
-- 'Iso'
---------------------------------------------------------------------

iso_fromto' :: Eq s => Iso' s a -> s -> Bool
iso_fromto' o = withIso o iso_fromto

iso_tofrom' :: Eq a => Iso' s a -> a -> Bool
iso_tofrom' o = withIso o iso_tofrom

iso_fromto :: Eq s => (s -> a) -> (a -> s) -> s -> Bool
iso_fromto sa as s = as (sa s) == s

iso_tofrom :: Eq a => (s -> a) -> (a -> s) -> a -> Bool
iso_tofrom sa as a = sa (as a) == a

---------------------------------------------------------------------
-- 'Prism'
---------------------------------------------------------------------

-- If we are able to view an existing focus, then building it will return the original structure.
prism_tofrom :: Eq s => (s -> s + a) -> (a -> s) -> s -> Bool
prism_tofrom seta bt s = either id bt (seta s) == s

-- If we build a whole from any focus, that whole must contain a focus.
prism_fromto :: Eq s => Eq a => (s -> s + a) -> (a -> s) -> a -> Bool
prism_fromto seta bt a = seta (bt a) == Right a

prism_tofrom' :: Eq s => Prism' s a -> s -> Bool
prism_tofrom' o = withPrism o prism_tofrom

-- Reviewing a value with a 'Prism' and then previewing returns the value.
prism_fromto' :: Eq s => Eq a => Prism' s a -> a -> Bool
prism_fromto' o = withPrism o prism_fromto

---------------------------------------------------------------------
-- 'Lens'
---------------------------------------------------------------------


-- | A 'Lens' is a valid 'Traversal' with the following additional laws:
--
-- * @view o (set o b a)  ≡ b@
--
-- * @set o (view o a) a  ≡ a@
--
-- * @set o c (set o b a) ≡ set o c a@
--
lens_tofrom :: Eq s => (s -> a) -> (s -> a -> s) -> s -> Bool
lens_tofrom sa sas s = sas s (sa s) == s

lens_fromto :: Eq a => (s -> a) -> (s -> a -> s) -> s -> a -> Bool
lens_fromto sa sas s a = sa (sas s a) == a

lens_idempotent :: Eq s => (s -> a -> s) -> s -> a -> a -> Bool
lens_idempotent sas s a1 a2 = sas (sas s a1) a2 == sas s a2

-- | Putting back what you got doesn't change anything.
--
lens_tofrom' :: Eq s => Lens' s a -> s -> Bool
lens_tofrom' o = withLens o lens_tofrom

-- | You get back what you put in.
--
lens_fromto' :: Eq a => Lens' s a -> s -> a -> Bool
lens_fromto' o = withLens o lens_fromto

-- | Setting twice is the same as setting once.
--
lens_idempotent' :: Eq s => Lens' s a -> s -> a -> a -> Bool
lens_idempotent' o = withLens o $ const lens_idempotent

---------------------------------------------------------------------
-- 'Grate'
---------------------------------------------------------------------

-- | The 'Grate' laws are that of an algebra for a parameterised continuation monad.
--
-- * @sabt ($ s) ≡ s@
--
grate_pure :: Eq s => Grate' s a -> s -> Bool
grate_pure o s = withGrate o $ \sabt -> sabt ($ s) == s

-- | The 'Grate' laws are that of an algebra for a parameterised continuation monad.
--
-- * @sabt (\k -> h (k . sabt)) ≡ sabt (\k -> h ($ k))@
--
grate_compose :: Eq s => Grate' s a -> ((((s -> a) -> a) -> a) -> a) -> Bool
grate_compose o f = withGrate o $ \sabt -> sabt (\k -> f (k . sabt)) == sabt (\k -> f ($ k))

---------------------------------------------------------------------
-- 'Traversal0'
---------------------------------------------------------------------

traversal0_tofrom :: Eq a => Eq s => (s -> s + a) -> (s -> a -> s) -> s -> a -> Bool
traversal0_tofrom seta sbt s a = seta (sbt s a) == either (Left . flip const a) Right (seta s)

traversal0_fromto :: Eq s => (s -> s + a) -> (s -> a -> s) -> s -> Bool
traversal0_fromto seta sbt s = either id (sbt s) (seta s) == s

traversal0_idempotent :: Eq s => (s -> a -> s) -> s -> a -> a -> Bool
traversal0_idempotent sbt s a1 a2 = sbt (sbt s a1) a2 == sbt s a2

traversal0_tofrom' :: Eq a => Eq s => Traversal0' s a -> s -> a -> Bool
traversal0_tofrom' o = withTraversal0 o traversal0_tofrom

traversal0_fromto' :: Eq s => Traversal0' s a -> s -> Bool
traversal0_fromto' o = withTraversal0 o traversal0_fromto

traversal0_idempotent' :: Eq s => Traversal0' s a -> s -> a -> a -> Bool
traversal0_idempotent' o = withTraversal0 o $ const traversal0_idempotent

---------------------------------------------------------------------
-- 'Traversal'
---------------------------------------------------------------------

-- | 'Traversal' is a valid 'Setter' with the following additional laws:
--
-- * @t pure ≡ pure@
--
-- * @fmap (t f) . t g ≡ getCompose . t (Compose . fmap f . g)@
--
-- These can be restated in terms of 'traverseOf':
--
-- * @traverseOf t (Identity . f) ≡  Identity (fmap f)@
--
-- * @Compose . fmap (traverseOf t f) . traverseOf t g == traverseOf t (Compose . fmap f . g)@
--
-- See also < https://www.cs.ox.ac.uk/jeremy.gibbons/publications/iterator.pdf >
--

traverse_pure :: forall f s a. (Applicative f, Eq (f s)) => ((a -> f a) -> s -> f s) -> s -> Bool
traverse_pure o s = o pure s == (pure s :: f s)

--traverse_compose :: (Applicative f, Applicative g, Eq (f (g s))) => Traversal' s a -> (a -> g a) -> (a -> f a) -> s -> Bool
--traverse_compose t f g s = (fmap (t f) . t g) s == (getCompose . t (Compose . fmap f . g)) s

---------------------------------------------------------------------
-- 'Setter'
---------------------------------------------------------------------

-- | A 'Setter' is only legal if the following 3 laws hold:
--
-- 1. @set o y (set o x a) ≡ set o y a@
--
-- 2. @over o id ≡ id@
--
-- 3. @over o f . over o g ≡ over o (f . g)@

setter_pure :: Eq s => Setter' s a -> s -> Bool
setter_pure o s = over o id s == s

setter_compose :: Eq s => Setter' s a -> (a -> a) -> (a -> a) -> s -> Bool
setter_compose o f g s = (over o f . over o g) s == over o (f . g) s

setter_idempotent :: Eq s => Setter' s a -> s -> a -> a -> Bool
setter_idempotent o s a b = set o b (set o a s) == set o b s
