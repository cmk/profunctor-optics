{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Property (
    -- * Iso
    Iso
  , fromto_iso
  , tofrom_iso
    -- * Prism
  , Prism
  , tofrom_prism
  , fromto_prism
  , idempotent_prism
    -- * Reprism
  , Reprism
  , tofrom_reprism
  , fromto_reprism
  , idempotent_reprism
    -- * Lens
  , Lens
  , id_lens
  , tofrom_lens
  , fromto_lens
  , idempotent_lens
    -- * Relens
  , Relens
  , const_relens
  , tofrom_relens
  , idempotent_relens
    -- * Colens
  , Colens
  , id_grate
  , const_grate
  , compose_grate
    -- * Traversal0
  , Traversal0
  , tofrom_traversal0
  , fromto_traversal0
  , idempotent_traversal0
    -- * Traversal
  , Traversal
  , id_traversal
  , id_traversal1
  , pure_traversal
  , compose_traversal
  , compose_traversal1
    -- * Cotraversal
  , Cotraversal
  , compose_cotraversal
    -- * Cofold
  , Cofold
  , id_cofold
  , compose_cofold
    -- * Setter
  , Setter
  , id_setter
  , compose_setter
  , idempotent_setter
    -- * Cosetter
  , Cosetter
  , id_cosetter
  , compose_cosetter
    -- * Sort
  , Sort
  , id_sort
  , compose_sort
  , id_category_sort
  , assoc_category_sort
) where

import Control.Monad as M (join)
import Control.Applicative
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Import
import Prelude (Bool(..), Eq(..), Monoid, (&&))
import qualified Control.Category as C
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Traversal
import Data.Profunctor.Optic.Setter
import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.Fold
-- invertible is provided by Import (inlined from lawz/Test.Function.Invertible)

---------------------------------------------------------------------
-- 'Iso'
---------------------------------------------------------------------

-- | Going back and forth doesn't change anything.
--
fromto_iso :: Eq s => Iso' s a -> s -> Bool
fromto_iso o s = withIso o $ \sa as -> as (sa s) == s

-- | Going back and forth doesn't change anything.
--
tofrom_iso :: Eq a => Iso' s a -> a -> Bool
tofrom_iso o a = withIso o $ \sa as -> sa (as a) == a

---------------------------------------------------------------------
-- 'Prism'
---------------------------------------------------------------------

-- | If we are able to view an existing focus, then building it will return the original structure.
--
-- * @(either id bt) (sta s) ≡ s@
--
tofrom_prism :: Eq s => Prism' s a -> s -> Bool
tofrom_prism o s = withPrism o $ \sta bt -> either id bt (sta s) == s

-- | If we build a whole from a focus, that whole must contain the focus.
--
-- * @sta (bt b) ≡ Right b@
--
fromto_prism :: Eq s => Eq a => Prism' s a -> a -> Bool
fromto_prism o a = withPrism o $ \sta bt -> sta (bt a) == Right a

-- |
--
-- * @left sta (sta s) ≡ left Left (sta s)@
--
idempotent_prism :: Eq s => Eq a => Prism' s a -> s -> Bool
idempotent_prism o s = withPrism o $ \sta _ -> left' sta (sta s) == left' Left (sta s)

---------------------------------------------------------------------
-- 'Reprism'
---------------------------------------------------------------------

-- | If we build and then match, we get back the original.
--
-- * @either id sa (bat a) ≡ a@
--
tofrom_reprism :: Eq a => Reprism' s a -> a -> Bool
tofrom_reprism o a = withReprism o $ \sa bat -> either id sa (bat a) == a

-- | If we match a built value, we always get 'Right'.
--
-- * @bat (sa s) ≡ Right s@
--
fromto_reprism :: Eq s => Eq a => Reprism' s a -> s -> Bool
fromto_reprism o s = withReprism o $ \sa bat -> bat (sa s) == Right s

-- | Matching the result of a match is the same as wrapping in 'Left'.
--
-- * @left' bat (bat a) ≡ left' Left (bat a)@
--
idempotent_reprism :: Eq s => Eq a => Reprism' s a -> a -> Bool
idempotent_reprism o a = withReprism o $ \_ bat -> left' bat (bat a) == left' Left (bat a)

---------------------------------------------------------------------
-- 'Lens'
---------------------------------------------------------------------

-- A 'Lens' is a valid 'Traversal' with the following additional laws:
--
id_lens :: Eq s => Lens' s a -> s -> Bool
id_lens o = M.join invertible $ runIdentity . cloneLensVl o Identity 

-- | You get back what you put in.
--
-- * @view o (set o b a) ≡ b@
--
tofrom_lens :: Eq s => Lens' s a -> s -> Bool
tofrom_lens o s = withLens o $ \sa sas -> sas s (sa s) == s

-- | Putting back what you got doesn't change anything.
--
-- * @set o (view o a) a  ≡ a@
--
fromto_lens :: Eq a => Lens' s a -> s -> a -> Bool
fromto_lens o s a = withLens o $ \sa sas -> sa (sas s a) == a

-- | Setting twice is the same as setting once.
--
-- * @set o c (set o b a) ≡ set o c a@
--
idempotent_lens :: Eq s => Lens' s a -> s -> a -> a -> Bool
idempotent_lens o s a1 a2 = withLens o $ \_ sas -> sas (sas s a1) a2 == sas s a2

---------------------------------------------------------------------
-- 'Relens'
---------------------------------------------------------------------

-- The 'Relens' laws are dual to the 'Lens' laws, with the roles of
-- structure and focus swapped.

-- | Co-get-set: setting to what we got gives back the structure.
--
-- * @bsa a (bt a) ≡ a@
--
const_relens :: Eq a => Relens' s a -> a -> Bool
const_relens o a = withRelens o $ \bsa bt -> bsa a (bt a) == a

-- | Co-set-get: getting from what we set gives back the focus.
--
-- * @bt (bsa a s) ≡ s@
--
tofrom_relens :: Eq s => Relens' s a -> a -> s -> Bool
tofrom_relens o a s = withRelens o $ \bsa bt -> bt (bsa a s) == s

-- | Co-set-set: setting twice is the same as setting once.
--
-- * @bsa (bsa a s1) s2 ≡ bsa a s2@
--
idempotent_relens :: Eq a => Relens' s a -> a -> s -> s -> Bool
idempotent_relens o a s1 s2 = withRelens o $ \bsa _ -> bsa (bsa a s1) s2 == bsa a s2

---------------------------------------------------------------------
-- 'Colens'
---------------------------------------------------------------------

-- The 'Colens' laws are that of an algebra for the parameterised continuation 'Coindex'.

id_grate :: Eq s => Colens' s a -> s -> Bool
id_grate o = M.join invertible $ cloneColensVl o runIdentity . Identity 

-- |
--
-- * @sabt ($ s) ≡ s@
--
const_grate :: Eq s => Colens' s a -> s -> Bool
const_grate o s = withColens o $ \sabt -> sabt ($ s) == s

compose_grate :: Eq s => Functor f => Functor g => Colens' s a -> (f a -> a) -> (g a -> a) -> f (g s) -> Bool
compose_grate o f g = liftA2 (==) lhs rhs
  where lhs = cloneColensVl o f . fmap (cloneColensVl o g) 
        rhs = cloneColensVl o (f . fmap g . getCompose) . Compose

---------------------------------------------------------------------
-- 'Traversal0'
---------------------------------------------------------------------

-- | You get back what you put in.
--
-- * @sta (sbt s a) ≡ either Left (const (Right a)) (sta s)@
--
tofrom_traversal0 :: Eq a => Eq s => Traversal0' s a -> s -> a -> Bool
tofrom_traversal0 o s a = withTraversal0 o $ \sta sbt -> sta (sbt s a) == either Left (const (Right a)) (sta s)

-- | Putting back what you got doesn't change anything.
--
-- * @either id (sbt s) (sta s) ≡ s@
--
fromto_traversal0 :: Eq s => Traversal0' s a -> s -> Bool
fromto_traversal0 o s = withTraversal0 o $ \sta sbt -> either id (sbt s) (sta s) == s

-- | Setting twice is the same as setting once.
--
-- * @sbt (sbt s a1) a2 ≡ sbt s a2@
--
idempotent_traversal0 :: Eq s => Traversal0' s a -> s -> a -> a -> Bool
idempotent_traversal0 o s a1 a2 = withTraversal0 o $ \_ sbt -> sbt (sbt s a1) a2 == sbt s a2

---------------------------------------------------------------------
-- 'Traversal'
---------------------------------------------------------------------

-- A 'Traversal' is a valid 'Setter' with the following additional laws:

id_traversal :: Eq s => Traversal' s a -> s -> Bool
id_traversal o = M.join invertible $ runIdentity . traverseOf o Identity 

id_traversal1 :: Eq s => Traversal1' s a -> s -> Bool
id_traversal1 o = M.join invertible $ runIdentity . traverseOf o Identity 

pure_traversal :: Eq (f s) => Applicative f => ATraversal' f s a -> s -> Bool
pure_traversal o = liftA2 (==) (traverseOf o pure) pure

compose_traversal :: Eq (f (g s)) => Applicative' f => Applicative' g => Traversal' s a -> (a -> g a) -> (a -> f a) -> s -> Bool
compose_traversal o f g = liftA2 (==) lhs rhs
  where lhs = fmap (traverseOf o f) . traverseOf o g
        rhs = getCompose . traverseOf o (Compose . fmap f . g)

compose_traversal1 :: Eq (f (g s)) => Apply f => Apply g => Traversal1' s a -> (a -> g a) -> (a -> f a) -> s -> Bool
compose_traversal1 o f g s = lhs s == rhs s
  where lhs = fmap (traverseOf o f) . traverseOf o g
        rhs = getCompose . traverseOf o (Compose . fmap f . g)

---------------------------------------------------------------------
-- 'Cotraversal'
---------------------------------------------------------------------

-- | A 'Cotraversal' is a valid 'Cosetter' with the following additional law:
--
-- * @abst f . fmap (abst g) ≡ abst (f . fmap g . getCompose) . Compose @
--
-- The cotraversal laws can be restated in terms of 'cotraverseOf':
--
-- * @cotraverseOf o (f . copure) ≡ fmap f . copure @
--
-- * @cotraverseOf o f . fmap (cotraverseOf o g) ≡ cotraverseOf o (f . fmap g . getCompose) . Compose@
--
-- See also < https://www.cs.ox.ac.uk/jeremy.gibbons/publications/iterator.pdf >
--
compose_cotraversal :: Eq s => Coapplicative f => Coapplicative g => Cotraversal' s a -> (f a -> a) -> (g a -> a) -> f (g s) -> Bool
compose_cotraversal o f g = liftA2 (==) lhs rhs
  where lhs = cotraverseOf o f . fmap (cotraverseOf o g)
        rhs = cotraverseOf o (f . fmap g . getCompose) . Compose

---------------------------------------------------------------------
-- 'Cofold'
---------------------------------------------------------------------

-- | @cofoldMapOf o id ≡ id@
--
id_cofold :: Eq t => ACofold t t t -> t -> Bool
id_cofold o t = cofoldMapOf o id t == t

-- | @cofoldMapOf o f . cofoldMapOf o g ≡ cofoldMapOf o (f . g)@
--
compose_cofold :: Eq t => ACofold t t t -> (t -> t) -> (t -> t) -> t -> Bool
compose_cofold o f g t = (cofoldMapOf o f . cofoldMapOf o g) t == cofoldMapOf o (f . g) t

---------------------------------------------------------------------
-- 'Setter'
---------------------------------------------------------------------

-- |
--
-- * @over o id ≡ id@
--
id_setter :: Eq s => Setter' s a -> s -> Bool
id_setter o s = over o id s == s

-- |
--
-- * @over o f . over o g ≡ over o (f . g)@
--
compose_setter :: Eq s => Setter' s a -> (a -> a) -> (a -> a) -> s -> Bool
compose_setter o f g s = (over o f . over o g) s == over o (f . g) s

-- |
--
-- * @set o y (set o x a) ≡ set o y a@
--
idempotent_setter :: Eq s => Setter' s a -> s -> a -> a -> Bool
idempotent_setter o s a b = set o b (set o a s) == set o b s

---------------------------------------------------------------------
-- 'Cosetter'
---------------------------------------------------------------------

-- | @cosets o id ≡ id@
--
id_cosetter :: Eq s => ACosetter s s a a -> s -> Bool
id_cosetter o s = cosets o id s == s

-- | @cosets o f . cosets o g ≡ cosets o (f . g)@
--
compose_cosetter :: Eq s => ACosetter s s a a -> (a -> a) -> (a -> a) -> s -> Bool
compose_cosetter o f g s = (cosets o f . cosets o g) s == cosets o (f . g) s

---------------------------------------------------------------------
-- 'Sort'
---------------------------------------------------------------------

-- | @dimap id id ≡ id@
--
id_sort :: Eq b => Sort i k a b -> (i -> (k, a)) -> Bool
id_sort s inp = runSort (dimap id id s) inp == runSort s inp

-- | @dimap f g . dimap h k ≡ dimap (h . f) (g . k)@
--
compose_sort :: Eq c => Sort i k a c -> (a -> a) -> (c -> c) -> (a -> a) -> (c -> c) -> (i -> (k, a)) -> Bool
compose_sort s f g h k inp =
  runSort (dimap f g . dimap h k $ s) inp == runSort (dimap (h . f) (g . k) s) inp

-- | @id . f ≡ f@ and @f . id ≡ f@
--
id_category_sort :: (Monoid i, Eq b) => Sort i k a b -> (i -> (k, a)) -> Bool
id_category_sort s inp =
  runSort (C.id C.. s) inp == runSort s inp &&
  runSort (s C.. C.id) inp == runSort s inp

-- | @(f . g) . h ≡ f . (g . h)@
--
assoc_category_sort :: (Monoid i, Eq d) => Sort i k a b -> Sort i k b c -> Sort i k c d -> (i -> (k, a)) -> Bool
assoc_category_sort f g h inp =
  runSort ((h C.. g) C.. f) inp == runSort (h C.. (g C.. f)) inp
