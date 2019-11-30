{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Lens (
    -- * Lens & Ixlens
    Strong(..)
  , Lens
  , Ixlens
  , Lens'
  , Ixlens'
  , ALens
  , ALens'
  , lens
  , ixlens
  , lensVl
  , ixlensVl
  , matching
  , cloneLens
    -- * Colens & Cxlens
  , Costrong(..)
  , Colens
  , Cxlens
  , Colens'
  , Cxlens'
  , AColens
  , AColens'
  , colens
  , cxlens
  , colensVl
  , comatching
  , cloneColens
    -- * Carriers
  , LensRep(..)
  , ColensRep(..)
    -- * Primitive operators
  , withLens
  , withColens
    -- * Optics
  , first
  , ixfirst
  , cofirst
  , second
  , ixsecond
  , cosecond
  , united
  , voided
  , valued
  , root
  , branches
    -- * Operators
  , toPastro
  , toTambara
) where

import Data.Profunctor.Strong
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Index
import Data.Profunctor.Optic.Type
import Data.Tree
import Data.Void (Void, absurd)
import GHC.Generics hiding (from, to)
import qualified Data.Bifunctor as B

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> import Data.Tree
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- 'Lens' & 'Ixlens'
---------------------------------------------------------------------

-- | Obtain a 'Lens' from a getter and setter.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input functions satisfy the following
-- properties:
--
-- * @sa (sbt s a) ≡ a@
--
-- * @sbt s (sa s) ≡ s@
--
-- * @sbt (sbt s a1) a2 ≡ sbt s a2@
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
lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens sa sbt = dimap (id &&& sa) (uncurry sbt) . second'
{-# INLINE lens #-}

-- | Obtain an indexed 'Lens' from an indexed getter and a setter.
--
-- Compare 'lens' and 'Data.Profunctor.Optic.Traversal.ixtraversal'.
--
ixlens :: (s -> (i , a)) -> (s -> b -> t) -> Ixlens i s t a b
ixlens sia sbt = ixlensVl $ \iab s -> sbt s <$> uncurry iab (sia s)
{-# INLINE ixlens #-}

-- | Transform a Van Laarhoven lens into a profunctor lens.
--
-- Compare 'Data.Profunctor.Optic.Grate.grateVl' and 'Data.Profunctor.Optic.Traversal.traversalVl'.
--
lensVl :: (forall f. Functor f => (a -> f b) -> s -> f t) -> Lens s t a b
lensVl o = dimap ((info &&& values) . o (flip Index id)) (uncurry id . swap) . first'
{-# INLINE lensVl #-}

-- | Transform an indexed Van Laarhoven lens into an indexed profunctor 'Lens'.
--
-- An 'Ixlens' is a valid 'Lens' and a valid 'IxTraversal'. 
--
-- Compare 'lensVl' & 'Data.Profunctor.Optic.Traversal.ixtraversalVl'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @iabst (const pure) ≡ pure@
--
-- * @fmap (iabst $ const f) . (iabst $ const g) ≡ getCompose . iabst (const $ Compose . fmap f . g)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
ixlensVl :: (forall f. Functor f => (i -> a -> f b) -> s -> f t) -> Ixlens i s t a b
ixlensVl f = lensVl $ \iab -> f (curry iab) . snd
{-# INLINE ixlensVl #-}

-- | Obtain a 'Lens' from its free tensor representation.
--
matching :: (s -> (c , a)) -> ((c , b) -> t) -> Lens s t a b
matching sca cbt = dimap sca cbt . second'

-- | TODO: Document
--
cloneLens :: ALens s t a b -> Lens s t a b
cloneLens o = withLens o lens 

---------------------------------------------------------------------
-- 'Colens' & 'Cxlens'
---------------------------------------------------------------------

-- | Obtain a 'Colens' from a getter and setter. 
--
-- @
-- 'colens' f g ≡ \\f g -> 're' ('lens' f g)
-- 'colens' bsia bt ≡ 'colensVl' '$' \\ts b -> bsia b '<$>' (ts . bt '$' b)
-- 'review' $ 'colens' f g ≡ f
-- 'set' . 're' $ 're' ('lens' f g) ≡ g
-- @
--
-- A 'Colens' is a 'Review', so you can specialise types to obtain:
--
-- @ 'review' :: 'Colens'' s a -> a -> s @
--
-- See 'Data.Profunctor.Optic.Property'.
--
colens :: (b -> s -> a) -> (b -> t) -> Colens s t a b
colens bsa bt = unsecond . dimap (uncurry bsa) (id &&& bt)

-- | TODO: Document
--
cxlens :: ((k -> b) -> s -> a) -> (b -> t) -> Cxlens k s t a b
cxlens bsa bt = colens bsa (bt .)

-- | Transform a Van Laarhoven colens into a profunctor colens.
--
-- Compare 'Data.Profunctor.Optic.Grate.grateVl'.
--
colensVl :: (forall f. Functor f => (t -> f s) -> b -> f a) -> Colens s t a b
colensVl o = unfirst . dimap (uncurry id . swap) ((info &&& values) . o (flip Index id))

-- | Obtain a 'Colens' from its free tensor representation.
--
comatching :: ((c , s) -> a) -> (b -> (c , t)) -> Colens s t a b
comatching csa bct = unsecond . dimap csa bct

-- | TODO: Document
--
cloneColens :: AColens s t a b -> Colens s t a b
cloneColens o = withColens o colens 

---------------------------------------------------------------------
-- 'LensRep'
---------------------------------------------------------------------

-- | The `LensRep` profunctor precisely characterizes a 'Lens'.
--
data LensRep a b s t = LensRep (s -> a) (s -> b -> t)

type ALens s t a b = Optic (LensRep a b) s t a b

type ALens' s a = ALens s s a a

instance Profunctor (LensRep a b) where
  dimap f g (LensRep sa sbt) = LensRep (sa . f) (\s -> g . sbt (f s))

instance Strong (LensRep a b) where
  first' (LensRep sa sbt) =
    LensRep (\(a, _) -> sa a) (\(s, c) b -> (sbt s b, c))

  second' (LensRep sa sbt) =
    LensRep (\(_, a) -> sa a) (\(c, s) b -> (c, sbt s b))

instance Sieve (LensRep a b) (Index a b) where
  sieve (LensRep sa sbt) s = Index (sa s) (sbt s)

instance Representable (LensRep a b) where
  type Rep (LensRep a b) = Index a b

  tabulate f = LensRep (\s -> info (f s)) (\s -> values (f s))

data ColensRep a b s t = ColensRep (b -> s -> a) (b -> t)

type AColens s t a b = Optic (ColensRep a b) s t a b

type AColens' s a = AColens s s a a 

instance Profunctor (ColensRep a b) where
  dimap f g (ColensRep bsa bt) = ColensRep (\b s -> bsa b (f s)) (g . bt)

instance Costrong (ColensRep a b) where
  unfirst (ColensRep baca bbc) = ColensRep (curry foo) (forget2 $ bbc . fst)
    where foo = uncurry baca . shuffle . B.second undefined . swap --TODO: B.second bbc
          shuffle (x,(y,z)) = (y,(x,z))

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Extract the two functions that characterize a 'Lens'.
--
withLens :: ALens s t a b -> ((s -> a) -> (s -> b -> t) -> r) -> r
withLens o f = case o (LensRep id (flip const)) of LensRep x y -> f x y

-- | Extract the two functions that characterize a 'Colens'.
--
withColens :: AColens s t a b -> ((b -> s -> a) -> (b -> t) -> r) -> r
withColens l f = case l (ColensRep (flip const) id) of ColensRep x y -> f x y

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

-- | TODO: Document
--
first :: Lens (a , c) (b , c) a b
first = first'

-- | TODO: Document
--
ixfirst :: Ixlens i (a , c) (b , c) a b
ixfirst = lmap assocl . first'

-- | TODO: Document
--
cofirst :: Colens a b (a , c) (b , c)
cofirst = unfirst

-- | TODO: Document
--
second :: Lens (c , a) (c , b) a b
second = second'

-- | TODO: Document
--
ixsecond :: Ixlens i (c , a) (c , b) a b
ixsecond = lmap (\(i, (c, a)) -> (c, (i, a))) . second'

-- | TODO: Document
--
cosecond :: Colens a b (c , a) (c , b)
cosecond = unsecond

-- | There is a `Unit` in everything.
--
-- >>> "hello" ^. united
-- ()
-- >>> "hello" & united .~ ()
-- "hello"
--
united :: Lens' a ()
united = lens (const ()) const

-- | There is everything in a `Void`.
--
-- >>> [] & fmapped . voided <>~ "Void" 
-- []
-- >>> Nothing & fmapped . voided ..~ abs
-- Nothing
--
voided :: Lens' Void a
voided = lens absurd const

-- | TODO: Document
--
-- Compare 'Data.Profunctor.Optic.Prism.keyed'.
--
valued :: Eq k => k -> Lens' (k -> v) v
valued k = lens ($ k) (\g v' x -> if (k == x) then v' else g x)

-- | A 'Lens' that focuses on the root of a 'Tree'.
--
-- >>> view root $ Node 42 []
-- 42
--
root :: Lens' (Tree a) a
root = lensVl $ \f (Node a as) -> (`Node` as) <$> f a
{-# INLINE root #-}

-- | A 'Lens' returning the direct descendants of the root of a 'Tree'
--
-- @'Data.Profunctor.Optic.View.view' 'branches' ≡ 'subForest'@
--
branches :: Lens' (Tree a) [Tree a]
branches = lensVl $ \f (Node a as) -> Node a <$> f as
{-# INLINE branches #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Use a 'Lens' to construct a 'Pastro'.
--
toPastro :: ALens s t a b -> p a b -> Pastro p s t
toPastro o p = withLens o $ \sa sbt -> Pastro (uncurry sbt . swap) p (\s -> (sa s, s))

-- | Use a 'Lens' to construct a 'Tambara'.
--
toTambara :: Strong p => ALens s t a b -> p a b -> Tambara p s t
toTambara o p = withLens o $ \sa sbt -> Tambara (first . lens sa sbt $ p)
