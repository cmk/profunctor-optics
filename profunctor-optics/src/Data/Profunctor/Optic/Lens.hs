{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Lens (
    -- * Types
    Lens
  , Lens'
  , ALens
  , ALens'
  , Relens
  , Relens'
  , ARelens
  , ARelens'
    -- * Indxed Types
  , Ixlens
  , Ixlens'
  , Rxlens
  , Rxlens'
    -- * Constructors
  , lens
  , relens
  , lensVl
  , relensVl
  , matching
  , rematching
  , toPastro
  , toTambara
  , cloneLens
  , cloneRelens
    -- * Indexed Constructors
  , ilens
  , ilensVl
  , rlens
  , rlensVl
    -- * Representatives
  , LensRep(..)
  , RelensRep(..)
    -- * Primitive operators
  , withLens
  , withRelens
    -- * Optics
  , first
  , second
  , refirst
  , resecond
    -- * Indexed optics
  , ifirst
  , isecond
  , rfirst
  , rsecond
    -- * Derived operators
  , unit
  , devoid
  , ix
    -- * Classes
  , Strong(..)
  , Costrong(..)
) where

import Data.Profunctor.Strong
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Indexed
import Data.Profunctor.Optic.Type
import Data.Void (Void, absurd)
import qualified Data.Bifunctor as B

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- 'Lens' & 'Relens'
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

-- | Obtain a 'Relens' from a getter and setter. 
--
-- * @relens f g ≡ \f g -> re (lens f g)@
--
-- * @review $ relens f g ≡ f@
--
-- * @set . re $ re (lens f g) ≡ g@
--
-- A 'Relens' is a 'Review', so you can specialise types to obtain:
--
-- @ 'review' :: 'Relens'' s a -> a -> s @
--
-- See 'Data.Profunctor.Optic.Property'.
--
relens :: (b -> s -> a) -> (b -> t) -> Relens s t a b
relens bsa bt = unsecond . dimap (uncurry bsa) (id &&& bt)

-- | Transform a Van Laarhoven lens into a profunctor lens.
--
-- Compare 'Data.Profunctor.Optic.Grate.grateVl'.
--
lensVl :: (forall f. Functor f => (a -> f b) -> s -> f t) -> Lens s t a b
lensVl o = dimap ((info &&& values) . o (flip Index id)) (uncurry id . swap) . first'
{-# INLINE lensVl #-}

-- | Transform a Van Laarhoven relens into a profunctor relens.
--
-- Compare 'Data.Profunctor.Optic.Grate.grateVl'.
--
relensVl :: (forall f. Functor f => (t -> f s) -> b -> f a) -> Relens s t a b 
relensVl o = unfirst . dimap (uncurry id . swap) ((info &&& values) . o (flip Index id))

-- | Obtain a 'Lens' from its free tensor representation.
--
matching :: (s -> (c , a)) -> ((c , b) -> t) -> Lens s t a b
matching sca cbt = dimap sca cbt . second'

-- | Obtain a 'Relens' from its free tensor representation.
--
rematching :: ((c , s) -> a) -> (b -> (c , t)) -> Relens s t a b
rematching csa bct = unsecond . dimap csa bct

-- | Use a 'Lens' to construct a 'Pastro'.
--
toPastro :: ALens s t a b -> p a b -> Pastro p s t
toPastro o p = withLens o $ \sa sbt -> Pastro (uncurry sbt . swap) p (\s -> (sa s, s))

-- | Use a 'Lens' to construct a 'Tambara'.
--
toTambara :: Strong p => ALens s t a b -> p a b -> Tambara p s t
toTambara o p = withLens o $ \sa sbt -> Tambara (first . lens sa sbt $ p)

-- | TODO: Document
--
cloneLens :: ALens s t a b -> Lens s t a b
cloneLens o = withLens o lens 

-- | TODO: Document
--
cloneRelens :: ARelens s t a b -> Relens s t a b
cloneRelens o = withRelens o relens 

---------------------------------------------------------------------
-- 'Ixlens' & 'Rxlens'
---------------------------------------------------------------------

-- | Obtain an indexed 'Lens' from an indexed getter and a setter.
--
-- Compare 'lens' and 'Data.Profunctor.Optic.Traversal.itraversal'.
--
ilens :: (s -> (i , a)) -> (s -> b -> t) -> Ixlens i s t a b
ilens sia sbt = ilensVl $ \iab s -> sbt s <$> uncurry iab (sia s)
{-# INLINE ilens #-}

-- | Obtain an indexed 'Relens' from an indexed getter and a setter.
--
rlens :: (b -> s -> (r , a)) -> (b -> t) -> Rxlens r s t a b
rlens bsia bt = rlensVl $ \ts b -> bsia b <$> (ts . bt $ b) 
{-# INLINE rlens #-}

-- | Transform an indexed Van Laarhoven lens into an indexed profunctor 'Lens'.
--
-- Compare 'lensVl'.
--
ilensVl :: (forall f. Functor f => (i -> a -> f b) -> s -> f t) -> Ixlens i s t a b
ilensVl f = lensVl $ \iab -> f (curry iab) . snd
{-# INLINE ilensVl #-}

-- | Transform an indexed Van Laarhoven relens into an indexed profunctor 'Relens'.
--
-- Compare 'ilensVl' and 'relensVl'.
--
rlensVl :: (forall f. Functor f => (t -> f s) -> b -> f (r, a)) -> Rxlens r s t a b
rlensVl f = relensVl $ \ts -> f (fmap snd . ts)
{-# INLINE rlensVl #-}

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

data RelensRep a b s t = RelensRep (b -> s -> a) (b -> t)

type ARelens s t a b = Optic (RelensRep a b) s t a b

type ARelens' s a = ARelens s s a a 

instance Profunctor (RelensRep a b) where
  dimap f g (RelensRep bsa bt) = RelensRep (\b s -> bsa b (f s)) (g . bt)

instance Costrong (RelensRep a b) where
  unfirst (RelensRep baca bbc) = RelensRep (curry foo) (forget2 $ bbc . fst)
    where foo = uncurry baca . shuffle . B.second undefined . swap --TODO: B.second bbc
          shuffle (x,(y,z)) = (y,(x,z))

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Extract the two functions that characterize a 'Lens'.
--
withLens :: ALens s t a b -> ((s -> a) -> (s -> b -> t) -> r) -> r
withLens o f = case o (LensRep id (flip const)) of LensRep x y -> f x y

-- | Extract the two functions that characterize a 'Relens'.
--
withRelens :: ARelens s t a b -> ((b -> s -> a) -> (b -> t) -> r) -> r
withRelens l f = case l (RelensRep (flip const) id) of RelensRep x y -> f x y

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

-- | TODO: Document
--
first :: Lens (a , c) (b , c) a b
first = first'

-- | TODO: Document
--
second :: Lens (c , a) (c , b) a b
second = second'

-- | TODO: Document
--
refirst :: Relens a b (a , c) (b , c)
refirst = unfirst

-- | TODO: Document
--
resecond :: Relens a b (c , a) (c , b)
resecond = unsecond

-- | There is a `Unit` in everything.
--
-- >>> "hello" ^. unit
-- ()
-- >>> "hello" & unit .~ ()
-- "hello"
--
unit :: Lens' a ()
unit = lens (const ()) const

-- | There is everything in a `Void`.
--
-- >>> [] & fmapped . devoid <>~ "Void" 
-- []
-- >>> Nothing & fmapped . devoid %~ abs
-- Nothing
--
devoid :: Lens' Void a
devoid = lens absurd const

-- | TODO: Document
--
ix :: Eq k => k -> Lens' (k -> v) v
ix k = lens ($ k) (\g v' x -> if (k == x) then v' else g x)

---------------------------------------------------------------------
-- Indexed optics 
---------------------------------------------------------------------

-- | TODO: Document
--
ifirst :: Ixlens i (a , c) (b , c) a b
ifirst = lmap assocl . first'

-- | TODO: Document
--
isecond :: Ixlens i (c , a) (c , b) a b
isecond = lmap (\(i, (c, a)) -> (c, (i, a))) . second'

-- | TODO: Document
--
rfirst :: Rxlens r a b (a , c) (b , c)
rfirst = unfirst . lmap assocr

-- | TODO: Document
--
rsecond :: Rxlens r a b (c , a) (c , b)
rsecond = unsecond . lmap (\(c, (r, a)) -> (r, (c, a)))
