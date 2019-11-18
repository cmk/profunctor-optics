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
  , Colens
  , Colens'
  , AColens
  , AColens'
    -- * Constructors
  , lens
  , vlens
  , colens
  , matching
  , rematching
  , toPastro
  , toTambara
  , cloneLens
  , cloneColens
    -- * Representatives
  , LensRep(..)
  , ColensRep(..)
    -- * Primitive operators
  , withLens
  , withColens
    -- * Common optics
  , first
  , second
  , rfirst
  , rsecond
    -- * Derived operators
  , unit
  , void 
  , ix
) where

import Data.Profunctor.Strong (Pastro(..), Tambara(..))
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Type
import Data.Void (Void, absurd)
import qualified Data.Bifunctor as B

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- 'Lens' 
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

-- | Transform a Van Laarhoven lens into a profunctor lens.
--
-- Compare 'Data.Profunctor.Optic.Grate.vlgrate'.
--
vlens :: (forall f. Functor f => (a -> f b) -> s -> f t) -> Lens s t a b
vlens o = dimap ((info &&& values) . o (flip Context id)) (uncurry id . swp) . first'

-- | Obtain a 'Colens' from a getter and setter. 
--
-- * @colens f g ≡ \f g -> re (lens f g)@
--
-- * @review $ colens f g ≡ f@
--
-- * @set . re $ re (lens f g) ≡ g@
--
-- A 'Colens' is a 'Review', so you can specialise types to obtain:
--
-- @ 'review' :: 'Colens'' s a -> a -> s @
--
-- See 'Data.Profunctor.Optic.Property'.
--
colens :: (b -> s -> a) -> (b -> t) -> Colens s t a b
colens bsa bt = unsecond . dimap (uncurry bsa) (id &&& bt)

-- | Obtain a 'Lens' from its free tensor representation.
--
matching :: (s -> (c , a)) -> ((c , b) -> t) -> Lens s t a b
matching sca cbt = dimap sca cbt . second'

-- | Obtain a 'Colens' from its free tensor representation.
--
rematching :: ((c , s) -> a) -> (b -> (c , t)) -> Colens s t a b
rematching csa bct = unsecond . dimap csa bct

-- | Use a 'Lens' to construct a 'Pastro'.
--
toPastro :: ALens s t a b -> p a b -> Pastro p s t
toPastro o p = withLens o $ \sa sbt -> Pastro (uncurry sbt . swp) p (\s -> (sa s, s))

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

instance Sieve (LensRep a b) (Context a b) where
  sieve (LensRep sa sbt) s = Context (sa s) (sbt s)

instance Representable (LensRep a b) where
  type Rep (LensRep a b) = Context a b

  tabulate f = LensRep (\s -> info (f s)) (\s -> values (f s))

data ColensRep a b s t = ColensRep (b -> s -> a) (b -> t)

type AColens s t a b = Optic (ColensRep a b) s t a b

type AColens' s a = AColens s s a a 

instance Profunctor (ColensRep a b) where
  dimap f g (ColensRep bsa bt) = ColensRep (\b s -> bsa b (f s)) (g . bt)

instance Costrong (ColensRep a b) where
  unfirst (ColensRep baca bbc) = ColensRep (curry foo) (forget2 $ bbc . fst)
    where foo = uncurry baca . shuffle . B.second undefined . swp --TODO: B.second bbc
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
-- Common lenses 
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
rfirst :: Colens a b (a , c) (b , c)
rfirst = unfirst

-- | TODO: Document
--
rsecond :: Colens a b (c , a) (c , b)
rsecond = unsecond

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
-- >>> [] & fmapped . void <>~ "Void" 
-- []
-- >>> Nothing & fmapped . void %~ abs
-- Nothing
--
void :: Lens' Void a
void = lens absurd const

-- | TODO: Document
--
ix :: Eq k => k -> Lens' (k -> v) v
ix k = lens ($ k) (\g v' x -> if (k == x) then v' else g x)
