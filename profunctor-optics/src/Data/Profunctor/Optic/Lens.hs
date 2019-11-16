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
    -- * Constructors
  , lens
  , relens
  , vllens
  , matching
  , rematching
  , toPastro
  , toTambara
  , foldingl
  , cloneLens
  , cloneRelens
    -- * Representatives
  , LensRep(..)
  , RelensRep(..)
    -- * Primitive operators
  , withLens
  , withRelens
    -- * Common optics
  , first
  , second
  , refirst
  , resecond
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
import qualified Control.Foldl as F

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
vllens :: (forall f. Functor f => (a -> f b) -> s -> f t) -> Lens s t a b
vllens o = dimap ((info &&& values) . o (flip PStore id)) (uncurry id . swp) . first'

-- | Obtain a 'Lens' from its free tensor representation.
--
matching :: (s -> (c , a)) -> ((c , b) -> t) -> Lens s t a b
matching sca cbt = dimap sca cbt . second'

-- | Obtain a 'Relens' from its free tensor representation.
--
rematching :: ((c , s) -> a) -> (b -> (c , t)) -> Relens s t a b
rematching csa bct = unsecond . dimap csa bct

-- | Lift a 'Lens' into a 'Pastro'.
--
toPastro :: ALens s t a b -> p a b -> Pastro p s t
toPastro o p = withLens o $ \sa sbt -> Pastro (uncurry sbt . swp) p (\s -> (sa s, s))

-- | Lift a 'Lens' into a 'Tambara'.
--
toTambara :: Strong p => ALens s t a b -> p a b -> Tambara p s t
toTambara o p = withLens o $ \sa sbt -> Tambara (first . lens sa sbt $ p)

-- | Lift a 'Lens'' into a Moore machine.
--
foldingl :: ALens s s a b -> s -> F.Fold b a
foldingl o s = withLens o $ \sa sbs -> F.Fold sbs s sa

-- | TODO: Document
--
cloneLens :: ALens s t a b -> Lens s t a b
cloneLens o = withLens o lens 

-- | TODO: Document
--
cloneRelens :: ARelens s t a b -> Relens s t a b
cloneRelens o = withRelens o relens 

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

instance Sieve (LensRep a b) (PStore a b) where
  sieve (LensRep sa sbt) s = PStore (sa s) (sbt s)

instance Representable (LensRep a b) where
  type Rep (LensRep a b) = PStore a b

  tabulate f = LensRep (\s -> info (f s)) (\s -> values (f s))

data RelensRep a b s t = RelensRep (b -> s -> a) (b -> t)

type ARelens s t a b = Optic (RelensRep a b) s t a b

type ARelens' s a = ARelens s s a a 

instance Profunctor (RelensRep a b) where
  dimap f g (RelensRep bsa bt) = RelensRep (\b s -> bsa b (f s)) (g . bt)

instance Costrong (RelensRep a b) where
  unfirst (RelensRep baca bbc) = RelensRep (curry foo) (forget2 $ bbc . fst)
    where foo = uncurry baca . shuffle . B.second undefined . swp --TODO: B.second bbc
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
