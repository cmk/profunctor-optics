{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
module Data.Profunctor.Optic.Iso (
    -- * Constructors
    Equality, Equality'
  , Iso, Iso'
  , iso
  , isoVl
  , reixing
  , recxing
  , fmapping
  , contramapping
  , dimapping
  , yoneda 
  , coyoneda
  , inverting
  , cloneIso
    -- * Optics
  , equaled
  , coerced
  , generic
  , generic1
  , adjuncted
  , tabulated
  , indexing
  , coindexing
  , unzipped
  , cozipped
  , swapped 
  , eswapped 
  , associated 
  , eassociated
  , excised
  , flipped 
  , involuted
  , uncurried
    -- * Operators
  , au
  , aup
  , withIso
  , re
    -- * Auxiliary Types
  , Re(..)
    -- * Classes
  , Profunctor(..)
) where

import Data.Coerce
import Data.Functor.Adjunction hiding (adjuncted)
import Data.Maybe (fromMaybe)
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Dual (Re(..), re)
import Data.Profunctor.Optic.Index
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Types
import Data.Profunctor.Yoneda (Coyoneda(..), Yoneda(..))
import qualified Data.Functor.Rep as F
import qualified GHC.Generics as G

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XAllowAmbiguousTypes
-- >>> import Data.Monoid
-- >>> import Data.Function ((&))
-- >>> import Data.Functor.Identity
-- >>> import Data.Functor.Const
-- >>> import Data.Profunctor.Types
-- >>> :load Data.Profunctor.Optic
-- >>> import Prelude

---------------------------------------------------------------------
-- 'Iso' 
---------------------------------------------------------------------

-- | Obtain an 'Iso' from two inverses.
--
-- @
-- o . 're' o ≡ 'id'
-- 're' o . o ≡ 'id'
-- 'Data.Profunctor.Optic.View.view' o ('Data.Profunctor.Optic.View.review' o b) ≡ b
-- 'Data.Profunctor.Optic.View.review' o ('Data.Profunctor.Optic.View.view' o s) ≡ s
-- @
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input functions satisfy the following
-- properties:
--
-- * @sa . bt ≡ id@
--
-- * @bt . sa ≡ id@
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
iso :: (s -> a) -> (b -> t) -> Iso s t a b
iso = dimap
{-# INLINE iso #-}

-- | Transform a Van Laarhoven 'Iso' into a profunctor 'Iso'.
--
isoVl :: (forall f g. Functor f => Functor g => (g a -> f b) -> g s -> f t) -> Iso s t a b
isoVl abst = iso f g
  where f = getConst . (abst (Const . runIdentity)) . Identity
        g = runIdentity . (abst (Identity . getConst)) . Const
{-# INLINE isoVl #-}

-- | Remap the indices of an indexed optic.
--
reixing :: Profunctor p => AIso' k1 k2 -> Ixoptic p k1 s t a b -> Ixoptic p k2 s t a b
reixing = flip withIso reix
{-# INLINE reixing #-}

-- | Remap the indices of a coindexed optic.
--
recxing :: Profunctor p => AIso' k1 k2 -> Cxoptic p k1 s t a b -> Cxoptic p k2 s t a b
recxing = flip withIso recx
{-# INLINE recxing #-}

-- | Lift an 'Iso' into a pair of functors.
--
fmapping :: Functor f => Functor g => AIso s t a b -> Iso (f s) (g t) (f a) (g b)
fmapping l = withIso l $ \sa bt -> iso (fmap sa) (fmap bt)
{-# INLINE fmapping #-}

-- | Lift an 'Iso' into a pair of 'Contravariant' functors.
--
contramapping :: Contravariant f => Contravariant g => AIso s t a b -> Iso (f a) (g b) (f s) (g t)
contramapping f = withIso f $ \sa bt -> iso (contramap sa) (contramap bt)
{-# INLINE contramapping #-}

-- | Lift a pair of 'Iso's into a pair of profunctors. 
--
dimapping :: Profunctor p => Profunctor q => AIso s1 t1 a1 b1 -> AIso s2 t2 a2 b2 -> Iso (p a1 s2) (q b1 t2) (p s1 a2) (q t1 b2)
dimapping f g = withIso f $ \sa1 bt1 -> withIso g $ \sa2 bt2 -> iso (dimap sa1 sa2) (dimap bt1 bt2)
{-# INLINE dimapping #-}

-- | Lift an 'Iso' into a 'Yoneda'.
--
yoneda :: Profunctor p => Iso s t a b -> p a b -> Yoneda p s t
yoneda o p = withIso o $ \sa bt -> Yoneda $ \f g -> dimap (sa . f) (g . bt) p 
{-# INLINE yoneda #-}

-- | Lift an 'Iso' into a 'Coyoneda'.
--
coyoneda :: Iso s t a b -> p a b -> Coyoneda p s t
coyoneda o p = withIso o $ \sa bt -> Coyoneda sa bt p
{-# INLINE coyoneda #-}

-- | Invert an isomorphism.
--
-- @
-- 'inverting' ('inverting' o) ≡ o
-- 'inverting' ≡ 'cloneIso' '.' 're'
-- @
--
inverting :: AIso s t a b -> Iso b a t s
inverting o = withIso o $ \sa bt -> iso bt sa
{-# INLINE inverting #-}

-- | Convert from 'AIso' back to any 'Iso'.
--
cloneIso :: AIso s t a b -> Iso s t a b
cloneIso k = withIso k $ \sa bt -> iso sa bt
{-# INLINE cloneIso #-}

---------------------------------------------------------------------
-- Optics
---------------------------------------------------------------------

-- | Obtain an 'Iso'' directly from type equaled constraints.
--
-- >>> :t (^. equaled)
-- (^. equaled) :: a -> a
--
equaled :: s ~ a => t ~ b => Equality s t a b
equaled = id
{-# INLINE equaled #-}

-- | Obtain an 'Iso' from data types that are representationally equal.
--
-- >>> view coerced 'x' :: Identity Char
-- Identity 'x'
--
coerced :: Coercible s a => Coercible t b => Iso s t a b
coerced = dimap coerce coerce
{-# INLINE coerced #-}

-- | An 'Iso' between 'Generic' representations.
--
-- >>> view (generic . re generic) "hello" :: String
-- "hello"
--
generic :: G.Generic a => G.Generic b => Iso a b (G.Rep a c) (G.Rep b c)
generic = iso G.from G.to
{-# INLINE generic #-}

-- | An 'Iso' between 'Generic1' representations.
--
generic1 :: G.Generic1 f => G.Generic1 g => Iso (f a) (g b) (G.Rep1 f a) (G.Rep1 g b)
generic1 = iso G.from1 G.to1
{-# INLINE generic1 #-}

-- | An 'Iso' between a functor and its adjoint.
--
-- Useful for converting between lens-like optics and grate-like optics:
--
-- @
-- 'Data.Profunctor.Optic.Setter.over' 'adjuncted' :: 'Adjunction' f u => ((a -> u b) -> s -> u t) -> (f a -> b) -> f s -> t
-- @
--
adjuncted :: Adjunction f u => Iso (f a -> b) (f s -> t) (a -> u b) (s -> u t)
adjuncted = iso leftAdjunct rightAdjunct
{-# INLINE adjuncted #-}

-- | An 'Iso' between a functor and its Yoneda representation.
--
tabulated :: F.Representable f => F.Representable g => Iso (f a) (g b) (F.Rep f -> a) (F.Rep g -> b)
tabulated = iso F.index F.tabulate
{-# INLINE tabulated #-}

-- | TODO: Document
--
indexing :: ((a -> b) -> s -> t) -> Iso s t (Index s x x) (Index s a b)
indexing abst = iso (flip Index id) (\(Index s ab) -> abst ab s) 
{-# INLINE indexing #-}

-- | TODO: Document
--
coindexing :: ((a -> b) -> s -> t) -> Iso s t (Coindex t b a) (Coindex t x x)
coindexing abst = iso (\s -> Coindex $ \ab -> abst ab s) trivial
{-# INLINE coindexing #-}

-- | A right adjoint admits an intrinsic notion of zipping.
--
unzipped :: Adjunction f u => Iso (u a , u b) (u c , u d) (u (a , b)) (u (c , d)) 
unzipped = iso zipR unzipR
{-# INLINE unzipped #-}

-- | A left adjoint must be inhabited by exactly one element.
--
cozipped :: Adjunction f u => Iso ((f a) + (f b)) ((f c) + (f d)) (f (a + b)) (f (c + d))
cozipped = iso uncozipL cozipL
{-# INLINE cozipped #-}

-- | Swap sides of a product.
--
swapped :: Iso (a , b) (c , d) (b , a) (d , c)
swapped = iso swap swap
{-# INLINE swapped #-}

-- | Swap sides of a sum.
--
eswapped :: Iso (a + b) (c + d) (b + a) (d + c)
eswapped = iso eswap eswap
{-# INLINE eswapped #-}

-- | An 'Iso' defined by left-association of nested tuples.
--
associated :: Iso (a , (b , c)) (d , (e , f)) ((a , b) , c) ((d , e) , f)
associated = iso assocl assocr
{-# INLINE associated #-}

-- | An 'Iso' defined by left-association of nested tuples.
--
eassociated :: Iso (a + (b + c)) (d + (e + f)) ((a + b) + c) ((d + e) + f)
eassociated = iso eassocl eassocr
{-# INLINE eassociated #-}

-- | Excise a single value from a type.
--
-- >>> review (excised "foo") "foo"
-- Nothing
-- >>> review (excised "foo") "foobar"
-- Just "foobar"
--
excised :: Eq a => a -> Iso' (Maybe a) a
excised a = iso (fromMaybe a) g
  where g a1 | a1 == a = Nothing
             | otherwise = Just a1
{-# INLINE excised #-}

-- | Flip two arguments of a function.
--
-- >>> (view flipped (,)) 1 2
-- (2,1)
--
flipped :: Iso (a -> b -> c) (d -> e -> f) (b -> a -> c) (e -> d -> f)
flipped = iso flip flip
{-# INLINE flipped #-}

-- | An 'Iso' defined by a function that is its own inverse.
--
-- @
-- 'involuted' ≡ 'Control.Monad.join' 'iso'
-- @
--
-- >>> "live" ^. involuted reverse
-- "evil"
--
-- >>> "live" & involuted reverse ..~ ('d':) 
-- "lived"
--
involuted :: (s -> a) -> Iso s a a s
involuted f = iso f f
{-# INLINE involuted #-}

-- | Uncurry a function.
--
-- >>> (fst ^. inverting uncurried) 3 4
-- 3
--
uncurried :: Iso (a -> b -> c) (d -> e -> f) ((a , b) -> c) ((d , e) -> f)
uncurried = iso uncurry curry
{-# INLINE uncurried #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Based on /ala/ from Conor McBride's work on Epigram.
--
-- This version is generalized to accept any 'Iso', not just a @newtype@.
--
-- >>> au (iso getSum Sum) foldMap [1,2,3,4]
-- 10
--
-- You may want to think of this combinator as having the following, simpler type:
--
-- @
-- 'au' :: 'AIso' s t a b -> ((b -> t) -> e -> s) -> e -> a
-- @
--
au :: Functor f => AIso s t a b -> ((b -> t) -> f s) -> f a
au k = withIso k $ \ sa bt f -> fmap sa (f bt)
{-# INLINE au #-}

-- | Variant of 'au' for profunctors. 
--
-- @
-- 'flip' 'aup' 'runStar' :: Functor f => AIso s t a (f a) -> Star f c s -> c -> t
-- @
--
aup :: Profunctor p => Functor f => AIso s t a b -> (p c a -> f b) -> p c s -> f t
aup o = withIso o $ \sa bt f g -> fmap bt (f (rmap sa g))
{-# INLINE aup #-}

-- | Given a conversion on one side of an 'Iso', recover the other.
-- reover moved to Data.Profunctor.Optic.Lens (generalized from AIso to ARelens)
