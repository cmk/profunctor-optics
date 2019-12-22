{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
module Data.Profunctor.Optic.Iso (
    -- * Types
    Equality
  , Equality'
  , Iso
  , Iso'
    -- * Constructors
  , iso
  , isoVl
  , imapping
  , kmapping
  , fmapping
  , contramapping
  , dimapping
  , toYoneda 
  , toCoyoneda
  , cloneIso
    -- * Optics
  , equaled
  , coerced
  , wrapped
  , rewrapped
  , rewrapped'
  , generic
  , generic1
  , adjuncted
  , tabulated
  , transposed
  , flipped 
  , curried
  , unzipped
  , cozipped
  , swapped 
  , coswapped 
  , associated 
  , coassociated
  , involuted 
  , added 
  , subtracted
  , non 
  , anon
    -- * Primitive operators
  , withIso
    -- * Operators
  , invert
  , reover
  , reixed
  , recxed
  , op
  , au 
  , aup
  , ala
    -- * Auxilliary Types
  , Re(..)
) where

import Control.Newtype.Generics (Newtype(..), op)
import Data.Coerce
import Data.Functor.Adjunction hiding (adjuncted)
import Data.Group
import Data.Maybe (fromMaybe)
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Index
import Data.Profunctor.Optic.Types
import Data.Profunctor.Yoneda (Coyoneda(..), Yoneda(..))


import qualified Data.Functor.Rep as F
import qualified Control.Monad as M (join)
import qualified GHC.Generics as G

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XAllowAmbiguousTypes
-- >>> import Data.Monoid
-- >>> import Data.Int.Instance ()
-- >>> import Data.List.Index
-- >>> import Data.Semiring
-- >>> import Data.Sequence as Seq hiding (reverse)
-- >>> import Data.Functor.Identity
-- >>> import Data.Functor.Const
-- >>> import Data.Profunctor.Types
-- >>> :load Data.Profunctor.Optic
-- >>> let itraversed :: Ixtraversal Int [a] [b] a b ; itraversed = itraversalVl itraverse

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

-- | Lift an 'Iso' into an indexed version. 
--
-- >>> ilists (itraversed . imapping swapped) [(40,'f'),(41,'o'),(42,'o')]
-- [(0,('f',40)),(1,('o',41)),(2,('o',42))]
--
imapping :: Profunctor p => AIso s t a b -> IndexedOptic p i s t a b
imapping o = withIso o imap
{-# INLINE imapping #-}

-- | Lift an 'Iso' into a coindexed version. 
--
kmapping :: Profunctor p => AIso s t a b -> CoindexedOptic p k s t a b
kmapping o = withIso o kmap
{-# INLINE kmapping #-}

-- | Lift an 'Iso' into a pair of functors.
--
fmapping :: Functor f => Functor g => AIso s t a b -> Iso (f s) (g t) (f a) (g b)
fmapping l = withIso l $ \sa bt -> iso (fmap sa) (fmap bt)
{-# INLINE fmapping #-}

-- | Lift an 'Iso' into a pair of 'Contravariant' functors.
--
-- @
-- contramapping :: 'Contravariant' f => 'Iso' s t a b -> 'Iso' (f a) (f b) (f s) (f t)
-- @
--
contramapping :: Contravariant f => Contravariant g => AIso s t a b -> Iso (f a) (g b) (f s) (g t)
contramapping f = withIso f $ \sa bt -> iso (contramap sa) (contramap bt)
{-# INLINE contramapping #-}

-- | Lift a pair of 'Iso's into a pair of profunctors. 
--
--
--
dimapping :: Profunctor p => Profunctor q => AIso s1 t1 a1 b1 -> AIso s2 t2 a2 b2 -> Iso (p a1 s2) (q b1 t2) (p s1 a2) (q t1 b2)
dimapping f g = withIso f $ \sa1 bt1 -> withIso g $ \sa2 bt2 -> iso (dimap sa1 sa2) (dimap bt1 bt2)
{-# INLINE dimapping #-}

-- | Lift an 'Iso' into a 'Yoneda'.
--
toYoneda :: Profunctor p => Iso s t a b -> p a b -> Yoneda p s t
toYoneda o p = withIso o $ \sa bt -> Yoneda $ \f g -> dimap (sa . f) (g . bt) p 
{-# INLINE toYoneda #-}

-- | Lift an 'Iso' into a 'Coyoneda'.
--
toCoyoneda :: Iso s t a b -> p a b -> Coyoneda p s t
toCoyoneda o p = withIso o $ \sa bt -> Coyoneda sa bt p
{-# INLINE toCoyoneda #-}

-- | Convert from 'AIso' back to any 'Iso'.
--
cloneIso :: AIso s t a b -> Iso s t a b
cloneIso k = withIso k iso
{-# INLINE cloneIso #-}

---------------------------------------------------------------------
-- Optics
---------------------------------------------------------------------

-- | Obtain an 'Iso'' directly from type equality constraints.
--
-- >>> :t (^. equaled)
-- (^. equaled) :: b -> b
--
equaled :: s ~ a => t ~ b => Iso s t a b
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

-- | Obtain an 'Iso' from a newtype.
--
-- @
-- 'Data.Profunctor.Optic.View.view' 'wrapped' f '.' f ≡ 'id'
-- f '.' 'Data.Profunctor.Optic.View.view' 'wrapped' f ≡ 'id'
-- @
--
-- >>> view wrapped $ Identity 'x'
-- 'x'
--
-- >>> view wrapped (Const "hello")
-- "hello"
--
wrapped :: Newtype s => Iso' s (O s)
wrapped = dimap unpack pack
{-# INLINE wrapped #-}

-- | Work between newtype wrappers.
--
-- >>> Const "hello" & rewrapped ..~ Prelude.length & getConst
-- 5
--
rewrapped :: Newtype s => Newtype t => Iso s t (O s) (O t)
rewrapped = withIso wrapped $ \ sa _ -> withIso wrapped $ \ _ bt -> iso sa bt
{-# INLINE rewrapped #-}

-- | Variant of 'rewrapped' that ignores its argument.
--
rewrapped' :: Newtype s => Newtype t => (O s -> s) -> Iso s t (O s) (O t)
rewrapped' _ = rewrapped
{-# INLINE rewrapped' #-}

-- | Obtain an 'Iso' from a 'Generic' representation.
--
-- >>> view (generic . re generic) "hello" :: String
-- "hello"
--
generic :: G.Generic a => G.Generic b => Iso a b (G.Rep a c) (G.Rep b c)
generic = iso G.from G.to
{-# INLINE generic #-}

-- | Obtain an 'Iso' from a 'Generic1' representation.
--
generic1 :: G.Generic1 f => G.Generic1 g => Iso (f a) (g b) (G.Rep1 f a) (G.Rep1 g b)
generic1 = iso G.from1 G.to1
{-# INLINE generic1 #-}

-- | Obtain an 'Iso' from a functor and its adjoint.
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

-- | Obtain an 'Iso' from a functor and its function representation.
--
tabulated :: F.Representable f => F.Representable g => Iso (f a) (g b) (F.Rep f -> a) (F.Rep g -> b)
tabulated = iso F.index F.tabulate
{-# INLINE tabulated #-}

-- | TODO: Document
--
transposed :: Functor f => Distributive g => Iso (f (g a)) (g (f a)) (g (f a)) (f (g a))
transposed = involuted distribute
{-# INLINE transposed #-}

-- | Flip two arguments of a function.
--
-- >>> (view flipped (,)) 1 2
-- (2,1)
--
flipped :: Iso (a -> b -> c) (d -> e -> f) (b -> a -> c) (e -> d -> f)
flipped = iso flip flip
{-# INLINE flipped #-}

-- | Curry a function.
--
-- >>> (fst ^. invert curried) 3 4
-- 3
--
curried :: Iso (a -> b -> c) (d -> e -> f) ((a , b) -> c) ((d , e) -> f)
curried = iso uncurry curry
{-# INLINE curried #-}

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
coswapped :: Iso (a + b) (c + d) (b + a) (d + c)
coswapped = iso eswap eswap
{-# INLINE coswapped #-}

-- | 'Iso' defined by left-association of nested tuples.
--
associated :: Iso (a , (b , c)) (d , (e , f)) ((a , b) , c) ((d , e) , f)
associated = iso assocl assocr
{-# INLINE associated #-}

-- | 'Iso' defined by left-association of nested tuples.
--
coassociated :: Iso (a + (b + c)) (d + (e + f)) ((a + b) + c) ((d + e) + f)
coassociated = iso eassocl eassocr
{-# INLINE coassociated #-}

-- | Obtain an 'Iso' from a function that is its own inverse.
--
-- @
-- 'involuted' ≡ 'Control.Monad.join' 'iso'
-- @
--
-- >>> "live" ^. involuted reverse
-- "evil"
--
-- >>> involuted reverse ..~ ('d':) $ "live"
-- "lived"
--
involuted :: (s -> a) -> Iso s a a s
involuted = M.join iso
{-# INLINE involuted #-}

-- | The group isomorphism defined by an element's action.
--
added :: Group a => a -> Iso' a a
added n = iso (<> n) (<< n)
{-# INLINE added #-}

-- | The group isomorphism defined by an element's inverse action.
--
-- @
-- 'subtracted' n = 're' ('added' n)
-- @
--
subtracted :: Group a => a -> Iso' a a
subtracted n = iso (<< n) (<> n)
{-# INLINE subtracted #-}

-- | Remove a single value from a type.
--
-- @
-- 'non' ≡ 'non'' '.' 'only'
-- @
--
-- >>> non 0 #^ rem 10 4
-- Just 2
--
-- >>> non 0 #^ rem 10 5
-- Nothing
--
non :: Eq a => a -> Iso' (Maybe a) a
non def = iso (fromMaybe def) g
  where g a | a == def  = Nothing
            | otherwise = Just a
{-# INLINE non #-}

-- | Generalize @'non' a@ to take any value and a predicate.
--
-- Assumes that @p a@ holds @'True'@ and generates an isomorphism between @'Maybe' (a | 'not' (p a))@ and @a@.
--
anon :: a -> (a -> Bool) -> Iso' (Maybe a) a
anon a p = iso (fromMaybe a) go where
  go b | p b       = Nothing
       | otherwise = Just b
{-# INLINE anon #-}

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

--withIsoVl

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Invert an isomorphism.
--
-- @
-- 'invert' ('invert' o) ≡ o
-- @
--
invert :: AIso s t a b -> Iso b a t s
invert o = withIso o $ \sa bt -> iso bt sa
{-# INLINE invert #-}

-- | Given a conversion on one side of an 'Iso', recover the other.
--
-- @
-- 'reover' ≡ 'over' '.' 're'
-- @
--
-- Compare 'Data.Profunctor.Optic.Setter.over'.
--
reover :: AIso s t a b -> (t -> s) -> b -> a
reover o = withIso o $ \sa bt ts -> sa . ts . bt
{-# INLINE reover #-}

-- | Remap the indices of an indexed optic.
--
reixed :: Profunctor p => AIso' i j -> IndexedOptic p i s t a b -> IndexedOptic p j s t a b
reixed o = withIso o reix
{-# INLINE reixed #-}

-- | Remap the indices of a coindexed optic.
--
recxed :: Profunctor p => AIso' k l -> CoindexedOptic p k s t a b -> CoindexedOptic p l s t a b
recxed o = withIso o recx
{-# INLINE recxed #-}

-- | Based on /ala/ from Conor McBride's work on Epigram.
--
-- This version is generalized to accept any 'Iso', not just a @newtype@.
--
-- >>> au (rewrapped' Sum) foldMap [1,2,3,4]
-- 10
--
-- You may want to think of this combinator as having the following, simpler type:
--
-- @
-- au :: AnIso s t a b -> ((b -> t) -> e -> s) -> e -> a
-- @
--
au :: Functor f => AIso s t a b -> ((b -> t) -> f s) -> f a
au k = withIso k $ \ sa bt f -> fmap sa (f bt)
{-# INLINE au #-}

-- | Variant of 'au' for profunctors. 
--
-- >>> :t flip aup runStar
-- flip aup runStar
--   :: Functor f => AIso s t a (f a) -> Star f c s -> c -> t
--
aup :: Profunctor p => Functor f => AIso s t a b -> (p c a -> f b) -> p c s -> f t
aup o = withIso o $ \sa bt f g -> fmap bt (f (rmap sa g))
{-# INLINE aup #-}

-- | This combinator is based on @ala@ from Conor McBride's work on Epigram.
--
-- As with 'rewrapped'', the user supplied function for the newtype is /ignored/.
--
-- >>> ala Sum foldMap [1,2,3,4]
-- 10
--
-- >>> ala All foldMap [True,True]
-- True
--
-- >>> ala All foldMap [True,False]
-- False
--
-- >>> ala Any foldMap [False,False]
-- False
--
-- >>> ala Any foldMap [True,False]
-- True
--
-- >>> ala Product foldMap [1,2,3,4]
-- 24
--
-- @
-- ala :: Newtype s => Newtype t => (O s -> s) -> ((O t -> t) -> e -> s) -> e -> O s
-- @
--
ala :: Newtype s => Newtype t => Functor f => (O s -> s) -> ((O t -> t) -> f s) -> f (O s) 
ala = au . rewrapped'
{-# INLINE ala #-}
