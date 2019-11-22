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
  , As
  , Iso
  , Iso'
  , AIso 
  , AIso'
    -- * Constructors
  , iso
  , viso
  , invert
  , mapping
  , contramapping
  , dimapping
  , toYoneda 
  , toCoyoneda
  , cloneIso
    -- * Representatives
  , IsoRep(..)
  , Index(..)
  , values
  , info 
  , Coindex(..)
  , trivial
    -- * Primitive operators
  , withIso 
  , reover
  , op
  , au 
  , aup
  , ala
    -- * Common optics
  , as
  , equaled
  , coerced
  , wrapped
  , rewrapped
  , rewrapping
  , flipped 
  , curried
  , swapped 
  , eswapped 
  , associated 
  , eassociated 
  , involuted 
  , added 
  , subtracted 
  , hushed 
  , duped
  , eduped
  , non 
  , anon
    -- * Auxilliary Types
  , Re(..)
    -- * Classes
  , Profunctor(..)
) where

import Control.Newtype.Generics (Newtype(..), op)
import Data.Coerce
import Data.Foldable
import Data.Group
import Data.Maybe (fromMaybe)
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.View (view)
import Data.Profunctor.Yoneda (Coyoneda(..), Yoneda(..))
import GHC.Generics hiding (from, to)
import qualified Control.Monad as M (join)

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XAllowAmbiguousTypes
-- >>> import Data.Monoid
-- >>> import Data.Semiring
-- >>> import Data.Functor.Identity
-- >>> import Data.Functor.Const
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- 'Iso' 
---------------------------------------------------------------------

-- | Obtain an 'Iso' from two inverses.
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
viso :: (forall f g. Functor f => Functor g => (g a -> f b) -> g s -> f t) -> Iso s t a b
viso abst = iso f g
  where f = getConst . (abst (Const . runIdentity)) . Identity
        g = runIdentity . (abst (Identity . getConst)) . Const
{-# INLINE viso #-}

-- | TODO: Document
--
mapping
  :: Functor f
  => Functor g
  => AIso s t a b
  -> Iso (f s) (g t) (f a) (g b)
mapping l = withIso l $ \sa bt -> iso (fmap sa) (fmap bt)
{-# INLINE mapping #-}

-- | Lift an 'Iso' into a 'Contravariant' functor.
--
-- @
-- contramapping :: 'Contravariant' f => 'Iso' s t a b -> 'Iso' (f a) (f b) (f s) (f t)
-- @
--
contramapping :: Contravariant f => AIso s t a b -> Iso (f a) (f b) (f s) (f t)
contramapping f = withIso f $ \ sa bt -> iso (contramap sa) (contramap bt)
{-# INLINE contramapping #-}

-- | TODO: Document
--
dimapping
  :: Profunctor p
  => Profunctor q
  => AIso s1 t1 a1 b1
  -> AIso s2 t2 a2 b2
  -> Iso (p a1 s2) (q b1 t2) (p s1 a2) (q t1 b2)
dimapping f g = withIso f $ \sa1 bt1 -> 
  withIso g $ \sa2 bt2 -> iso (dimap sa1 sa2) (dimap bt1 bt2)
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
-- 'IsoRep'
---------------------------------------------------------------------

-- | The 'IsoRep' profunctor precisely characterizes an 'Iso'.
data IsoRep a b s t = IsoRep (s -> a) (b -> t)

-- | When you see this as an argument to a function, it expects an 'Iso'.
type AIso s t a b = Optic (IsoRep a b) s t a b

type AIso' s a = AIso s s a a

instance Functor (IsoRep a b s) where
  fmap f (IsoRep sa bt) = IsoRep sa (f . bt)
  {-# INLINE fmap #-}

instance Profunctor (IsoRep a b) where
  dimap f g (IsoRep sa bt) = IsoRep (sa . f) (g . bt)
  {-# INLINE dimap #-}
  lmap f (IsoRep sa bt) = IsoRep (sa . f) bt
  {-# INLINE lmap #-}
  rmap f (IsoRep sa bt) = IsoRep sa (f . bt)
  {-# INLINE rmap #-}

instance Sieve (IsoRep a b) (Index a b) where
  sieve (IsoRep sa bt) s = Index (sa s) bt

instance Cosieve (IsoRep a b) (Coindex a b) where
  cosieve (IsoRep sa bt) (Coindex sab) = bt (sab sa)

-- | An indexed store that characterizes a 'Data.Profunctor.Optic.Lens.Lens'
--
-- @'Index' a b r ≡ forall f. 'Functor' f => (a -> f b) -> f r@,
--
data Index a b r = Index a (b -> r)

values :: Index a b r -> b -> r
values (Index _ br) = br
{-# INLINE values #-}

info :: Index a b r -> a
info (Index a _) = a
{-# INLINE info #-}

instance Functor (Index a b) where
  fmap f (Index a br) = Index a (f . br)
  {-# INLINE fmap #-}

instance Profunctor (Index a) where
  dimap f g (Index a br) = Index a (g . br . f)
  {-# INLINE dimap #-}

instance a ~ b => Foldable (Index a b) where
  foldMap f (Index b br) = f . br $ b

-- | An indexed continuation that characterizes a 'Data.Profunctor.Optic.Grate.Grate'
--
-- @'Coindex' a b i ≡ forall f. 'Functor' f => (f a -> b) -> f i@,
--
-- See also 'Data.Profunctor.Optic.Grate.zipWithFOf'.
--
newtype Coindex a b i = Coindex { runCoindex :: (i -> a) -> b } deriving Generic

-- | Change the @Monoid@ used to combine indices.
--
instance Functor (Coindex a b) where
  fmap ij (Coindex abi) = Coindex $ \ja -> abi (ja . ij)

instance a ~ b => Apply (Coindex a b) where
  (Coindex idab) <.> (Coindex abi) = Coindex $ \da -> idab $ \id -> abi (da . id) 

trivial :: Coindex a b a -> b
trivial (Coindex f) = f id
{-# INLINE trivial #-}

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Extract the two functions that characterize an 'Iso'.
--
withIso :: AIso s t a b -> ((s -> a) -> (b -> t) -> r) -> r
withIso x k = case x (IsoRep id id) of IsoRep sa bt -> k sa bt
{-# INLINE withIso #-}

-- | TODO: Document
--
-- @
-- 'reover' ≡ 'over' '.' 're'
-- @
--
reover :: AIso s t a b -> (t -> s) -> b -> a
reover x = withIso x $ \sa bt ts -> sa . ts . bt
{-# INLINE reover #-}

-- | Invert an isomorphism.
--
-- @
-- 'invert' ('invert' o) ≡ o
-- @
--
invert :: AIso s t a b -> Iso b a t s
invert o = withIso o $ \sa bt -> iso bt sa
{-# INLINE invert #-}

-- | Based on /ala/ from Conor McBride's work on Epigram.
--
-- This version is generalized to accept any 'Iso', not just a @newtype@.
--
-- >>> au (rewrapping Sum) foldMap [1,2,3,4]
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
-- As with '_Wrapping', the user supplied function for the newtype is /ignored/.
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
-- You may want to think of this combinator as having the following, simpler, type.
--
-- @
-- ala :: Newtype s => Newtype t => (O s -> s) -> ((O t -> t) -> e -> s) -> e -> O s
-- @
--
ala :: Newtype s => Newtype t => Functor f => (O s -> s) -> ((O t -> t) -> f s) -> f (O s) 
ala = au . rewrapping
{-# INLINE ala #-}

---------------------------------------------------------------------
-- Common 'Iso's
---------------------------------------------------------------------

-- | Obtain an 'Optic'' from an 'Optic'.
--
-- Useful for reducing polymorphism.
--
-- >>> :t (^. equaled . as @Int)
-- (^. equaled . as @Int) :: Int -> Int
--
as :: As a
as = id
{-# INLINE as #-}

-- | Capture type constraints as an 'Iso''.
--
-- >>> :t (^. equaled)
-- (^. equaled) :: b -> b
--
equaled :: s ~ a => t ~ b => Iso s t a b
equaled = id
{-# INLINE equaled #-}

-- | Data types that are representationally equal.
--
-- >>> view coerced 'x' :: Identity Char
-- Identity 'x'
--
coerced :: Coercible s a => Coercible t b => Iso s t a b
coerced = dimap coerce coerce
{-# INLINE coerced #-}

-- | Work under a newtype wrapper.
--
-- @
-- 'view wrapped' f '.' f ≡ 'id'
-- f '.' 'view wrapped' f ≡ 'id'
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
-- >>> Const "hello" & rewrapped %~ Prelude.length & getConst
-- 5
--
rewrapped :: Newtype s => Newtype t => Iso s t (O s) (O t)
rewrapped = withIso wrapped $ \ sa _ -> withIso wrapped $ \ _ bt -> iso sa bt
{-# INLINE rewrapped #-}

-- | Variant of 'rewrapped' that ignores its argument.
--
rewrapping :: Newtype s => Newtype t => (O s -> s) -> Iso s t (O s) (O t)
rewrapping _ = rewrapped
{-# INLINE rewrapping #-}

-- | Flip two arguments of a function.
--
-- >>> (view flipped (,)) 1 2
-- (2,1)
--
flipped :: Iso (a -> b -> c) (d -> e -> f) (b -> a -> c) (e -> d -> f)
flipped = iso flip flip
{-# INLINE flipped #-}

-- | TODO: Document
--
-- >>> (fst ^. curried) 3 4
-- 3
--
-- >>> view curried fst 3 4
-- 3
--
curried :: Iso ((a , b) -> c) ((d , e) -> f) (a -> b -> c) (d -> e -> f)
curried = iso curry uncurry
{-# INLINE curried #-}

-- | TODO: Document
--
swapped :: Iso (a , b) (c , d) (b , a) (d , c)
swapped = iso swap swap
{-# INLINE swapped #-}

-- | TODO: Document
--
eswapped :: Iso (a + b) (c + d) (b + a) (d + c)
eswapped = iso eswap eswap
{-# INLINE eswapped #-}

-- | 'Iso' defined by left-association of nested tuples.
--
associated :: Iso (a , (b , c)) (d , (e , f)) ((a , b) , c) ((d , e) , f)
associated = iso assocl assocr
{-# INLINE associated #-}

-- | 'Iso' defined by left-association of nested tuples.
--
eassociated :: Iso (a + (b + c)) (d + (e + f)) ((a + b) + c) ((d + e) + f)
eassociated = iso eassocl eassocr
{-# INLINE eassociated #-}

-- | Obtain an 'Iso' from a function that is its own inverse.
--
-- @
-- 'involuted' ≡ 'Control.Monad.join' 'iso'
-- @
--
-- >>> "live" ^. involuted reverse
-- "evil"
--
-- >>> involuted reverse %~ ('d':) $ "live"
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

-- | TODO: Document
--
hushed :: Iso (Maybe a) (Maybe b) (() + a) (() + b)
hushed = iso (maybe (Left ()) Right) (const Nothing ||| Just)
{-# INLINE hushed #-}

-- | TODO: Document
--
duped :: Iso (Bool -> a) (Bool -> b) (a , a) (b , b)
duped = iso to fro
 where
  to f = (f False, f True)
  fro p True = fst p
  fro p False = snd p
{-# INLINE duped #-}

-- | TODO: Document
--
eduped :: Iso (Bool , a) (Bool , b) (a + a) (b + b)
eduped = iso f ((,) False ||| (,) True)
 where
  f (False,a) = Left a
  f (True,a) = Right a
{-# INLINE eduped #-}

-- | Remove a single value from a type.
--
-- @
-- 'non' ≡ 'non'' '.' 'only'
-- @
--
-- >>> non 0 # rem 10 4
-- Just 2
--
-- >>> non 0 # rem 10 5
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
