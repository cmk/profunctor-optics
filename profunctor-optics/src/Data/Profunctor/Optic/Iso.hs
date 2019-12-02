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
  , isoVl
  , ixmapping
  , cxmapping
  , fmapping
  , contramapping
  , dimapping
  , toYoneda 
  , toCoyoneda
  , cloneIso
    -- * Carriers
  , IsoRep(..)
    -- * Primitive operators
  , withIso
  , invert
  , reover
  , reixed
  , recxed
  , op
  , au 
  , aup
  , ala
    -- * Optics
  , equaled
  , coerced
  , wrapped
  , rewrapped
  , rewrapping
  , generic
  , generic1
  , flipped 
  , curried
  , swapped 
  , eswapped 
  , associated 
  , eassociated 
  , involuted 
  , added 
  , subtracted
  , viewedl
  , viewedr
  , non 
  , anon
  , u1
  , par1
  , rec1
  , k1
  , m1
    -- * Auxilliary Types
  , Re(..)
) where

import Control.Newtype.Generics (Newtype(..), op)
import Data.Coerce
import Data.Group
import Data.Maybe (fromMaybe)
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Index
import Data.Profunctor.Optic.Type hiding (Rep)
import Data.Profunctor.Yoneda (Coyoneda(..), Yoneda(..))
import Data.Sequence as Seq
import GHC.Generics hiding (from, to)
import qualified Control.Monad as M (join)
import qualified GHC.Generics as GHC (to, from, to1, from1)

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
-- >>> :load Data.Profunctor.Optic
-- >>> let ixtraversed :: Ixtraversal Int [a] [b] a b ; ixtraversed = ixtraversalVl itraverse

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
isoVl :: (forall f g. Functor f => Functor g => (g a -> f b) -> g s -> f t) -> Iso s t a b
isoVl abst = iso f g
  where f = getConst . (abst (Const . runIdentity)) . Identity
        g = runIdentity . (abst (Identity . getConst)) . Const
{-# INLINE isoVl #-}

-- | Lift an 'Iso' into an indexed version. 
--
-- >>> ixlists (ixtraversed . ixmapping swapped) [(40,'f'),(41,'o'),(42,'o')]
-- [(0,('f',40)),(1,('o',41)),(2,('o',42))]
--
ixmapping :: Profunctor p => AIso s t a b -> IndexedOptic p i s t a b
ixmapping o = withIso o ixmap
{-# INLINE ixmapping #-}

-- | Lift an 'Iso' into a coindexed version. 
--
cxmapping :: Profunctor p => AIso s t a b -> CoindexedOptic p k s t a b
cxmapping o = withIso o cxmap
{-# INLINE cxmapping #-}

-- | TODO: Document
--
fmapping
  :: Functor f
  => Functor g
  => AIso s t a b
  -> Iso (f s) (g t) (f a) (g b)
fmapping l = withIso l $ \sa bt -> iso (fmap sa) (fmap bt)
{-# INLINE fmapping #-}

-- | Lift an 'Iso' into a 'Contravariant' functor.
--
-- @
-- contramapping :: 'Contravariant' f => 'Iso' s t a b -> 'Iso' (f a) (f b) (f s) (f t)
-- @
--
contramapping :: Contravariant f => Contravariant g => AIso s t a b -> Iso (f a) (g b) (f s) (g t)
contramapping f = withIso f $ \sa bt -> iso (contramap sa) (contramap bt)
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

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Extract the two functions that characterize an 'Iso'.
--
withIso :: AIso s t a b -> ((s -> a) -> (b -> t) -> r) -> r
withIso x k = case x (IsoRep id id) of IsoRep sa bt -> k sa bt
{-# INLINE withIso #-}

-- | Invert an isomorphism.
--
-- @
-- 'invert' ('invert' o) ≡ o
-- @
--
invert :: AIso s t a b -> Iso b a t s
invert o = withIso o $ \sa bt -> iso bt sa
{-# INLINE invert #-}

-- | Given a conversion on one side of an 'Iso', reover the other.
--
-- @
-- 'reover' ≡ 'over' '.' 're'
-- @
--
-- Compare 'Data.Profunctor.Optic.Setter.reover'.
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
-- >>> Const "hello" & rewrapped ..~ Prelude.length & getConst
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

-- | Convert between a data type and its 'Generic' representation.
--
-- >>> view (generic . re generic) "hello" :: String
-- "hello"
--
generic :: Generic a => Generic b => Iso a b (Rep a c) (Rep b c)
generic = iso GHC.from GHC.to
{-# INLINE generic #-}

-- | Convert between a data type and its 'Generic1' representation.
--
generic1 :: Generic1 f => Generic1 g => Iso (f a) (g b) (Rep1 f a) (Rep1 g b)
generic1 = iso GHC.from1 GHC.to1
{-# INLINE generic1 #-}

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

-- | A 'Seq' is isomorphic to a 'ViewL'
--
-- @'viewl' m ≡ m 'Data.Profunctor.Optic.Operator.^.' 'viewedl'@
--
-- >>> Seq.fromList [1,2,3] ^. viewedl
-- 1 :< fromList [2,3]
--
-- >>> Seq.empty ^. viewedl
-- EmptyL
--
-- >>> EmptyL ^. re viewedl
-- fromList []
--
-- >>> review viewedl $ 1 Seq.:< fromList [2,3]
-- fromList [1,2,3]
--
viewedl :: Iso (Seq a) (Seq b) (ViewL a) (ViewL b)
viewedl = iso viewl $ \xs -> case xs of
  EmptyL      -> mempty
  a Seq.:< as -> a Seq.<| as
{-# INLINE viewedl #-}

-- | A 'Seq' is isomorphic to a 'ViewR'
--
-- @'viewr' m ≡ m 'Data.Profunctor.Optic.Operator.^.' 'viewedr'@
--
-- >>> Seq.fromList [1,2,3] ^. viewedr
-- fromList [1,2] :> 3
--
-- >>> Seq.empty ^. viewedr
-- EmptyR
--
-- >>> EmptyR ^. re viewedr
-- fromList []
--
-- >>> review viewedr $ fromList [1,2] Seq.:> 3
-- fromList [1,2,3]
--
viewedr :: Iso (Seq a) (Seq b) (ViewR a) (ViewR b)
viewedr = iso viewr $ \xs -> case xs of
  EmptyR      -> mempty
  as Seq.:> a -> as Seq.|> a
{-# INLINE viewedr #-}

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

u1 :: Iso (U1 p) (U1 q) () ()
u1 = iso (const ()) (const U1)
{-# INLINE u1 #-}

k1 :: Iso (K1 i c p) (K1 j d q) c d
k1 = iso unK1 K1
{-# INLINE k1 #-}

m1 :: Iso (M1 i c f p) (M1 j d g q) (f p) (g q)
m1 = iso unM1 M1
{-# INLINE m1 #-}

par1 :: Iso (Par1 p) (Par1 q) p q
par1 = iso unPar1 Par1
{-# INLINE par1 #-}

rec1 :: Iso (Rec1 f p) (Rec1 g q) (f p) (g q)
rec1 = iso unRec1 Rec1
{-# INLINE rec1 #-}
