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
  , iso
  , isoVl
  , cloneIso
  , fmapping
  , contramapping
  , dimapping
  , toYoneda 
  , toCoyoneda
  , invert
    -- * Optics
  , equal
  , coerced
  , wrapped
  , rewrapped
  , rewrapped'
  , generic
  , generic1
  , adjuncted
  , inhabited
  , zipped
  , cozipped
  , swapped 
  , coswapped 
  , associated 
  , coassociated
  , excised
  , flipped 
  , involuted
  , uncurried
  , zipListed
  , zipFolded
    -- * Bytestring optics
  , short
  , strict
  , chunked
  , chars
  , chars'
  , bytes
  , bytes'
    -- * Operators
  , op
  , au 
  , aup
  , ala
  , reover
    -- * Re
  , Re(..)
    -- * Classes
  , Profunctor(..)
) where

import Control.Applicative (ZipList(..))
import Control.Newtype.Generics (Newtype(..), op)
import Data.Coerce
import Data.Maybe (fromMaybe)
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Combinator
import Data.Profunctor.Rep.Fold (Free,ZipFold(..))
import Data.Profunctor.Yoneda (Coyoneda(..), Yoneda(..))
import Data.Word
import qualified Control.Monad as M (join)
import qualified Data.ByteString       as BS
import qualified Data.ByteString.Char8 as CS
import qualified Data.ByteString.Lazy       as BL
import qualified Data.ByteString.Lazy.Char8 as CL
import qualified Data.ByteString.Short.Internal as Short
import qualified GHC.Generics as G
import qualified Data.Functor.Rep as F

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XAllowAmbiguousTypes
-- >>> import Data.Monoid
-- >>> import Data.List.Index
-- >>> import Data.Semiring
-- >>> import Data.Function ((&))
-- >>> import Data.Functor.Identity
-- >>> import Data.Functor.Const
-- >>> import Data.Profunctor.Types
-- >>> :load Data.Profunctor.Optic

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
toYoneda :: Profunctor p => Iso s t a b -> p a b -> Yoneda p s t
toYoneda o p = withIso o $ \sa bt -> Yoneda $ \f g -> dimap (sa . f) (g . bt) p 
{-# INLINE toYoneda #-}

-- | Lift an 'Iso' into a 'Coyoneda'.
--
toCoyoneda :: Iso s t a b -> p a b -> Coyoneda p s t
toCoyoneda o p = withIso o $ \sa bt -> Coyoneda sa bt p
{-# INLINE toCoyoneda #-}

-- | Invert an isomorphism.
--
-- @
-- 'invert' ('invert' o) ≡ o
-- @
--
invert :: AIso s t a b -> Iso b a t s
invert o = withIso o $ \sa bt -> iso bt sa
{-# INLINE invert #-}

-- | Convert from 'AIso' back to any 'Iso'.
--
cloneIso :: AIso s t a b -> Iso s t a b
cloneIso k = withIso k iso
{-# INLINE cloneIso #-}

---------------------------------------------------------------------
-- Optics
---------------------------------------------------------------------

-- | The identity for 'Iso' optics.
--
-- >>> view equal "foo"
-- "foo"
--
equal :: Iso a b a b
equal = id
{-# INLINE equal #-}

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
-- >>> view wrapped $ Identity 'f'
-- 'f'
--
-- >>> view wrapped (Const "foo")
-- "foo"
--
wrapped :: Newtype s => Iso' s (O s)
wrapped = dimap unpack pack
{-# INLINE wrapped #-}

-- | An 'Iso' between newtype wrappers.
--
-- >>> Const "hello" & rewrapped ..~ Prelude.length & getConst
-- 5
--
rewrapped :: Newtype s => Newtype t => Iso s t (O s) (O t)
rewrapped = withIso wrapped $ \ sa _ -> withIso wrapped $ \ _ bt -> iso sa bt
{-# INLINE rewrapped #-}

-- | A variant of 'rewrapped' that ignores its argument.
--
rewrapped' :: Newtype s => Newtype t => (O s -> s) -> Iso s t (O s) (O t)
rewrapped' _ = rewrapped
{-# INLINE rewrapped' #-}

-- | An 'Iso' between 'Generic' representations.
--
-- >>> view (generic . re generic) "foo" :: String
-- "foo"
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
-- Useful for converting between star-like optics and costar-like optics:
--
-- @
-- 'Data.Profunctor.Optic.Combinator.over' 'adjuncted' :: 'Adjunction' f u => ((a -> u b) -> s -> u t) -> (f a -> b) -> f s -> t
-- @
--
adjuncted :: Adjunction f u => Iso (f a -> b) (f s -> t) (a -> u b) (s -> u t)
adjuncted = iso leftAdjunct rightAdjunct
{-# INLINE adjuncted #-}

-- | A left adjoint must be inhabited.
--
inhabited :: Adjunction f u => Iso' (f Void) Void
inhabited = iso unabsurdL absurdL
{-# INLINE inhabited #-}

-- | A right adjoint admits an intrinsic notion of zipping.
--
zipped :: Adjunction f u => Iso (u a , u b) (u c , u d) (u (a , b)) (u (c , d)) 
zipped = iso zipR unzipR
{-# INLINE zipped #-}

-- | A left adjoint admits an intrinsic notion of co-zipping.
--
cozipped :: Adjunction f u => Iso (f a + f b) (f c + f d) (f (a + b)) (f (c + d))
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

-- | Left-associate nested products.
--
associated :: Iso (a , (b , c)) (d , (e , f)) ((a , b) , c) ((d , e) , f)
associated = iso assocl assocr
{-# INLINE associated #-}

-- | Left-associate nested sums.
--
coassociated :: Iso (a + (b + c)) (d + (e + f)) ((a + b) + c) ((d + e) + f)
coassociated = iso eassocl eassocr
{-# INLINE coassociated #-}

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

-- | Involute an involutive function (i.e. one that is its own inverse).
--
-- @
-- 'involuted' ≡ 'Control.Monad.join' 'iso'
-- @
--
-- >>> "live" ^. involuted reverse
-- "evil"
-- >>> "live" & involuted reverse ..~ ('d':) 
-- "lived"
--
involuted :: (s -> a) -> Iso s a a s
involuted sa = iso sa sa
{-# INLINE involuted #-}

-- | Uncurry a function.
--
-- >>> (fst ^. invert uncurried) 3 4
-- 3
--
uncurried :: Iso (a -> b -> c) (d -> e -> f) ((a , b) -> c) ((d , e) -> f)
uncurried = iso uncurry curry
{-# INLINE uncurried #-}

-- | Convert to the 'Control.Applicative.ZipList' applicative.
--
zipListed :: Iso [a] [b] (ZipList a) (ZipList b)
zipListed = iso ZipList getZipList
{-# INLINE zipListed #-}

-- | Convert to the 'Data.Free.ZipList' applicative.
--
zipFolded :: Iso (Free a) (Free b) (ZipFold a) (ZipFold b)
zipFolded = iso ZipFold getZipFold
{-# INLINE zipFolded #-}

---------------------------------------------------------------------
-- ByteString optics
---------------------------------------------------------------------

-- | Convert between strict 'BS.ByteString's and short 'Short.ShortByteString's.
--
short :: Iso' BS.ByteString Short.ShortByteString 
short = iso Short.toShort Short.fromShort
{-# INLINE short #-}

-- | Convert between lazy 'BL.ByteString's and strict 'BS.ByteString's.
--
strict :: Iso' BL.ByteString BS.ByteString
strict = iso BL.toStrict BL.fromStrict
{-# INLINE strict #-}

-- | Chunk a list of strict 'BS.ByteString's into a lazy 'BL.ByteString'.
--
chunked :: Iso' [BS.ByteString] BL.ByteString
chunked = iso BL.fromChunks BL.toChunks
{-# INLINE chunked #-}

-- | Pack a list of characters into a lazy 'CL.ByteString'.
--
-- When writing back to the 'ByteString' it is assumed that every 'Char' lies
-- between @'\x00'@ and @'\xff'@.
--
-- @
-- 'Data.ByteString.Lazy.Char8.pack' x ≡ x '^.' 'chars'
-- 'Data.ByteString.Lazy.Char8.unpack' x ≡ x '^.' 're' 'chars'
-- @
--
-- >>> [104,101,108,108,111] ^. re bytes . unpacked
-- "hello"
--
chars :: Iso' String BL.ByteString
chars = iso CL.pack CL.unpack
{-# INLINE chars #-}

-- | Pack a list of characters into a strict 'CS.ByteString'.
--
-- When writing back to the 'ByteString' it is assumed that every 'Char' lies
-- between @'\x00'@ and @'\xff'@.
--
-- 
-- 'Data.ByteString.Char8.pack' x ≡ x '^.' 'chars''
-- 'Data.ByteString.Char8.unpack' x ≡ x '^.' 're' 'chars''
-- @
--
-- >>> "hello" ^. packed
-- [104,101,108,108,111]
--
chars' :: Iso' String BS.ByteString
chars' = iso CS.pack CS.unpack
{-# INLINE chars' #-}

-- | Unpack a lazy 'BL.ByteString' into a list of bytes.
--
-- @
-- 'Data.ByteString.Lazy.pack' x ≡  x '^.' 'bytes'
-- 'Data.ByteString.Lazy.unpack' x ≡ x '^.' 're' 'bytes'
-- @
--
-- >>> [104,101,108,108,111] ^. bytes
-- "hello"
--
bytes :: Iso' [Word8] BL.ByteString
bytes = iso BL.pack BL.unpack
{-# INLINE bytes #-}

-- | Unpack a strict 'ByteString' into a list of bytes.
--
-- @
-- 'Data.ByteString.pack' x ≡  x '^.' 'bytes''
-- 'Data.ByteString.unpack' x ≡ x '^.' 're' 'bytes''
-- @
--
bytes' :: Iso' [Word8] BS.ByteString
bytes' = iso BS.pack BS.unpack
{-# INLINE bytes' #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

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

-- | This combinator is based on @ala@ from Conor McBride's work on Epigram.
--
-- As with 'rewrapped'', the user supplied function for the newtype is /ignored/.
--
-- >>> ala Sum foldMap [1,2,3,4]
-- 10
-- >>> ala All foldMap [True,False]
-- False
-- >>> ala Product foldMap [1,2,3,4]
-- 24
--
-- @
-- 'ala' :: 'Newtype' s => 'Newtype' t => ('O' s -> s) -> (('O' t -> t) -> e -> s) -> e -> O s
-- @
--
ala :: Newtype s => Newtype t => Functor f => (O s -> s) -> ((O t -> t) -> f s) -> f (O s) 
ala = au . rewrapped'
{-# INLINE ala #-}

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
