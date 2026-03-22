{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Data.Profunctor.Optic.Fold (
    -- * Constructors
    -- ** Fold, Ixfold
    Fold, Ixfold
  , fold_
  , afold
  , aixfold
  , foldVl
  , ixfoldVl
  , folding
  , failing
    -- ** Fold0, Ixfold0
  , Fold0, Ixfold0
  , afold0
  , fold0
  , fold0'
  , ixfold0
    -- ** Fold1, Ixfold1
  , Fold1, Ixfold1
  , fold1_
  , foldVl1
  , ixfoldVl1
  , folding1
    -- * Dual Constructors
    -- ** Cofold, Cxfold
  , Cofold, Cxfold
  , acofold
  , cofoldVl
  , cofolding
    -- ** Cofold1, Cxfold1
  , Cofold1, Cxfold1
  , cofoldVl1
  , cofolding1

    -- * Optics
    -- ** Fold, Ixfold
  , afolded
  , folded
  , folded_
  , ixfoldedRep
    -- ** Fold0, Ixfold0
  , folded0
  , filtered
    -- ** Fold1, Ixfold1
  , afolded1
  , folded1
  , folded1_
    -- * Dual Optics
    -- ** Cofold, Cxfold
  , acolist
  , cofolded
    -- ** Cofold1, Cxfold1
  , acolist1

    -- * Operators
    -- ** Fold, Ixfold
  , foldMapOf
  , ixfoldMapOf
  , foldOfA
  , toListOf
  , ixtoListOf
  , foldrOf
  , ixfoldrOf
  , foldlOf
  , ixfoldlOf
  , foldrOf'
  , ixfoldrOf'
  , foldlOf'
  , ixfoldlOf'
  , foldrMOf
  , ixfoldrMOf
  , foldlMOf
  , ixfoldlMOf
  , traverseOf_
  , ixtraverseOf_
  , has
  , hasn't
  , anyOf
  , allOf
  , noneOf
  , lengthOf
  , sumOf
  , productOf
  , maximumOf
  , minimumOf
  , maximumByOf
  , minimumByOf
  , findOf
  , elemOf
  , headOf
  , lastOf
    -- ** Fold0, Ixfold0
  , foldOf0
  , ixfoldOf0
  , preview
  , ixpreview
  , previews
  , ixpreviews
  , preuse
  , preuses
    -- * Dual Operators
    -- ** Cofold, Cxfold
  , cofoldMapOf
  , cofoldOfA
  , cxfoldMapOf
    -- * Auxiliary Types
  , EndoM(..)
    -- * Reexports
  , Strong(..)
  , Choice(..)
  , Closed(..)
  , Representable(..)
  , Corepresentable(..)
) where

import Control.Applicative as A
import Prelude (Num)
import Control.Monad (void)
import Control.Monad.Reader as Reader hiding (lift)
import Control.Monad.State as State hiding (lift)
import Data.Foldable (Foldable, traverse_)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe
import Data.Monoid
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Combinator
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Traversal
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Prism
import qualified Data.Functor.Rep as F
import qualified Data.List as L
import qualified Data.List.NonEmpty as NNL

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XRankNTypes
-- >>> import Control.Exception hiding (catches)
-- >>> import Data.Functor.Identity
-- >>> import Data.List.NonEmpty (NonEmpty(..))
-- >>> import qualified Data.List.NonEmpty as NE
-- >>> import Data.Int
-- >>> import Data.Map as Map
-- >>> import Data.Maybe
-- >>> import Data.Monoid
-- >>> :load Data.Profunctor.Optic
-- >>> import Prelude

---------------------------------------------------------------------
-- Constructors
---------------------------------------------------------------------

-- | Obtain a 'Fold' directly.
--
-- @
-- 'fold_' ('toListOf' o) ≡ o
-- 'fold_' f ≡ 'to' f . 'foldVl' 'traverse_'
-- 'fold_' f ≡ 'coercedR' . 'lmap' f . 'lift' 'traverse_'
-- @
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- This can be useful to lift operations from @Data.List@ and elsewhere into a 'Fold'.
--
-- >>> [1,2,3,4] ^.. fold_ (Prelude.drop 1)
-- [2,3,4]
--
fold_ :: Foldable f => (s -> f a) -> Fold s a
fold_ f = coercedR . lmap f . foldVl traverse_
{-# INLINE fold_ #-}

-- | TODO: Document
--
-- @
-- 'afold' :: ((a -> r) -> s -> r) -> 'AFold' r s a
-- @
--
afold :: ((a -> r) -> s -> r) -> ATraversal (Const r) s t a b
afold f = atraversal $ (Const #.) #. f .# (getConst #.)
{-# INLINE afold #-}

-- | TODO: Document
--
-- @since 0.0.3
aixfold :: ((k -> a -> r) -> s -> r) -> AIxtraversal (Const r) k s t a b
aixfold f = afold $ \iar s -> f (curry iar) $ snd s
{-# INLINE aixfold #-}

-- | Obtain a 'Fold' from a Van Laarhoven 'Fold'.
--
foldVl :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> Fold s a
foldVl f = coercedR . traversalVl f . coercedR
{-# INLINE foldVl #-}

-- | Obtain a 'Ixfold' from a Van Laarhoven 'Fold'.
--
-- @since 0.0.3
ixfoldVl :: (forall f. Applicative f => (k -> a -> f b) -> s -> f t) -> Ixfold k s a
ixfoldVl f = coercedR . ixtraversalVl f . coercedR
{-# INLINE ixfoldVl #-}

-- | Obtain a 'Fold' from a 'Traversable' functor.
--
-- @
-- 'folding' f ≡ 'traversed' . 'to' f
-- 'folding' f ≡ 'foldVl' 'traverse' . 'to' f
-- @
--
folding :: Traversable f => (s -> a) -> Fold (f s) a
folding f = foldVl traverse . coercedR . lmap f
{-# INLINE folding #-}

infix 3 `failing`

-- | If the first 'Fold0' has no focus then try the second one.
--
failing :: AFold0 a s a -> AFold0 a s a -> Fold0 s a
failing a b = fold0 $ \s -> maybe (preview b s) Just (preview a s)
{-# INLINE failing #-}

---------------------------------------------------------------------
-- Fold0 Constructors
---------------------------------------------------------------------

-- | TODO: Document
--
afold0 :: ((a -> Maybe r) -> s -> Maybe r) -> AFold0 r s a
afold0 f = afold $ (Alt #.) #. f .# (getAlt #.)
{-# INLINE afold0 #-}

-- | Obtain a 'Fold0' directly.
--
-- @
-- 'fold0' . 'preview' ≡ id
-- 'fold0' ('view' o) ≡ o . 'just'
-- @
--
-- >>> preview (fold0 listToMaybe) "foo"
-- Just 'f'
--
fold0 :: (s -> Maybe a) -> Fold0 s a
fold0 f = coercedR . lmap (\s -> maybe (Left s) Right (f s)) . right'
{-# INLINE fold0 #-}

-- | Obtain a 'Fold0' from a 'View'.
--
-- @
-- 'fold0'' o ≡ o . 'just'
-- 'fold0'' o ≡ 'fold0' ('view' o)
-- @
--
fold0' :: View s (Maybe a) -> Fold0 s a
fold0' o pab = o (just pab)
{-# INLINE fold0' #-}

-- | Obtain a 'View' from a 'Fold0'
--
-- > 'viewing' = 'to' . 'preview'
--
viewing ::  AFold0 a s a -> View s (Maybe a)
viewing o = coercedR . lmap (preview o)
{-# INLINE viewing #-}

-- | Obtain an 'Ixfold0' directly.
--
-- @since 0.0.3
ixfold0 :: (s -> Maybe (k, a)) -> Ixfold0 k s a
ixfold0 g = ixtraversalVl0 (\point f s -> maybe (point s) (uncurry f) $ g s) . coercedR
{-# INLINE ixfold0 #-}

---------------------------------------------------------------------
-- Fold1 Constructors
---------------------------------------------------------------------

-- | Obtain a 'Fold1' directly.
--
-- @
-- 'fold1_' (toNonEmpty o) ≡ o
-- 'fold1_' f ≡ 'to' f . 'foldVl1' 'traverse1_'
-- 'fold1_' f ≡ 'coercedR' . 'lmap' f . 'lift' 'traverse1_'
-- @
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- This can be useful to representing operations from @Data.List.NonEmpty@ and elsewhere into a 'Fold1'.
--
fold1_ :: Foldable1 f => (s -> f a) -> Fold1 s a
fold1_ f = coercedR . lmap f . foldVl1 traverse1_
{-# INLINE fold1_ #-}

-- | Obtain a 'Fold1' from a Van Laarhoven 'Fold1'.
--
-- See 'Data.Profunctor.Optic.Property'.
--
foldVl1 :: (forall f. Apply f => (a -> f b) -> s -> f t) -> Fold1 s a
foldVl1 f = coercedR . representing f . coercedR
{-# INLINE foldVl1 #-}

-- | Obtain a 'Ixfold' from a Van Laarhoven 'Fold'.
--
-- @since 0.0.3
ixfoldVl1 :: (forall f. Apply f => (k -> a -> f b) -> s -> f t) -> Ixfold1 k s a
ixfoldVl1 f = coercedR . ixtraversalVl1 f . coercedR
{-# INLINE ixfoldVl1 #-}

-- | Obtain a 'Fold1' from a 'Traversable1' functor.
--
-- @
-- 'folding1' f ≡ 'traversed1' . 'to' f
-- 'folding1' f ≡ 'foldVl1' 'traverse1' . 'to' f
-- @
--
folding1 :: Traversable1 f => (s -> a) -> Fold1 (f s) a
folding1 f = foldVl1 traverse1 . coercedR . lmap f
{-# INLINE folding1 #-}

---------------------------------------------------------------------
-- Dual Constructors
---------------------------------------------------------------------

-- | TODO: Document
--
acofold :: ((r -> b) -> r -> t) -> ACofold r t b
acofold f = acotraversal $ (.# getConst) #. f .# (.# Const)
{-# INLINE acofold #-}

-- | Obtain a 'Cofold' from a Van Laarhoven 'Cofold'.
--
cofoldVl :: (forall f. Coapplicative f => (f a -> b) -> f s -> t) -> Cofold t b
cofoldVl f = coercedL . cotraversalVl f . coercedL
{-# INLINE cofoldVl #-}

-- | TODO: Document
--
-- > 'cofoldVl' 'cotraverse' . 'from' f
--
cofolding :: Distributive g => (b -> t) -> Cofold (g t) b
cofolding f = cofoldVl cotraverse . coercedL . rmap f
{-# INLINE cofolding #-}

---------------------------------------------------------------------
-- Dual Fold1 Constructors
---------------------------------------------------------------------

-- | Obtain a 'Cofold1' from a Van Laarhoven 'Cofold1'.
--
cofoldVl1 :: (forall f. Coapply f => (f a -> b) -> f s -> t) -> Cofold1 t b
cofoldVl1 f = coercedL . cotraversalVl1 f . coercedL
{-# INLINE cofoldVl1 #-}

-- | TODO: Document
--
-- > 'cofolding1' f = 'cofoldVl1' 'cotraverse1' . 'from' f
--
cofolding1 :: Distributive1 g => (b -> t) -> Cofold1 (g t) b
cofolding1 f = cofoldVl1 cotraverse1 . coercedL . rmap f
{-# INLINE cofolding1 #-}

---------------------------------------------------------------------
-- Optics
---------------------------------------------------------------------

-- | TODO: Document
--
afolded :: Foldable f => Monoid r => AFold r (f a) a
afolded = afold foldMap
{-# INLINE afolded #-}

-- | Obtain a 'Fold' from a 'Traversable' functor.
--
folded :: Traversable f => Fold (f a) a
folded = folding id
{-# INLINE folded #-}

-- | The canonical 'Fold'.
--
-- @
-- 'Data.Foldable.foldMap' ≡ 'withForget' 'folded_''
-- @
--
folded_ :: Foldable f => Fold (f a) a
folded_ = fold_ id
{-# INLINE folded_ #-}

---------------------------------------------------------------------
-- Indexed Optics
---------------------------------------------------------------------

-- | Obtain an 'Ixfold' from a 'F.Representable' functor.
--
-- @since 0.0.3
ixfoldedRep :: F.Representable f => Traversable f => Ixfold (F.Rep f) (f a) a
ixfoldedRep = ixfoldVl F.itraverseRep
{-# INLINE ixfoldedRep #-}

{-
import qualified Data.Functor.Foldable as F

aapo :: Corecursive t => ACofold b t (Base t (t + b))
aapo = acofold F.apo
{-# INLINE aapo #-}

-- | TODO: Document
--
-- >>> import Data.Functor.Foldable (ListF(..))
-- >>> :{
--  let
--    fromListF :: Num a => ListF a (Sum a) -> Sum a
--    fromListF Nil = mempty
--    fromListF (Cons a r) = Sum a <> r
--  in foldMapOf acata fromListF $ [1..5]
-- :}
-- Sum {getSum = 15}
--
acata :: Recursive s => AFold a s (Base s a)
acata = afold F.cata
{-# INLINE acata #-}

apara :: Recursive s => AFold a s (Base s (s , a))
apara = afold F.para
{-# INLINE apara #-}

acataA :: Recursive s => AFold (f a) s (Base s (f a))
acataA = afold F.cataA
{-# INLINE acataA #-}
-}

---------------------------------------------------------------------
-- Fold0 Optics
---------------------------------------------------------------------

-- | The canonical 'Fold0'.
--
-- >>> [Just 1, Nothing] ^.. folded . folded0
-- [1]
--
folded0 :: Fold0 (Maybe a) a
folded0 = fold0 id
{-# INLINE folded0 #-}

-- | Filter another optic.
--
-- >>> [1..10] ^.. folded . filtered even
-- [2,4,6,8,10]
--
filtered :: (a -> Bool) -> Fold0 a a
filtered p = traversalVl0 (\point f a -> if p a then f a else point a) . coercedR
{-# INLINE filtered #-}

---------------------------------------------------------------------
-- Fold1 Optics
---------------------------------------------------------------------

-- | TODO: Document
--
afolded1 :: Foldable1 f => Semigroup r => AFold r (f a) a
afolded1 = afold foldMap1
{-# INLINE afolded1 #-}

-- | Obtain a 'Fold1' from a 'Traversable1' functor.
--
folded1 :: Traversable1 f => Fold1 (f a) a
folded1 = folding1 id
{-# INLINE folded1 #-}

-- | The canonical 'Fold1'.
--
-- @
-- 'Data.Semigroup.Foldable.foldMap1' ≡ 'withForget' 'folded1_''
-- @
--
folded1_ :: Foldable1 f => Fold1 (f a) a
folded1_ = fold1_ id
{-# INLINE folded1_ #-}

---------------------------------------------------------------------
-- Dual Optics
---------------------------------------------------------------------

-- | Right list unfold over an optic.
--
acolist :: ACofold a [b] (Maybe (b, a))
acolist = acofold L.unfoldr
{-# INLINE acolist #-}

--abytestring :: ACofold a Words.ByteString (Maybe (Word8, a))
--abytestring = acofold Words.unfoldr

-- | TODO: Document
--
-- > 'cofoldVl' 'cotraverse' . 'from' f
--
cofolded :: Distributive g => Cofold (g b) b
cofolded = cofolding id
{-# INLINE cofolded #-}

-- | Right non-empty list unfold over an optic.
--
acolist1 :: ACofold a (NonEmpty b) (b, Maybe a)
acolist1 = acofold NNL.unfoldr
{-# INLINE acolist1 #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Map an optic to a monoid and combine the results.
--
-- @
-- 'Data.Foldable.foldMap' = 'foldMapOf' 'folded_'
-- @
--
-- >>> foldMapOf bitraversed (\x -> [x, x + 1]) (1,3)
-- [1,2,3,4]
-- >>> foldMapOf bitraversed id (["foo"], ["bar", "baz"])
-- ["foo","bar","baz"]
--
foldMapOf :: ATraversal (Const r) s t a b -> (a -> r) -> s -> r
foldMapOf o = (getConst #.) #. traverseOf o .# (Const #.)
{-# INLINE foldMapOf #-}

-- | Map an indexed optic to a monoid and combine the results.
--
-- /Benchmark: indexed fold via Conjoin, ~1.08x overhead. See "Data.Profunctor.Optic.Bench"./
--
-- @since 0.0.3
ixfoldMapOf :: Monoid k => AIxfold r k s a -> (k -> a -> r) -> s -> r
ixfoldMapOf o f = curry (foldMapOf o $ uncurry f) mempty
{-# INLINE ixfoldMapOf #-}

-- | TODO: Document
--
foldOfA :: Applicative f => AFold (f a) s a -> s -> f a
foldOfA = flip foldMapOf pure
{-# INLINE foldOfA #-}

-- | Infix alias of 'toListOf'.
--
-- @
-- 'Data.Foldable.toList' xs ≡ xs '^..' 'folding'
-- ('^..') ≡ 'flip' 'toListOf'
-- @
--
-- >>> [[1,2], [3 :: Int64]] ^.. id
-- [[[1,2],[3]]]
-- >>> [[1,2], [3 :: Int64]] ^.. traversed
-- [[1,2],[3]]
-- >>> [[1,2], [3 :: Int64]] ^.. traversed . traversed
-- [1,2,3]
--
-- | Collect the fock of an optic into a list.
--
-- @
-- 'toListOf' 'folded_' = 'Data.Foldable.toList'
-- @
--
-- /Benchmark: 1.73x vs Map.elems on Map (Endo closure chain)./
-- /Same overhead as lens's toListOf — both use the Endo path./
-- /Note: ~8x vs foldr (:) [] on toListOf is misleading (foldr (:) []/
-- /on [a] is id). See "Data.Profunctor.Optic.Bench"./
--
toListOf :: AFold (Endo [a]) s a -> s -> [a]
toListOf o = foldrOf o (:) []
{-# INLINE toListOf #-}

-- | Collect the fock of an indexed optic into a list of index-value pairs.
--
-- @
-- 'toListOf' l ≡ 'map' 'snd' '.' 'ixtoListOf' l
-- @
--
-- >>> ixtoListOf (ix (Sum 1) traversed) ["foo","bar"]
-- [(Sum {getSum = 0},"foo"),(Sum {getSum = 1},"bar")]
--
-- @since 0.0.3
ixtoListOf :: Monoid k => AIxfold (Endo [(k, a)]) k s a -> s -> [(k, a)]
ixtoListOf o = ixfoldrOf o (\k a -> ((k,a):)) []
{-# INLINE ixtoListOf #-}

-- | Extract a 'NonEmpty' of the fock of an optic.
-- | Right fold over an optic.
--
-- >>> foldrOf folded (+) 0 [1..5::Int64]
-- 15
--
foldrOf :: AFold (Endo r) s a -> (a -> r -> r) -> r -> s -> r
foldrOf o f r = (`appEndo` r) . foldMapOf o (Endo . f)
{-# INLINE foldrOf #-}

-- | Indexed right fold over an indexed optic.
--
-- @
-- 'foldrOf' o ≡ 'ixfoldrOf' o '.' 'const'
-- 'foldrWithKey' f ≡ 'ixfoldrOf' 'ixfolded' f
-- @
--
-- @since 0.0.3
ixfoldrOf :: Monoid k => AIxfold (Endo r) k s a -> (k -> a -> r -> r) -> r -> s -> r
ixfoldrOf o f r = (`appEndo` r) . ixfoldMapOf o (\j -> Endo . f j)
{-# INLINE ixfoldrOf #-}

-- | Left fold over an optic.
--
foldlOf :: AFold ((Endo-Dual) r) s a -> (r -> a -> r) -> r -> s -> r
foldlOf o f r = (`appEndo` r) . getDual . foldMapOf o (Dual . Endo . flip f)
{-# INLINE foldlOf #-}

-- | Left fold over an indexed optic.
--
-- @
-- 'foldlOf' o ≡ 'ixfoldlOf' o '.' 'const'
-- 'foldlWithKey' f ≡ 'ixfoldlOf' 'ixfolded' f
-- @
--
-- @since 0.0.3
ixfoldlOf :: Monoid k => AIxfold ((Endo-Dual) r) k s a -> (k -> r -> a -> r) -> r -> s -> r
ixfoldlOf o f r = (`appEndo` r) . getDual . ixfoldMapOf o (\k -> Dual . Endo . flip (f k))
{-# INLINE ixfoldlOf #-}

-- | Strict right fold over an optic.
--
foldrOf' :: AFold ((Endo-Dual) (Endo r)) s a -> (a -> r -> r) -> r -> s -> r
foldrOf' o f r xs = foldlOf o f' (Endo id) xs `appEndo` r where f' (Endo k) x = Endo $ \ z -> k $! f x z
{-# INLINE foldrOf' #-}

-- | Strict right fold over an indexed optic.
--
-- @
-- 'foldrOf'' o ≡ 'ixfoldrOf'' o '.' 'const'
-- 'foldrWithKey'' f ≡ 'ixfoldrOf'' 'ixfolded' f
-- @
--
-- @since 0.0.3
ixfoldrOf' :: Monoid k => AIxfold ((Endo-Dual) (Endo r)) k s a -> (k -> a -> r -> r) -> r -> s -> r
ixfoldrOf' o f r s = ixfoldlOf o f' (Endo id) s `appEndo` r where f' k (Endo acc) x = Endo $ \ z -> acc $! f k x z
{-# INLINE ixfoldrOf' #-}

-- | Strict left fold over an optic.
--
-- @
-- 'Data.Foldable.foldl'' ≡ 'foldlOf'' 'folding'
-- @
--
foldlOf' :: AFold (Endo (Endo r)) s a -> (r -> a -> r) -> r -> s -> r
foldlOf' o f r s = foldrOf o f' (Endo id) s `appEndo` r where f' x (Endo k) = Endo $ \z -> k $! f z x
{-# INLINE foldlOf' #-}

-- | Strict left fold over an indexed optic.
--
-- @
-- 'foldlOf'' o ≡ 'ixfoldlOf'' o '.' 'const'
-- 'foldlWithKey'' f ≡ 'ixfoldlOf'' 'ixfolded' f
-- @
--
-- @since 0.0.3
ixfoldlOf' :: Monoid k => AIxfold (Endo (Endo r)) k s a -> (k -> r -> a -> r) -> r -> s -> r
ixfoldlOf' o f r s = ixfoldrOf o f' (Endo id) s `appEndo` r where f' k x (Endo acc) = Endo $ \z -> acc $! f k z x
{-# INLINE ixfoldlOf' #-}

{-
safeHead [] = print "Ouch!" >> return 'x'
safeHead (x:_) = print x >> return x

foo a r = safeHead a >>= (\x -> return $ x : r)

λ> foldrMOf folded_ foo "" ["alpha","beta","gamma"]
'g'
'b'
'a'
"abg"

λ> foldlMOf folded_ foo "" ["alpha","beta","gamma"]
"Ouch!"
'x'
'x'
"xgamma"
-}

-- | Monadic right fold over an optic.
--
-- >>> foldrMOf folded_ (\x y -> Identity (x++y)) "" ["foo","bar","baz"]
-- Identity "foobarbaz"
--
foldrMOf :: Monad m => AFold ((Endo-Dual) (EndoM m r)) s a -> (a -> r -> m r) -> r -> s -> m r
foldrMOf o f r xs = foldlOf o f' mempty xs `appEndoM` r where f' e a = e <> EndoM (f a) -- f x z >>= k
{-# INLINE foldrMOf #-}

-- | Monadic right fold over an indexed optic.
--
-- @
-- 'foldrMOf' ≡ 'ixfoldrM' '.' 'const'
-- @
--
-- @since 0.0.3
ixfoldrMOf :: Monoid k => Monad m => AIxfold ((Endo-Dual) (EndoM m r)) k s a -> (k -> a -> r -> m r) -> r -> s -> m r
ixfoldrMOf o f r xs = ixfoldlOf o f' mempty xs `appEndoM` r where f' k e a = e <> EndoM (f k a)
{-# INLINE ixfoldrMOf #-}

-- | Monadic left fold over an optic.
--
foldlMOf :: Monad m => AFold (Endo (EndoM m r)) s a -> (r -> a -> m r) -> r -> s -> m r
foldlMOf o f r xs = foldrOf o f' mempty xs `appEndoM` r where f' a e = e <> EndoM (`f` a)
{-# INLINE foldlMOf #-}

-- | Monadic left fold over an indexed optic.
--
-- @
-- 'foldlMOf' ≡ 'ixfoldlMOf' '.' 'const'
-- @
--
-- @since 0.0.3
ixfoldlMOf :: Monoid k => Monad m => AIxfold (Endo (EndoM m r)) k s a -> (k -> r -> a -> m r) -> r -> s -> m r
ixfoldlMOf o f r xs = ixfoldrOf o f' mempty xs `appEndoM` r where f' k a e = e <> EndoM (flip (f k) a)
{-# INLINE ixfoldlMOf #-}

-- | Applicative fold over an optic.
--
-- @
-- 'Data.Foldable.traverse_' ≡ 'traverseOf_' 'folded'
-- @
--
-- >>> traverseOf_ bitraversed putStrLn ("hello","world")
-- hello
-- world
--
traverseOf_ :: Applicative f => AFold (Endo (f ())) s a -> (a -> f r) -> s -> f ()
traverseOf_ p f = foldrOf p (\a fu -> void (f a) *> fu) (pure ())
{-# INLINE traverseOf_ #-}

-- | Applicative fold over an indexed optic.
--
-- @
-- 'ixtraverseOf_' 'ixfolded' ≡ 'traverseWithKey_'
-- @
--
-- @since 0.0.3
ixtraverseOf_ :: Monoid k => Applicative f => AIxfold (Endo (f ())) k s a -> (k -> a -> f r) -> s -> f ()
ixtraverseOf_ p f = ixfoldrOf p (\k a fu -> void (f k a) *> fu) (pure ())
{-# INLINE ixtraverseOf_ #-}

-- | Check whether an optic matchOf any focus.
--
-- >>> has just (Just 1)
-- True
-- >>> has just Nothing
-- False
--
has :: AFold0 a s a -> s -> Bool
has o = maybe False (const True) . preview o
{-# INLINE has #-}

-- | Check whether an optic has no focus.
--
hasn't :: AFold0 a s a -> s -> Bool
hasn't o = maybe True (const False) . preview o
{-# INLINE hasn't #-}

-- | Check whether any focus matchOf a predicate.
--
anyOf :: AFold Any s a -> (a -> Bool) -> s -> Bool
anyOf o f = getAny . foldMapOf o (Any . f)
{-# INLINE anyOf #-}

-- | Check whether all foci match a predicate.
--
allOf :: AFold All s a -> (a -> Bool) -> s -> Bool
allOf o f = getAll . foldMapOf o (All . f)
{-# INLINE allOf #-}

-- | Check that no focus matchOf a predicate.
--
noneOf :: AFold Any s a -> (a -> Bool) -> s -> Bool
noneOf o f = not . anyOf o f
{-# INLINE noneOf #-}

-- | Count the number of foci.
--
lengthOf :: AFold (Sum Int) s a -> s -> Int
lengthOf o = getSum . foldMapOf o (const (Sum 1))
{-# INLINE lengthOf #-}

-- | Sum all foci.
--
sumOf :: Num a => AFold (Sum a) s a -> s -> a
sumOf o = getSum . foldMapOf o Sum
{-# INLINE sumOf #-}

-- | Multiply all foci.
--
productOf :: Num a => AFold (Product a) s a -> s -> a
productOf o = getProduct . foldMapOf o Product
{-# INLINE productOf #-}

-- | Find the maximum focus, if any.
--
maximumOf :: Ord a => AFold (Endo (Endo (Maybe a))) s a -> s -> Maybe a
maximumOf o = foldlOf' o (\acc a -> Just $ maybe a (max a) acc) Nothing
{-# INLINE maximumOf #-}

-- | Find the minimum focus, if any.
--
minimumOf :: Ord a => AFold (Endo (Endo (Maybe a))) s a -> s -> Maybe a
minimumOf o = foldlOf' o (\acc a -> Just $ maybe a (min a) acc) Nothing
{-# INLINE minimumOf #-}

-- | Find the maximum focus by a comparison function, if any.
--
maximumByOf :: AFold (Endo (Endo (Maybe a))) s a -> (a -> a -> Ordering) -> s -> Maybe a
maximumByOf o cmp = foldlOf' o (\acc a -> Just $ maybe a (\b -> if cmp a b == GT then a else b) acc) Nothing
{-# INLINE maximumByOf #-}

-- | Find the minimum focus by a comparison function, if any.
--
minimumByOf :: AFold (Endo (Endo (Maybe a))) s a -> (a -> a -> Ordering) -> s -> Maybe a
minimumByOf o cmp = foldlOf' o (\acc a -> Just $ maybe a (\b -> if cmp a b == LT then a else b) acc) Nothing
{-# INLINE minimumByOf #-}

-- | Find the first focus matching a predicate, if any.
--
findOf :: AFold (Endo (Maybe a)) s a -> (a -> Bool) -> s -> Maybe a
findOf o f = foldrOf o (\a r -> if f a then Just a else r) Nothing
{-# INLINE findOf #-}

-- | Check whether a value is a focus of an optic.
--
elemOf :: Eq a => AFold Any s a -> a -> s -> Bool
elemOf o a = anyOf o (== a)
{-# INLINE elemOf #-}

-- | Retrieve the first focus, if any.
--
headOf :: AFold (Endo (Maybe a)) s a -> s -> Maybe a
headOf o = foldrOf o (\a _ -> Just a) Nothing
{-# INLINE headOf #-}

-- | Retrieve the last focus, if any.
--
lastOf :: AFold (Endo (Endo (Maybe a))) s a -> s -> Maybe a
lastOf o = foldlOf' o (\_ a -> Just a) Nothing
{-# INLINE lastOf #-}

---------------------------------------------------------------------
-- Fold0 Operators
---------------------------------------------------------------------

-- | TODO: Document
--
foldOf0 :: AFold0 r s a -> (a -> Maybe r) -> s -> Maybe r
foldOf0 o = (getAlt #.) #. foldMapOf o .# (Alt #.)
{-# INLINE foldOf0 #-}

-- | TODO: Document
--
-- @since 0.0.3
ixfoldOf0 :: Monoid k => AIxfold0 r k s a -> (k -> a -> Maybe r) -> s -> Maybe r
ixfoldOf0 o f = curry ((getAlt #.) #. foldMapOf o .# (Alt #.) $ uncurry f) mempty
{-# INLINE ixfoldOf0 #-}

-- | An infk alias for 'preview''.
--
-- @
-- ('^?') ≡ 'flip' 'preview''
-- @
--
-- Perform a safe 'head' of a 'Fold' or 'Traversal' or retrieve 'Just'
-- the result from a 'View' or 'Lens'.
--
-- When using a 'Traversal' as a partial 'Lens', or a 'Fold' as a partial
-- 'View' this can be a convenient way to extract the optional value.
-- | Preview the focus of a 'Fold0'.
--
-- /Benchmark: 1.01x vs direct (zero-cost). See "Data.Profunctor.Optic.Bench"./
--
preview :: MonadReader s m => AFold0 a s a -> m (Maybe a)
preview = flip previews id
{-# INLINE preview #-}

-- | TODO: Document
--
-- @since 0.0.3
ixpreview :: Monoid k => AIxfold0 (k , a) k s a -> s -> Maybe (k , a)
ixpreview o = ixpreviews o (,)
{-# INLINE ixpreview #-}

-- | TODO: Document
--
previews :: MonadReader s m => AFold0 r s a -> (a -> r) -> m (Maybe r)
previews o f = Reader.asks (foldOf0 o (Just . f))
{-# INLINE previews #-}

-- | TODO: Document
--
-- @since 0.0.3
ixpreviews :: Monoid k => AIxfold0 r k s a -> (k -> a -> r) -> s -> Maybe r
ixpreviews o f = ixfoldOf0 o (\k -> Just . f k)
{-# INLINE ixpreviews #-}

-- | TODO: Document
--
preuse :: MonadState s m => AFold0 a s a -> m (Maybe a)
preuse = flip preuses id
{-# INLINE preuse #-}

-- | TODO: Document
--
preuses :: MonadState s m => AFold0 r s a -> (a -> r) -> m (Maybe r)
preuses o f = State.gets $ previews o f
{-# INLINE preuses #-}

---------------------------------------------------------------------
-- Dual Operators
---------------------------------------------------------------------

-- | TODO: Document
--
-- >>> cofoldMapOf (from succ) (*2) 3
-- 7
--
-- Compare 'Data.Profunctor.Optic.View.reviews'.
--
cofoldMapOf :: ACotraversal (Const r) s t a b -> (r -> b) -> r -> t
cofoldMapOf o = (.# Const) #. cotraverseOf o .# (.# getConst)
{-# INLINE cofoldMapOf #-}

-- | TODO: Document
--
cofoldOfA :: Coapplicative f => ACofold (f b) t b -> f b -> t
cofoldOfA = flip cofoldMapOf copure
{-# INLINE cofoldOfA #-}

-- | TODO: Document
--
-- @since 0.0.3
cxfoldMapOf :: Monoid k => ACxfold r k t b -> (k -> r -> b) -> r -> t
cxfoldMapOf o f = flip (cofoldMapOf o $ flip f) mempty
{-# INLINE cxfoldMapOf #-}

---------------------------------------------------------------------
-- Auxiliary Types
---------------------------------------------------------------------

newtype EndoM m a = EndoM { appEndoM :: a -> m a }

instance Monad m => Semigroup (EndoM m a) where
    (EndoM f) <> (EndoM g) = EndoM (f <=< g)
    {-# INLINE (<>) #-}

instance Monad m => Monoid (EndoM m a) where
    mempty = EndoM return
    {-# INLINE mempty #-}

    mappend = (<>)
    {-# INLINE mappend #-}
