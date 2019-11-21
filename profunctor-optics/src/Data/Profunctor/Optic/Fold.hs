{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Fold (
    -- * Types
    Fold0
  , AFold0
  , Fold
  , AFold
  , Fold1
  , AFold1
  , Cofold
  , ACofold
    -- * Constructors
  , fold0 
  , foldVl
  , fold1Vl
  , cofoldVl 
  , folding 
  , folding1
  , cofolding
  , folding_
  , folding1_
  , afold
  , afold1
  , acofold
  , failing
  , toFold0
  , toFold 
  , toFold1
  , fromFold0 
  , cloneFold
  , cloneFold1
    -- * Representatives
  , Fold0Rep(..)
  , Pre(..)
    -- * Primitive operators
  , maybeOf
  , previewOf
  , foldMapOf
  , foldMap1Of 
  , cofoldMapOf
  , foldOf 
  , fold1Of 
  , cofoldOf 
  , toListOf
  , toNelOf
  , toPureOf
  , productOf
  , product1Of
    -- * Common optics
  , folded0
  , folded
  , folded1 
  , cofolded 
  , folded_ 
  , folded1_
  , unital
  , nonunital
  , presemiring
  , summed
  , summed1
  , multiplied 
  , multiplied1 
    -- * Derived operators
  , (^?)
  , is
  , isnt
  , preview 
  , preuse
  , (^..)
  , foldsr
  , foldsl
  , foldsl'
  , foldsM'
  , endo 
  , endoM 
  , has
  , hasnt 
  , nulls 
  , min
  , max
  , pmin
  , pmax
  , joins
  , joins'
  , meets
  , meets'
  , all 
  , any 
  , elem
  , pelem
    -- * MonadUnliftIO 
  , tries
  , tries_ 
  , catches
  , catches_
  , handles
  , handles_
    -- * Auxilliary Types
  , All, Any
  , NonEmptyDList(..)
) where

import Control.Exception (Exception)
import Control.Monad ((<=<))
import Control.Monad.IO.Unlift
import Control.Monad.Reader as Reader hiding (lift)
import Control.Monad.State as State hiding (lift)
import Data.Foldable (Foldable, foldMap, traverse_)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe
import Data.Monoid hiding (All(..), Any(..))
import Data.Prd (Prd(..), Min(..), Max(..))
import Data.Prd.Lattice (Lattice(..))
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Prism (right, just, async)
import Data.Profunctor.Optic.Traversal (matches)
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.View (to, from, view, cloneView)
import Data.Semiring (Semiring(..), Prod(..))
import qualified Control.Exception as Ex
import qualified Data.List.NonEmpty as NEL
import qualified Data.Prd as Prd
import qualified Data.Semiring as Rng
import qualified Prelude as Pre 

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> import Control.Exception hiding (catches)
-- >>> import Data.Maybe
-- >>> import Data.Monoid
-- >>> import Data.Semiring hiding (unital,nonunital, presemiring)
-- >>> import Data.List.NonEmpty (NonEmpty(..))
-- >>> import qualified Data.List.NonEmpty as NE
-- >>> import Data.Functor.Identity
-- >>> :load Data.Profunctor.Optic


---------------------------------------------------------------------
-- 'Fold0', 'Fold' & 'Cofold'
---------------------------------------------------------------------

-- | Obtain a 'Fold0' from a partial function.
--
-- @
-- 'fold0' ('maybeOf' o) ≡ o
-- 'fold0' ('view' o) ≡ o . 'just'
-- @
--
-- >>> preview (fold0 listToMaybe) "foo"
-- Just 'f'
--
-- >>> [Just 1, Nothing] ^.. folded . folded0
-- [1]
--
fold0 :: (s -> Maybe a) -> Fold0 s a
fold0 f = to (\s -> maybe (Left s) Right (f s)) . right'
{-# INLINE fold0 #-}

-- | Obtain a 'Fold' from a Van Laarhoven 'Fold'.
--
foldVl :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> Fold s a
foldVl f = coercer . repn f . coercer
{-# INLINE foldVl #-}

-- | Obtain a 'Fold1' from a Van Laarhoven 'Fold1'.
--
-- See 'Data.Profunctor.Optic.Property'.
--
fold1Vl :: (forall f. Apply f => (a -> f b) -> s -> f t) -> Fold1 s a
fold1Vl f = coercer . repn f . coercer
{-# INLINE fold1Vl #-}

-- | Obtain a 'Cofold' from a Van Laarhoven 'Cofold'.
--
cofoldVl :: (forall f. ComonadApply f => (f a -> b) -> f s -> t) -> Cofold t b
cofoldVl f = coercel . corepn f . coercel
{-# INLINE cofoldVl #-}

-- | Obtain a 'Fold' from a 'Traversable' functor.
--
-- @
-- 'folding' f ≡ 'traversed' . 'to' f
-- 'folding' f ≡ 'foldVl' 'traverse' . 'to' f
-- @
--
folding :: Traversable f => (s -> a) -> Fold (f s) a
folding f = foldVl traverse . to f
{-# INLINE folding #-}

-- | Obtain a 'Fold1' from a 'Traversable1' functor.
--
-- @
-- 'folding1' f ≡ 'traversed1' . 'to' f
-- 'folding1' f ≡ 'fold1Vl' 'traverse1' . 'to' f
-- @
--
folding1 :: Traversable1 f => (s -> a) -> Fold1 (f s) a
folding1 f = fold1Vl traverse1 . to f
{-# INLINE folding1 #-}

-- | Obtain an 'Cofold' from a 'Distributive' functor. 
--
-- @
-- 'cofolding' f ≡ 'cotraversed' . 'from' f
-- 'cofolding' f ≡ 'cofoldVl' 'cotraverse' . 'from' f
-- @
--
cofolding :: Distributive f => (b -> t) -> Cofold (f t) b
cofolding f = cofoldVl cotraverse . from f
{-# INLINE cofolding #-}

-- | Obtain a 'Fold' by lifting an operation that returns a 'Foldable' result.
--
-- @ 
-- 'folding_' ('toListOf' o) ≡ o
-- 'folding_' f ≡ 'to' f . 'foldVl' 'traverse_'
-- 'folding_' f ≡ 'coercer' . 'lmap' f . 'lift' 'traverse_'
-- @
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- This can be useful to repn operations from @Data.List@ and elsewhere into a 'Fold'.
--
-- >>> [1,2,3,4] ^.. folding_ tail
-- [2,3,4]
--
folding_ :: Foldable f => (s -> f a) -> Fold s a
folding_ f = to f . foldVl traverse_
{-# INLINE folding_ #-}

-- | Obtain a 'Fold1' by lifting an operation that returns a 'Foldable1' result.
--
-- @ 
-- 'folding1_' ('toNelOf' o) ≡ o
-- 'folding1_' f ≡ 'to' f . 'fold1Vl' 'traverse1_'
-- 'folding1_' f ≡ 'coercer' . 'lmap' f . 'lift' 'traverse1_'
-- @
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- This can be useful to repn operations from @Data.List.NonEmpty@ and elsewhere into a 'Fold1'.
--
folding1_ :: Foldable1 f => (s -> f a) -> Fold1 s a
folding1_ f = to f . fold1Vl traverse1_
{-# INLINE folding1_ #-}

-- | TODO: Document
--
afold :: Monoid r => ((a -> r) -> s -> r) -> AFold r s a
afold o = Star #. (Const #.) #. o .# (getConst #.) .# runStar
{-# INLINE afold #-}

-- | TODO: Document
--
afold1 :: Semigroup r => ((a -> r) -> s -> r) -> AFold1 r s a
afold1 o = Star #. (Const #.) #. o .# (getConst #.) .# runStar
{-# INLINE afold1 #-}

-- | TODO: Document
--
acofold :: ((r -> b) -> r -> t) -> ACofold r t b
acofold o = Costar #. (.# getConst) #. o .#  (.# Const) .# runCostar  
{-# INLINE acofold #-}

infixl 3 `failing` -- Same as (<|>)

-- | Try the first 'Fold0'. If it returns no entry, try the second one.
--
failing :: AFold0 a s a -> AFold0 a s a -> Fold0 s a
failing a b = fold0 $ \s -> maybe (preview b s) Just (preview a s)
{-# INLINE failing #-}

-- | Obtain a 'Fold0' from a 'View'.
--
-- @
-- 'toFold0' o ≡ o . 'just'
-- 'toFold0' o ≡ 'fold0' ('view' o)
-- @
--
toFold0 :: View s (Maybe a) -> Fold0 s a
toFold0 = (. just)
{-# INLINE toFold0 #-}

-- | Obtain a 'Fold' from a 'View' or 'AFold'.
--
toFold :: AView s a -> Fold s a
toFold = to . view
{-# INLINE toFold #-}

-- | Obtain a 'Fold1' from a 'View' or 'AFold1'.
--
toFold1 :: AView s a -> Fold1 s a
toFold1 = to . view
{-# INLINE toFold1 #-}

-- | Obtain a partial 'View' from a 'Fold0' 
--
fromFold0 ::  AFold0 a s a -> View s (Maybe a)
fromFold0 = to . preview
{-# INLINE fromFold0 #-}

-- | Obtain a 'Fold' from a 'AFold'.
--
cloneFold :: Monoid a => AFold a s a -> View s a
cloneFold = cloneView
{-# INLINE cloneFold #-}

-- | Obtain a 'Fold1' from a 'AFold1'.
--
cloneFold1 :: Semigroup a => AFold1 a s a -> View s a
cloneFold1 = cloneView
{-# INLINE cloneFold1 #-}

---------------------------------------------------------------------
-- 'Fold0Rep'
---------------------------------------------------------------------

newtype Fold0Rep r a b = Fold0Rep { runFold0Rep :: a -> Maybe r }

type AFold0 r s a = Optic' (Fold0Rep r) s a

instance Functor (Fold0Rep r a) where
  fmap _ (Fold0Rep p) = Fold0Rep p

instance Contravariant (Fold0Rep r a) where
  contramap _ (Fold0Rep p) = Fold0Rep p

instance Profunctor (Fold0Rep r) where
  dimap f _ (Fold0Rep p) = Fold0Rep (p . f)

instance Choice (Fold0Rep r) where
  left' (Fold0Rep p) = Fold0Rep (either p (const Nothing))
  right' (Fold0Rep p) = Fold0Rep (either (const Nothing) p)

instance Cochoice (Fold0Rep r) where
  unleft  (Fold0Rep k) = Fold0Rep (k . Left)
  unright (Fold0Rep k) = Fold0Rep (k . Right)

instance Strong (Fold0Rep r) where
  first' (Fold0Rep p) = Fold0Rep (p . fst)
  second' (Fold0Rep p) = Fold0Rep (p . snd)

instance Sieve (Fold0Rep r) (Pre r) where
  sieve = (Pre .) . runFold0Rep

instance Representable (Fold0Rep r) where
  type Rep (Fold0Rep r) = Pre r
  tabulate = Fold0Rep . (getPre .)
  {-# INLINE tabulate #-}

-- | 'Pre' is 'Maybe' with a phantom type variable.
--
newtype Pre a b = Pre { getPre :: Maybe a } deriving (Eq, Ord, Show)

instance Functor (Pre a) where fmap _ (Pre p) = Pre p

instance Contravariant (Pre a) where contramap _ (Pre p) = Pre p

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | TODO: Document
--
maybeOf :: AFold0 a s a -> s -> Maybe a
maybeOf = flip previewOf Just

-- | TODO: Document
--
previewOf :: Optic' (Fold0Rep r) s a -> (a -> Maybe r) -> s -> Maybe r
previewOf o = runFold0Rep #. o .# Fold0Rep

-- | Map parts of a structure to a monoid and combine the results.
--
-- @
-- 'Data.Foldable.foldMap' = 'foldMapOf' 'foldVl''
-- @
--
-- >>> foldMapOf both id (["foo"], ["bar", "baz"])
-- ["foo","bar","baz"]
--
-- @
-- 'foldMapOf' ::                  'Iso'' s a        -> (a -> r) -> s -> r
-- 'foldMapOf' ::                  'Lens'' s a       -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Monoid' r    => 'Prism'' s a      -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Monoid' r    => 'Traversal'' s a  -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Monoid' r    => 'Affine'' s a     -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Monoid' r    => 'Fold' s a        -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Semigroup' r => 'Fold1' s a       -> (a -> r) -> s -> r
-- @
--
foldMapOf :: Monoid r => AFold r s a -> (a -> r) -> s -> r
foldMapOf o = (getConst #.) #. runStar #. o .# Star .# (Const #.)
{-# INLINE foldMapOf #-}

-- | Map parts of a structure to a semigroup and combine the results.
--
foldMap1Of :: Semigroup r => AFold1 r s a -> (a -> r) -> s -> r
foldMap1Of o = (getConst #.) #. runStar #. o .# Star .# (Const #.)
{-# INLINE foldMap1Of #-}

-- | TODO: Document
--
-- >>> cofoldMapOf (from succ) (*2) 3
-- 7
--
-- Compare 'Data.Profunctor.Optic.View.reviews'.
--
cofoldMapOf :: ACofold r t b -> (r -> b) -> r -> t
cofoldMapOf o = (.# Const) #. runCostar #. o .# Costar .# (.# getConst)
{-# INLINE cofoldMapOf #-}

-- | TODO: Document
--
foldOf :: Monoid a => AFold a s a -> s -> a
foldOf = flip foldMapOf id
{-# INLINE foldOf #-}

-- | TODO: Document
--
fold1Of :: Semigroup a => AFold1 a s a -> s -> a
fold1Of = flip foldMap1Of id
{-# INLINE fold1Of #-}

-- | TODO: Document
--
cofoldOf :: ACofold b t b -> b -> t
cofoldOf = flip cofoldMapOf id
{-# INLINE cofoldOf #-}

-- | Collect the foci of a `Fold` into a list.
--
toListOf :: AFold (Endo [a]) s a -> s -> [a]
toListOf o = foldsr o (:) []
{-# INLINE toListOf #-}

{-
>>> toNelOf bitraversed1 ('h' :| "ello", 'w' :| "orld")
 "hello" :| ["world"]
-}

-- | Extract a 'NonEmpty' of the targets of 'Fold1'.
--
--
-- @
-- 'toNelOf' :: 'View' s a        -> s -> NonEmpty a
-- 'toNelOf' :: 'Fold1' s a       -> s -> NonEmpty a
-- 'toNelOf' :: 'Lens'' s a       -> s -> NonEmpty a
-- 'toNelOf' :: 'Iso'' s a        -> s -> NonEmpty a
-- 'toNelOf' :: 'Traversal1'' s a -> s -> NonEmpty a
-- 'toNelOf' :: 'Prism'' s a      -> s -> NonEmpty a
-- @
--
toNelOf :: AFold1 (NonEmptyDList a) s a -> s -> NonEmpty a
toNelOf l = flip getNonEmptyDList [] . foldMap1Of l (NonEmptyDList #. (:|))
{-# INLINE toNelOf #-}

-- | TODO: Document
-- 
-- @
-- toPureOf :: Fold s a -> s -> [a]
-- toPureOf :: Applicative f => Setter s t a b -> s -> f a
-- @
--
toPureOf :: Applicative f => Monoid (f a) => AFold (f a) s a -> s -> f a
toPureOf o = foldMapOf o pure
{-# INLINE toPureOf #-}

-- | Compute the semiring product of a fold.
--
-- For semirings without a multiplicative unit this is equivalent to @const mempty@:
--
-- >>> productOf folded Just [1..(5 :: Int)]
-- Just 0
--
-- In this situation you most likely want to use 'product1Of'.
--
productOf :: Monoid r => Semiring r => AFold (Prod r) s a -> (a -> r) -> s -> r
productOf o p = getProd . foldMapOf o (Prod . p)
{-# INLINE productOf #-}

-- | Compute the semiring product of a non-empty fold.
--
product1Of :: Semiring r => AFold1 (Prod r) s a -> (a -> r) -> s -> r
product1Of o p = getProd . foldMap1Of o (Prod . p)
{-# INLINE product1Of #-}

---------------------------------------------------------------------
-- Common 'Fold's
---------------------------------------------------------------------

-- | Obtain a 'Fold0' from a partial function.
--
-- >>> [Just 1, Nothing] ^.. folded . folded0
-- [1]
--
folded0 :: Fold0 (Maybe a) a
folded0 = fold0 id
{-# INLINE folded0 #-}

-- | Obtain a 'Fold' from a 'Traversable' functor.
--
folded :: Traversable f => Fold (f a) a
folded = folding id
{-# INLINE folded #-}

-- | Obtain a 'Fold1' from a 'Traversable1' functor.
--
folded1 :: Traversable1 f => Fold1 (f a) a
folded1 = folding1 id
{-# INLINE folded1 #-}

-- | Obtain an 'Cofold' from a 'Distributive' functor. 
--
cofolded :: Distributive f => Cofold (f b) b
cofolded = cofolding id
{-# INLINE cofolded #-}

-- | The canonical 'Fold'.
--
folded_ :: Foldable f => Fold (f a) a
folded_ = folding_ id
{-# INLINE folded_ #-}

-- | The canonical 'Fold1'.
--
folded1_ :: Foldable1 f => Fold1 (f a) a
folded1_ = folding1_ id
{-# INLINE folded1_ #-}

-- | Compute the result of an expression in a unital semiring.
--
-- @ 
-- 'unital' ≡ 'summed' . 'multiplied'
-- @
--
-- >>> foldOf unital [[1,2], [3,4 :: Int]]
-- 14
--
-- For semirings without a multiplicative unit this is 
-- equivalent to @const mempty@:
--
-- >>> foldOf unital $ (fmap . fmap) Just [[1,2], [3,4 :: Int]]
-- Just 0
--
-- In this situation you most likely want to use 'nonunital'.
--
unital :: Foldable f => Foldable g => Monoid r => Semiring r => AFold r (f (g a)) a
unital = summed . multiplied

-- | Semiring fold with no multiplicative unit.
--
-- @ 
-- 'nonunital' ≡ 'summed' . 'multiplied1'
-- @
--
-- >>> foldOf nonunital $ (fmap . fmap) Just [1 :| [2], 3 :| [4 :: Int]]
-- Just 14
--
nonunital :: Foldable f => Foldable1 g => Monoid r => Semiring r => AFold r (f (g a)) a
nonunital = summed . multiplied1

-- | Semiring fold with no additive or multiplicative unit.
--
-- @ 
-- 'presemiring' ≡ 'summed1' . 'multiplied1'
-- @
--
presemiring :: Foldable1 f => Foldable1 g => Semiring r => AFold1 r (f (g a)) a
presemiring = summed1 . multiplied1

-- | Compute the monoidal sum of a 'Fold'.
--
-- >>> 1 <> 2 <> 3 <> 4 :: Int
-- 10
-- >>> foldOf summed [1,2,3,4 :: Int]
-- 10
--
-- 'summed' and 'multiplied' compose just as they do in arithmetic:
--
-- >>> 1 >< 2 <> 3 >< 4 :: Int
-- 14
-- >>> foldOf (summed . multiplied) [[1,2], [3,4 :: Int]]
-- 14
-- >>> (1 <> 2) >< (3 <> 4) :: Int
-- 21
-- >>> foldOf (multiplied . summed) [[1,2], [3,4 :: Int]]
-- 21
--
summed :: Foldable f => Monoid r => AFold r (f a) a
summed = afold foldMap

-- | Compute the semigroup sum of a 'Fold1'.
--
-- >>> 1 <> 2 <> 3 <> 4 :: Int
-- 10
-- >>> fold1Of summed1 $ 1 :| [2,3,4 :: Int]
-- 10
--
summed1 :: Foldable1 f => Semigroup r => AFold1 r (f a) a
summed1 = afold1 foldMap1

-- | Compute the semiring product of a 'Fold'.
--
-- >>> 1 >< 2 >< 3 >< 4 :: Int
-- 24
-- >>> foldOf multiplied [1,2,3,4 :: Int]
-- 24
--
-- For semirings without a multiplicative unit this is 
-- equivalent to @const mempty@:
--
-- >>> foldOf multiplied $ fmap Just [1..(5 :: Int)]
-- Just 0
--
-- In this situation you most likely want to use 'multiplied1'.
--
multiplied :: Foldable f => Monoid r => Semiring r => AFold r (f a) a
multiplied = afold Rng.product

-- | Compute the semiring product of a 'Fold1'.
--
-- >>> fold1Of multiplied1 $ fmap Just (1 :| [2..(5 :: Int)])
-- Just 120 
--
multiplied1 :: Foldable1 f => Semiring r => AFold1 r (f a) a
multiplied1 = afold1 Rng.product1

---------------------------------------------------------------------
-- Derived operators
---------------------------------------------------------------------

infixl 8 ^?

-- | An infix variant of 'preview''.
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
--
-- >>> Left 4 ^? left
-- Just 4
--
-- >>> Right 4 ^? left
-- Nothing
--
(^?) :: s -> AFold0 a s a -> Maybe a
s ^? o = maybeOf o s

-- | Check to see if this 'Fold0' doesn't match.
--
-- >>> is just Nothing
-- False
--
is :: AFold0 a s a -> s -> Bool
is k s = isJust (preview k s)
{-# INLINE is #-}

-- | Check to see if this 'Fold0' doesn't match.
--
-- >>> isnt just Nothing
-- True
--
isnt :: AFold0 a s a -> s -> Bool
isnt k s = not (isJust (preview k s))
{-# INLINE isnt #-}

-- | TODO: Document
--
preview :: MonadReader s m => AFold0 a s a -> m (Maybe a)
preview o = Reader.asks $ maybeOf o
{-# INLINE preview #-}

-- | TODO: Document
--
preuse :: MonadState s m => AFold0 a s a -> m (Maybe a)
preuse o = State.gets $ preview o
{-# INLINE preuse #-}

infixl 8 ^..

-- | Infix version of 'toListOf'.
--
-- @
-- 'Data.Foldable.toList' xs ≡ xs '^..' 'folding'
-- ('^..') ≡ 'flip' 'toListOf'
-- @
--
-- >>> [[1,2], [3 :: Int]] ^.. id
-- [[[1,2],[3]]]
-- >>> [[1,2], [3 :: Int]] ^.. traversed
-- [[1,2],[3]]
-- >>> [[1,2], [3 :: Int]] ^.. traversed . traversed
-- [1,2,3]
--
-- >>> (1,2) ^.. bitraversed
-- [1,2]
--
-- @
-- ('^..') :: s -> 'View' s a     -> [a]
-- ('^..') :: s -> 'Fold' s a       -> [a]
-- ('^..') :: s -> 'Lens'' s a      -> [a]
-- ('^..') :: s -> 'Iso'' s a       -> [a]
-- ('^..') :: s -> 'Traversal'' s a -> [a]
-- ('^..') :: s -> 'Prism'' s a     -> [a]
-- ('^..') :: s -> 'Affine'' s a    -> [a]
-- @
--
(^..) :: s -> AFold (Endo [a]) s a -> [a]
(^..) = flip toListOf
{-# INLINE (^..) #-}

-- | Right fold over a 'Fold'.
--
-- >>> foldsr folded (<>) 0 [1..5::Int]
-- 15
--
foldsr :: AFold (Endo r) s a -> (a -> r -> r) -> r -> s -> r
foldsr p f r = (`appEndo` r) . foldMapOf p (Endo . f)

-- | Left fold over a 'Fold'.
--
foldsl :: AFold (Dual (Endo c)) s a -> (c -> a -> c) -> c -> s -> c
foldsl p f r = (`appEndo` r) . getDual . foldMapOf p (Dual . Endo . flip f)

-- | Fold repn the elements of a structure, associating to the left, but strictly.
--
-- @
-- 'Data.Foldable.foldl'' ≡ 'foldsl'' 'folding'
-- @
--
-- @
-- 'foldsl'' :: 'Iso'' s a        -> (c -> a -> c) -> c -> s -> c
-- 'foldsl'' :: 'Lens'' s a       -> (c -> a -> c) -> c -> s -> c
-- 'foldsl'' :: 'View' s a        -> (c -> a -> c) -> c -> s -> c
-- 'foldsl'' :: 'Fold' s a        -> (c -> a -> c) -> c -> s -> c
-- 'foldsl'' :: 'Traversal'' s a  -> (c -> a -> c) -> c -> s -> c
-- 'foldsl'' :: 'Traversal0'' s a -> (c -> a -> c) -> c -> s -> c
-- @
--
foldsl' :: AFold (Endo (Endo c)) s a -> (c -> a -> c) -> c -> s -> c
foldsl' o f c s = foldsr o f' (Endo id) s `appEndo` c
  where f' x (Endo k) = Endo $ \z -> k $! f z x
{-# INLINE foldsl' #-}

-- | A strict monadic left fold.
--
foldsM' :: Monad m => AFold (Endo (EndoM m r)) s a -> (r -> a -> m r) -> r -> s -> m r
foldsM' o f c s = foldsr o f' mempty s `appEndoM` c
  where f' x (EndoM k) = EndoM $ \z -> (f $! z) x >>= k

-- | TODO: Document
--
endo :: AFold (Endo (a -> a)) s (a -> a) -> s -> a -> a
endo o = foldsr o (.) id

-- | TODO: Document
--
endoM :: Monad m => AFold (Endo (a -> m a)) s (a -> m a) -> s -> a -> m a
endoM o = foldsr o (<=<) pure

-- | Determine whether a `Fold` has at least one focus.
--
has :: AFold Any s a -> s -> Bool
has p = foldMapOf p (const True)

-- | Determine whether a `Fold` does not have a focus.
--
hasnt :: AFold All s a -> s -> Bool
hasnt p = productOf p (const False)

-- | TODO: Document
--
nulls :: AFold All s a -> s -> Bool
nulls o = all o (const False)

-- | Compute the minimum of a totally ordered fold. 
--
min :: Ord a => AFold (Endo (Endo a)) s a -> a -> s -> a
min o = foldsl' o Pre.min

-- | Compute the maximum of a totally ordered fold.
--
max :: Ord a => AFold (Endo (Endo a)) s a -> a -> s -> a
max o = foldsl' o Pre.max

-- | Compute the minimum of a partially ordered fold, if one exists.
--
pmin :: Eq a => Prd a => AFold (Endo (EndoM Maybe a)) s a -> a -> s -> Maybe a
pmin o = foldsM' o Prd.pmin

-- | Compute the maximum of a partially ordered fold, if one exists.
--
pmax :: Eq a => Prd a => AFold (Endo (EndoM Maybe a)) s a -> a -> s -> Maybe a
pmax o = foldsM' o Prd.pmax

-- | Compute the join of a fold. 
--
joins :: Lattice a => AFold (Endo (Endo a)) s a -> a -> s -> a
joins o = foldsl' o (\/)

-- | Compute the join of a fold including a least element.
--
joins' :: Lattice a => Min a => AFold (Endo (Endo a)) s a -> s -> a
joins' o = joins o minimal

-- | Compute the meet of a fold.
--
meets :: Lattice a => AFold (Endo (Endo a)) s a -> a -> s -> a
meets o = foldsl' o (/\)

-- | Compute the meet of a fold including a greatest element.
--
meets' :: Lattice a => Max a => AFold (Endo (Endo a)) s a -> s -> a
meets' o = meets o maximal

-- | TODO: Document
--
all :: AFold All s a -> (a -> Bool) -> s -> Bool
all = productOf

-- | TODO: Document
--
any :: AFold Any s a -> (a -> Bool) -> s -> Bool
any = foldMapOf

-- | Determine whether a `Fold` contains a given element.
--
elem :: Eq a => AFold Any s a -> a -> s -> Bool
elem o a = any o (== a)

-- | Determine whether a `Fold` contains an element equivalent to a given element.
--
pelem :: Prd a => AFold Any s a -> a -> s -> Bool
pelem o a = foldMapOf o (Prd.=~ a)

------------------------------------------------------------------------------
-- 'MonadUnliftIO'
------------------------------------------------------------------------------

-- | Test for synchronous exceptions that match a given optic.
--
-- In the style of 'safe-exceptions' this function rethrows async exceptions 
-- synchronously in order to preserve async behavior,
-- 
-- @
-- 'tries' :: 'MonadUnliftIO' m => 'AFold0' e 'Ex.SomeException' e -> m a -> m ('Either' e a)
-- 'tries' 'exception' :: 'MonadUnliftIO' m => 'Exception' e => m a -> m ('Either' e a)
-- @
--
tries :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> m a -> m (Either e a)
tries o a = withRunInIO $ \run -> run (Right `liftM` a) `Ex.catch` \e ->
  if matches async e then throwM e else run $ maybe (throwM e) (return . Left) (preview o e)

-- | A variant of 'tries' that returns synchronous exceptions.
--
tries_ :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> m a -> m (Maybe a)
tries_ o a = preview right `liftM` tries o a
{-# INLINE tries_ #-}

-- | Catch synchronous exceptions that match a given optic.
--
-- Rethrows async exceptions synchronously in order to preserve async behavior.
--
-- @
-- 'catches' :: 'MonadUnliftIO' m => 'AFold0' e 'Ex.SomeException' e -> m a -> (e -> m a) -> m a
-- 'catches' 'exception' :: 'MonadUnliftIO' m => Exception e => m a -> (e -> m a) -> m a
-- @
--
-- >>> catches (only Overflow) (throwIO Overflow) (\_ -> return "caught")
-- "caught"
--
catches :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> m a -> (e -> m a) -> m a
catches o a ea = withRunInIO $ \run -> run a `Ex.catch` \e ->
  if matches async e then throwM e else run $ maybe (throwM e) ea (preview o e)

-- | Catch synchronous exceptions that match a given optic, discarding the match.
--
-- >>> catches_ (only Overflow) (throwIO Overflow) (return "caught")
-- "caught"
--
catches_ :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> m a -> m a -> m a
catches_ o x y = catches o x $ const y
{-# INLINE catches_ #-}

-- | Flipped variant of 'catches'.
--
-- >>> handles (only Overflow) (\_ -> return "caught") $ throwIO Overflow
-- "caught"
--
handles :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> (e -> m a) -> m a -> m a
handles o = flip $ catches o

-- | Flipped variant of 'catches_'.
--
-- >>> handles_ (only Overflow) (return "caught") $ throwIO Overflow
-- "caught"
--
handles_ :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> m a -> m a -> m a
handles_ o = flip $ catches_ o

throwM :: MonadIO m => Exception e => e -> m a
throwM = liftIO . Ex.throwIO

------------------------------------------------------------------------------
-- Auxilliary Types
------------------------------------------------------------------------------

type All = Prod Bool

type Any = Bool

newtype NonEmptyDList a
  = NonEmptyDList { getNonEmptyDList :: [a] -> NEL.NonEmpty a }

instance Semigroup (NonEmptyDList a) where
  NonEmptyDList f <> NonEmptyDList g = NonEmptyDList (f . NEL.toList . g)

{-|
> instance Monad m => Monoid (EndoM m a) where
>     mempty = EndoM return
>     mappend (EndoM f) (EndoM g) = EndoM (f <=< g)
-}
newtype EndoM m a = EndoM { appEndoM :: a -> m a }

instance Monad m => Semigroup (EndoM m a) where
    (EndoM f) <> (EndoM g) = EndoM (f <=< g)
    {-# INLINE (<>) #-}

instance Monad m => Monoid (EndoM m a) where
    mempty = EndoM return
    {-# INLINE mempty #-}

    mappend = (<>)
    {-# INLINE mappend #-}
