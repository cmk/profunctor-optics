{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Data.Profunctor.Optic.Fold (
    -- * Fold0
    Fold0
  , fold0
  , afold0
  , failing
  , toFold0
  , fromFold0
    -- * Fold
  , Fold
  , Cofold
  , fold_
  , ofold_
  , afold
  , folding
  , acofold
  , cofolding
  , foldVl
  , cofoldVl
    -- * Fold1
  , Fold1
  , Cofold1
  , fold1_
  , folding1
  , cofolding1
  , fold1Vl
  , cofold1Vl
    -- * Optics
  , folded0
  , filtered
  , folded
  , values
  , ofolded
  , folded_
  , ofolded_
  , folded1 
  , folded1_
  , afolded
  , aofolded
  , afolded1
  , aofolded1
  , acolist
  , acolist1
    -- * Operators
  , folds0
  , folds
  , cofolds
  , (^?)
  , preview 
  , previews
  , preuse
  , preuses
  , (^..)
  , lists
  , colists
  , lists1
  , foldsr
  , cofoldsr
  , foldsl
  , foldsr'
  , foldsl'
  , foldsrM
  , foldslM
  , traverses_
) where

import Control.Applicative as A
import Control.Monad (void)
import Control.Monad.Reader as Reader hiding (lift)
import Control.Monad.State as State hiding (lift)
import Data.Foldable (Foldable, traverse_)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe
import Data.Monoid
import Data.MonoTraversable (Element,MonoTraversable(..),MonoFoldable(..))
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Combinator
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Traversal
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Prism
import Data.Profunctor.Rep.Foldl (EndoM(..))
import qualified Data.List as L
import qualified Data.List.NonEmpty as NNL
import qualified Data.Profunctor.Rep.Foldl1 as M
--import qualified Data.NonNull as NN
import Data.Containers as C
import Data.NonNull 

type (g - f) a = f (g a)

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

---------------------------------------------------------------------
-- 'Fold0'
---------------------------------------------------------------------

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
fold0 f = coercer . lmap (\s -> maybe (Left s) Right (f s)) . right'
{-# INLINE fold0 #-}

-- | TODO: Document
--
afold0 :: ((a -> Maybe r) -> s -> Maybe r) -> AFold0 r s a
afold0 f = afold $ (Alt #.) #. f .# (getAlt #.) 
{-# INLINE afold0 #-}

infixl 3 `failing`

-- | If the first 'Fold0' has no focus then try the second one.
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

-- | Obtain a 'View' from a 'Fold0' 
--
-- > 'fromFold0' = 'to' . 'preview'
--
fromFold0 ::  AFold0 a s a -> View s (Maybe a)
fromFold0 = (\f -> coercer . lmap f) . preview
{-# INLINE fromFold0 #-}

---------------------------------------------------------------------
-- 'Fold'
---------------------------------------------------------------------

-- | Obtain a 'Fold' directly.
--
-- @ 
-- 'fold_' ('lists' o) ≡ o
-- 'fold_' f ≡ 'to' f . 'foldVl' 'traverse_'
-- 'fold_' f ≡ 'coercer' . 'lmap' f . 'lift' 'traverse_'
-- @
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- This can be useful to lift operations from @Data.List@ and elsewhere into a 'Fold'.
--
-- >>> [1,2,3,4] ^.. fold_ tail
-- [2,3,4]
--
fold_ :: Foldable f => (s -> f a) -> Fold s a
fold_ f = coercer . lmap f . foldVl traverse_
{-# INLINE fold_ #-}

-- | Obtain a 'Fold' directly.
--
-- >>> "foobar" ^.. ofold_ tail
-- "oobar"
--
ofold_ :: MonoFoldable a => (s -> a) -> Fold s (Element a)
ofold_ f = coercer . lmap f . foldVl otraverse_
{-# INLINE ofold_ #-}

-- | TODO: Document
--
-- @ 
-- 'afold' :: ((a -> r) -> s -> r) -> 'AFold' r s a
-- @
--
afold :: ((a -> r) -> s -> r) -> ATraversal (Const r) s t a b
afold f = atraversal $ (Const #.) #. f .# (getConst #.)
{-# INLINE afold #-}

-- | Obtain a 'Fold' from a 'Traversable' functor.
--
-- @
-- 'folding' f ≡ 'traversed' . 'to' f
-- 'folding' f ≡ 'foldVl' 'traverse' . 'to' f
-- @
--
folding :: Traversable f => (s -> a) -> Fold (f s) a
folding f = foldVl traverse . coercer . lmap f
{-# INLINE folding #-}

-- | Obtain a 'Fold' from a 'MonoTraversable' functor.
--
-- @
-- 'folding' f ≡ 'otraversed' . 'to' f
-- 'folding' f ≡ 'foldVl' 'otraverse' . 'to' f
-- @
--
ofolding :: MonoTraversable s => (Element s -> a) -> Fold s a
ofolding f = foldVl otraverse . coercer . lmap f
{-# INLINE ofolding #-}

-- | TODO: Document
--
acofold :: ((r -> b) -> r -> t) -> ACofold r t b
acofold f = acotraversal $ (.# getConst) #. f .# (.# Const)
{-# INLINE acofold #-}

-- | TODO: Document
--
-- > 'cofoldVl' 'cotraverse' . 'from' f
--
cofolding :: Distributive g => (b -> t) -> Cofold (g t) b
cofolding f = cofoldVl cotraverse . coercel . rmap f
{-# INLINE cofolding #-}

-- | Obtain a 'Fold' from a Van Laarhoven 'Fold'.
--
foldVl :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> Fold s a
foldVl f = coercer . traversalVl f . coercer
{-# INLINE foldVl #-}

-- | Obtain a 'Cofold' from a Van Laarhoven 'Cofold'.
--
cofoldVl :: (forall f. Coapplicative f => (f a -> b) -> f s -> t) -> Cofold t b
cofoldVl f = coercel . cotraversalVl f . coercel
{-# INLINE cofoldVl #-}

---------------------------------------------------------------------
-- Fold1
---------------------------------------------------------------------

-- | Obtain a 'Fold1' directly.
--
-- @ 
-- 'fold1_' ('lists1' o) ≡ o
-- 'fold1_' f ≡ 'to' f . 'fold1Vl' 'traverse1_'
-- 'fold1_' f ≡ 'coercer' . 'lmap' f . 'lift' 'traverse1_'
-- @
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- This can be useful to represent operations from @Data.List.NonEmpty@ and elsewhere into a 'Fold1'.
--
fold1_ :: Foldable1 f => (s -> f a) -> Fold1 s a
fold1_ f = coercer . lmap f . fold1Vl traverse1_
{-# INLINE fold1_ #-}

-- | Obtain a 'Fold1' from a 'Traversable1' functor.
--
-- @
-- 'folding1' f ≡ 'traversed1' . 'to' f
-- 'folding1' f ≡ 'fold1Vl' 'traverse1' . 'to' f
-- @
--
folding1 :: Traversable1 f => (s -> a) -> Fold1 (f s) a
folding1 f = fold1Vl traverse1 . coercer . lmap f
{-# INLINE folding1 #-}

-- | TODO: Document
--
-- > 'cofolding1' f = 'cofold1Vl' 'cotraverse1' . 'from' f
--
cofolding1 :: Distributive1 g => (b -> t) -> Cofold1 (g t) b
cofolding1 f = cofold1Vl cotraverse1 . coercel . rmap f
{-# INLINE cofolding1 #-}

-- | Obtain a 'Fold1' from a Van Laarhoven 'Fold1'.
--
-- See 'Data.Profunctor.Optic.Property'.
--
fold1Vl :: (forall f. Apply f => (a -> f b) -> s -> f t) -> Fold1 s a
fold1Vl f = coercer . represent f . coercer
{-# INLINE fold1Vl #-}

-- | Obtain a 'Cofold1' from a Van Laarhoven 'Cofold1'.
--
cofold1Vl :: (forall f. Coapply f => (f a -> b) -> f s -> t) -> Cofold1 t b
cofold1Vl f = coercel . cotraversal1Vl f . coercel
{-# INLINE cofold1Vl #-}

---------------------------------------------------------------------
-- Optics 
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
filtered p = traversal0Vl (\point f a -> if p a then f a else point a) . coercer
{-# INLINE filtered #-}

-- | Obtain a 'Fold' from a 'Traversable' functor.
--
folded :: Traversable f => Fold (f a) a
folded = folding id
{-# INLINE folded #-}

-- | 'Fold' over the values of a 'IsMap', in ascending key order.
--
-- >>> lists values [(1,3),(2,4)]
-- [3,4]
--
values :: IsMap s => Fold s (Value s)
values = fold_ C.mapToList . second'
{-# INLINE values #-}

-- | Obtain a 'Fold' from a 'MonoTraversable' functor.
--
ofolded :: MonoTraversable a => Fold a (Element a)
ofolded = ofolding id
{-# INLINE ofolded #-}

-- | The canonical 'Fold'.
--
-- @
-- 'Data.Foldable.foldMap' ≡ 'withForget' 'folded_''
-- @
--
folded_ :: Foldable f => Fold (f a) a
folded_ = fold_ id
{-# INLINE folded_ #-}

-- | Obtain a 'Fold' from a 'MonoFoldable'.
--
ofolded_ :: MonoFoldable a => Fold a (Element a)
ofolded_ = ofold_ id
{-# INLINE ofolded_ #-}

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

-- | TODO: Document
--
afolded :: Foldable f => Monoid r => AFold r (f a) a
afolded = afold foldMap
{-# INLINE afolded #-}

-- | TODO: Document
--
aofolded :: MonoFoldable a => Monoid r => AFold r a (Element a)
aofolded = afold ofoldMap
{-# INLINE aofolded #-}

-- | TODO: Document
--
afolded1 :: Foldable1 f => Semigroup r => AFold r (f a) a
afolded1 = afold foldMap1
{-# INLINE afolded1 #-}

-- | TODO: Document
--
aofolded1 :: MonoFoldable a => Semigroup r => AFold r (NonNull a) (Element a)
aofolded1 = afold ofoldMap1
{-# INLINE aofolded1 #-}

-- | Right list unfold over an optic.
--
acolist :: ACofold a [b] (Maybe (b, a))
acolist = acofold L.unfoldr
{-# INLINE acolist #-}

--abytestring :: ACofold a Words.ByteString (Maybe (Word8, a))
--abytestring = acofold Words.unfoldr

-- | Right non-empty list unfold over an optic.
--
acolist1 :: ACofold a (NonEmpty b) (b, Maybe a)
acolist1 = acofold NNL.unfoldr
{-# INLINE acolist1 #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | TODO: Document
--
folds0 :: AFold0 r s a -> (a -> Maybe r) -> s -> Maybe r
folds0 o = (getAlt #.) #. folds o .# (Alt #.)
{-# INLINE folds0 #-}

-- | Map an optic to a monoid and combine the results.
--
-- @
-- 'Data.Foldable.foldMap' = 'folds' 'folded_'
-- @
--
-- >>> folds both (\x -> [x, x + 1]) (1,3)
-- [1,2,3,4]
-- >>> folds both id (["foo"], ["bar", "baz"])
-- ["foo","bar","baz"]
--
folds :: AFold r s a -> (a -> r) -> s -> r
folds o = (getConst #.) #. traverses o .# (Const #.)
{-# INLINE folds #-}

-- | TODO: Document
--
-- >>> cofolds (from succ) (*2) 3
-- 7
--
-- Compare 'Data.Profunctor.Optic.View.reviews'.
--
cofolds :: ACofold r t b -> (r -> b) -> r -> t
cofolds o = (.# Const) #. cotraverses o .# (.# getConst) 
{-# INLINE cofolds #-}

infixl 8 ^?

-- | An infix alias for 'preview''.
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
-- >>> Left 4 ^? left'
-- Just 4
-- >>> Right 4 ^? left'
-- Nothing
--
(^?) :: s -> AFold0 a s a -> Maybe a
(^?) = flip preview
{-# INLINE (^?) #-}

-- | TODO: Document
--
preview :: MonadReader s m => AFold0 a s a -> m (Maybe a)
preview = flip previews id
{-# INLINE preview #-}

-- | TODO: Document
--
previews :: MonadReader s m => AFold0 r s a -> (a -> r) -> m (Maybe r)
previews o f = Reader.asks (folds0 o (Just . f))
{-# INLINE previews #-}

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

infixl 8 ^..

-- | Infix alias of 'lists'.
--
-- @
-- 'Data.Foldable.toList' xs ≡ xs '^..' 'folding'
-- ('^..') ≡ 'flip' 'lists'
-- @
--
-- >>> [[1,2], [3 :: Int64]] ^.. id
-- [[[1,2],[3]]]
-- >>> [[1,2], [3 :: Int64]] ^.. traversed
-- [[1,2],[3]]
-- >>> [[1,2], [3 :: Int64]] ^.. traversed . traversed
-- [1,2,3]
--
-- >>> (1,2) ^.. bitraversed
-- [1,2]
--
(^..) :: s -> AFold (Endo [a]) s a -> [a]
(^..) = flip lists
{-# INLINE (^..) #-}

-- | Collect the foci of an optic into a list.
--
-- @
-- 'lists' 'folded_' = 'Data.Foldable.toList'
-- @
--
lists :: AFold (Endo [a]) s a -> s -> [a]
lists o = foldsr o (:) []
{-# INLINE lists #-}

-- | TODO: Document.
--
colists :: ACofold b (Endo [t]) (Endo [b]) -> b -> [t]
colists o = cofoldsr o (:) []
{-# INLINE colists #-}

-- | Extract a 'NonEmpty' of the foci of an optic.
--
-- @
-- 'lists1' 'folded1_' = 'Data.Semigroup.Foldable.toNonEmpty'
-- @
--
-- >>> lists1 bitraversed1 ('h' :| "ello", 'w' :| "orld")
-- ('h' :| "ello") :| ['w' :| "orld"]
--
lists1 :: AFold (M.Nedl a) s a -> s -> NonEmpty a
lists1 l = M.runNedl . folds l (M.Nedl . (:|))
{-# INLINE lists1 #-}

-- | Right fold over an optic.
--
-- >>> foldsr folded (+) 0 [1..5::Int64]
-- 15
--
foldsr :: AFold (Endo r) s a -> (a -> r -> r) -> r -> s -> r
foldsr o f r = (`appEndo` r) . folds o (Endo . f)
{-# INLINE foldsr #-}

-- | TODO: Document
--
cofoldsr :: ACofold r (Endo t) (Endo b) -> (r -> b -> b) -> t -> r -> t
cofoldsr o f t = (`appEndo` t) . cofolds o (Endo . f)
{-# INLINE cofoldsr #-}

-- | Left fold over an optic.
--
foldsl :: AFold ((Endo-Dual) r) s a -> (r -> a -> r) -> r -> s -> r
foldsl o f r = (`appEndo` r) . getDual . folds o (Dual . Endo . flip f)
{-# INLINE foldsl #-}

-- | Strict right fold over an optic.
--
foldsr' :: AFold ((Endo-Dual) (Endo r)) s a -> (a -> r -> r) -> r -> s -> r
foldsr' o f r xs = foldsl o f' (Endo id) xs `appEndo` r where f' (Endo k) x = Endo $ \ z -> k $! f x z
{-# INLINE foldsr' #-}

-- | Strict left fold over an optic.
--
-- @
-- 'Data.Foldable.foldl'' ≡ 'foldsl'' 'folding'
-- @
--
foldsl' :: AFold (Endo (Endo r)) s a -> (r -> a -> r) -> r -> s -> r
foldsl' o f r s = foldsr o f' (Endo id) s `appEndo` r where f' x (Endo k) = Endo $ \z -> k $! f z x
{-# INLINE foldsl' #-}

{- 
safeHead [] = print "Ouch!" >> return 'x'
safeHead (x:_) = print x >> return x

foo a r = safeHead a >>= (\x -> return $ x : r)

λ> foldsrM folded_ foo "" ["alpha","beta","gamma"]
'g'
'b'
'a'
"abg"

λ> foldslM folded_ foo "" ["alpha","beta","gamma"]
"Ouch!"
'x'
'x'
"xgamma"
-}

-- | Monadic right fold over an optic.
--
-- >>> foldsrM folded_ (\x y -> Identity (x++y)) "" ["foo","bar","baz"]
-- Identity "foobarbaz"
--
foldsrM :: Monad m => AFold ((Endo-Dual) (EndoM m r)) s a -> (a -> r -> m r) -> r -> s -> m r
foldsrM o f r xs = foldsl o f' mempty xs `appEndoM` r where f' e a = e <> EndoM (f a) -- f x z >>= k
{-# INLINE foldsrM #-}

-- | Monadic left fold over an optic.
--
foldslM :: Monad m => AFold (Endo (EndoM m r)) s a -> (r -> a -> m r) -> r -> s -> m r
foldslM o f r xs = foldsr o f' mempty xs `appEndoM` r where f' a e = e <> EndoM (`f` a)
{-# INLINE foldslM #-}

-- | Applicative fold over an optic.
--
-- >>> traverses_ both putStrLn ("hello","world")
-- hello
-- world
--
-- @
-- 'Data.Foldable.traverse_' ≡ 'traverses_' 'folded'
-- @
--
traverses_ :: Applicative f => AFold (Endo (f ())) s a -> (a -> f r) -> s -> f ()
traverses_ p f = foldsr p (\a fu -> void (f a) *> fu) (pure ())
{-# INLINE traverses_ #-}
