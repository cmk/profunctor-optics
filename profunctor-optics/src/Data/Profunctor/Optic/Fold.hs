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
  , ixfold0
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
  , aixfold
  , folding
  , ofolding
  , foldVl
  , ixfoldVl
  , acofold
  , cofolding
  , cofoldVl
    -- * Fold1
  , Fold1
  , Cofold1
  , fold1_
  , folding1
  , foldVl1
  , ixfoldVl1
  , cofolding1
  , cofoldVl1
    -- * Optics
  , folded0
  , filtered
  , folded
  , cofolded
  , ofolded
  , folded_
  , ofolded_
  , ixfoldedRep
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
  , (^?)
  , preview 
  , previews
  , preuse
  , preuses
  , folds
  , cofolds
  , foldsa
  , cofoldsa
  , (^..)
  , lists
  , lists1
  , foldsr
  , foldsl
  , foldsr'
  , foldsl'
  , foldsrM
  , foldslM
  , traverses_
    -- * Indexed operators
  , folds0WithKey
  , previewWithKey
  , previewsWithKey
  , foldsWithKey
  , cofoldsWithKey
  , (^%%)
  , listsWithKey
  , foldsrWithKey
  , foldslWithKey
  , foldsrWithKey'
  , foldslWithKey'
  , foldsrMWithKey
  , foldslMWithKey
  , traversesWithKey_
    -- * IO
  , tries
  , tries_
  , catches
  , catches_
  , handles
  , handles_
    -- * EndoM
  , EndoM(..)
    -- * Classes
  , Strong(..)
  , Choice(..)
  , Closed(..)
  , Representable(..)
  , Corepresentable(..)
) where

import Control.Applicative as A
import Control.Monad (void)
import Control.Monad.Reader as Reader hiding (lift)
import Control.Monad.State as State hiding (lift)
import Control.Monad.IO.Unlift
import Data.Foldable (Foldable, traverse_)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe
import Data.Monoid
import Data.MonoTraversable (Element,MonoTraversable(..),MonoFoldable(..))
import Data.NonNull 
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Combinator
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Traversal
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Prism
import qualified Data.Functor.Rep as F
import qualified Data.List as L
import qualified Data.List.NonEmpty as NNL
import qualified Data.Profunctor.Rep.Foldl1 as M
import qualified Data.Profunctor.Rep.Foldl as L
import Control.Exception (Exception (..), SomeException (..), SomeAsyncException (..))
import qualified Control.Exception as Ex

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

-- | Obtain an 'Ixfold0' directly.
--
-- @since 0.0.3
ixfold0 :: (s -> Maybe (k, a)) -> Ixfold0 k s a
ixfold0 g = ixtraversalVl0 (\point f s -> maybe (point s) (uncurry f) $ g s) . coercer
{-# INLINE ixfold0 #-}

-- | TODO: Document
--
afold0 :: ((a -> Maybe r) -> s -> Maybe r) -> AFold0 r s a
afold0 f = afold $ (Alt #.) #. f .# (getAlt #.) 
{-# INLINE afold0 #-}

infix 3 `failing`

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
-- Fold
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

-- | Obtain a mono 'Fold' directly.
--
-- >>> "foobar" ^.. ofold_ tail
-- "oobar"
--
-- @since 0.0.3
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

-- | TODO: Document
--
-- @since 0.0.3
aixfold :: ((k -> a -> r) -> s -> r) -> AIxtraversal (Const r) k s t a b
aixfold f = afold $ \iar s -> f (curry iar) $ snd s
{-# INLINE aixfold #-}

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
-- @since 0.0.3
ofolding :: MonoTraversable s => (Element s -> a) -> Fold s a
ofolding f = foldVl otraverse . coercer . lmap f
{-# INLINE ofolding #-}

-- | Obtain a 'Fold' from a Van Laarhoven 'Fold'.
--
foldVl :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> Fold s a
foldVl f = coercer . traversalVl f . coercer
{-# INLINE foldVl #-}

-- | Obtain a 'Ixfold' from a Van Laarhoven 'Fold'.
--
-- @since 0.0.3
ixfoldVl :: (forall f. Applicative f => (k -> a -> f b) -> s -> f t) -> Ixfold k s a
ixfoldVl f = coercer . ixtraversalVl f . coercer
{-# INLINE ixfoldVl #-}

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
-- 'fold1_' f ≡ 'to' f . 'foldVl1' 'traverse1_'
-- 'fold1_' f ≡ 'coercer' . 'lmap' f . 'lift' 'traverse1_'
-- @
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- This can be useful to represent operations from @Data.List.NonEmpty@ and elsewhere into a 'Fold1'.
--
fold1_ :: Foldable1 f => (s -> f a) -> Fold1 s a
fold1_ f = coercer . lmap f . foldVl1 traverse1_
{-# INLINE fold1_ #-}

-- | Obtain a 'Fold1' from a 'Traversable1' functor.
--
-- @
-- 'folding1' f ≡ 'traversed1' . 'to' f
-- 'folding1' f ≡ 'foldVl1' 'traverse1' . 'to' f
-- @
--
folding1 :: Traversable1 f => (s -> a) -> Fold1 (f s) a
folding1 f = foldVl1 traverse1 . coercer . lmap f
{-# INLINE folding1 #-}

-- | Obtain a 'Fold1' from a Van Laarhoven 'Fold1'.
--
-- See 'Data.Profunctor.Optic.Property'.
--
foldVl1 :: (forall f. Apply f => (a -> f b) -> s -> f t) -> Fold1 s a
foldVl1 f = coercer . represent f . coercer
{-# INLINE foldVl1 #-}

-- | Obtain a 'Ixfold' from a Van Laarhoven 'Fold'.
--
-- @since 0.0.3
ixfoldVl1 :: (forall f. Apply f => (k -> a -> f b) -> s -> f t) -> Ixfold1 k s a
ixfoldVl1 f = coercer . ixtraversalVl1 f . coercer
{-# INLINE ixfoldVl1 #-}

-- | TODO: Document
--
-- > 'cofolding1' f = 'cofoldVl1' 'cotraverse1' . 'from' f
--
cofolding1 :: Distributive1 g => (b -> t) -> Cofold1 (g t) b
cofolding1 f = cofoldVl1 cotraverse1 . coercel . rmap f
{-# INLINE cofolding1 #-}

-- | Obtain a 'Cofold1' from a Van Laarhoven 'Cofold1'.
--
cofoldVl1 :: (forall f. Coapply f => (f a -> b) -> f s -> t) -> Cofold1 t b
cofoldVl1 f = coercel . cotraversalVl1 f . coercel
{-# INLINE cofoldVl1 #-}

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
filtered p = traversalVl0 (\point f a -> if p a then f a else point a) . coercer
{-# INLINE filtered #-}

-- | Obtain a 'Fold' from a 'Traversable' functor.
--
folded :: Traversable f => Fold (f a) a
folded = folding id
{-# INLINE folded #-}

-- | TODO: Document
--
-- > 'cofoldVl' 'cotraverse' . 'from' f
--
cofolded :: Distributive g => Cofold (g b) b
cofolded = cofolding id
{-# INLINE cofolded #-}

-- | Obtain a 'Fold' from a 'MonoTraversable' functor.
--
-- @since 0.0.3
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
-- @since 0.0.3
ofolded_ :: MonoFoldable a => Fold a (Element a)
ofolded_ = ofold_ id
{-# INLINE ofolded_ #-}

-- | Obtain an 'Ixfold' from a 'F.Representable' functor.
--
-- @since 0.0.3
ixfoldedRep :: F.Representable f => Traversable f => Ixfold (F.Rep f) (f a) a
ixfoldedRep = ixfoldVl F.itraverseRep
{-# INLINE ixfoldedRep #-}

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
-- @since 0.0.3
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
-- @since 0.0.3
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
--  in folds acata fromListF $ [1..5]
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
-- Operators
---------------------------------------------------------------------

-- | TODO: Document
--
folds0 :: AFold0 r s a -> (a -> Maybe r) -> s -> Maybe r
folds0 o = (getAlt #.) #. folds o .# (Alt #.)
{-# INLINE folds0 #-}

infix 8 ^?

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

-- | Map an optic to a monoid and combine the results.
--
-- @
-- 'Data.Foldable.foldMap' = 'folds' 'folded_'
-- @
--
-- >>> folds bitraversed (\x -> [x, x + 1]) (1,3)
-- [1,2,3,4]
-- >>> folds bitraversed id (["foo"], ["bar", "baz"])
-- ["foo","bar","baz"]
--
folds :: ATraversal (Const r) s t a b -> (a -> r) -> s -> r
folds o = (getConst #.) #. traverses o .# (Const #.)
{-# INLINE folds #-}

-- | TODO: Document
--
-- >>> cofolds (from succ) (*2) 3
-- 7
--
-- Compare 'Data.Profunctor.Optic.View.reviews'.
--
cofolds :: ACotraversal (Const r) s t a b -> (r -> b) -> r -> t
cofolds o = (.# Const) #. cotraverses o .# (.# getConst) 
{-# INLINE cofolds #-}

-- | TODO: Document
--
foldsa :: Applicative f => AFold (f a) s a -> s -> f a
foldsa = flip folds pure
{-# INLINE foldsa #-} 

-- | TODO: Document
--
cofoldsa :: Coapplicative f => ACofold (f b) t b -> f b -> t
cofoldsa = flip cofolds copure
{-# INLINE cofoldsa #-} 

infix 8 ^..

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

-- | Collect the fock of an optic into a list.
--
-- @
-- 'lists' 'folded_' = 'Data.Foldable.toList'
-- @
--
lists :: AFold (Endo [a]) s a -> s -> [a]
lists o = foldsr o (:) []
{-# INLINE lists #-}

-- | Extract a 'NonEmpty' of the fock of an optic.
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
-- @
-- 'Data.Foldable.traverse_' ≡ 'traverses_' 'folded'
-- @
--
-- >>> traverses_ bitraversed putStrLn ("hello","world")
-- hello
-- world
--
traverses_ :: Applicative f => AFold (Endo (f ())) s a -> (a -> f r) -> s -> f ()
traverses_ p f = foldsr p (\a fu -> void (f a) *> fu) (pure ())
{-# INLINE traverses_ #-}

---------------------------------------------------------------------
-- Indexed operators
---------------------------------------------------------------------

-- | TODO: Document 
--
-- @since 0.0.3
folds0WithKey :: Monoid k => AIxfold0 r k s a -> (k -> a -> Maybe r) -> s -> Maybe r
folds0WithKey o f = curry ((getAlt #.) #. folds o .# (Alt #.) $ uncurry f) mempty
{-# INLINE folds0WithKey #-}

-- | TODO: Document 
--
-- @since 0.0.3
previewWithKey :: Monoid k => AIxfold0 (k , a) k s a -> s -> Maybe (k , a)
previewWithKey o = previewsWithKey o (,)
{-# INLINE previewWithKey #-}

-- | TODO: Document 
--
-- @since 0.0.3
previewsWithKey :: Monoid k => AIxfold0 r k s a -> (k -> a -> r) -> s -> Maybe r
previewsWithKey o f = folds0WithKey o (\k -> Just . f k)
{-# INLINE previewsWithKey #-}

-- | Map an indexed optic to a monoid and combine the results.
--
-- @since 0.0.3
foldsWithKey :: Monoid k => AIxfold r k s a -> (k -> a -> r) -> s -> r
foldsWithKey o f = curry (folds o $ uncurry f) mempty
{-# INLINE foldsWithKey #-}

-- | TODO: Document 
--
-- @since 0.0.3
cofoldsWithKey :: Monoid k => ACxfold r k t b -> (k -> r -> b) -> r -> t
cofoldsWithKey o f = flip (cofolds o $ flip f) mempty
{-# INLINE cofoldsWithKey #-}

-- | Collect the fock of an indexed optic into a list of index-value pairs.
--
-- @
-- 'lists' l ≡ 'map' 'snd' '.' 'listsWithKey' l
-- @
--
-- >>> listsWithKey (ix (Sum 1) traversed) ["foo","bar"]
-- [(Sum {getSum = 0},"foo"),(Sum {getSum = 1},"bar")]
--
-- @since 0.0.3
listsWithKey :: Monoid k => AIxfold (Endo [(k, a)]) k s a -> s -> [(k, a)]
listsWithKey o = foldsrWithKey o (\k a -> ((k,a):)) []
{-# INLINE listsWithKey #-}

infix 8 ^%%

-- | Infix version of 'listsWithKey'.
--
-- @since 0.0.3
(^%%) :: Monoid k => s -> AIxfold (Endo [(k, a)]) k s a -> [(k, a)]
(^%%) = flip listsWithKey
{-# INLINE (^%%) #-}

-- | Indexed right fold over an indexed optic.
--
-- @
-- 'foldsr' o ≡ 'foldsrWithKey' o '.' 'const'
-- 'foldrWithKey' f ≡ 'foldsrWithKey' 'ixfolded' f
-- @
--
-- @since 0.0.3
foldsrWithKey :: Monoid k => AIxfold (Endo r) k s a -> (k -> a -> r -> r) -> r -> s -> r
foldsrWithKey o f r = (`appEndo` r) . foldsWithKey o (\j -> Endo . f j)
{-# INLINE foldsrWithKey #-}

-- | Left fold over an indexed optic.
--
-- @
-- 'foldsl' o ≡ 'foldslWithKey' o '.' 'const'
-- 'foldlWithKey' f ≡ 'foldslWithKey' 'ixfolded' f
-- @
--
-- @since 0.0.3
foldslWithKey :: Monoid k => AIxfold ((Endo-Dual) r) k s a -> (k -> r -> a -> r) -> r -> s -> r
foldslWithKey o f r = (`appEndo` r) . getDual . foldsWithKey o (\k -> Dual . Endo . flip (f k))
{-# INLINE foldslWithKey #-}

-- | Strict right fold over an indexed optic.
--
-- @
-- 'foldsr'' o ≡ 'foldsrWithKey'' o '.' 'const'
-- 'foldrWithKey'' f ≡ 'foldsrWithKey'' 'ixfolded' f
-- @
--
-- @since 0.0.3
foldsrWithKey' :: Monoid k => AIxfold ((Endo-Dual) (Endo r)) k s a -> (k -> a -> r -> r) -> r -> s -> r
foldsrWithKey' o f r s = foldslWithKey o f' (Endo id) s `appEndo` r where f' k (Endo acc) x = Endo $ \ z -> acc $! f k x z
{-# INLINE foldsrWithKey' #-}

-- | Strict left fold over an indexed optic.
--
-- @
-- 'foldsl'' o ≡ 'foldslWithKey'' o '.' 'const'
-- 'foldlWithKey'' f ≡ 'foldslWithKey'' 'ixfolded' f
-- @
--
-- @since 0.0.3
foldslWithKey' :: Monoid k => AIxfold (Endo (Endo r)) k s a -> (k -> r -> a -> r) -> r -> s -> r
foldslWithKey' o f r s = foldsrWithKey o f' (Endo id) s `appEndo` r where f' k x (Endo acc) = Endo $ \z -> acc $! f k z x
{-# INLINE foldslWithKey' #-}

-- | Monadic right fold over an indexed optic.
--
-- @
-- 'foldsrM' ≡ 'ixfoldrM' '.' 'const'
-- @
--
-- @since 0.0.3
foldsrMWithKey :: Monoid k => Monad m => AIxfold ((Endo-Dual) (EndoM m r)) k s a -> (k -> a -> r -> m r) -> r -> s -> m r
foldsrMWithKey o f r xs = foldslWithKey o f' mempty xs `appEndoM` r where f' k e a = e <> EndoM (f k a)
{-# INLINE foldsrMWithKey #-}

-- | Monadic left fold over an indexed optic.
--
-- @
-- 'foldslM' ≡ 'foldslMWithKey' '.' 'const'
-- @
--
-- @since 0.0.3
foldslMWithKey :: Monoid k => Monad m => AIxfold (Endo (EndoM m r)) k s a -> (k -> r -> a -> m r) -> r -> s -> m r
foldslMWithKey o f r xs = foldsrWithKey o f' mempty xs `appEndoM` r where f' k a e = e <> EndoM (flip (f k) a)
{-# INLINE foldslMWithKey #-}

-- | Applicative fold over an indexed optic.
--
-- @
-- 'traversesWithKey_' 'ixfolded' ≡ 'traverseWithKey_'
-- @
--
-- @since 0.0.3
traversesWithKey_ :: Monoid k => Applicative f => AIxfold (Endo (f ())) k s a -> (k -> a -> f r) -> s -> f ()
traversesWithKey_ p f = foldsrWithKey p (\k a fu -> void (f k a) *> fu) (pure ())
{-# INLINE traversesWithKey_ #-}

---------------------------------------------------------------------
-- Exception handling
---------------------------------------------------------------------

is :: AFold0 a s a -> s -> Bool
is k s = isJust (preview k s)

isnt k s = not $ is k s

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
  if is async e then throwM e else run $ maybe (throwM e) (return . Left) (preview o e)
{-# INLINE tries #-}

-- | A variant of 'tries' that returns synchronous exceptions.
--
tries_ :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> m a -> m (Maybe a)
tries_ o a = preview right' `liftM` tries o a
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
  if is async e then throwM e else run $ maybe (throwM e) ea (preview o e)
{-# INLINE catches #-}

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
{-# INLINE handles #-}

-- | Flipped variant of 'catches_'.
--
-- >>> handles_ (only Overflow) (return "caught") $ throwIO Overflow
-- "caught"
--
handles_ :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> m a -> m a -> m a
handles_ o = flip $ catches_ o
{-# INLINE handles_ #-}

throwM :: MonadIO m => Exception e => e -> m a
throwM = liftIO . Ex.throwIO
{-# INLINE throwM #-}

---------------------------------------------------------------------
-- EndoM
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
