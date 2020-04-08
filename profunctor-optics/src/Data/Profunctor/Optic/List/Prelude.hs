{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.List.Prelude where
{-
  , mconcats
  , sconcats
  , minimizes
  , maximizes
  , minimizesDef
  , maximizesDef
  , minimizesBy 
  , maximizesBy
  , minimizesByDef
  , maximizesByDef
  
  , anyOf, allOf, noneOf
  , andOf, orOf
  -- , productOf, sumOf
  --, meanOf, varianceOf, stdOf
  , nubOf, eqNubOf, lengthOf
  , elemOf, notElemOf
  , nullOf, notNullOf
  , firstOf, firstl1Of, lastOf, lastl1Of
  , maximumOf, maximuml1Of, minimumOf, minimuml1Of
  , maximumByOf, minimumByOf
  , findOf, lookupOf
  , elemIndexOf, elemIndicesOf
  , findIndexOf, findIndicesOf
) where
-}

import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Combinator
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Types
import Data.Profunctor.Rep.Fold (Fold(..))
import Data.Profunctor.Rep.Fold1 (Fold1(..))
import Data.Semigroup
import Data.Semigroup.Foldable as F1
import Data.Word
import qualified Control.Category as C
import qualified Control.Foldl.ByteString as B
import qualified Control.Foldl.Text as T
import qualified Data.Foldable as F
import qualified Data.List as L
import qualified Data.Profunctor.Optic.Fold as FO
import qualified Data.Profunctor.Optic.Types as T (Fold, Fold1)
import qualified Data.Profunctor.Rep.Fold as M
import qualified Data.Profunctor.Rep.Fold1 as M

{-
anyOf :: Foldable f => AFoldl s t a Bool -> (a -> Bool) -> f s -> t
anyOf o f s = flip M.fold s . o $ M.any f
 
allOf :: Foldable f => AFoldl s t a Bool -> (a -> Bool) -> f s -> t
allOf o f s = flip M.fold s . o $ M.any f

andOf :: Foldable f => AFoldl s t Bool Bool -> f s -> t
andOf o s = flip M.fold s . o $ M.and

orOf :: Foldable f => AFoldl s t Bool Bool -> f s -> t
orOf o s = flip M.fold s . o $ M.or

-- | TODO: Document
--
nubOf :: Foldable f => Ord a => AFoldl s t a [a] -> f s -> t
nubOf o s = flip M.fold s . o $ M.nub
{-# INLINE nubOf #-}

-- | TODO: Document
--
eqNubOf :: Foldable f => Eq a => AFoldl s t a [a] -> f s -> t
eqNubOf o s = flip M.fold s . o $ M.eqNub
{-# INLINE eqNubOf #-}

-- | Return /True/ if the container has an element equal to /a/,
--
elemOf :: Foldable f => Eq a => AFoldl s t a Bool -> a -> f s -> t
elemOf o a s = flip M.fold s . o $ M.elem a
{-# INLINE elemOf #-}

-- | Return /True/ if the container has no element equal to /a/,
--
notElemOf :: Foldable f => Eq a => AFoldl s t a Bool -> a -> f s -> t
notElemOf o a s = flip M.fold s . o $ M.notElem a
{-# INLINE notElemOf #-}

nullOf o s = flip M.fold1 s . o $ M.null

headOf :: Foldable f => AFoldl s t a (Maybe a) -> f s -> t
headOf o s = flip M.fold s . o $ M.head
{-# INLINE headOf #-}

head1Of :: Foldable1 f => AFoldl1 s t a a -> f s -> t
head1Of o s = flip M.fold1 s . o $ M.head1
{-# INLINE head1Of #-}

lastOf :: Foldable f => AFoldl s t a (Maybe a) -> f s -> t
lastOf o s = flip M.fold s . o $ M.last
{-# INLINE lastOf #-}

last1Of :: Foldable1 f => AFoldl1 s t a a -> f s -> t
last1Of o s = flip M.fold1 s . o $ M.last1
{-# INLINE last1Of #-}

-- | TODO: Document
--
-- >>> findOf (prefiltered isUpper) isLetter "foo"
-- Nothing
-- >>> findOf (prefiltered isUpper) isLetter "foO"
-- Just 'O'
-- >>> findOf cotraversed1 isLetter ["foo", "bar", "bip"]
-- [Just 'f',Just 'o',Just 'o']
-- >>> findOf cotraversed1 isLetter ["1o2", "b3r", "bip"]
-- [Just 'b',Just 'o',Just 'r']
-- >>> findOf cotraversed1 isLetter ["12o", "3ar", "45p"]
-- [Nothing,Just 'a',Just 'o']
--
-- See also 'Data.Profunctor.Optic.Fold.findOf'.
--
findOf :: Foldable f => AFoldl s t a (Maybe a) -> (a -> Bool) -> f s -> t
findOf o f s = flip M.fold s . o $ M.find f
{-# INLINE findOf #-}

-- | TODO: Document
--
-- >>> indexOf cotraversed1 1 ["foo", "bar", "bip"]
-- [Just 'b',Just 'a',Just 'r']
-- >>> indexOf cotraversed1 1 ["foo", "ba", "bip"]
-- [Just 'b',Just 'a',Just 'p']
-- >>> indexOf cotraversed1 1 ["foo", "ba", "bi"]
-- [Just 'b',Just 'a',Nothing]
--
indexOf :: Foldable f => AFoldl s t a (Maybe a) -> Int -> f s -> t
indexOf o i s = flip M.fold s . o $ M.index i
{-# INLINE indexOf #-}

-- | TODO: Document
--
elemIndexOf :: Foldable f => Eq a => AFoldl s t a (Maybe Int) -> a -> f s -> t
elemIndexOf o a s = flip M.fold s . o $ M.elemIndex a
{-# INLINE elemIndexOf #-}

-- | TODO: Document
--
findIndexOf :: Foldable f => AFoldl s t a (Maybe Int) -> (a -> Bool) -> f s -> t
findIndexOf o f s = flip M.fold s . o $ M.findIndex f
{-# INLINE findIndexOf #-}

-- | TODO: Document
--
lookupOf :: Foldable f => Eq a => AFoldl s t (a, b) (Maybe b) -> a -> f s -> t
lookupOf o a s = flip M.fold s . o $ M.lookup a
{-# INLINE lookupOf #-}

-}
---------------------------------------------------------------------
-- Prelude
---------------------------------------------------------------------

-- | TODO: Document
--
-- >>> mconcats cotraversed1 id id [["foo","bar"],["baz","bip"]]
-- ["foobaz","barbip"]
-- >>> mconcats cotraversed1 Sum getSum [[1,2,3],[4,5,6,7]]
-- [5,7,9]
--
-- @since 0.0.3
mconcats :: Foldable f => Monoid m => AFoldl s t a b -> (a -> m) -> (m -> b) -> f s -> t
mconcats o f g s = flip L.foldl s . o $ L.mconcat f g
{-# INLINE mconcats #-}

-- | TODO: Document
--
-- @since 0.0.3
sconcats :: Foldable1 f => Semigroup m => AFoldl1 s t a b -> (a -> m) -> (m -> b) -> f s -> t
sconcats o f g s = flip L1.foldl1 s . o $ L1.sconcat f g
{-# INLINE sconcats #-}

-- | TODO: Document
--
-- @since 0.0.3
minimizes :: Foldable1 f => Ord a => AFoldl1 s t a a -> f s -> t 
minimizes o = buildl1 o $ L1.minimum
{-# INLINE minimizes #-}

-- | TODO: Document
--
-- @since 0.0.3
maximizes :: Foldable1 f => Ord a => AFoldl1 s t a a -> f s -> t 
maximizes o = buildl1 o $ L1.maximum
{-# INLINE maximizes #-}

-- | TODO: Document
--
-- >>> minimizesDef (maximizedDef (0,[]) second) "" [(0,"zero"),(1,"one"),(2,"two")]
-- (2,"one")
--
-- @since 0.0.3
minimizesDef :: Foldable f => Ord a => AFoldl s t a a -> a -> f s -> t 
minimizesDef o a = buildl o $ L.minimumDef a
{-# INLINE minimizesDef #-}

-- | TODO: Document
--
-- >>> maximizesDef (maximizedDef (0,[]) second) "" [(0,"zero"),(1,"one"),(2,"two")]
-- (2,"zero")
--
-- @since 0.0.3
maximizesDef :: Foldable f => Ord a => AFoldl s t a a -> a -> f s -> t 
maximizesDef o a = buildl o $ L.maximumDef a
{-# INLINE maximizesDef #-}

-- | TODO: Document
--
-- @since 0.0.3
minimizesBy :: Foldable1 f => AFoldl1 s t a a -> (a -> a -> Ordering) -> f s -> t 
minimizesBy o f = buildl1 o $ L1.minimumBy f
{-# INLINE minimizesBy #-}

-- | TODO: Document
--
-- @since 0.0.3
maximizesBy :: Foldable1 f => AFoldl1 s t a a -> (a -> a -> Ordering) -> f s -> t 
maximizesBy o f = buildl1 o $ L1.maximumBy f
{-# INLINE maximizesBy #-}

-- | TODO: Document
--
-- @since 0.0.3
minimizesByDef :: Foldable f => AFoldl s t a a -> (a -> a -> Ordering) -> a -> f s -> t 
minimizesByDef o f a = buildl o $ L.minimumByDef f a
{-# INLINE minimizesByDef #-}

-- | TODO: Document
--
-- @since 0.0.3
maximizesByDef :: Foldable f => AFoldl s t a a -> (a -> a -> Ordering) -> a -> f s -> t 
maximizesByDef o f a = buildl o $ L.maximumByDef f a
{-# INLINE maximizesByDef #-}


