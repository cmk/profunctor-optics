{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Map.Optic (
    fromIxfold
  , at
  , iat
  , values
  , imapped
  , ifiltered
  , itraversed
  , ifolded
  , altered
  , ialtered
  , alteredF
  , ialteredF
  , adjusted
  , updated
  , updateLooked
  , lookedMin
  , lookedMax
  , lookedLT
  , lookedLE
  , lookedGE
  , lookedGT
  , validated
    -- * Structural (via pattern functor)
  , depth
  , sizes
  , rebalanced
) where


import Data.Container.Pattern
import Data.Functor.Fixed (Mu)
import Data.Functor.Foldable (fold, unfold, refold)
import Data.Profunctor.Optic
import qualified Data.Map.Lazy as Map

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> import Data.Char
-- >>> import Data.Map as Map
-- >>> import Data.Profunctor.Optic

-- | /O(1)/. Create a 'Map.Map' from an 'Ixfold'.
--
fromIxfold :: Ord k => Monoid k => AIxfold (Map.Map k a) k s a -> s -> Map.Map k a
fromIxfold o = ixfolds o Map.singleton
{-# INLINE fromIxfold #-}

-- | /O(log n)/. Affine traversal into the value at a key of a 'Map.Map'.
--
-- >>> Map.fromList [(1,"world")] ^. at 0
-- ""
-- >>> Map.fromList [(1,"world")] ^. at 1
-- "world"
-- >>> Map.fromList [(67,'C')] & at 99 ..~ toLower
-- fromList [(67,'C')]
-- >>> Map.fromList [(67,'C')] & at 67 ..~ toLower
-- fromList [(67,'c')]
--
at :: Ord k => k -> Traversal0' (Map.Map k a) a
at k = traversal0' (Map.lookup k) (flip $ Map.insert k)
{-# INLINE at #-}

-- | /O(log n)/. Indexed affine traversal into the value at a key of a 'Map.Map'.
--
-- >>> Map.fromList [(1,"world")] ^% iat 0 
-- (Nothing,"")
-- >>> Map.fromList [(1,"world")] ^% iat 1
-- (Just 1,"world")
-- >>> Map.fromList [(67,'C')] & iat 99 %~ chr
-- fromList [(67,'C')]
-- >>> Map.fromList [(67,'C')] & iat 67 %%~ const toLower
-- fromList [(67,'c')]
-- >>> iat 2 %%~ (\i x -> if odd i then not x else x) $ Map.fromList [(1,True),(2,False)]
-- fromList [(1,True),(2,False)]
--
iat :: Ord k => k -> Ixtraversal0' k (Map.Map k a) a
iat k = ixtraversal0' (\s -> (k,) <$> Map.lookup k s) (flip $ Map.insert k)
{-# INLINE iat #-}

-- | /O(n)/. 'Fold' over the values of a 'Map.Map', in ascending key order.
--
-- Subject to list fusion.
--
-- >>> toListOf values $ Map.fromList [(1,3),(2,4)]
-- [3,4]
--
values :: Fold (Map.Map k a) a
values = fold_ Map.toAscList . second'
{-# INLINE values #-}

-- | /O(n)/. 'Ixsetter' over the values of a 'Map.Map'.
--
-- >>> iover imapped (+) $ Map.fromList [(1,3),(2,4)]
-- fromList [(1,4),(2,6)]
--
-- See also 'Data.Map.mapWithKey'.
--
imapped :: Ixsetter k (Map.Map k a) (Map.Map k b) a b
imapped = ixsetter Map.mapWithKey
{-# INLINE imapped #-}

-- | /O(n)/. 'Ixsetter' filtering the values of a 'Map.Map'.
--
ifiltered :: Ixsetter k (Map.Map k a) (Map.Map k a) a Bool
ifiltered = ixsetter Map.filterWithKey
{-# INLINE ifiltered #-}

-- | /O(n)/. 'Ixtraversal' over the values of a 'Map.Map'.
--
itraversed :: Ord k => Ixtraversal k (Map.Map k a) (Map.Map k b) a b
itraversed = ixtraversalVl Map.traverseWithKey
{-# INLINE itraversed #-}

-- | /O(n)/. 'Ixfold' over the values of a 'Map.Map'.
--
-- @
-- fromIxfold ifolded ≡ id
-- @
--
-- >>> ilists ifolded $ Map.fromList [(1,3),(2,4)]
-- [(1,3),(2,4)]
-- >>> ilists ifolded $ Map.empty 
-- []
--
ifolded :: Ixfold k (Map.Map k a) a
ifolded = ixfoldVl Map.traverseWithKey
{-# INLINE ifolded #-}

-- | /O(log n)/. Alter the value at a specific key.
--
-- 'altered' can be used to insert, delete, or update a value in a 'Map'.
--
-- >>> let f _ = Nothing
-- >>> over (altered 7) f $ Map.fromList [(5,"a"), (3,"b")]
-- fromList [(3,"b"),(5,"a")]
-- >>> over (altered 5) f $ Map.fromList [(5,"a"), (3,"b")]
-- fromList [(3,"b")]
--
-- >>> let f _ = Just "c"
-- >>> over (altered 7) f $ Map.fromList [(5,"a"), (3,"b")]
-- fromList [(3,"b"),(5,"a"),(7,"c")]
-- >>> over (altered 5) f $ Map.fromList [(5,"a"), (3,"b")]
-- fromList [(3,"b"),(5,"c")]
--
-- See also 'Data.Map.alter'.
--
altered :: Ord k => k -> Setter' (Map.Map k a) (Maybe a)
altered k = setter $ \ab -> Map.alter ab k
{-# INLINE altered #-}

-- | /O(log n)/. Alter the value at a specific key.
--
-- 'ialtered' can be used to insert, delete, or update a value in a 'Map'.
--
-- >>> let f _ _ = Nothing
-- >>> iover (ialtered 7) f $ Map.fromList [(5,"a"), (3,"b")]
-- fromList [(3,"b"),(5,"a")]
-- >>> iover (ialtered 5) f $ Map.fromList [(5,"a"), (3,"b")]
-- fromList [(3,"b")]
--
-- >>> let f i _ = if i == 7 then Just "c" else Nothing
-- >>> iover (ialtered 7) f $ Map.fromList [(5,"a"), (3,"b")]
-- fromList [(3,"b"),(5,"a"),(7,"c")]
-- >>> iover (ialtered 5) f $ Map.fromList [(5,"a"), (3,"b")]
-- fromList [(3,"b")]
--
-- See also 'Data.Map.alter'.
--
ialtered :: Ord k => k -> Ixsetter' k (Map.Map k a) (Maybe a)
ialtered k = ixsetter $ \kab -> Map.alter (kab k) k
{-# INLINE ialtered #-}

-- | /O(log n)/. Lens into /Maybe/ of a value at a key of a 'Map.Map'.
--
alteredF :: Ord k => k -> Lens' (Map.Map k a) (Maybe a)
alteredF k = lensVl $ flip Map.alterF k
{-# INLINE alteredF #-}

-- | /O(log n)/. Alter the value at a specific key.
--
-- >>> let f _ _ = Just "c"
-- >>> iover (ialteredF 7) f $ Map.fromList [(5,"a"), (3,"b")]
-- fromList [(3,"b"),(5,"a"),(7,"c")]
-- >>> iover (ialteredF 5) f $ Map.fromList [(5,"a"), (3,"b")]
-- fromList [(3,"b"),(5,"c")]
-- >>> Map.fromList [(5,"a"), (3,"b")] ^%% ialteredF 5 
-- [(5,Just "a")]
--
-- See also 'Data.Map.alterF'.
--
ialteredF :: Ord k => k -> Ixlens' k (Map.Map k a) (Maybe a)
ialteredF k = ixlensVl $ \kab -> Map.alterF (kab k) k
{-# INLINE ialteredF #-}

-- | /O(log n)/. Adjust a value at a specific key.
--
-- >>> let f key x = (show key) ++ ":new " ++ x
-- >>> iover (adjusted 5) f $ Map.fromList [(5,"a"), (3,"b")]
-- fromList [(3,"b"),(5,"5:new a")]
-- >>> iover (adjusted 7) f $ Map.fromList [(5,"a"), (3,"b")]
-- fromList [(3,"b"),(5,"a")]
-- >>> iover (adjusted 7) f Map.empty
-- fromList []
--
-- See also 'Data.Map.adjustWithKey'.
--
adjusted :: Ord k => k -> Ixsetter' k (Map.Map k a) a
adjusted k = ixsetter $ \kab -> Map.adjustWithKey kab k
{-# INLINE adjusted #-}

-- | /O(log n)/. Update a value at a specific key.
--
-- If (@f k x@) is 'Nothing', the element is deleted. If it is (@'Just' y@), 
-- the key @k@ is bound to the new value @y@.
--
-- >>> let f k x = if x == "a" then Just ((show k) ++ ":new a") else Nothing
-- >>> iover (updated 5) f $ Map.fromList [(5,"a"), (3,"b")]
-- fromList [(3,"b"),(5,"5:new a")]
-- >>> iover (updated 7) f $ Map.fromList [(5,"a"), (3,"b")]
-- fromList [(3,"b"),(5,"a")]
-- >>> iover (updated 3) f $ Map.fromList [(5,"a"), (3,"b")]
-- fromList [(5,"a")]
--
-- See also 'Data.Map.updateWithKey'.
--
updated :: Ord k => k -> Ixsetter k (Map.Map k a) (Map.Map k a) a (Maybe a)
updated k = ixsetter $ \kab -> Map.updateWithKey kab k
{-# INLINE updated #-}

-- | /O(log n)/. Lookup and update a value at a specific key.
--
-- Returns the changed value, if it is updated. Returns the original key value
-- if the map entry is deleted.
--
-- >>> let f k x = if x == "a" then Just ((show k) ++ ":new a") else Nothing
-- >>> iover (updateLooked 5) f $ Map.fromList [(5,"a"), (3,"b")]
-- (Just "5:new a",fromList [(3,"b"),(5,"5:new a")])
-- >>> iover (updateLooked 7) f $ Map.fromList [(5,"a"), (3,"b")]
-- (Nothing,fromList [(3,"b"),(5,"a")])
-- >>> iover (updateLooked 3) f $ Map.fromList [(5,"a"), (3,"b")]
-- (Just "b",fromList [(5,"a")])
--
-- See also 'Data.Map.updateLookupWithKey'.
--
updateLooked :: Ord k => k -> Ixsetter k (Map.Map k a) (Maybe a, Map.Map k a) a (Maybe a)
updateLooked k = ixsetter $ \kab -> Map.updateLookupWithKey kab k
{-# INLINE updateLooked #-}

-- | /O(log n)/. 'Ixoption' into the value at the minimal key of a 'Map.Map'.
--
lookedMin :: Ixfold0 k (Map.Map k a) a
lookedMin = ixfold0 Map.lookupMin
{-# INLINE lookedMin #-}

-- | /O(log n)/. 'Ixoption' into the value at the maximal key of a 'Map.Map'.
--
lookedMax :: Ixfold0 k (Map.Map k a) a
lookedMax = ixfold0 Map.lookupMax
{-# INLINE lookedMax #-}

-- | /O(log n)/. Indexed affine traversal into the value at the largest key smaller than the given one.
--
-- >>> ipreview (lookedLT 3) (Map.fromList [(3,'a'), (5,'b')])
-- Nothing
-- >>> ipreview (lookedLT 4) (Map.fromList [(3,'a'), (5,'b')])
-- Just (3,'a')
--
lookedLT :: Ord k => k -> Ixtraversal0' k (Map.Map k a) a
lookedLT k = ixtraversal0' (Map.lookupLT k) (flip $ Map.insert k)
{-# INLINE lookedLT #-}

-- | /O(log n)/. Indexed affine traversal into the value at the largest key smaller than or equal to the given one.
--
-- >>> ipreview (lookedLE 3) $ Map.fromList [(3,'a'), (5,'b')]
-- Just (3,'a')
--
lookedLE :: Ord k => k -> Ixtraversal0' k (Map.Map k a) a
lookedLE k = ixtraversal0' (Map.lookupLE k) (flip $ Map.insert k)
{-# INLINE lookedLE #-}

-- | /O(log n)/. Indexed affine traversal into the value at the largest key greater than or equal to the given one.
--
-- >>> ipreview (lookedGE 3) $ Map.fromList [(3,'a'), (5,'b')]
-- Just (3,'a')
-- >>> ipreview (lookedGE 4) $ Map.fromList [(3,'a'), (5,'b')]
-- Just (5,'b')
-- >>> ipreview (lookedGE 6) $ Map.fromList [(3,'a'), (5,'b')]
-- Nothing
--
lookedGE :: Ord k => k -> Ixtraversal0' k (Map.Map k a) a
lookedGE k = ixtraversal0' (Map.lookupGE k) (flip $ Map.insert k)
{-# INLINE lookedGE #-}

-- | /O(log n)/. Indexed affine traversal into the value at the largest key greater than the given one.
-- 
-- >>> ipreview (lookedGT 4) $ Map.fromList [(3,'a'), (5,'b')]
-- Just (5,'b')
-- >>> ipreview (lookedGT 5) $ Map.fromList [(3,'a'), (5,'b')]
-- Nothing
--
lookedGT :: Ord k => k -> Ixtraversal0' k (Map.Map k a) a
lookedGT k = ixtraversal0' (Map.lookupGT k) (flip $ Map.insert k)
{-# INLINE lookedGT #-}

-- | /O(n)/. Test if the internal map structure is valid.
--
-- >>> is validated (Map.fromAscList [(3,"b"), (5,"a")])
-- True
-- >>> isnt validated (Map.fromAscList [(5,"a"), (3,"b")])
-- True
--
-- See also 'Data.Map.valid'.
--
validated :: Ord k => Fold0 (Map.Map k a) (Map.Map k a)
validated = filtered Map.valid
{-# INLINE validated #-}

---------------------------------------------------------------------
-- Structural (via pattern functor)
---------------------------------------------------------------------

-- | Compute the depth of a 'Map.Map' using its tree structure.
--
-- This operates on the internal BST representation via 'MapF',
-- something not possible with the standard Map API.
--
-- >>> depth (Map.fromList [(1,'a'),(2,'b'),(3,'c'),(4,'d'),(5,'e')])
-- 3
--
depth :: Map.Map k v -> Int
depth = fold alg . toMapF
  where
    alg MapTip = 0
    alg (MapBin _ _ _ l r) = 1 + max l r

-- | Collect the sizes stored at each internal node.
--
-- Useful for inspecting or validating the balance invariant.
--
-- >>> sizes (Map.fromList [(1,'a'),(2,'b'),(3,'c')])
-- [3,1,1]
--
sizes :: Map.Map k v -> [Int]
sizes = fold alg . toMapF
  where
    alg MapTip = []
    alg (MapBin sz _ _ l r) = sz : l ++ r

-- | Rebuild a 'Map.Map' from its pattern functor representation.
--
-- @rebalanced = fromMapF . toMapF@
--
-- Since 'Map.Bin' preserves the original sizes, this is the
-- identity. Useful as a building block for transformations
-- that modify the tree structure then reconstruct.
--
rebalanced :: Map.Map k v -> Map.Map k v
rebalanced = fromMapF . toMapF
