{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
-- | Left and right carriers are characterized by their representation
-- functors ('Rep' and 'Corep'). 'Iso' sits at the top where both
-- are trivial ('Identity'). 'Adjoint' sits at the bottom where they
-- form a full adjunction (@'Corep' p ⊣ 'Rep' p@). A left-indexed
-- ('Ix') optic threads an index through the left adjoint functor
-- @(,) k@, while a right-indexed ('Cx') optic threads a coindex
-- through the right adjoint functor @(->) k@.
module Data.Map.NonEmpty.Optic (
    fromIxfold1
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
  , foundMin
  , foundMax
  , lookedLT
  , lookedLE
  , lookedGE
  , lookedGT
  , validated
) where 

import Data.Profunctor.Optic
import qualified Data.Map as Unsafe
import qualified Data.Map.NonEmpty as Map

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> import Data.Char
-- >>> import Data.List.NonEmpty
-- >>> import Data.Map.NonEmpty as Map
-- >>> import Data.Profunctor.Optic

-- | /O(1)/. Create a 'Map.NEMap' from an 'Ixfold1'.
--
fromIxfold1 :: Ord k => Monoid k => AIxfold (Unsafe.Map k a) k s a -> s -> Unsafe.Map k a
fromIxfold1 o = ixfoldMapOf o Unsafe.singleton
{-# INLINE fromIxfold1 #-}

-- | /O(log n)/. Affine traversal into the value at a key of a 'Map.NEMap'.
--
-- >>> Map.fromList ((0,"hello") :| [(1,"world")]) ^. at 0
-- "hello"
-- >>> Map.fromList ((0,"hello") :| [(1,"world")]) ^. at 1
-- "world"
-- >>> Map.fromList ((67,'C') :| []) & at 99 ..~ toLower
-- fromList ((67,'C') :| [])
-- >>> Map.fromList ((67,'C') :| []) & at 67 ..~ toLower
-- fromList ((67,'c') :| [])
--
at :: Ord k => k -> Traversal0' (Map.NEMap k a) a
at k = traversal0' (Map.lookup k) (flip $ Map.insert k)
{-# INLINE at #-}

-- | /O(log n)/. Indexed affine traversal into the value at a key of a 'Map.NEMap'.
--
-- >>> Map.fromList ((0,"hello") :| [(1,"world")]) ^% iat (0 :: Int)
-- (Just 0,"hello")
-- >>> Map.fromList ((1,"world") :| []) ^% iat (1 :: Int)
-- (Just 1,"world")
-- >>> Map.fromList ((67,'C') :| []) & iat 99 %~ chr
-- fromList ((67,'C') :| [])
-- >>> Map.fromList ((67,'C') :| []) & iat 67 %%~ const toLower
-- fromList ((67,'c') :| [])
-- >>> iat 2 %%~ (\i x -> if odd i then not x else x) $ Map.fromList ((1,True) :| [(2,False)])
-- fromList ((1,True) :| [(2,False)])
--
iat :: Ord k => k -> Ixtraversal0' k (Map.NEMap k a) a
iat k = ixtraversal0' (\s -> (k,) <$> Map.lookup k s) (flip $ Map.insert k)
{-# INLINE iat #-}

-- | /O(n)/. 'Fold1' over the values of a 'Map.NEMap', in ascending key order.
--
-- Subject to list fusion.
--
-- >>> nelists values (Map.fromList ((5,'a') :| [(3,'b')]))
-- 'b' :| "a"
--
values :: Fold1 (Map.NEMap k a) a
values = fold1_ Map.toAscList . second'
{-# INLINE values #-}

-- | /O(n)/. 'Ixsetter' over the values of a 'Map.NEMap'.
--
imapped :: Semigroup k => Ixsetter k (Map.NEMap k a) (Map.NEMap k b) a b
imapped = ixsetter $ \f k -> Map.mapWithKey (\i -> f (k <> i))
{-# INLINE imapped #-}

-- | /O(n)/. 'Ixsetter' filtering the values of a 'Map.NEMap'.
--
ifiltered :: Semigroup k => Ixsetter k (Map.NEMap k a) (Unsafe.Map k a) a Bool
ifiltered = ixsetter $ \f k -> Map.filterWithKey (\i -> f (k <> i))
{-# INLINE ifiltered #-}

-- | /O(n)/. 'Ixtraversal1' over the values of a 'Map.NEMap'.
--
itraversed :: (Ord k, Semigroup k) => Ixtraversal1 k (Map.NEMap k a) (Map.NEMap k b) a b
itraversed = ixtraversalVl1 $ \f k -> Map.traverseWithKey1 (\i -> f (k <> i))
{-# INLINE itraversed #-}

-- | /O(n)/. 'Ixfold1' over the values of a 'Map.NEMap'.
--
ifolded :: Semigroup k => Ixfold k (Map.NEMap k a) a
ifolded = ixfoldVl $ \f k -> Map.traverseWithKey (\i -> f (k <> i))
{-# INLINE ifolded #-}

-- | /O(log n)/. Alter the value at a specific key.
--
-- 'altered' can be used to insert, delete, or update a value in a 'Map'.
--
-- >>> let f _ = Nothing
-- >>> over (altered 7) f $ Map.fromList ((5,'a') :| [(3,'b')])
-- fromList [(3,'b'),(5,'a')] 
-- >>> over (altered 5) f $ Map.fromList ((5,'a') :| [(3,'b')])
-- fromList [(3,'b')]
--
-- >>> let f _ = Just "c"
-- >>> over (altered 7) f $ Map.fromList ((5,"a") :| [(3,"b")])
-- fromList [(3,"b"),(5,"a"),(7,"c")]
-- >>> over (altered 5) f $ Map.fromList ((5,"a") :| [(3,"b")])
-- fromList [(3,"b"),(5,"c")]
--
-- See also 'Data.Map.NonEmpty.alter'.
--
altered :: Ord k => k -> Setter (Map.NEMap k a) (Unsafe.Map k a) (Maybe a) (Maybe a)
altered k = setter $ \ab -> Map.alter ab k

-- | /O(log n)/. Alter the value at a specific key.
--
-- 'ialtered' can be used to insert, delete, or update a value in a 'Map'.
--
-- >>> let f _ _ = Nothing
-- >>> iover (ialtered 7) f $ Map.fromList ((5,"a") :| [(3,"b")])
-- fromList [(3,"b"),(5,"a")]
-- >>> iover (ialtered 5) f $ Map.fromList ((5,"a") :| [(3,"b")])
-- fromList [(3,"b")]
--
-- >>> let f i _ = if i == 7 then Just "c" else Nothing
-- >>> iover (ialtered 7) f $ Map.fromList ((5,"a") :| [(3,"b")])
-- fromList [(3,"b"),(5,"a"),(7,"c")]
-- >>> iover (ialtered 5) f $ Map.fromList ((5,"a") :| [(3,"b")])
-- fromList [(3,"b")]
--
-- See also 'Data.Map.NonEmpty.alter'.
--
ialtered :: Ord k => Ixsetter k (Map.NEMap k a) (Unsafe.Map k a) (Maybe a) (Maybe a)
ialtered = ixsetter $ \f k -> Map.alter (f k) k

-- | /O(log n)/. Lens into /Maybe/ of a value at a key of a 'Map.NEMap'.
--
alteredF :: Ord k => k -> Lens (Map.NEMap k a) (Unsafe.Map k a) (Maybe a) (Maybe a)
alteredF k = lensVl $ flip Map.alterF k
{-# INLINE alteredF #-}

-- | /O(log n)/. Alter the value at a specific key.
--
-- >>> let f _ _ = Just "c"
-- >>> iover ialteredF f $ Map.fromList ((5,"a") :| [(3,"b")])
-- fromList [(3,"b"),(5,"c")]
--
-- See also 'Data.Map.NonEmpty.alterF'.
--
ialteredF :: Ord k => Ixlens k (Map.NEMap k a) (Unsafe.Map k a) (Maybe a) (Maybe a)
ialteredF = ixlensVl $ \f k -> Map.alterF (f k) k

-- | /O(log n)/. Adjust a value at a specific key.
--
-- >>> let f key x = (show key) ++ ":new " ++ x
-- >>> iover (adjusted 5) f $ Map.fromList ((5,"a") :| [(3,"b")])
-- fromList ((3,"b") :| [(5,"5:new a")])
-- >>> iover (adjusted 7) f $ Map.fromList ((5,"a") :| [(3,"b")])
-- fromList ((3,"b") :| [(5,"a")])
--
-- See also 'Data.Map.NonEmpty.adjustWithKey'.
--
adjusted :: Ord k => Ixsetter k (Map.NEMap k a) (Map.NEMap k a) a a
adjusted = ixsetter $ \f k -> Map.adjust (f k) k

-- | /O(log n)/. Update a value at a specific key.
--
-- If (@f k x@) is 'Nothing', the element is deleted. If it is (@'Just' y@), 
-- the key @k@ is bound to the new value @y@.
--
-- >>> let f k x = if x == "a" then Just ((show k) ++ ":new a") else Nothing
-- >>> iover (updated 5) f $ Map.fromList ((5,"a") :| [(3,"b")])
-- fromList [(3,"b"),(5,"5:new a")]
-- >>> iover (updated 7) f $ Map.fromList ((5,"a") :| [(3,"b")])
-- fromList [(3,"b"),(5,"a")]
-- >>> iover (updated 3) f $ Map.fromList ((5,"a") :| [(3,"b")])
-- fromList [(5,"a")]
--
-- See also 'Data.Map.NonEmpty.updateWithKey'.
--
updated :: Ord k => Ixsetter k (Map.NEMap k a) (Unsafe.Map k a) a (Maybe a)
updated = ixsetter $ \f k -> Map.updateWithKey (\_ -> f k) k

-- | /O(log n)/. Lookup and update a value at a specific key.
--
-- Returns the changed value, if it is updated. Returns the original key value
-- if the map entry is deleted.
--
-- >>> let f k x = if x == "a" then Just ((show k) ++ ":new a") else Nothing
-- >>> iover (updateLooked 5) f $ Map.fromList ((5,"a") :| [(3,"b")])
-- (Just "5:new a",fromList [(3,"b"),(5,"5:new a")])
-- >>> iover (updateLooked 7) f $ Map.fromList ((5,"a") :| [(3,"b")])
-- (Nothing,fromList [(3,"b"),(5,"a")])
-- >>> iover (updateLooked 3) f $ Map.fromList ((5,"a") :| [(3,"b")])
-- (Just "b",fromList [(5,"a")])
--
-- See also 'Data.Map.NonEmpty.updateLookupWithKey'.
--
updateLooked :: Ord k => Ixsetter k (Map.NEMap k a) (Maybe a, Unsafe.Map k a) a (Maybe a)
updateLooked = ixsetter $ \f k -> Map.updateLookupWithKey (\_ -> f k) k

-- | /O(1)/. 'Ixview' into the value at the minimal key of a 'Map.NEMap'.
--
-- This function is asymptotically more efficient than 'lookedMin' if you have a non-empty map.
--
foundMin :: Ixview k (Map.NEMap k a) a
foundMin = ixto Map.findMin
{-# INLINE foundMin #-}

-- | /O(1)/. 'Ixview' into the value at the maximal key of a 'Map.NEMap'.
--
-- This function is asymptotically more efficient than 'lookedMax' if you have a non-empty map.
--
foundMax :: Ixview k (Map.NEMap k a) a
foundMax = ixto Map.findMax
{-# INLINE foundMax #-}

-- | /O(log n)/. Indexed affine traversal into the value at the largest key smaller than the given one.
--
-- >>> ipreview (lookedLT 3) $ Map.fromList ((3,'a') :| [(5,'b')])
-- Nothing
-- >>> ipreview (lookedLT 4) $ Map.fromList ((3,'a') :| [(5,'b')])
-- Just (3,'a')
--
lookedLT :: Ord k => k -> Ixtraversal0' k (Map.NEMap k a) a
lookedLT k = ixtraversal0' (Map.lookupLT k) (flip $ Map.insert k) 
{-# INLINE lookedLT #-}

-- | /O(log n)/. Indexed affine traversal into the value at the largest key smaller than or equal to the given one.
--
-- >>> ipreview (lookedLE 3) $ Map.fromList ((3,'a') :| [(5,'b')])
-- Just (3,'a')
--
lookedLE :: Ord k => k -> Ixtraversal0' k (Map.NEMap k a) a
lookedLE k = ixtraversal0' (Map.lookupLE k) (flip $ Map.insert k)
{-# INLINE lookedLE #-}

-- | /O(log n)/. Indexed affine traversal into the value at the largest key greater than or equal to the given one.
--
-- >>> ipreview (lookedGE 3) $ Map.fromList ((3,'a') :| [(5,'b')]) 
-- Just (3,'a')
-- >>> ipreview (lookedGE 4) $ Map.fromList ((3,'a') :| [(5,'b')])
-- Just (5,'b')
-- >>> ipreview (lookedGE 6) $ Map.fromList ((3,'a') :| [(5,'b')])
-- Nothing
--
lookedGE :: Ord k => k -> Ixtraversal0' k (Map.NEMap k a) a
lookedGE k = ixtraversal0' (Map.lookupGE k) (flip $ Map.insert k)
{-# INLINE lookedGE #-}

-- | /O(log n)/. Indexed affine traversal into the value at the largest key greater than the given one.
-- 
-- >>> ipreview (lookedGT 4) $ Map.fromList ((3,'a') :| [(5,'b')])
-- Just (5,'b')
-- >>> ipreview (lookedGT 5) $ Map.fromList ((3,'a') :| [(5,'b')])
-- Nothing
--
lookedGT :: Ord k => k -> Ixtraversal0' k (Map.NEMap k a) a
lookedGT k = ixtraversal0' (Map.lookupGT k) (flip $ Map.insert k)
{-# INLINE lookedGT #-}

-- | /O(n)/. Test if the internal map structure is valid.
--
-- >>> is validated $ Map.fromAscList ((3,'a') :| [(5,'b')])
-- True
-- >>> isnt validated $ Map.fromAscList ((5,'a') :| [(3,'b')])
-- True
--
-- See also 'Data.Map.NonEmpty.valid'.
--
validated :: Ord k => Fold0 (Map.NEMap k a) (Map.NEMap k a)
validated = filtered Map.valid
{-# INLINE validated #-}
