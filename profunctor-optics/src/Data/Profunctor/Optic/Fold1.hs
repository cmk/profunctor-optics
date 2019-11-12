module Data.Profunctor.Optic.Fold.NonEmpty where

import Data.DList.NonEmpty (NonEmptyDList)
import Data.Functor.Apply (Apply(..))
import Data.List.NonEmpty (NonEmpty(..))
import Data.Profunctor.Optic.View (view, to)
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Type
import Data.Semigroup
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import qualified Data.DList.NonEmpty as NEL

---------------------------------------------------------------------
-- 'Fold1'
---------------------------------------------------------------------

{-
A 'Fold1' can interpret 'a' in a semigroup so long as 's' can also be interpreted that way.
Fold1 laws:
fold1_complete :: Fold1 s a -> Bool
fold1_complete o = tripping o $ folding1 (toNonEmptyOf o)

-}









---------------------------------------------------------------------
-- 'Fold1Rep'
---------------------------------------------------------------------

-- | TODO: Document
--
afold1 :: Semigroup r => ((a -> r) -> s -> r) -> AFold1 r s a
afold1 = between (Star . (Const .)) ((getConst .) . runStar)

-- | TODO: Document
--
afold1' :: Foldable f => AFold1 r (f a) a
afold1' = afold1 foldMap



---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------


-- | Helper for 'Optics.Fold.traverseOf_' and the like for better
-- efficiency than the foldr-based version.
--
-- Note that the argument @a@ of the result should not be used.
newtype Traversed f a = Traversed (f a)

runTraversed :: Functor f => Traversed f a -> f ()
runTraversed (Traversed fa) = () <$ fa
{-# INLINE runTraversed #-}

instance Applicative f => Semigroup (Traversed f a) where
  Traversed ma <> Traversed mb = Traversed (ma *> mb)
  {-# INLINE (<>) #-}

instance Applicative f => Monoid (Traversed f a) where
  mempty = Traversed (pure (error "Traversed: value used"))
  mappend = (<>)
  {-# INLINE mempty #-}
  {-# INLINE mappend #-}

--traverseOf_ :: (Is k A_Fold, Applicative f) => Optic' k is s a -> (a -> f r) -> s -> f ()
traverseOf_ o = \f -> runTraversed . foldMapOf o (Traversed #. f)
{-# INLINE traverseOf_ #-}

--summing :: Optic' p s a -> Optic' p s a -> Fold s a
summing :: Applicative f => AFold (Traversed f a) s a -> AFold (Traversed f a) s a -> Fold s a
summing a b = folding $ \f s -> traverseOf_ a f s *> traverseOf_ b f s





  , foldsl1
  , foldsl1'

-- | A variant of 'foldlOf' that has no base case and thus may only be applied to lenses and structures such
-- that the 'Lens' views at least one element of the structure.
--
-- >>> foldsl1 each (+) (1,2,3,4)
-- 10
--
-- @
-- 'foldsl1' l f ≡ 'Prelude.foldl1' f '.' 'toListOf' l
-- 'Data.Foldable.foldl1' ≡ 'foldsl1' 'folded'
-- @
--
-- @
-- 'foldsl1' :: 'Getter' s a     -> (a -> a -> a) -> s -> a
-- 'foldsl1' :: 'Fold' s a       -> (a -> a -> a) -> s -> a
-- 'foldsl1' :: 'Iso'' s a       -> (a -> a -> a) -> s -> a
-- 'foldsl1' :: 'Lens'' s a      -> (a -> a -> a) -> s -> a
-- 'foldsl1' :: 'Traversal'' s a -> (a -> a -> a) -> s -> a
-- @
--foldsl1 :: HasCallStack => Getting (Dual (Endo (Maybe a))) s a -> (a -> a -> a) -> s -> a
foldsl1 l def f xs = fromMaybe (error "foldsl1: empty structure") (foldsl l mf Nothing xs) where
  mf mx y = Just $ case mx of
    Nothing -> y
    Just x  -> f x y
{-# INLINE foldsl1 #-}

-- | A variant of 'foldlOf'' that has no base case and thus may only be applied
-- to folds and structures such that the fold views at least one element of
-- the structure.
--
-- @
-- 'foldsl1'' l f ≡ 'Data.List.foldl1'' f '.' 'toListOf' l
-- @
--
-- @
-- 'foldsl1'' :: 'Getter' s a     -> (a -> a -> a) -> s -> a
-- 'foldsl1'' :: 'Fold' s a       -> (a -> a -> a) -> s -> a
-- 'foldsl1'' :: 'Iso'' s a       -> (a -> a -> a) -> s -> a
-- 'foldsl1'' :: 'Lens'' s a      -> (a -> a -> a) -> s -> a
-- 'foldsl1'' :: 'Traversal'' s a -> (a -> a -> a) -> s -> a
-- @
--foldsl1' :: HasCallStack => Getting (Endo (Endo (Maybe a))) s a -> (a -> a -> a) -> s -> a
foldsl1' l f xs = fromMaybe (error "foldsl1': empty structure") (foldsl' l mf Nothing xs) where
  mf Nothing y = Just $! y
  mf (Just x) y = Just $! f x y
{-# INLINE foldsl1' #-}


{-
-- | Find the join of a sublattice. 
--
joins1 :: Lattice a => AFold1 (Endo (Endo a)) s a -> s -> a
joins1 o = undefined

-- | Find the meet of a sublattice.
--
meet1 :: Lattice a => AFold1 (Endo (Endo a)) s a -> s -> a
meet1 o = undefined

-}

