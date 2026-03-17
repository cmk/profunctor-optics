{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}

-- | Pattern functors for @containers@ types.
--
-- These mirror the internal structure of 'Data.Map.Map',
-- 'Data.IntMap.IntMap', 'Data.Set.Set', and 'Data.IntSet.IntSet',
-- enabling recursion schemes from @scheme-extensions@ to operate
-- on their tree structure.
--
-- @
-- Map k v   ≅  Mu (MapF k v)
-- IntMap a  ≅  Mu (IntMapF a)
-- Set a     ≅  Mu (SetF a)
-- IntSet    ≅  Mu IntSetF
-- @
--
-- Use 'toMapF'\/'fromMapF' etc. to convert between the container
-- types and their fixed-point representations.
module Data.Container.Pattern (
    -- * Map
    MapF (..),
    toMapF,
    fromMapF,

    -- * IntMap
    IntMapF (..),
    toIntMapF,
    fromIntMapF,

    -- * Set
    SetF (..),
    toSetF,
    fromSetF,

    -- * IntSet
    IntSetF (..),
    toIntSetF,
    fromIntSetF,
) where

import Data.Functor.Fixed (Mu)
import Data.Functor.Foldable (fold, unfold)

import qualified Data.Map.Internal as Map
import qualified Data.IntMap.Internal as IntMap
import qualified Data.Set.Internal as Set
import qualified Data.IntSet.Internal as IntSet

---------------------------------------------------------------------
-- Map
---------------------------------------------------------------------

-- | Pattern functor for 'Data.Map.Map'.
data MapF k v r
    = MapTip
    | MapBin {-# UNPACK #-} !Int !k v r r
    deriving (Functor, Foldable, Traversable, Show)

-- | Unfold a 'Map.Map' into @Mu (MapF k v)@.
toMapF :: Map.Map k v -> Mu (MapF k v)
toMapF = unfold coalg
  where
    coalg Map.Tip = MapTip
    coalg (Map.Bin sz k v l r) = MapBin sz k v l r

-- | Fold a @Mu (MapF k v)@ back into 'Map.Map'.
fromMapF :: Mu (MapF k v) -> Map.Map k v
fromMapF = fold alg
  where
    alg MapTip = Map.Tip
    alg (MapBin sz k v l r) = Map.Bin sz k v l r

---------------------------------------------------------------------
-- IntMap
---------------------------------------------------------------------

-- | Pattern functor for 'Data.IntMap.IntMap'.
data IntMapF a r
    = IntMapNil
    | IntMapTip {-# UNPACK #-} !IntMap.Key a
    | IntMapBin {-# UNPACK #-} !IntMap.Prefix {-# UNPACK #-} !IntMap.Mask r r
    deriving (Functor, Foldable, Traversable, Show)

-- | Unfold an 'IntMap.IntMap' into @Mu (IntMapF a)@.
toIntMapF :: IntMap.IntMap a -> Mu (IntMapF a)
toIntMapF = unfold coalg
  where
    coalg IntMap.Nil = IntMapNil
    coalg (IntMap.Tip k v) = IntMapTip k v
    coalg (IntMap.Bin p m l r) = IntMapBin p m l r

-- | Fold a @Mu (IntMapF a)@ back into 'IntMap.IntMap'.
fromIntMapF :: Mu (IntMapF a) -> IntMap.IntMap a
fromIntMapF = fold alg
  where
    alg IntMapNil = IntMap.Nil
    alg (IntMapTip k v) = IntMap.Tip k v
    alg (IntMapBin p m l r) = IntMap.Bin p m l r

---------------------------------------------------------------------
-- Set
---------------------------------------------------------------------

-- | Pattern functor for 'Data.Set.Set'.
data SetF a r
    = SetTip
    | SetBin {-# UNPACK #-} !Int !a r r
    deriving (Functor, Foldable, Traversable, Show)

-- | Unfold a 'Set.Set' into @Mu (SetF a)@.
toSetF :: Set.Set a -> Mu (SetF a)
toSetF = unfold coalg
  where
    coalg Set.Tip = SetTip
    coalg (Set.Bin sz a l r) = SetBin sz a l r

-- | Fold a @Mu (SetF a)@ back into 'Set.Set'.
fromSetF :: Mu (SetF a) -> Set.Set a
fromSetF = fold alg
  where
    alg SetTip = Set.Tip
    alg (SetBin sz a l r) = Set.Bin sz a l r

---------------------------------------------------------------------
-- IntSet
---------------------------------------------------------------------

-- | Pattern functor for 'Data.IntSet.IntSet'.
data IntSetF r
    = IntSetNil
    | IntSetTip {-# UNPACK #-} !IntSet.Prefix {-# UNPACK #-} !IntSet.BitMap
    | IntSetBin {-# UNPACK #-} !IntSet.Prefix {-# UNPACK #-} !IntSet.Mask r r
    deriving (Functor, Foldable, Traversable, Show)

-- | Unfold an 'IntSet.IntSet' into @Mu IntSetF@.
toIntSetF :: IntSet.IntSet -> Mu IntSetF
toIntSetF = unfold coalg
  where
    coalg IntSet.Nil = IntSetNil
    coalg (IntSet.Tip p bm) = IntSetTip p bm
    coalg (IntSet.Bin p m l r) = IntSetBin p m l r

-- | Fold a @Mu IntSetF@ back into 'IntSet.IntSet'.
fromIntSetF :: Mu IntSetF -> IntSet.IntSet
fromIntSetF = fold alg
  where
    alg IntSetNil = IntSet.Nil
    alg (IntSetTip p bm) = IntSet.Tip p bm
    alg (IntSetBin p m l r) = IntSet.Bin p m l r
