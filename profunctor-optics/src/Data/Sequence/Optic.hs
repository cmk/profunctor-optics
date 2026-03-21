{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Sequence.Optic (
    slicedTo
  , slicedFrom
  , sliced
  , viewedl
  , viewedr
) where

import Data.Profunctor.Optic
import Data.Profunctor.Optic.Import
import Data.Sequence (Seq, ViewL(..), ViewR(..), viewl, viewr)
import qualified Data.Sequence as Seq
import Prelude

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> import Data.Sequence (fromList)
-- >>> import Data.Profunctor.Optic
-- >>> import qualified Data.Sequence as Seq

-- | Traverse the first @n@ elements of a 'Seq'
--
-- >>> fromList [1,2,3,4,5] ^.. slicedTo 2
-- [1,2]
--
-- >>> fromList [1,2,3,4,5] & slicedTo 2 %~ (*10)
-- fromList [10,20,3,4,5]
--
-- >>> fromList [1,2,4,5,6] & slicedTo 10 .~ 0
-- fromList [0,0,0,0,0]
slicedTo :: Int -> Traversal' (Seq a) a
slicedTo n = traversalVl $ \f m -> case Seq.splitAt n m of
  (l, r) -> (Seq.>< r) <$> traverse f l
{-# INLINE slicedTo #-}

-- | Traverse all but the first @n@ elements of a 'Seq'
--
-- >>> fromList [1,2,3,4,5] ^.. slicedFrom 2
-- [3,4,5]
--
-- >>> fromList [1,2,3,4,5] & slicedFrom 2 %~ (*10)
-- fromList [1,2,30,40,50]
--
-- >>> fromList [1,2,3,4,5] & slicedFrom 10 .~ 0
-- fromList [1,2,3,4,5]
slicedFrom :: Int -> Traversal' (Seq a) a
slicedFrom n = traversalVl $ \f m -> case Seq.splitAt n m of
  (l, r) -> (l Seq.><) <$> traverse f r
{-# INLINE slicedFrom #-}

-- | Traverse all the elements numbered from @i@ to @j@ of a 'Seq'
--
-- >>> fromList [1,2,3,4,5] & sliced 1 3 %~ (*10)
-- fromList [1,20,30,4,5]
--
-- >>> fromList [1,2,3,4,5] ^.. sliced 1 3
-- [2,3]
--
-- >>> fromList [1,2,3,4,5] & sliced 1 3 .~ 0
-- fromList [1,0,0,4,5]
sliced :: Int -> Int -> Traversal' (Seq a) a
sliced i j = traversalVl $ \f s -> case Seq.splitAt i s of
  (l, mr) -> case Seq.splitAt (j-i) mr of
    (m, r) -> traverse f m <&> \n -> l Seq.>< n Seq.>< r
{-# INLINE sliced #-}


-- | A 'Seq' is isomorphic to a 'ViewL'
--
-- @'viewl' m ≡ m 'Data.Profunctor.Optic.Operator.^.' 'viewedl'@
--
-- >>> Seq.fromList [1,2,3] ^. viewedl
-- 1 :< fromList [2,3]
--
-- >>> Seq.empty ^. viewedl
-- EmptyL
--
-- >>> EmptyL ^. re viewedl
-- fromList []
--
-- >>> review viewedl $ 1 Seq.:< fromList [2,3]
-- fromList [1,2,3]
--
viewedl :: Iso (Seq a) (Seq b) (ViewL a) (ViewL b)
viewedl = iso viewl $ \xs -> case xs of
  EmptyL      -> mempty
  a Seq.:< as -> a Seq.<| as
{-# INLINE viewedl #-}

-- | A 'Seq' is isomorphic to a 'ViewR'
--
-- @'viewr' m ≡ m 'Data.Profunctor.Optic.Operator.^.' 'viewedr'@
--
-- >>> Seq.fromList [1,2,3] ^. viewedr
-- fromList [1,2] :> 3
--
-- >>> Seq.empty ^. viewedr
-- EmptyR
--
-- >>> EmptyR ^. re viewedr
-- fromList []
--
-- >>> review viewedr $ fromList [1,2] Seq.:> 3
-- fromList [1,2,3]
--
viewedr :: Iso (Seq a) (Seq b) (ViewR a) (ViewR b)
viewedr = iso viewr $ \xs -> case xs of
  EmptyR      -> mempty
  as Seq.:> a -> as Seq.|> a
{-# INLINE viewedr #-}
