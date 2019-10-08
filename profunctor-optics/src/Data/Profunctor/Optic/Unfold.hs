module Data.Profunctor.Optic.Unfold where

import Data.Functor.Foldable (Corecursive, Base, unfold)
import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Review
import Data.Profunctor.Optic.Type 
import qualified Data.List as L (unfoldr)

---------------------------------------------------------------------
-- 'Unfold'
---------------------------------------------------------------------

{-

'Unfold' laws:

unfold_complete :: Fold s a -> Bool
unfold_complete o = tripping o $ unfolding (_ o)
-}

unfolding :: Distributive g => (b -> t) -> Unfold (g t) b
unfolding f = cowander cotraverse . unto f

-- corecursing :: Functor f => UnfoldLike a (Fix f) (f a)
corecursing :: Corecursive t => UnfoldLike b t (Base t b)
corecursing = unfoldLike unfold

unfoldLike :: ((r -> b) -> r -> t) -> UnfoldLike r t b
unfoldLike = between (ucostar getConst) (dcostar Const) 

unfoldr :: UnfoldLike b [t] (Maybe (t, b))
unfoldr = unfoldLike L.unfoldr 

cloneUnfold :: AReview t b -> Unfold t b
cloneUnfold = unto . review

cofolded :: (Foldable f, Monoid b) => (a -> b) -> Costar f a b
cofolded f = Costar (foldMap f)

nfoldLike f = between (ucostar ) (dcostar $ foldMap f) 

---------------------------------------------------------------------
-- Primitive Operators
---------------------------------------------------------------------

unfoldMapOf :: UnfoldLike r t b -> (r -> b) -> r -> t
unfoldMapOf = between (dcostar Const) (ucostar getConst)

unfoldOf :: AReview t b -> b -> t
unfoldOf = flip unfoldMapOf id
