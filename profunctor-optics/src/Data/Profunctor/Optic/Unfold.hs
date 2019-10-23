module Data.Profunctor.Optic.Unfold where

import Data.Functor.Foldable (Corecursive, Base, unfold)
import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Review
import Data.Profunctor.Optic.Type
import qualified Data.List as L (unfoldr)

---------------------------------------------------------------------
-- 'Unfold'
---------------------------------------------------------------------

unfolding :: Distributive g => (b -> t) -> Unfold (g t) b
unfolding f = lower cotraverse . unto f --coercel' . rmap f

corecursing :: Corecursive t => AUnfold b t (Base t b)
corecursing = unfoldLike unfold

unfoldLike :: ((r -> b) -> r -> t) -> AUnfold r t b
unfoldLike = between (ucostar getConst) (dcostar Const)

unfoldr :: AUnfold b [t] (Maybe (t, b))
unfoldr = unfoldLike L.unfoldr

cloneUnfold :: AReview t b -> Unfold t b
cloneUnfold = unto . review --coercel' . rmap . review

cofolded :: (Foldable f, Monoid b) => (a -> b) -> Costar f a b
cofolded f = Costar (foldMap f)

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

unfoldMapOf :: AUnfold r t b -> (r -> b) -> r -> t
unfoldMapOf = between (dcostar Const) (ucostar getConst)

unfoldOf :: AReview t b -> b -> t
unfoldOf = flip unfoldMapOf id
