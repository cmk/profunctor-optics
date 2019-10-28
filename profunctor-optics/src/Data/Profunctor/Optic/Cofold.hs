module Data.Profunctor.Optic.Cofold where

import Data.Functor.Foldable (Corecursive, Base, unfold)
import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Review
import Data.Profunctor.Optic.Type
import qualified Data.List as L (unfoldr)

---------------------------------------------------------------------
-- 'Cofold'
---------------------------------------------------------------------

unfolding :: Distributive g => (b -> t) -> Cofold (g t) b
unfolding f = lower cotraverse . unto f --coercel' . rmap f

corecursing :: Corecursive t => ACofold b t (Base t b)
corecursing = unfoldLike unfold

unfoldLike :: ((r -> b) -> r -> t) -> ACofold r t b
unfoldLike = between (ucostar getConst) (dcostar Const)

unfoldr :: ACofold b [t] (Maybe (t, b))
unfoldr = unfoldLike L.unfoldr

cloneCofold :: AReview t b -> Cofold t b
cloneCofold = unto . review --coercel' . rmap . review

cofolded :: (Foldable f, Monoid b) => (a -> b) -> Costar f a b
cofolded f = Costar (foldMap f)

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

unfoldMapOf :: ACofold r t b -> (r -> b) -> r -> t
unfoldMapOf = between (dcostar Const) (ucostar getConst)

unfoldOf :: AReview t b -> b -> t
unfoldOf = flip unfoldMapOf id
