module Data.Profunctor.Optic.Cofold where

import Data.Foldable (Foldable, foldMap)
import Data.Functor.Foldable (Corecursive, Base)
import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.View
import Data.Profunctor.Optic.Type
import qualified Data.List as L (unfoldr)
import qualified Data.Functor.Foldable as F

---------------------------------------------------------------------
-- 'Cofold'
---------------------------------------------------------------------

cofold :: Distributive g => (b -> t) -> Cofold (g t) b
cofold f = lower cotraverse . unto f --coercel' . rmap f

corecursing :: Corecursive t => ACofold b t (Base t b)
corecursing = acofold F.unfold

acofold :: ((r -> b) -> r -> t) -> ACofold r t b
acofold = between (ucostar getConst) (dcostar Const)

acofold' :: ACofold b [t] (Maybe (t, b))
acofold' = acofold L.unfoldr

cloneCofold :: AReview t b -> Cofold t b
cloneCofold = unto . review

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

unfoldMapOf :: ACofold r t b -> (r -> b) -> r -> t
unfoldMapOf = between (dcostar Const) (ucostar getConst)

unfoldOf :: AReview t b -> b -> t
unfoldOf = flip unfoldMapOf id
