module Data.Profunctor.Optic (
  module Export
) where


import Data.Profunctor.Optic.Fold             as Export
import Data.Profunctor.Optic.Fold.Affine      as Export
--import Data.Profunctor.Optic.Fold.NonEmpty   as Export
import Data.Profunctor.Optic.Unfold           as Export
import Data.Profunctor.Optic.Grate            as Export
import Data.Profunctor.Optic.Iso              as Export
import Data.Profunctor.Optic.Lens             as Export
import Data.Profunctor.Optic.Traversal        as Export
import Data.Profunctor.Optic.Traversal.Affine as Export
import Data.Profunctor.Optic.Setter           as Export
import Data.Profunctor.Optic.Prism            as Export
import Data.Profunctor.Optic.Review           as Export
import Data.Profunctor.Optic.Cotraversal      as Export
import Data.Profunctor.Optic.Type             as Export
import Data.Profunctor.Optic.View           as Export

import Data.Profunctor.Optic.Prelude
import Linear.V2
import Linear.V3
import Linear.V4
import Control.Monad.State

{-
extractPair :: (forall f g. (Functor f, Functor g) => (g a -> f b) -> g s -> f t) -> (s -> a, b -> t)
extractPair l = (getConst . (l (Const . runIdentity)) . Identity, runIdentity . (l (Identity . getConst)) . Const)

extractPair' :: (((s -> a) -> Store (s -> a) b b) -> (s -> s) -> Store (s -> a) b t) -> (s -> a, b -> t)
extractPair' l = (f, g) where Store g f = l (Store id) id

-}
newtype Zipping a b = Zipping { runZipping :: a -> a -> b }

instance Functor (Zipping a) where fmap f (Zipping p) = Zipping $ \x y-> f (p x y)

instance Applicative (Zipping a) where
  pure x = Zipping $ \_ _ -> x
  liftA2 f (Zipping p) (Zipping q) = Zipping (\x y -> f (p x y) (q x y))

instance Profunctor Zipping where
  dimap f g (Zipping p) = Zipping (\x y -> g (p (f x) (f y)))

instance Closed Zipping where
  closed (Zipping p) = Zipping (\f g x -> p (f x) (g x))

instance Choice Zipping where
  right' (Zipping p) = Zipping (\x y -> p <$> x <*> y)

instance Strong Zipping where
  first' (Zipping p) = Zipping (\(x, c) (y, _) -> (p x y, c))

zipWithOf' :: Optic Zipping a2 b2 a1 b1 -> (a1 -> a1 -> b1) -> a2 -> a2 -> b2
zipWithOf' = between runZipping Zipping

type SLens s t a b = forall p. Strong p => (forall x. Applicative (p x)) => Optic p s t a b
type SLens' s a = SLens s s a a


v4 :: SLens (V4 a) (V4 b) a b
v4 p = dimap (\(V4 x y z w) -> (x, (y, (z, w)))) (\(x, (y, (z, w))) -> V4 x y z w) (p @@@ p @@@ p @@@ p)

--v2 :: Semigroupal p => Optic p (V2 a) (V2 b) a b



v2s :: SLens (V2 a) (V2 b) a b
v2s p = dimap (\(V2 x y) -> (x, y)) (\(x, y) -> V2 x y) (p @@@ p)

v2 :: Grate' (V2 a) a
v2 = represented

v2d :: Grate' (V2 a) a
v2d = distributed

v2t :: Traversal' (V2 a) a
v2t = traversed

as = V2 (Left ())     (Right (1,2))
bs = V2 (Right (3,4)) (Right (5,6))

res0 = review (v2d . _R) 1
--V2 (Right 1) (Right 1)

res1 = zipWithOf' (v2d . _R . _1) (+) as bs
--V2 (Left ()) (Right (6,2))

--f :: (MonadState a m, Num a) => a -> m a
f x = state (\s -> (x + s, s +1))

res2 = evalState (traverseOf v2t f (V2 5 7)) 1
--V2 6 9







--foo x = zipWithOf' (x . pright . pfirst) (,) as bs

{-λ> review (v2 . pright) 1 :: V2 (Either Bool (V2 Int))
λ> toListOf (v2 . v2) (V2 (V2 1 2) (V2 3 4))
[1,2,3,4]

-- >>>  contents skipLast (1,2,3)
-- [1,2]
skipLast :: SLens (a, a, c) (b, b, c) a b
skipLast p = dimap group ungroup (pfirst (p *** p)) where
  group  (x, y, z) = ((x, y), z)
  ungroup ((x, y), z) = (x, y, z)

skipLast' :: SLens' (V3 a) a
skipLast' p = dimap group ungroup (pfirst (p *** p)) where
  group  (V3 x y z) = ((x, y), z)
  ungroup ((x, y), z) = V3 x y z
-}


