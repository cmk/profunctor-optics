module Data.Profunctor.Optic (
  module Export
) where

import Data.Profunctor.Optic.Fold             as Export
import Data.Profunctor.Optic.Fold0            as Export
--import Data.Profunctor.Optic.Fold1  as Export
import Data.Profunctor.Optic.Cofold           as Export
import Data.Profunctor.Optic.Grate            as Export
import Data.Profunctor.Optic.Iso              as Export
import Data.Profunctor.Optic.Lens             as Export
import Data.Profunctor.Optic.Traversal        as Export
import Data.Profunctor.Optic.Traversal0       as Export
import Data.Profunctor.Optic.Setter           as Export
import Data.Profunctor.Optic.Prism            as Export
import Data.Profunctor.Optic.Cotraversal      as Export
import Data.Profunctor.Optic.Type             as Export
import Data.Profunctor.Optic.View             as Export

import Data.Profunctor.Optic.Prelude

import Control.Monad.State hiding (lift)


import qualified Data.Functor.Rep as F


-- | TODO: Document
--
--aresetter :: ((a -> b) -> s -> t) -> AResetter s t a b
--aresetter sec = between Costar runCostar $ \f -> sec (f . Identity) . runIdentity

env :: F.Representable f => p a b -> Environment p (f a) (f b)
env p = Environment F.tabulate p F.index

-- | TODO: Document
--
lifting :: F.Representable (Rep p) => ((a -> b) -> s -> t) -> RepnLike p s t a b
lifting f = lift $ genMap' f

genMap' :: F.Representable f => ((a -> b) -> s -> t) -> (a -> f b) -> s -> f t
genMap' f afb s = F.tabulate $ \i -> f (flip F.index i . afb) s

closed' :: Corepn (c -> a) (c -> b) a b
closed' = lower cotraverse

--set . re :: Colens s t a b -> s -> b -> a
--reset :: Optic (Re (->) a b) s t a b -> b -> s -> a
--reset o = set o . re


--applied :: Grate a (b -> c) (a , b) c
--appliedl :: Grid (a -> b, a) c b c
--appliedl = puncurry . closed


distributed' :: Distributive f => Corepn (f a) (f b) a b
distributed' = corepresented $ \fab fs -> fmap fab $ distribute fs

-- | TODO: Document
--
cloneRepn :: Optic (Star (Rep p)) s t a b -> RepnLike p s t a b
cloneRepn = between fromStar toStar

-- | TODO: Document
--
cloneCorepn :: Optic (Costar (Corep p)) s t a b -> CorepnLike p s t a b
cloneCorepn = between fromCostar toCostar

represented :: ((a -> Rep p b) -> s -> Rep p t) -> RepnLike p s t a b
represented = between tabulate sieve

corepresented :: ((Corep p a -> b) -> Corep p s -> t) -> CorepnLike p s t a b
corepresented = between cotabulate cosieve
--moore = corepresented $ \fab fs -> fmap fab $ distribute fs

--type AMoore p s t a b = Optic L.Fold s t a b
--type Mealy p s t a b = Optic L.Fold1 s t a b


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


