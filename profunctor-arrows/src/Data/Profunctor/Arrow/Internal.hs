{-# LANGUAGE ExistentialQuantification, DefaultSignatures, UndecidableInstances #-}

module Data.Profunctor.Arrow.Internal where

import Data.Functor.Compose (Compose(..))
import Data.Functor.Identity (Identity(..))
import Data.Kind
import Data.Profunctor
import Data.Profunctor.Choice
import Data.Profunctor.Closed
import Data.Profunctor.Extra
import Data.Profunctor.Mapping
import Data.Profunctor.Monad
import Data.Profunctor.Strong
import Data.Profunctor.Traversing
import Data.Profunctor.Unsafe
import Data.Profunctor.Yoneda
import Data.Void

import Prelude


type family Arg  (x :: * -> *) where Arg  (f a)   = a
type family Arg1 (x :: * -> *) where Arg1 (f a b) = a
type family Arg2 (x :: * -> *) where Arg2 (f a b) = b

--Trans m p ~ m f => (Costar f) `Procompose` p `Procompose` (Star f)
data Trans m p a b = forall x y f. m f => Trans (a -> f x) (p x y) (f y -> b)

instance Profunctor (Trans m p) where
  dimap f g (Trans l p r) = Trans (l . f) p (g . r)
  lmap f (Trans l p r) = Trans (l . f) p r
  rmap g (Trans l p r) = Trans l p (g . r)
  g #. Trans l p r = Trans l p (g #. r)
  Trans l p r .# f = Trans (l .# f) p r

instance ProfunctorFunctor (Trans m) where
  promap f (Trans l p r) = Trans l (f p) r


type ChoiceT = Trans WithChoice

type StrongT = Trans WithStrong

type ClosedT = Trans WithClosed

type AffineT = Trans WithAffine

type TraversingT = Trans Traversable

type MappingT = Trans Functor


runMappingT :: Mapping q => p :-> q -> MappingT p a b -> q a b
runMappingT pq (Trans l p r) = dimap l r (map' (pq p))

--prisms

choice_lift :: p a b -> ChoiceT p a b
choice_lift p = Trans Right p rgt'

--see also PastroSum's Choice instance
choice_trans :: ChoiceT p a b -> ChoiceT p (c + a) (c + b)
choice_trans (Trans l p r) = Trans
    (either (Left . Left) (either (Left . Right) Right . l)) p
    (either (either Left (Right . r . Left)) (Right . r . Right))


--lenses

strong_lift :: p a b -> StrongT p a b
strong_lift p = Trans ((,) ()) p snd

-- see also Pastro's Strong instance
strong_trans :: StrongT p a b -> StrongT p (c, a) (c, b)
strong_trans (Trans l p r) = Trans (\(d,s) -> ((d , fst (l s)), snd (l s))) p (\((d,c),b) -> (d,r (c,b)))


--grates

closed_lift :: p a b -> ClosedT p a b
closed_lift p = Trans const p ($ ())

--see also Environment's Closed instance
closed_trans :: ClosedT p a b -> ClosedT p (c -> a) (c -> b)
closed_trans (Trans l p r) = Trans (\f (d , c) -> l (f d) c) p ((r .) . curry)


--affine traversals

affine :: Choice p => Strong p => p a b -> p (Affine c d a) (Affine c d b)
affine = dimap unAffine Affine . right' . second'

affine_lift :: p a b -> AffineT p a b 
affine_lift p = Trans (Affine . Right . ((,) ())) p (either absurd snd . unAffine)

affine_trans :: AffineT p a b -> AffineT p (Affine c d a) (Affine c d b)
affine_trans (Trans l p r) = Trans (u l) p (v r)
  where
    u :: (s -> Affine c d a) -> Affine e f s -> Affine (Either e (f,c)) (f,d) a
    u _ (Affine (Left e))      = Affine $ Left $ Left e
    u l (Affine (Right (f,s))) = Affine $ case unAffine (l s) of
      (Left c)      -> (Left (Right (f,c)))
      (Right (d,a)) -> (Right ((f,d),a))

    v :: (Affine c d b -> t) -> Affine (Either e (f,c)) (f,d) b -> Affine e f t
    v _ (Affine (Left  (Left e)))         = Affine $ Left e
    v r (Affine (Left  (Right (f,c))))    = Affine $ Right (f,r $ Affine $ Left c)
    v r (Affine (Right ((f,d),b)))        = Affine $ Right (f , r . Affine $ Right (d,b))

-- traversals

traversal_lift :: p a b -> TraversingT p a b
traversal_lift p = Trans Identity p runIdentity

--see also TransTraversing's Traversing instance
traversal_trans :: Traversable f => TraversingT p a b -> TraversingT p (f a) (f b)
traversal_trans (Trans l p r) = Trans (Compose . fmap l) p (fmap r . getCompose)


-- setters

setter_lift :: p a b -> MappingT p a b
setter_lift p = Trans Identity p runIdentity

--see also TransMapping's Mapping instance
setter_trans :: Functor f => MappingT p a b -> MappingT p (f a) (f b)
setter_trans (Trans l p r) = Trans (Compose . fmap l) p (fmap r . getCompose)


--instances

class f ~ (Either (Arg f)) => WithChoice f

instance WithChoice (Either c)

class f ~ ((,) (Arg f)) => WithStrong f

instance WithStrong ((,) c)

class (f ~ ((->) (Arg f))) => WithClosed f

instance WithClosed ((->) c)

newtype Affine a b c = Affine { unAffine :: a + (b , c) }

class f ~ Affine (Arg1 f) (Arg2 f) => WithAffine f

instance WithAffine (Affine c d)


instance Choice (ChoiceT p) where right' = choice_trans

instance Strong (StrongT p) where second' = strong_trans

instance Closed (ClosedT p) where closed = closed_trans

instance Choice (AffineT p) where right' = dimap (Affine . either (Left . id) (Right . ((,) ()))) (either Left (Right . snd) . unAffine) . affine_trans

instance Strong (AffineT p) where second' = dimap (Affine . Right) (either absurd id . unAffine) . affine_trans

instance Strong (TraversingT p) where second' = traverse'

instance Choice (TraversingT p) where right' = traverse'

instance Traversing (TraversingT p) where traverse' = traversal_trans

instance Strong (MappingT p) where second' = map'

instance Choice (MappingT p) where right' = map'

instance Closed (MappingT p) where closed = map'

instance Traversing (MappingT p) where traverse' = map'

instance Mapping (MappingT p) where map' = setter_trans

