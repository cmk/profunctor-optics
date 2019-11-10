{-# LANGUAGE ExistentialQuantification, DefaultSignatures, UndecidableInstances #-}

module Data.Profunctor.Trans (
    module Data.Profunctor.Trans
  , module Export
  ) where

import Data.Profunctor
import Data.Profunctor.Misc
import Data.Profunctor.Choice
import Data.Profunctor.Closed
import Data.Profunctor.Strong
import Data.Profunctor.Traversing
import Data.Profunctor.Trans.Class as Export
import Data.Profunctor.Mapping
import Data.Profunctor.Monad
import Data.Profunctor.Yoneda
import Prelude

import Data.Kind
import Data.Profunctor.Unsafe
import Data.Functor.Compose
--import Data.Tagged
import Data.Void
import Data.Functor.Identity

--Data.Profunctor.Trans.Closed
--Data.Profunctor.Trans.Affine
--Data.Profunctor.Trans.AChroma

instance ProfunctorTrans FreeChoice where
  type Sigma FreeChoice = WithChoice
  type Theta FreeChoice = Choice

  plift = choice_lift

  trans = choice_trans

instance ProfunctorTrans FreeStrong where
  type Sigma FreeStrong = WithStrong

  plift = strong_lift

  trans = strong_trans
 
instance ProfunctorTrans FreeClosed where
  type Sigma FreeClosed = WithClosed

  plift = closed_lift

  trans = closed_trans

instance ProfunctorTrans FreeAffine where
  type Sigma FreeAffine = WithAffine

  plift = affine_lift

  trans = affine_trans

instance ProfunctorFunctor (Free m) where
  promap f (Free l p r) = Free l (f p) r



type family Arg  (x :: * -> *) where Arg  (f a)   = a
type family Arg1 (x :: * -> *) where Arg1 (f a b) = a
type family Arg2 (x :: * -> *) where Arg2 (f a b) = b

--Free m p ~ m f => (Costar f) `Procompose` p `Procompose` (Star f)

--data Free m p s t where Free :: m f => (s -> f a) -> p a b -> (f b -> t) -> Free m p s t
data Free m p a b = forall x y f. m f => Free (a -> f x) (p x y) (f y -> b)

type FreeChoice = Free WithChoice

type FreeStrong = Free WithStrong

type FreeClosed = Free WithClosed

type FreeAffine = Free WithAffine

type FreeTraversal = Free Traversable

type FreeSetter = Free Functor


--prisms

choice_lift :: p a b -> FreeChoice p a b
choice_lift p = Free Right p rgt'

--see also PastroSum's Choice instance
choice_trans :: FreeChoice p a b -> FreeChoice p (c + a) (c + b)
choice_trans (Free l p r) = Free
    (either (Left . Left) (either (Left . Right) Right . l)) p
    (either (either Left (Right . r . Left)) (Right . r . Right))


--lenses

strong_lift :: p a b -> FreeStrong p a b
strong_lift p = Free ((,) ()) p snd

-- see also Pastro's Strong instance
strong_trans :: FreeStrong p a b -> FreeStrong p (c, a) (c, b)
strong_trans (Free l p r) = Free (\(d,s) -> ((d , fst (l s)), snd (l s))) p (\((d,c),b) -> (d,r (c,b)))


--grates

closed_lift :: p a b -> FreeClosed p a b
closed_lift p = Free const p ($ ())

--see also Environment's Closed instance
closed_trans :: FreeClosed p a b -> FreeClosed p (c -> a) (c -> b)
closed_trans (Free l p r) = Free (\f (d , c) -> l (f d) c) p ((r .) . curry)


--affine traversals

affine :: Choice p => Strong p => p a b -> p (Affine c d a) (Affine c d b)
affine = dimap unAffine Affine . right' . second'

affine_lift :: p a b -> FreeAffine p a b 
affine_lift p = Free (Affine . Right . ((,) ())) p (either absurd snd . unAffine)

affine_trans :: FreeAffine p a b -> FreeAffine p (Affine c d a) (Affine c d b)
affine_trans (Free l p r) = Free (u l) p (v r)
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

traversal_lift :: p a b -> FreeTraversal p a b
traversal_lift p = Free Identity p runIdentity

--see also FreeTraversing's Traversing instance
traversal_trans :: Traversable f => FreeTraversal p a b -> FreeTraversal p (f a) (f b)
traversal_trans (Free l p r) = Free (Compose . fmap l) p (fmap r . getCompose)


-- setters

setter_lift :: p a b -> FreeSetter p a b
setter_lift p = Free Identity p runIdentity

--see also FreeMapping's Mapping instance
setter_trans :: Functor f => FreeSetter p a b -> FreeSetter p (f a) (f b)
setter_trans (Free l p r) = Free (Compose . fmap l) p (fmap r . getCompose)


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

instance Profunctor (Free m p) where
  dimap f g (Free l p r) = Free (l . f) p (g . r)
  lmap f (Free l p r) = Free (l . f) p r
  rmap g (Free l p r) = Free l p (g . r)
  g #. Free l p r = Free l p (g #. r)
  Free l p r .# f = Free (l .# f) p r

instance Choice (FreeChoice p) where right' = choice_trans

instance Strong (FreeStrong p) where second' = strong_trans

instance Closed (FreeClosed p) where closed = closed_trans

instance Choice (FreeAffine p) where right' = dimap (Affine . either (Left . id) (Right . ((,) ()))) (either Left (Right . snd) . unAffine) . affine_trans

instance Strong (FreeAffine p) where second' = dimap (Affine . Right) (either absurd id . unAffine) . affine_trans

instance Strong (FreeTraversal p) where second' = traverse'

instance Choice (FreeTraversal p) where right' = traverse'

instance Traversing (FreeTraversal p) where traverse' = traversal_trans

instance Strong (FreeSetter p) where second' = map'

instance Choice (FreeSetter p) where right' = map'

instance Closed (FreeSetter p) where closed = map'

instance Traversing (FreeSetter p) where traverse' = map'

instance Mapping (FreeSetter p) where map' = setter_trans

