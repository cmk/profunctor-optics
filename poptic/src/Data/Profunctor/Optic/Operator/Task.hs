{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GADTs #-}

module Data.Profunctor.Optic.Operator.Task where

import Control.Comonad
import Control.Comonad.Store.Class

import Data.Profunctor.Optic.Type.Class 
import Data.Profunctor.Optic.Prelude

import qualified Data.Profunctor.Optic.Type.VL as VL
import Control.Applicative.Free (Ap, liftAp, runAp)
import Data.Traversable (fmapDefault, foldMapDefault)

---------------------------------------------------------------------
-- 'Task'
---------------------------------------------------------------------


-- https://arxiv.org/pdf/1402.1699.pdf (sections 1.1, 4)
-- https://hackage.haskell.org/package/build-1.0/docs/Build-Task.html#t:Task
newtype Task c p i k v = Task { runTask :: forall f. c f => p i (f k) -> f v }

-- A 'Context' is like a 'Lens' that has already been applied to a some structure.
-- @
-- 'Context' i k v == 'Context i k v 
-- 'Context' i k v == exists s. (s, 'Lens' s t a b)
-- @.
-- https://bartoszmilewski.com/2015/07/13/from-lenses-to-yoneda-embedding/
-- http://hackage.haskell.org/package/lens-4.17/docs/src/Control.Lens.Internal.Store.html#Store
type Context i k v = Task Functor (->) i k v

-- A 'Bazaar' is like a 'Traversal' that has already been applied to a some structure.
-- same as FunLists 
-- Bazaar (->) i k v = data FunList i k v = Done t | More a (FunList a b (b -> t))
-- https://bartoszmilewski.com/2018/10/12/trading-funlists-at-a-bazaar-with-yoneda/
type Bazaar p i k v = Task Applicative p i k v

{-
-- not a profunctor, but is Invariant : invmap :: (a -> b) -> (b -> a) -> f a -> f b

instance (Functor :- c) => Invariant (Task c (->)) where
  invmap f g (Task t) = Task $ \h -> fmap f (t h) where h 
-}

pureTaskF :: a -> Task Functor (->) a b b
pureTaskF a = Task $ \aft -> fmap id (aft a)

pureTask :: a -> Task c (->) a b b
pureTask a = Task ($ a)

-- | Lift an applicative task to @Task Monad@. Use this function when applying
-- monadic task combinators to applicative tasks.
liftTask :: Task Functor p i k v -> Task Applicative p i k v
liftTask (Task task) = Task task

-- TODO: instance (Functor :- c) => Functor (Task c p a b)
instance Functor (Task Applicative p i k) where
  fmap f (Task fps) = Task $ (fmap f) . fps

instance Functor (Task Functor p i k) where
  fmap f (Task fps) = Task $ (fmap f) . fps

-- TODO: instance (Applicative :- c) => Functor (Task c p a b)
instance Applicative (Task Applicative (->) i k) where
  pure x = Task $ const (pure x)
  Task f <*> Task x = Task $ \op -> (f op) <*> (x op)

newtype WrappedTask k v i= WrappedTask { getWrappedTask :: Task Applicative (->) i k v }

instance Functor (WrappedTask k v) where
  fmap = fmapDefault

instance Foldable (WrappedTask k v) where
  foldMap = foldMapDefault

instance Traversable (WrappedTask k v) where
  traverse f (WrappedTask (Task fps)) = fmap WrappedTask . getCompose $
    fps (Compose . fmap pureTask . f)

{-
-- Free applicative over Identity if you could force Identity to be monomorphic on x.
data Mono x y a where Mono :: x -> Mono x y y

liftMono :: x -> Ap (Mono x y) y
liftMono = liftAp . Mono

unMono :: (x -> y) -> Mono x y a -> a
unMono f (Mono x) = f x

runMono :: (x -> y) -> Ap (Mono x y) a -> a
runMono f = runIdentity . runAp (Identity . unMono f)

data FunList i k v = Done v | More i (FunList i k (k -> v))

--data FlistF i k v r = Done t | More a r
-}

---------------------------------------------------------------------
-- 'Store'
---------------------------------------------------------------------



-- | The indexed store can be used to characterize a 'Lens'
-- and is used by 'cloneLens'.
--
-- @'Context i k v@ is isomorphic to
-- @newtype 'Context i k v = 'Context { runStore :: forall f. 'Functor' f => (a -> f b) -> f t }@,
-- and to @exists s. (s, 'Lens' s t a b)@.
--
-- A 'Context is like a 'Lens' that has already been applied to a some structure.
--data Store i k v = Store (b -> t) a

-- | An abstract datatype for a key/value store with build information of type @a@.
data Store i k v = Store { values :: k -> v, info :: i }

instance Functor (Store i k) where
    fmap g (Store h i) = Store (g . h) i
    {-# INLINE fmap #-}

instance Profunctor (Store i) where
    dimap f g (Store h i) = Store (g . h . f) i
    {-# INLINE dimap #-}

instance i ~ k => Comonad (Store i k) where
  extract   (Store f a) = f a
  {-# INLINE extract #-}
  duplicate (Store f a) = Store (Store f) a
  {-# INLINE duplicate #-}
  extend g  (Store f a) = Store (g . Store f) a
  {-# INLINE extend #-}

instance i ~ k => ComonadStore i (Store i k) where
  pos (Store _ i) = i
  {-# INLINE pos #-}
  peek b (Store h _) = h b
  {-# INLINE peek #-}
  peeks f (Store h i) = h (f i)
  {-# INLINE peeks #-}
  seek a (Store h _) = Store h a
  {-# INLINE seek #-}
  seeks f (Store h i) = Store h (f i)
  {-# INLINE seeks #-}
  experiment f (Store h i) = h <$> f i
  {-# INLINE experiment #-}

-- The type ∀ f, g : Functor. (g a → f b) → g s → f t is isomorphic to the type (s → a)×(b → t). 
-- The Van Laarhoven representation of isomorphisms uses this representation 
-- of a pair of functions to capture the notion of an isomorphism.
extractPair :: (((s -> a) -> Store (s -> a) b b) -> (s -> s) -> Store (s -> a) b t)
            -> (s -> a, b -> t)
extractPair l = (f, g) where Store g f = l (Store id) id

--_Store :: Iso (Store a1 b1 t1) (Store a2 b2 t2) (Context a1 b1 t1) (Context a2 b2 t2)
--_Store = dimap fromStore toStore

toStore :: Context i k v -> Store i k v
toStore (Task t) = t $ Store id

fromStore :: Store i k v -> Context i k v
fromStore (Store f i) = Task $ \ifk -> fmap f (ifk i)

-- | Read the build information.
getInfo :: Store i k v -> i
getInfo = info

-- | Read the value of a key.
getValue :: k -> Store i k v -> v
getValue = flip values

-- | Write the build information.
putInfo :: i -> Store i k v -> Store i k v
putInfo i s = s { info = i }

-- | Modify the build information.
mapInfo :: (i -> j) -> Store i k v -> Store j k v
mapInfo f (Store kv i) = Store kv (f i)

-- | Update the value of a key.
putValue :: Eq k => k -> v -> Store i k v -> Store i k v
putValue k v s = s { values = \key -> if key == k then v else values s key }

-- | Initialise the store.
initialise :: (k -> v) -> i -> Store i k v
initialise = Store

