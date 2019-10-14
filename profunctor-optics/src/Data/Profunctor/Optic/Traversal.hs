{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GADTs #-}

module Data.Profunctor.Optic.Traversal where

--import Data.Bitraversable 
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Prelude-- ((+), dup, dedup, swp, coswp, apply)

import Data.Traversable (fmapDefault, foldMapDefault)

--import Data.Profunctor.Task
import Data.Profunctor.Choice
import Data.Profunctor.Monad
import Data.Profunctor.Strong
import Control.Applicative.Free.Fast
import Data.Functor.Identity
import Data.Profunctor.Types
import Data.Profunctor.Unsafe

import qualified Data.Tuple as T
import Prelude hiding (mapM, id, (.))
--import Control.Category
--import Control.Arrow 
import qualified Control.Category as C
import qualified Control.Arrow as A
{-
---------------------------------------------------------------------
-- 'Traversal'
---------------------------------------------------------------------

-- | TODO: Document
--
traversal :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> Traversal s t a b
traversal = lift

-- | TODO: Document
--
traversed :: Traversable t => Traversal (t a) (t b) a b
traversed = lift traverse

-- | Traverse both parts of a 'Bitraversable' container with matching types.
--
-- Usually that type will be a pair.
--
-- >>> (1,2) & both *~ 10
-- (10,20)
--
-- >>> lift both length ("hello","world")
-- (5,5)
--
-- >>> ("hello","world")^.both
-- "helloworld"
--
-- @
-- 'both' :: 'Traversal' (a, a)       (b, b)       a b
-- 'both' :: 'Traversal' ('Either' a a) ('Either' b b) a b
-- @
both :: Bitraversable t => Traversal (t a a) (t b b) a b
both = lift $ \f -> bitraverse f f
{-# INLINE both #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

{-
The laws for a 'Traversal' follow from the laws for 'Traversable' as stated in "The Essence of the Iterator Pattern".

Identity:

traverseOf t (Identity . f) ≡  Identity (fmap f)

Composition:

Compose . fmap (traverseOf t f) . traverseOf t g == traverseOf t (Compose . fmap f . g)

One consequence of this requirement is that a 'Traversal' needs to leave the same number of elements as a
candidate for subsequent 'Traversal' that it started with. 

-}
-- ^ @
-- traverseOf :: Functor f => Lens s t a b -> (a -> f b) -> s -> f t
-- traverseOf :: Applicative f => Traversal s t a b -> (a -> f b) -> s -> f t
-- traverseOf $ _1 . _R :: Applicative f => (a -> f b) -> (Either c a, d) -> f (Either c b, d)
-- traverseOf == between runStar Star 
-- @

-- | TODO: Document
--
traverseOf :: LensLike f s t a b -> (a -> f b) -> s -> f t
traverseOf o f = tf where Star tf = o (Star f)

-- | TODO: Document
--
--sequenceOf :: Applicative f => LensLike f s t (f a) a -> s -> f t
--sequenceOf t = traverseOf t id
-}


data Mono x y a where Mono :: x -> Mono x y y

runFunList :: Applicative f => FunList a b t -> (a -> f b) -> f t
runFunList (Done b) _ = pure b
runFunList (More s r) f = f s <**> runFunList r f

makeFunList :: Traversable t => t a -> FunList a b (t b)
makeFunList = traverse (\a -> More a (Done id))


{-

infixl 4 :<*>

-- A list of values that have been traversed over so far. d is the input type;
-- e is the planned output.
data TList d e a where
  TNil :: TList d e ()
  (:<*>) :: d -> TList d e u -> TList d e (e, u)

-- Trav is a Church-encoded free applicative, which is used to make traversing
-- and assembling a TList faster by left-associating and bringing all the
-- fmaps to the top. See https://www.eyrie.org/~zednenem/2013/06/freeapp-2 for
-- details.
newtype Trav d e a = Trav (forall u y z. (forall x. (x -> y) -> TList d e x -> z) -> (u -> a -> y) -> TList d e u -> z)

instance Functor (Trav d e) where
  {-# INLINE fmap #-}
  fmap f (Trav m) = Trav $ \k s -> m k (\u -> s u . f)

  {-# INLINE (<$) #-}
  a <$ Trav m = Trav $ \k s -> m k (\u -> const $ s u a)

instance Applicative (Trav d e) where
  {-# INLINE pure #-}
  pure a = Trav $ \k s -> k (flip s a)

  {-# INLINE (<*>) #-}
  Trav mf <*> Trav ma = Trav $ \k s -> ma (mf k) (\u a g -> s u (g a))

-- Coyoneda encoding of a Functor.
data Coyo f a where
  Coyo :: (u -> a) -> f u -> Coyo f a

-- Lift a d into an appropriate Trav with an unknown return type.
{-# INLINE tLift #-}
tLift :: d -> Trav d e e
tLift d = Trav $ \k s p -> k (\ (a, u) -> s u a) (d :<*> p)

-- Convert the Trav into an actual list.
{-# INLINE runTrav #-}
runTrav :: Trav d e a -> Coyo (TList d e) a
runTrav (Trav m) = m Coyo (const id) TNil

-- Split a Coyoneda-encoded TList into something an ArrowChoice can traverse.
{-# INLINE unTList #-}
unTList :: Coyo (TList d e) a -> Either a (d, Coyo (TList d e) (e -> a))
unTList (Coyo f TNil) = Left (f ())
unTList (Coyo f (d :<*> t)) = Right (d, Coyo (\u e -> f (e, u)) t)


select ::  ArrowChoice a1 => a1 (Either d (a2, a2 -> d)) d --(a + (b, b -> a)) -> a
select = id ||| arr apply

wanderA :: forall p a b s t. (ArrowChoice p)
  => (forall f. (Applicative f) => (a -> f b) -> s -> f t)
  -> p a b -> p s t
wanderA tr p = go . arr (runTrav . tr tLift) where
  go :: forall u. p (Coyo (TList a b) u) u
  go = (id ||| arr apply . (p *** go)) . arr unTList



-}


--go p = (id ||| arr apply . (p *** go p)) 
{-
wanderA :: forall p a b s t. Category p => Strong p => Choice p
  => (forall f. (Applicative f) => (a -> f b) -> s -> f t)
  -> p a b -> p s t
wanderA tr p = go . arr (runTrav . tr tLift) where
  go :: forall u. p (Coyo (TList a b) u) u
  go = (select . (_ p go)) .  arr unTList

type (+) = Either



(***) :: Category a => Strong a => a b c -> a b' c' -> a (b , b') (c , c')
f *** g = first' f >>> braid >>> first' g >>> braid

(+++) :: Category a => Choice a => a b c -> a b' c' -> a (b + b') (c + c')
f +++ g = left' f >>> cobraid >>> left' g >>> cobraid

(&&&) :: Category p => Strong p => p a0 c0 -> p a0 c'0 -> p a0 (c0 , c'0)
f &&& g = diag >>> f *** g

(|||) :: Category p => Choice p => p b c -> p b' c -> p (b + b') c
f ||| g = f +++ g >>> codiag


papply :: Category p => Strong p => p a (b -> c) -> p a b -> p a c
papply f x = dimap dup (uncurry ($)) (f *** x)




foo :: p (Coyo (TList a b) u) (a, Coyo (TList a b) c'0)
foo = undefined
-}
{-
wanderA :: forall p a b s t. Category p => Strong p => Choice p
  => (forall f. (Applicative f) => (a -> f b) -> s -> f t)
  -> p a b -> p s t
wanderA tr p = go . arr (runTrav . tr tLift) where
  go :: forall u. p (Coyo (TList a b) u) u
  go = (select . (p *** go)) . arr unTList


wanderA :: forall p a b s t. (ArrowChoice p)
  => (forall f. (Applicative f) => (a -> f b) -> s -> f t)
  -> p a b -> p s t
wanderA tr p = go . arr (runTrav . tr tLift) where
  go :: forall u. p (Coyo (TList a b) u) u
  go = (id ||| arr (uncurry $ flip id) . (p *** go)) . arr unTList
-}

{-
idl = arr snd -- p ((),a) a
idr = arr fst
coidl = arr $ \a -> ((),a) -- p a ((), a)
coidr = arr $ \a -> (a,())
c
f ||| g = f +++ g >>> codiag
-}



--go :: p a b -> p (Coyo (TList a b) u) u
--go p = (id A.||| A.arr (uncurry $ flip id) C.. (p A.*** go)) C.. A.arr unTList


--foo' = p (Me x) x -> p a b -> p (a, Me (b -> y)) y
--p (a, Coyo (TList a b) (b -> u)) u

--go :: (Coyo (TList a b) u) -> u

{-

id A.||| A.arr (uncurry $ flip id)
  :: Either b1 (b2, b2 -> b1) -> b1

(****) :: p a (b -> c) -> p a b -> p a c
(****) = undefined

{-# INLINE wanderA #-}
wanderA :: forall p a b s t. (ArrowChoice p)
  => (forall f. (Applicative f) => (a -> f b) -> s -> f t)
  -> p a b -> p s t
wanderA tr p = go . arr (runTrav . tr tLift) where
  go :: forall u. p (Coyo (TList a b) u) u
  go = (id ||| arr (uncurry $ flip id) . (p *** go)) . arr unTList

{-# INLINE traverseA #-}
traverseA :: (ArrowChoice p, Traversable f) => p a b -> p (f a) (f b)
traverseA = wanderA traverse


traversing k = dimap out inn (right' (par k (traversing k)))

go p = (id ||| arr (uncurry $ flip id) . (p *** go)) . arr unTList


{-# INLINE wanderA #-}
wanderA :: forall p a b s t. Choice p
  => (forall f. (Applicative f) => (a -> f b) -> s -> f t)
  -> p a b -> p s t
wanderA tr p = go . arr (runTrav . tr tLift) where
  go :: forall u. (Coyo (TList a b) u) -> u
  go = (id ||| arr (uncurry $ flip id) . (p *** go)) . arr unTList



wander :: forall p a b s t. (Choice p, StrongSemigroup p)
  => (forall f. (Applicative f) => (a -> f b) -> s -> f t)
  -> p a b -> p s t
wander tr p = lmap (runTrav . tr tLift) go where
  go :: forall u. p (Coyo (TList a b) u) u
  go = dimap unTList dedup . right' $ (lmap T.fst go) `par` (lmap T.snd p)


foo :: p (Coyo (TList a b) u0) u0 -> p a b -> p (a, Coyo (TList a b) (b -> u)) u
foo = undefined


type FL a b t = Ap (Mono a b) t

liftMono :: a -> FL a b b
liftMono = liftAp . Mono

unMono :: (a -> b) -> Mono a b t -> t
unMono f (Mono x) = f x

runMono :: (a -> b) -> FL a b t -> t
runMono f = runIdentity . runAp (Identity . unMono f)

foo :: Traversable t => (a -> b) -> t a -> t b
foo f = runMono f . traverse liftMono

also'' :: Traversable t => FL b a (t a) -> t b
also'' = undefined

makeFunList' :: Traversable t => t a -> FL a b (t b)
makeFunList' = traverse liftMono
-}



{-




newtype RotateFunList b t a = Rotate { unrotate :: FunList a b t }

instance Functor (RotateFunList b t) where
  fmap f (Rotate (Done x)) = Rotate (Done x)
  fmap f (Rotate (More x l)) = Rotate (flip More (unrotate (fmap f (Rotate l))) (f x))

-- I am not 100% certain that the Foldable and Traversable instances are not reversed.
instance Foldable (RotateFunList b t) where
  foldMap f (Rotate (Done x)) = mempty
  foldMap f (Rotate (More x l)) = f x <> foldMap f (Rotate l)

instance Traversable (RotateFunList b t) where
  traverse f (Rotate (Done x)) = pure (Rotate (Done x))
  traverse f (Rotate (More x l)) = Rotate <$> (f x <**> (flip More . unrotate <$> traverse f (Rotate l)))


--lensvl :: (forall f. Functor f => (a -> f b) -> s -> f t) -> Lens s t a b
--lensvl l = dimap ((values &&& info) . l (Store id)) (uncurry id) . second'

{-
contents :: s -> [a] and fill :: ([b], s) -> t.

-}
data TraversalRep a b s t = TraversalRep {runTraversalRep :: s -> FunList a b t}

instance Profunctor (TraversalRep a b) where
  dimap f g (TraversalRep h) = TraversalRep (fmap g . h . f)

instance Strong (TraversalRep a b) where
  first' (TraversalRep h) = TraversalRep (\(s,c) -> fmap (,c) (h s))

  second' (TraversalRep h) = TraversalRep (\(c,s) -> fmap (c,) (h s))

instance Choice (TraversalRep a b) where
  left' (TraversalRep h) = TraversalRep (either (fmap Left . h) (Done . Right))
  right' (TraversalRep h) = TraversalRep (either (Done . Left) (fmap Right . h))

instance StrongSemigroup (TraversalRep a b) where
  par (TraversalRep h) (TraversalRep k) = TraversalRep $ \(x, y) -> pure (,) <*> h x <*> k y

instance StrongMonoid (TraversalRep a b) where
  pempty = TraversalRep pure


type TraversalP s t a b = forall p . Choice p => StrongSemigroup p => Optic p s t a b

--TraversalRep a b s d -> p a b -> p s d
traversalC2P :: TraversalRep a b s t -> TraversalP s t a b
traversalC2P (TraversalRep h) k = dimap h fuse (traversing k)

traversalP2C :: TraversalP s t a b -> TraversalRep a b s t
traversalP2C l = l (TraversalRep single)

data Trvsl s t a b = Trvsl { contents :: s -> [a], fill :: ([b], s) -> t }

--traversalC2P :: Trvsl s t a b -> Traversal s t a b
traversalC2P' :: Trvsl s t a b -> (a -> b) -> s -> t
traversalC2P' (Trvsl c f) = dimap dup f . first . lmap c . ylw where
  ylw h = dimap (maybe (Right []) Left . uncons) dedup $ left' $ rmap cons $ par h (ylw h)
  cons = uncurry (:)
  uncons :: [a] -> Maybe (a, [a])
  uncons = undefined


--traverseOf' :: TraversalP s t a b -> (forall f . Applicative f => (a -> f b) -> s -> f t)
--traverseOf' p f = runStar (p (Star f))

--traversal' :: (forall f . Applicative f => (a -> f b) -> s -> f t) -> TraversalP s t a b
--traversal' = between Star runStar


traversing' :: Choice p => StrongSemigroup p => p a b -> p (Bazaar (->) a c t) (Bazaar (->) b c t)
traversing' = undefined

need' :: Traversable t => t a -> Bazaar (->) a b (t b) --FunList a b (t b)
need' t = Task $ flip traverse t

sell :: Corepresentable p => p a (Bazaar p a b b)
sell = cotabulate $ \ w -> Task (`cosieve` w)
-}


