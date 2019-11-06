{-# Language FunctionalDependencies #-}
module Data.Profunctor.Optic (
    module Type
  , module Operator
  , module Property
  , module Iso
  , module View
  , module Setter
  , module Lens
  , module Prism
  , module Grate
  , module Fold
  , module Fold0
  , module Cofold
  , module Traversal
  , module Traversal0
  , module Traversal1
  , module Cotraversal
) where

import Data.Profunctor.Optic.Type             as Type
import Data.Profunctor.Optic.Operator         as Operator
import Data.Profunctor.Optic.Property         as Property
import Data.Profunctor.Optic.Iso              as Iso
import Data.Profunctor.Optic.View             as View
import Data.Profunctor.Optic.Setter           as Setter
import Data.Profunctor.Optic.Lens             as Lens
import Data.Profunctor.Optic.Prism            as Prism
import Data.Profunctor.Optic.Grate            as Grate
import Data.Profunctor.Optic.Fold             as Fold
import Data.Profunctor.Optic.Fold0            as Fold0
import Data.Profunctor.Optic.Cofold           as Cofold
import Data.Profunctor.Optic.Traversal        as Traversal
import Data.Profunctor.Optic.Traversal0       as Traversal0
import Data.Profunctor.Optic.Traversal1       as Traversal1
import Data.Profunctor.Optic.Cotraversal      as Cotraversal

import Data.Profunctor.Traversing
import qualified Prelude as Prelude
import Data.Monoid
import Data.Profunctor.Unsafe
import Data.Foldable
import Data.Profunctor.Optic.Prelude
-- | Class for 'Functor's that have an additional read-only index available.
class Functor f => FunctorWithIndex i f | f -> i where
  imap :: (i -> a -> b) -> f a -> f b


-- | Class for 'Foldable's that have an additional read-only index available.
class (FunctorWithIndex i f, Foldable f
      ) => FoldableWithIndex i f | f -> i where
  ifoldMap :: Monoid m => (i -> a -> m) -> f a -> m


  ifoldr :: (i -> a -> b -> b) -> b -> f a -> b
  ifoldr iabb b0 = (\e -> appEndo e b0) . ifoldMap (\i -> Endo #. iabb i)
  {-# INLINE ifoldr #-}

  ifoldl' :: (i -> b -> a -> b) -> b -> f a -> b
  ifoldl' ibab b0 s = ifoldr (\i a bb b -> bb $! ibab i b a) id s b0
  {-# INLINE ifoldl' #-}

-- | Traverse 'FoldableWithIndex' ignoring the results.
itraverse_ :: (FoldableWithIndex i t, Applicative f) => (i -> a -> f b) -> t a -> f ()
itraverse_ f = undefined --runTraversed . ifoldMap (\i -> Traversed #. f i)
{-# INLINE itraverse_ #-}

-- | Flipped 'itraverse_'.
ifor_ :: (FoldableWithIndex i t, Applicative f) => t a -> (i -> a -> f b) -> f ()
ifor_ = flip itraverse_
{-# INLINE ifor_ #-}

-- | Class for 'Traversable's that have an additional read-only index available.
class (FoldableWithIndex i t, Traversable t
      ) => TraversableWithIndex i t | t -> i where
  itraverse :: Applicative f => (i -> a -> f b) -> t a -> f (t b)


--type IxOptic p i j m n s t a b = p i j a b -> p m n s t

type IxOptic p i o s t a b = p i a b -> p o s t
type IxOptic' p i o s a = p i a a -> p o s s

-- | Needed for indexed traversals.
newtype IxStar f i a b = IxStar { runIxStar :: i -> a -> f b }

-- | Needed for indexed folds.
newtype IxForget r i a b = IxForget { runIxForget :: i -> a -> r }

-- | Needed for indexed affine folds.
newtype IxForgetM r i a b = IxForgetM { runIxForgetM :: i -> a -> Maybe r }

-- | Needed for indexed setters.
newtype IxFunArrow i a b = IxFunArrow { runIxFunArrow :: i -> a -> b }

class IxProfunctor p where
    ilmap :: (i -> j) -> p j a b -> p i a b

class IxProfunctor p => TraversingWithIndexC p where
    itraversedC :: (TraversableWithIndex i t)
                => IxOptic p r (i -> r) (t a) (t b) a b
    itraversedC = iwanderC itraverse

    iwanderC :: (forall f. Applicative f
                 => (i -> a -> f b)
                 -> (s -> f t))
             -> IxOptic p r (i -> r) s t a b

cps_ex1 :: ( TraversingWithIndexC p
           , TraversableWithIndex i t, TraversableWithIndex i' t'
           )
        => IxOptic p r (i -> i' -> r) (t (t' a)) (t (t' b)) a b
cps_ex1 =  itraversedC . itraversedC

itoListOfC :: IxOptic' (IxForget [(i, a)]) i (i -> i) s a
           -> s -> [(i, a)]
itoListOfC o = ifoldMapOfC o (\i a -> [(i, a)])

ifoldMapOfC :: IxOptic' (IxForget r) i (i -> i) s a
            -> (i -> a -> r) -> s -> r
ifoldMapOfC o f = runIxForget (o (IxForget f)) id

ifoldMapOfC2 :: IxOptic' (IxForget r) k (i -> j -> k) s a
             -> (i -> j -> k) -> (k -> a -> r) -> s -> r
ifoldMapOfC2 o ijk f = runIxForget (o (IxForget f)) ijk

ifoldMapOfC2' :: IxOptic' (IxForget r)
                 (a -> r) (i -> j -> a -> r) s a
              -> (i -> j -> a -> r) -> s -> r
ifoldMapOfC2' o f = runIxForget (o (IxForget id)) f

flattenIndicesC
    :: IxProfunctor p
    => (i -> j -> k)
    -> p (i -> j -> z) a b
    -> p (k -> z) a b
flattenIndicesC f = ilmap (\g i j -> g (f i j))

instance FunctorWithIndex () Identity where
  imap f (Identity a) = Identity (f () a)
  {-# INLINE imap #-}

instance FoldableWithIndex () Identity where
  ifoldMap f (Identity a) = f () a
  {-# INLINE ifoldMap #-}

instance TraversableWithIndex () Identity where
  itraverse f (Identity a) = Identity <$> f () a
  {-# INLINE itraverse #-}

-- (,) k

instance FunctorWithIndex k ((,) k) where
  imap f (k, a) = (k, f k a)
  {-# INLINE imap #-}

instance FoldableWithIndex k ((,) k) where
  ifoldMap = uncurry
  {-# INLINE ifoldMap #-}

instance TraversableWithIndex k ((,) k) where
  itraverse f (k, a) = (,) k <$> f k a
  {-# INLINE itraverse #-}

-- (->) r

instance FunctorWithIndex r ((->) r) where
  imap f g x = f x (g x)
  {-# INLINE imap #-}

-- []

instance FunctorWithIndex Int []
instance FoldableWithIndex Int []
instance TraversableWithIndex Int [] where
  -- Faster than @indexing traverse@, also best for folds and setters.
  itraverse f = traverse (uncurry f) . Prelude.zip [0..]
  {-# INLINE itraverse #-}


-- Maybe

instance FunctorWithIndex () Maybe where
  imap f = fmap (f ())
  {-# INLINE imap #-}
instance FoldableWithIndex () Maybe where
  ifoldMap f = foldMap (f ())
  {-# INLINE ifoldMap #-}
instance TraversableWithIndex () Maybe where
  itraverse f = traverse (f ())
  {-# INLINE itraverse #-}

{-
cps_ex2
  :: (TraversingWithIndexC (IxForget [((a1, b), a2)]),
      TraversableWithIndex a1 t1, TraversableWithIndex b t2) =>
     t1 (t2 a2) -> [((a1, b), a2)]
cps_ex2 = itoListOfC (flattenIndicesC (,) . itraversedC . itraversedC) [[1,2],[3,4,5]]
    ~=?
    [((0,0),1),((0,1),2),((1,0),3),((1,1),4),((1,2),5)]

cps_ex3 = ifoldMapOfC2' (itraversedC . itraversedC) (\i j a -> [(i,j,a)]) [[1,2],[3,4,5]]
    ~=?
    [(0,0,1),(0,1,2),(1,0,3),(1,1,4),(1,2,5)]

-}
instance Profunctor (IxForget r i) where
    dimap f _ (IxForget p) = IxForget (\i -> p i . f)

instance Strong (IxForget r i) where
    first' (IxForget p) = IxForget (\i -> p i . fst)

instance Monoid r => Choice (IxForget r i) where
    right' (IxForget p) =  IxForget (\i -> either (const mempty) (p i))

instance Monoid r => Traversing (IxForget r i) where
    wander f (IxForget p) = IxForget (\i -> getConst . f (Const . p i))

instance IxProfunctor (IxForget r) where
    ilmap f (IxForget p) = IxForget (p . f)

{-
instance Monoid r => TraversingWithIndex (IxForget r) where
    iwanderI f (IxForget p) = IxForget $ \o ->
        getConst . f (\i -> Const . p (i, o))
-}
instance Monoid r => TraversingWithIndexC (IxForget r) where
    iwanderC f (IxForget p) = IxForget $ \ij ->
        getConst . f (\i -> Const . p (ij i))

type IndexedOpticJ p i j k l s t a b =
    p i j a b -> p k l s t
--one index pair for the contravariant argument (as previously), and one more pair for covariant.

--Writing operations using this encoding isn't different than previously. We make some concrete profunctor, use optic to transform it, and then use the result:

ifoldMapOfJ :: IndexedOpticJ (IndexedForgetJ r) (i, ()) () () k s t a b
            -> (i -> a -> r) -> s -> Either k r
ifoldMapOfJ o f =
    runIndexedForgetJ (o (IndexedForgetJ $ \(i, ()) -> Right . f i)) ()

newtype IndexedForgetJ r i j a b =
    IndexedForgetJ { runIndexedForgetJ :: i -> a -> Either j r }

instance Profunctor (IndexedForgetJ r i j) where
    dimap f _ (IndexedForgetJ p) =
        IndexedForgetJ (\i  -> p i . f)

instance Strong (IndexedForgetJ r i j) where
    first' (IndexedForgetJ p) =
        IndexedForgetJ (\i -> p i . fst)

instance Monoid r => Choice (IndexedForgetJ r i j) where
    right' (IndexedForgetJ p) =
        IndexedForgetJ (\i -> either (const (Right mempty)) (p i))

instance Monoid r => Traversing (IndexedForgetJ r i j) where
    wander f (IndexedForgetJ p)  = IndexedForgetJ $ \i ->
        getE . getConst . f (Const . E . p i)
--That's not exactly a ifoldMapOf variant, as it can fail with a description!

--Let's define few constructors to play with examples. We will use bare String for errors, in real library you probably want something more structured.

type Err = String
--To define prisms we need a variant of Choice, not that we

newtype E a b = E { getE :: Either a b }

instance Semigroup r => Semigroup (E a r) where
    (<>) x@(E (Left _)) _ = x
    (<>) _ x@(E (Left _)) = x
    (<>) (E (Right a)) (E (Right b)) = E (Right ((<>) a b))

instance Monoid r => Monoid (E a r) where
    mempty = E (Right mempty)
    mappend = (<>)


--We have to define auxiliary type to select the right error when traversing:

newtype E2 a b = E2 { runE2 :: Either (Either Err a) b }

instance Semigroup b => Semigroup (E2 a b) where
    (<>) = mappend
instance Semigroup b => Monoid (E2 a b) where
    mempty = E2 (Left (Left "Empty Fold"))
    mappend (E2 (Right a)) (E2 (Right b)) = E2 (Right (a <> b))
    mappend x@(E2 Right{}) _ = x
    mappend _ x@(E2 Right{}) = x
    -- make inner errors more important!
    mappend x@(E2 (Left (Right _))) _ = x
    mappend _ x@(E2 (Left (Right _))) = x
    mappend x _ = x

class IndexedProfunctorJ p => ChoiceWithIndexJ p where
    irightJ :: IndexedOpticJ p i j i (Either Err j)
                               (Either c a) (Either c b) a b

instance ChoiceWithIndexJ (IndexedForgetJ r) where
    irightJ (IndexedForgetJ p) =
        IndexedForgetJ $ \i eca -> case fmap (p i) eca of
            Right (Right r) -> Right r
            Right (Left j)  -> Left (Right j)
            Left _c         -> Left (Left "right' failed")

class IndexedProfunctorJ p where
    idimapJ :: (i -> j) -> (k -> l)
            -> IndexedOpticJ p j k i l a b a b

    ilmapJ :: (i -> j)
          -> IndexedOpticJ p j k i k a b a b
    ilmapJ f = idimapJ f id

instance IndexedProfunctorJ (IndexedForgetJ r) where
    idimapJ f g (IndexedForgetJ p)
        = IndexedForgetJ $ \i -> first g . p (f i)
--And a Traversing variant. Let's make examples interesting by making IndexedFOrgetJ instance "fail", if the Traversal is empty:

class ChoiceWithIndexJ p => TraversingWithIndexJ p where
    itraversedJ :: TraversableWithIndex i t
                => IndexedOpticJ p (i, j) k j (Either Err k)
                                   (t a) (t b) a b
    itraversedJ = iwanderJ itraverse

    iwanderJ :: (forall f. Applicative f
                   => (i -> a -> f b)
                   -> (s -> f t))
             -> p (i, j) k a b -> p j (Either Err k) s t

instance Semigroup r => TraversingWithIndexJ (IndexedForgetJ r) where
    iwanderJ f (IndexedForgetJ p) =
        IndexedForgetJ $ \j s -> runE2 $ getConst $
            f (\i a -> Const $ E2 $ first Right $ p (i, j) a ) s


{-
coindexed_ex1 = ifoldMapOfJ (irightJ . idimapJ ((),) id) (,) (Right 'a')
    ~=?
    Right ((), 'a')

coindexed_ex2 :: (TraversableWithIndex a t, Data.String.IsString (t b)) => Either (Either Err ()) [(a, b)]
coindexed_ex2 = ifoldMapOfJ itraversedJ (\i x -> [(i, x)]) "foobar"
    ~=?
    Right [(0,'f'),(1,'o'),(2,'o'),(3,'b'),(4,'a'),(5,'r')]
Note if traverse' zooms into empty Traversable, it won't be an error. But we can make a variant which would make that erroneous as well.

coindexed_ex3
  :: (Traversing (IndexedForgetJ [(Int, b)] (Int, ()) ()),
      Traversable f, IsString (f b)) =>
     Either (Either Err ()) [(Int, b)]
coindexed_ex3 = ifoldMapOfJ (itraversedJ . (traverse' @_ @[])) (\i x -> [(i, x)]) ["foo", "bar"]
    ~=?
    Right [(0,'f'),(0,'o'),(0,'o'),(1,'b'),(1,'a'),(1,'r')]

coindexed_ex4 :: Either (Either Err ()) [(Int, Char)]
coindexed_ex4 = ifoldMapOfJ (traverse' . (itraversedJ @_ @Int @[])) (\i x -> [(i, x)]) ["foo", "bar"]
--Right [(0,'f'),(1,'o'),(2,'o'),(0,'b'),(1,'a'),(2,'r')]
    ~=?
    Right [(0,'f'),(1,'o'),(2,'o'),(0,'b'),(1,'a'),(2,'r')]

coindexed_ex5 :: Either (Either Err (Either Err ())) [((Int, Int), Char)]
coindexed_ex5 = ifoldMapOfJ (itraversedJ . (itraversedJ @_ @Int @[]) . idimapJ assocl id) (\i x -> [(i, x)]) ["foo", "bar"]
-- Right [((0,0),'f'),((1,0),'o'),((2,0),'o'),((0,1),'b'),((1,1),'a'),((2,1),'r')]

The erroneous cases work as we want: looking at wrong value through Prism gives Prism error, Looking through Traversal at empty list gives an empty fold error:

coindexed_ex6 = ifoldMapOfJ (irightJ . idimapJ ((),) id) (,) (Left True)
    ~=?
    (Left (Left "right' failed") :: Either (Either Err ()) ((), ()))
coindexed_ex7 =
    ifoldMapOfJ itraversedJ (\i x -> [(i, x)]) ""
    ~=?
    Left (Left "Empty Fold")
If we combine a Traversal and a Prism we'll see how different erroneous cases work. If all elements of the list are Right, we get them. If some is Left, but there's at least one Right; we still get Right. If all values are Left we get prism error; and if the list is empty we get an empty fold error. Here we could use idimapJ to flatten errors, but it's good to see on which "level" error occurred.

coindexed_ex8 =
    ifoldMapOfJ (itraversedJ . irightJ) (\i x -> [(i, x)])
    [Right 'a', Right 'b']
    ~=?
    Right [(0,'a'),(1,'b')]

coindexed_ex9 =
    ifoldMapOfJ (itraversedJ . irightJ) (\i x -> [(i, x)])
    [Right 'a', Left False]
    ~=?
    Right [(0,'a')]

coindexed_exA =
    ifoldMapOfJ (itraversedJ . irightJ) (\i x -> [(i, x)])
    [Left False]
    ~=?
    (Left (Right (Left "right' failed"))
        :: Either (Either Err (Either Err ())) [(Int, ())])

coindexed_exB =
    ifoldMapOfJ (itraversedJ . irightJ) (\i x -> [(i, x)]) []
    ~=?
    (Left (Left "Empty Fold")
        :: Either (Either Err (Either Err ())) [(Int, ())])
-}
