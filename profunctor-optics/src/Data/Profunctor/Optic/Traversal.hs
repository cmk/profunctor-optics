{-# LANGUAGE TupleSections #-}
module Data.Profunctor.Optic.Traversal (
    -- * Types
    ATraversal0 
  , ATraversal0'
  , ARetraversal0
    -- * Constructors
  , traversal0
  , traversal0'
  , traversal
  , traversal1
  , traversing0
  , traversing
  , traversing1
  , cotraversing
  , traversed 
  , traversed1
  , cotraversed
    -- * Representatives
  , Traversal0Rep(..)
    -- * Primitive operators
  , withTraversal0
  , matchOf
  , rematchOf
  , traverseOf
  , traverse1Of
  , cotraverseOf
  , sequenceOf
  , sequence1Of
  , distributeOf
    -- * Common optics
  , nulled
  , selected
  , predicated
  , bitraversed
  , bitraversed1
  , repeated 
  , iterated
  , cycled 
    -- * Derived operators
  , isMatched
  , isntMatched 
) where

import Data.Bifunctor (first, second)
import Data.Bitraversable
import Data.Semigroup.Bitraversable
import Data.Profunctor.Optic.Prism
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Type

---------------------------------------------------------------------
-- 'Traversal0', 'Traversal', 'Traversal1', & 'Cotraversal'
---------------------------------------------------------------------

-- | Create an 'Traversal0' from a constructor and a matcher.
--
-- \( \quad \mathsf{Traversal0}\;S\;A =\exists C, D, S \cong D + C \times A \)
--
-- /Caution/: In order for the 'Traversal0' to be well-defined,
-- you must ensure that the three affine traversal laws hold:
--
-- * @sta (sbt (a, s)) ≡ either (Left . const a) Right (sta s)@
--
-- * @either (\a -> sbt (a, s)) id (sta s) ≡ s@
--
-- * @sbt (a2, (sbt (a1, s))) ≡ sbt (a2, s)@
--
-- More generally, a profunctor optic must be monoidal as a natural 
-- transformation:
-- 
-- * @o id ≡ id@
--
-- * @o ('Data.Profunctor.Composition.Procompose' p q) ≡ 'Data.Profunctor.Composition.Procompose' (o p) (o q)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
traversal0 :: (s -> t + a) -> (s -> b -> t) -> Traversal0 s t a b
traversal0 sta sbt = dimap f g . right' . first'
  where f s = (,s) <$> sta s
        g = id ||| (uncurry . flip $ sbt)

-- | Create a 'Traversal0'' from a constructor and a matcher function.
--
traversal0' :: (s -> Maybe a) -> (s -> a -> s) -> Traversal0' s a
traversal0' sa sas = flip traversal0 sas $ \s -> maybe (Left s) Right (sa s)

-- | Obtain a 'Traversal' from a getter and setter.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input functions satisfy the following
-- properties:
--
-- * @sa (sbt s a) ≡ a@
--
-- * @sbt s (sa s) ≡ s@
--
-- * @sbt (sbt s a1) a2 ≡ sbt s a2@
--
-- More generally, a profunctor optic must be monoidal as a natural 
-- transformation:
-- 
-- * @o id ≡ id@
--
-- * @o ('Data.Profunctor.Composition.Procompose' p q) ≡ 'Data.Profunctor.Composition.Procompose' (o p) (o q)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
traversal :: Traversable f => (s -> f a) -> (s -> f b -> t) -> Traversal s t a b
traversal sa sbt = dimap fork (uncurry sbt) . second' . lmap sa . lift traverse

-- | Obtain a 'Traversal1' optic from a getter and setter.
--
-- \( \mathsf{Traversal1}\;S\;A = \exists F : \mathsf{Traversable1}, S \equiv F\,A \)
--
--
traversal1 :: Traversable1 f => (s -> f a) -> (s -> f b -> t) -> Traversal1 s t a b
traversal1 sa sbt = dimap fork (uncurry sbt) . second' . lmap sa . lift traverse1

-- | Transform a Van Laarhoven 'Traversal0' into a profunctor 'Traversal0'.
--
traversing0 :: (forall f. Functor f => (forall c. c -> f c) -> (a -> f b) -> s -> f t) -> Traversal0 s t a b
traversing0 f = dimap (\s -> (match s, s)) (\(ebt, s) -> either (update s) id ebt) . first' . left'
  where
    match s = f Right Left s
    update s b = runIdentity $ f Identity (\_ -> Identity b) s

-- | Transform a Van Laarhoven 'Traversal' into a profunctor 'Traversal'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @abst pure ≡ pure@
--
-- * @fmap (abst f) . abst g ≡ getCompose . abst (Compose . fmap f . g)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
traversing :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> Traversal s t a b
traversing abst = lift abst

-- | Transform a Van Laarhoven 'Traversal1' into a profunctor 'Traversal1'.
--
-- /Caution/: In order for the generated family to be well-defined,
-- you must ensure that the traversal1 law holds for the input function:
--
-- * @fmap (abst f) . abst g ≡ getCompose . abst (Compose . fmap f . g)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
traversing1 :: (forall f. Apply f => (a -> f b) -> s -> f t) -> Traversal1 s t a b
traversing1 abst = lift abst

-- | Transform a Van Laarhoven 'Cotraversal' into a profunctor 'Cotraversal'.
--
cotraversing :: (forall f. Functor f => (f a -> b) -> f s -> t) -> Cotraversal s t a b
cotraversing = lower

-- | TODO: Document
--
traversed :: Traversable f => Traversal (f a) (f b) a b
traversed = traversing traverse

-- | Create a 'Traversal1' from a 'Traversable1' functor.
--
traversed1 :: Traversable1 t => Traversal1 (t a) (t b) a b
traversed1 = traversing1 traverse1

-- | TODO: Document
--
cotraversed :: Distributive f => Cotraversal (f a) (f b) a b 
cotraversed = cotraversing cotraverse

---------------------------------------------------------------------
-- 'Traversal0Rep'
---------------------------------------------------------------------

-- | The `Traversal0Rep` profunctor precisely characterizes an 'Traversal0'.
data Traversal0Rep a b s t = Traversal0Rep (s -> t + a) (s -> b -> t)

type ATraversal0 s t a b = Optic (Traversal0Rep a b) s t a b

type ATraversal0' s a = ATraversal0 s s a a

type ARetraversal0 s t a b = Optic (Re (Traversal0Rep t s) a b) s t a b

instance Profunctor (Traversal0Rep u v) where
  dimap f g (Traversal0Rep getter setter) = Traversal0Rep
      (\a -> first g $ getter (f a))
      (\a v -> g (setter (f a) v))

instance Strong (Traversal0Rep u v) where
  first' (Traversal0Rep getter setter) = Traversal0Rep
      (\(a, c) -> first (,c) $ getter a)
      (\(a, c) v -> (setter a v, c))

instance Choice (Traversal0Rep u v) where
  right' (Traversal0Rep getter setter) = Traversal0Rep
      (\eca -> eassocl (second getter eca))
      (\eca v -> second (`setter` v) eca)

instance Sieve (Traversal0Rep a b) (PStore0 a b) where
  sieve (Traversal0Rep sta sbt) s = PStore0 (sbt s) (sta s)

instance Representable (Traversal0Rep a b) where
  type Rep (Traversal0Rep a b) = PStore0 a b

  tabulate f = Traversal0Rep (\s -> info0 (f s)) (\s -> values0 (f s))

data PStore0 a b t = PStore0 (b -> t) (t + a)

values0 :: PStore0 a b t -> b -> t
values0 (PStore0 bt _) = bt

info0 :: PStore0 a b t -> t + a
info0 (PStore0 _ a) = a

instance Functor (PStore0 a b) where
  fmap f (PStore0 bt ta) = PStore0 (f . bt) (first f ta)
  {-# INLINE fmap #-}

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | TODO: Document
--
withTraversal0 :: ATraversal0 s t a b -> ((s -> t + a) -> (s -> b -> t) -> r) -> r
withTraversal0 o f = case o (Traversal0Rep Right $ const id) of Traversal0Rep x y -> f x y

-- | Retrieve the value targeted by a 'Traversal0' or return the original.
--
--
-- Allows the type to change if the optic does not match.
--
-- @
-- 'preview' o ≡ 'either' ('const' 'Nothing') 'id' . 'matchOf' o
-- @
--
matchOf :: ATraversal0 s t a b -> s -> t + a
matchOf o = withTraversal0 o $ \match _ -> match

-- | Reverse match on a 'Reprism' or similar.
--
-- * @rematching . re $ prism _ sa ≡ sa@
--
rematchOf :: ARetraversal0 s t a b -> b -> a + t
rematchOf o = matchOf (re o)

-- | 
--
-- The traversal laws can be stated in terms of 'traverseOf':
-- 
-- Identity:
-- 
-- @
-- traverseOf t (Identity . f) ≡  Identity (fmap f)
-- @
-- 
-- Composition:
-- 
-- @ 
-- Compose . fmap (traverseOf t f) . traverseOf t g ≡ traverseOf t (Compose . fmap f . g)
-- @
--
-- @
-- traverseOf :: Functor f => Lens s t a b -> (a -> f b) -> s -> f t
-- traverseOf :: Applicative f => Traversal s t a b -> (a -> f b) -> s -> f t
-- @
--
traverseOf :: Applicative f => ATraversal f s t a b -> (a -> f b) -> s -> f t
traverseOf p = runStar #. p .# Star

-- | 
--
-- The traversal laws can be stated in terms or 'traverse1Of':
-- 
-- Identity:
-- 
-- @
-- traverse1Of t (Identity . f) ≡  Identity (fmap f)
-- @
-- 
-- Composition:
-- 
-- @ 
-- Compose . fmap (traverse1Of t f) . traverse1Of t g ≡ traverse1Of t (Compose . fmap f . g)
-- @
--
-- @
-- traverse1Of :: Functor f => Lens s t a b -> (a -> f b) -> s -> f t
-- traverse1Of :: Apply f => Traversal1 s t a b -> (a -> f b) -> s -> f t
-- @
--
traverse1Of :: Apply f => ATraversal1 f s t a b -> (a -> f b) -> s -> f t
traverse1Of p = runStar #. p .# Star

-- | TODO: Document
--
-- @
-- 'cotraverseOf' $ 'Data.Profuncto.Optic.Grate.grate' (flip 'Data.Distributive.cotraverse' id) ≡ 'Data.Distributive.cotraverse'
-- @
--
cotraverseOf :: Functor f => Optic (Costar f) s t a b -> (f a -> b) -> (f s -> t)
cotraverseOf p = runCostar #. p .# Costar

-- | TODO: Document
--
sequenceOf :: Applicative f => ATraversal f s t (f a) a -> s -> f t
sequenceOf t = traverseOf t id

-- | TODO: Document
--
sequence1Of :: Apply f => ATraversal1 f s t (f a) a -> s -> f t
sequence1Of t = traverse1Of t id

-- | TODO: Document
--
distributeOf :: Functor f => ACotraversal f s t a (f a) -> f s -> t
distributeOf t = cotraverseOf t id

---------------------------------------------------------------------
-- Common 'Traversal0's, 'Traversal's, 'Traversal1's, & 'Cotraversal's
---------------------------------------------------------------------

-- | TODO: Document
--
nulled :: Traversal0' s a
nulled = traversal0 Left const 
{-# INLINE nulled #-}

-- | TODO: Document
--
-- See also 'Data.Profunctor.Optic.Prism.keyed'.
--
selected :: (a -> Bool) -> Traversal0' (a, b) b
selected p = traversal0 (\kv@(k,v) -> branch p kv v k) (\kv@(k,_) v' -> if p k then (k,v') else kv)
{-# INLINE selected #-}

-- | Filter result(s) that don't satisfy a predicate.
--
-- /Caution/: While this is a valid 'Traversal0', it is only a valid 'Traversal'
-- if the predicate always evaluates to 'True' on the targets of the 'Traversal'.
--
-- @
-- 'predicated' p ≡ 'traversing0' $ \point f a -> if p a then f a else point a
-- @
--
-- >>> [1..10] ^.. fold id . predicated even
-- [2,4,6,8,10]
--
-- See also 'Data.Profunctor.Optic.Prism.filtered'.
--
predicated :: (a -> Bool) -> Traversal0' a a
predicated p = traversal0 (branch' p) (flip const)
{-# INLINE predicated #-}

-- | Traverse both parts of a 'Bitraversable' container with matching types.
--
-- >>> traverseOf bitraversed (pure . length) (Right "hello")
-- Right 5
--
-- >>> traverseOf bitraversed (pure . length) ("hello","world")
-- (5,5)
--
-- >>> ("hello","world") ^. bitraversed
-- "helloworld"
--
-- @
-- 'bitraversed' :: 'Traversal' (a , a) (b , b) a b
-- 'bitraversed' :: 'Traversal' (a + a) (b + b) a b
-- @
--
bitraversed :: Bitraversable f => Traversal (f a a) (f b b) a b
bitraversed = lift $ \f -> bitraverse f f
{-# INLINE bitraversed #-}

-- | Traverse both parts of a 'Bitraversable1' container with matching types.
--
-- Usually that type will be a pair.
--
-- @
-- 'bitraversed1' :: 'Traversal1' (a, a)       (b, b)       a b
-- 'bitraversed1' :: 'Traversal1' ('Either' a a) ('Either' b b) a b
-- @
--
bitraversed1 :: Bitraversable1 r => Traversal1 (r a a) (r b b) a b
bitraversed1 = lift $ \f -> bitraverse1 f f
{-# INLINE bitraversed1 #-}

-- | Form a 'Traversal1'' by repeating the input forever.
--
-- @
-- 'repeat' ≡ 'toListOf' 'repeated'
-- @
--
-- >>> take 5 $ 5 ^.. repeated
-- [5,5,5,5,5]
--
-- @
-- repeated :: Fold1 a a
-- @
--
repeated :: Traversal1' a a
repeated = lift $ \g a -> go g a where go g a = g a .> go g a
{-# INLINE repeated #-}

-- | @x '^.' 'iterated' f@ returns an infinite 'Traversal1'' of repeated applications of @f@ to @x@.
--
-- @
-- 'toListOf' ('iterated' f) a ≡ 'iterate' f a
-- @
--
-- >>> take 3 $ (1 :: Int) ^.. iterated (+1)
-- [1,2,3]
--
-- @
-- iterated :: (a -> a) -> 'Fold1' a a
-- @
iterated :: (a -> a) -> Traversal1' a a
iterated f = lift $ \g a0 -> go g a0 where go g a = g a .> go g (f a)
{-# INLINE iterated #-}

-- | Transform a 'Traversal1'' into a 'Traversal1'' that loops lift its elements repeatedly.
--
-- >>> take 7 $ (1 :| [2,3]) ^.. cycled traversed1
-- [1,2,3,1,2,3,1]
--
-- @
-- cycled :: 'Fold1' s a -> 'Fold1' s a
-- @
cycled :: Apply f => ATraversal1' f s a -> ATraversal1' f s a
cycled o = lift $ \g a -> go g a where go g a = (traverse1Of o g) a .> go g a
{-# INLINE cycled #-}

---------------------------------------------------------------------
-- Derived operators
---------------------------------------------------------------------

-- | Test whether the optic matches or not.
--
-- >>> isMatched just Nothing
-- False
--
isMatched :: ATraversal0 s t a b -> s -> Bool
isMatched o = either (const False) (const True) . matchOf o

-- | Test whether the optic matches or not.
--
-- >>> isntMatched just Nothing
-- True
--
isntMatched :: ATraversal0 s t a b -> s -> Bool
isntMatched o = either (const True) (const False) . matchOf o

