{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Traversal (
    -- * Types
    Traversal
  , Traversal'
  , ATraversal
  , ATraversal'
  , Cotraversal
  , Cotraversal'
  , ACotraversal
  , ACotraversal'
  , Traversal0
  , Traversal0'
  , ATraversal0 
  , ATraversal0'
  , Traversal1
  , Traversal1'
  , ATraversal1
  , ATraversal1'
    -- * Indxed Types
  , Ixtraversal
  , Ixtraversal'
  , Cxtraversal
  , Cxtraversal'
  , Ixtraversal0
  , Ixtraversal0'
    -- * Constructors
  , traversal
  , traversing
  , traversalVl
  , cotraversal
  , cotraversing
  , retraversing
  , cotraversalVl
  , traversal0
  , traversal0'
  , traversal0Vl
  , traversal1
  , traversal1Vl
    -- * Indexed Constructors
  , itraversal0
  , itraversal
  , itraversal0Vl
  , itraversalVl
  , itraversalVl'
  , indexing
  , ktraversalVl
    -- * Representatives
  , Traversal0Rep(..)
    -- * Primitive operators
  , withTraversal0
  , matchOf
  , traverseOf
  , traverse1Of
  , cotraverseOf
  , sequenceOf
  , sequence1Of
  , distributeOf
    -- * Common optics
  , traversed
  , traversed1
  , cotraversed
  , nulled
  , both
  , both1
  , duplicated
  , bitraversed
  , bitraversed1
  , selected
  , predicated
  , repeated 
  , iterated
  , cycled 
  , iat
    -- * Derived operators
  , matches
) where

import Data.Bifunctor (first, second)
import Data.Bitraversable
import Data.Semigroup.Bitraversable
import Data.Profunctor.Optic.Lens hiding (first, second, unit)
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Grate
import Data.Profunctor.Optic.Type
import Data.Semiring
import Control.Monad.Trans.State

import Data.List.Index

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> import Data.Maybe
-- >>> import Data.List.NonEmpty (NonEmpty(..))
-- >>> import qualified Data.List.NonEmpty as NE
-- >>> import Data.Functor.Identity
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- 'Traversal', 'Cotraversal', 'Traversal0' & 'Traversal1'
---------------------------------------------------------------------

-- | Obtain a 'Traversal' directly. 
--
traversal :: Traversable f => (s -> f a) -> (s -> f b -> t) -> Traversal s t a b
traversal sa sbt = lens sa sbt . repn traverse

-- | Obtain a 'Traversal' by lifting a lens getter and setter into a 'Traversable' functor.
--
-- The resulting optic can detect copies of the lens stucture inside
-- any 'Traversable' container. For example:
--
-- >>> lists (traversing snd $ \(s,_) b -> (s,b)) [(0,'f'),(1,'o'),(2,'o'),(3,'b'),(4,'a'),(5,'r')]
-- "foobar"
--
-- @
--  'withLens' o 'traversing' ≡ 'traversed' . o
-- @
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
traversing :: Traversable f => (s -> a) -> (s -> b -> t) -> Traversal (f s) (f t) a b
traversing bsa bt = repn traverse . lens bsa bt

-- | Obtain a profunctor 'Traversal' from a Van Laarhoven 'Traversal'.
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
traversalVl :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> Traversal s t a b
traversalVl abst = tabulate . abst . sieve

-- | Obtain a 'Cotraversal' directly. 
--
cotraversal :: Distributive g => (g b -> s -> g a) -> (g b -> t) -> Cotraversal s t a b
cotraversal bsa bt = relens bsa bt . corepn cotraverse

-- | Obtain a 'Cotraversal' by lifting a grate continuation into a 'Distributive' functor. 
--
-- @
--  'withGrate' o 'cotraversing' ≡ 'cotraversed' . o
-- @
--
cotraversing :: Distributive g => (((s -> a) -> b) -> t) -> Cotraversal (g s) (g t) a b
cotraversing sabt = corepn cotraverse . grate sabt

-- | Obtain a 'Cotraversal' by lifting a reversed lens getter and setter into a 'Distributive' functor.
--
-- @
--  'withRelens' o 'retraversing' ≡ 'cotraversed' . o
-- @
--
retraversing :: Distributive g => (b -> s -> a) -> (b -> t) -> Cotraversal (g s) (g t) a b
retraversing bsa bt = corepn cotraverse . relens bsa bt 

-- | Obtain a profunctor 'Cotraversal' from a Van Laarhoven 'Cotraversal'.
--
cotraversalVl :: (forall f. ComonadApply f => (f a -> b) -> f s -> t) -> Cotraversal s t a b
cotraversalVl abst = cotabulate . abst . cosieve 

-- | Create a 'Traversal0' from a constructor and a matcher.
--
-- /Caution/: In order for the 'Traversal0' to be well-defined,
-- you must ensure that the input functions satisfy the following
-- properties:
--
-- * @sta (sbt a s) ≡ either (Left . const a) Right (sta s)@
--
-- * @either (\a -> sbt a s) id (sta s) ≡ s@
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
traversal0 :: (s -> t + a) -> (s -> b -> t) -> Traversal0 s t a b
traversal0 sta sbt = dimap f g . right' . first'
  where f s = (,s) <$> sta s
        g = id ||| (uncurry . flip $ sbt)

-- | Obtain a 'Traversal0'' from a constructor and a matcher function.
--
traversal0' :: (s -> Maybe a) -> (s -> a -> s) -> Traversal0' s a
traversal0' sa sas = flip traversal0 sas $ \s -> maybe (Left s) Right (sa s)

-- | Transform a Van Laarhoven 'Traversal0' into a profunctor 'Traversal0'.
--
traversal0Vl :: (forall f. Functor f => (forall c. c -> f c) -> (a -> f b) -> s -> f t) -> Traversal0 s t a b
traversal0Vl f = dimap (\s -> (match s, s)) (\(ebt, s) -> either (update s) id ebt) . first' . left'
  where
    match s = f Right Left s
    update s b = runIdentity $ f Identity (\_ -> Identity b) s

-- | Obtain a 'Traversal1' optic from a getter and setter.
--
-- \( \mathsf{Traversal1}\;S\;A = \exists F : \mathsf{Traversable1}, S \equiv F\,A \)
--
traversal1 :: Traversable1 f => (s -> f a) -> (s -> f b -> t) -> Traversal1 s t a b
traversal1 sa sbt = lens sa sbt . repn traverse1

-- | Obtain a profunctor 'Traversal1' from a Van Laarhoven 'Traversal1'.
--
-- /Caution/: In order for the generated family to be well-defined,
-- you must ensure that the traversal1 law holds for the input function:
--
-- * @fmap (abst f) . abst g ≡ getCompose . abst (Compose . fmap f . g)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
traversal1Vl :: (forall f. Apply f => (a -> f b) -> s -> f t) -> Traversal1 s t a b
traversal1Vl abst = tabulate . abst . sieve 

---------------------------------------------------------------------
-- 'Ixtraversal0', 'Ixtraversal', 'Ixtraversal1', & 'Cxtraversal'
---------------------------------------------------------------------

itraversal0 :: (s -> t + (i , a)) -> (s -> b -> t) -> Ixtraversal0 i s t a b
itraversal0 stia sbt = itraversal0Vl $ \pur f s -> either pur (fmap (sbt s) . uncurry f) (stia s)

itraversal0' :: (s -> Maybe (i , a)) -> (s -> a -> s) -> Ixtraversal0' i s a
itraversal0' sia = itraversal0 $ \s -> maybe (Left s) Right (sia s) 

-- | Obtain an indexed 'Lens' from an indexed getter and a setter.
--
-- Compare 'traversal' and 'Data.Profunctor.Optic.Lens.ilens'.
--
itraversal :: Monoid i => Traversable f => (s -> (i , f a)) -> (s -> f b -> t) -> Ixtraversal i s t a b
itraversal sia sbt = ilens sia sbt . (repn $ \iab -> traverse (curry iab mempty) . snd)

-- | Transform an indexed Van Laarhoven 'Traversal0' into an indexed profunctor 'Traversal0'.
--
itraversal0Vl :: (forall f. Functor f => (forall c. c -> f c) -> (i -> a -> f b) -> s -> f t) -> Ixtraversal0 i s t a b
itraversal0Vl f = traversal0Vl $ \cc iab -> f cc (curry iab) . snd

-- | Lift an indexed VL traversal into an indexed profunctor traversal.
--
itraversalVl :: (forall f. Applicative f => (i -> a -> f b) -> s -> f t) -> Ixtraversal i s t a b
itraversalVl f = traversalVl $ \iab -> f (curry iab) . snd

-- | Lift a VL traversal into an indexed profunctor traversal that ignores its input.
--
-- Useful as the first optic in a chain when no indexed equivalent is at hand.
--
-- >>> ilists (itraversalVl' traverse . itraversed) ["foo", "bar"]
-- [(0,'f'),(1,'o'),(2,'o'),(0,'b'),(1,'a'),(2,'r')]
-- >>> ilists (itraversed . itraversalVl' traverse) ["foo", "bar"]
-- [(0,'f'),(0,'o'),(0,'o'),(0,'b'),(0,'a'),(0,'r')]
--
itraversalVl' :: Monoid i => (forall f. Applicative f => (a -> f b) -> s -> f t) -> Ixtraversal i s t a b
itraversalVl' f = itraversalVl $ \iab -> f (iab mempty)

-- | Statefully index a traversal.
--
-- >>> ilists (indexing traversed . itraversed) ["foo", "bar"]
-- [(0,'f'),(1,'o'),(2,'o'),(0,'b'),(1,'a'),(2,'r')]
-- >>> ilists (itraversed . indexing traversed) ["foo", "bar"]
-- [(0,'f'),(1,'o'),(2,'o'),(0,'b'),(1,'a'),(2,'r')]
--
indexing :: Monoid i => Semiring i => Traversal s t a b -> Ixtraversal i s t a b
indexing abst =
  itraversalVl $ \f s ->
    flip evalState mempty . getCompose . flip runStar s . abst . Star $ \a ->
      Compose $ (f <$> get <*> pure a) <* modify (<> unit) 

-- | Lift an indexed VL cotraversal into a (co-)indexed profunctor cotraversal.
--
ktraversalVl :: (forall f. ComonadApply f => (k -> f a -> b) -> f s -> t) -> Cxtraversal k s t a b
ktraversalVl f = cotraversalVl $ \kab -> const . f (flip kab)

---------------------------------------------------------------------
-- 'Traversal0Rep'
---------------------------------------------------------------------

-- | The `Traversal0Rep` profunctor precisely characterizes an 'Traversal0'.
data Traversal0Rep a b s t = Traversal0Rep (s -> t + a) (s -> b -> t)

type ATraversal0 s t a b = Optic (Traversal0Rep a b) s t a b

type ATraversal0' s a = ATraversal0 s s a a

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

instance Sieve (Traversal0Rep a b) (Indexed0 a b) where
  sieve (Traversal0Rep sta sbt) s = Indexed0 (sbt s) (sta s)

instance Representable (Traversal0Rep a b) where
  type Rep (Traversal0Rep a b) = Indexed0 a b

  tabulate f = Traversal0Rep (\s -> info0 (f s)) (\s -> values0 (f s))

data Indexed0 a b t = Indexed0 (b -> t) (t + a)

values0 :: Indexed0 a b t -> b -> t
values0 (Indexed0 bt _) = bt

info0 :: Indexed0 a b t -> t + a
info0 (Indexed0 _ a) = a

instance Functor (Indexed0 a b) where
  fmap f (Indexed0 bt ta) = Indexed0 (f . bt) (first f ta)
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
traverseOf o = runStar #. o .# Star

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
traverse1Of o = runStar #. o .# Star

-- | TODO: Document
--
-- @
-- 'cotraverseOf' $ 'Data.Profuncto.Optic.Grate.grate' (flip 'Data.Distributive.cotraverse' id) ≡ 'Data.Distributive.cotraverse'
-- @
--
cotraverseOf :: Functor f => Optic (Costar f) s t a b -> (f a -> b) -> (f s -> t)
cotraverseOf o = runCostar #. o .# Costar

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
distributeOf :: ComonadApply f => ACotraversal f s t a (f a) -> f s -> t
distributeOf t = cotraverseOf t id

---------------------------------------------------------------------
-- Common 'Traversal0's, 'Traversal's, 'Traversal1's, & 'Cotraversal's
---------------------------------------------------------------------

-- | TODO: Document
--
traversed :: Traversable f => Traversal (f a) (f b) a b
traversed = traversalVl traverse

-- | Obtain a 'Traversal1' from a 'Traversable1' functor.
--
traversed1 :: Traversable1 t => Traversal1 (t a) (t b) a b
traversed1 = traversal1Vl traverse1

-- | TODO: Document
--
cotraversed :: Distributive f => Cotraversal (f a) (f b) a b 
cotraversed = cotraversalVl cotraverse

-- | TODO: Document
--
nulled :: Traversal0' s a
nulled = traversal0 Left const 
{-# INLINE nulled #-}

-- | TODO: Document
--
-- >>> traverseOf both (pure . length) ("hello","world")
-- (5,5)
--
both :: Traversal (a , a) (b , b) a b
both p = p **** p

-- | TODO: Document
--
-- >>> traverse1Of both1 (pure . NE.length) ('h' :| "ello", 'w' :| "orld")
-- (5,5)
--
both1 :: Traversal1 (a , a) (b , b) a b
both1 p = dimap fst (,) p <<.>> lmap snd p

-- | Duplicate the results of any 'Fold'. 
--
-- >>> lists (both . duplicated) ("hello","world")
-- ["hello","hello","world","world"]
--
duplicated :: Traversal a b a b
duplicated p = pappend p p

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
bitraversed = repn $ \f -> bitraverse f f
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
bitraversed1 = repn $ \f -> bitraverse1 f f
{-# INLINE bitraversed1 #-}

-- | TODO: Document
--
-- See also 'Data.Profunctor.Optic.Prism.keyed'.
--
-- >>>  preview (selected even) (2, "hi")
-- Just "hi"
-- >>>  preview (selected even) (3, "hi")
-- Nothing
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
-- 'predicated' p ≡ 'traversal0Vl' $ \point f a -> if p a then f a else point a
-- @
--
-- >>> [1..10] ^.. folded . predicated even
-- [2,4,6,8,10]
--
-- See also 'Data.Profunctor.Optic.Prism.filtered'.
--
predicated :: (a -> Bool) -> Traversal0' a a
predicated p = traversal0 (branch' p) (flip const)
{-# INLINE predicated #-}

-- | Obtain a 'Traversal1'' by repeating the input forever.
--
-- @
-- 'repeat' ≡ 'lists' 'repeated'
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
repeated = repn $ \g a -> go g a where go g a = g a .> go g a
{-# INLINE repeated #-}

-- | @x '^.' 'iterated' f@ returns an infinite 'Traversal1'' of repeated applications of @f@ to @x@.
--
-- @
-- 'lists' ('iterated' f) a ≡ 'iterate' f a
-- @
--
-- >>> take 3 $ (1 :: Int) ^.. iterated (+1)
-- [1,2,3]
--
-- @
-- iterated :: (a -> a) -> 'Fold1' a a
-- @
iterated :: (a -> a) -> Traversal1' a a
iterated f = repn $ \g a0 -> go g a0 where go g a = g a .> go g (f a)
{-# INLINE iterated #-}

-- | Transform a 'Traversal1'' into a 'Traversal1'' that loops repn its elements repeatedly.
--
-- >>> take 7 $ (1 :| [2,3]) ^.. cycled traversed1
-- [1,2,3,1,2,3,1]
--
-- @
-- cycled :: 'Fold1' s a -> 'Fold1' s a
-- @
--
cycled :: Apply f => ATraversal1' f s a -> ATraversal1' f s a
cycled o = repn $ \g a -> go g a where go g a = (traverse1Of o g) a .> go g a
{-# INLINE cycled #-}

-- | A 'Traversal0' focused on a given index of a list.
--
-- >>> iset (iat 2) (const 0) [1,2,3 :: Int]
-- [1,2,0]
--
iat :: Int -> Ixtraversal0' Int [a] a
iat i = itraversal0' (ifind $ \n _ -> n == i) $ \s a -> modifyAt i (const a) s

---------------------------------------------------------------------
-- Derived operators
---------------------------------------------------------------------

-- | Test whether the optic matches or not.
--
-- >>> matches just Nothing
-- False
--
matches :: ATraversal0 s t a b -> s -> Bool
matches o = either (const False) (const True) . matchOf o
{-# INLINE matches #-}
