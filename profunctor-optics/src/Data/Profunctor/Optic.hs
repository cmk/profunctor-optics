module Data.Profunctor.Optic (
    module Type
  , module Operator
  , module Property
  , module Iso
  , module Lens
  , module Prism
  , module Grate
  , module Repn
  , module Traversal
  , module Fold
  , module View
  , module Setter
  , module Indexed
  , module Data.Profunctor.Optic
) where

import Data.Profunctor.Optic.Type             as Type
import Data.Profunctor.Optic.Operator         as Operator
import Data.Profunctor.Optic.Property         as Property
import Data.Profunctor.Optic.Iso              as Iso
import Data.Profunctor.Optic.Lens             as Lens
import Data.Profunctor.Optic.Prism            as Prism
import Data.Profunctor.Optic.Grate            as Grate
import Data.Profunctor.Optic.Repn             as Repn
import Data.Profunctor.Optic.Traversal        as Traversal
import Data.Profunctor.Optic.Fold             as Fold
import Data.Profunctor.Optic.View             as View
import Data.Profunctor.Optic.Setter           as Setter
import Data.Profunctor.Optic.Indexed          as Indexed

import Control.Monad.State 
import Control.Monad.Reader
import Data.Monoid
import Data.Profunctor.Optic.Import
import Data.Semiring
import Prelude (Num(..))

import qualified Data.Bifunctor as B

reindexed' :: Profunctor p => (j -> i) -> (i -> j) -> Iso (Ix p i a b) (Ix p i s t) (Ix p j a b) (Ix p j s t)
reindexed' ji ij = iso (reindex ji) (reindex ij)

{-
λ> :t zipWithOf coindexed (,)
zipWithOf coindexed (,) :: s -> s -> Coindex a (a, a) s

λ> :t constOf coindexed
constOf coindexed :: b -> Coindex a b s

λ> :t constOf (coindexed . coindexed)
constOf (coindexed . coindexed) :: b -> Coindex a1 (Coindex a2 b a1) s
-}


coindexed :: Grate i (Coindex a b i) a b
coindexed = grate Coindex

-- >>> iover (iat 1) (+) [1,2,3 :: Int]
-- [1,3,3]
--
-- >>> iover (iat 5) (+) [1,2,3 :: Int]
-- [1,2,3]
--
iover :: Monoid i => Ixsetter i s t a b -> (i -> a -> b) -> s -> t
iover o f = curry (over o (uncurry f)) mempty

--ktraversing :: (forall f. ComonadApply f => (k -> f a -> b) -> f s -> t) -> Cxtraversal k s t a b
--ktraversing f = cotraversing $ \kab -> const . f (flip kab)


-- >>> kover kclosed (,) (*2) 5
-- ((),10)
--
kover :: Monoid k => Cxsetter k s t a b -> (k -> a -> b) -> s -> t 
kover o f = flip (under o (flip f)) mempty

-- | Set with index. Equivalent to 'iover' with the current value ignored.
--
-- When you do not need access to the index, then 'set' is more liberal in what it can accept.
--
-- @
-- 'set' o ≡ 'iset' o '.' 'const'
-- @
--
-- >>> iset (iat 2) (2-) [1,2,3 :: Int]
-- [1,2,0]
--
-- >>> iset (iat 5) (const 0) [1,2,3 :: Int]
-- [1,2,3]
--
iset :: Monoid i => Ixsetter i s t a b -> (i -> b) -> s -> t
iset o = iover o . (const .)



-- | Build an 'IndexedSetter' from an 'Control.Lens.Indexed.imap'-like function.
--
-- Your supplied function @f@ is required to satisfy:
--
-- @
-- f 'id' ≡ 'id'
-- f g '.' f h ≡ f (g '.' h)
-- @
--
-- Equational reasoning:
--
-- @
-- 'isets' '.' 'iover' ≡ 'id'
-- 'iover' '.' 'isets' ≡ 'id'
-- @
--
-- Another way to view 'isets' is that it takes a \"semantic editor combinator\"
-- which has been modified to carry an index and transforms it into a 'IndexedSetter'.
--isets :: ((i -> a -> b) -> s -> t) -> Ixsetter i s t a b
--isets f = sets (f . indexed)
--{-# INLINE isets #-}

--dimap (uncurry sta) (id ||| const bt) . right'
{-
ileft :: Ixprism i (a + c) (b + c) a b
ileft p = lmap assocl' (left' p)

-- | Obtain an 'Ixprism'' from a reviewer and an indexed matcher function.
--
iprism :: (i -> s -> t + a) -> (b -> t) -> Ixprism i s t a b
iprism ista = prism $ \(i,s) -> fmap (i,) (ista i s)

(p a b -> p s t) -> p (i,a) b -> p (i,s) t


igrateVl :: (forall f. Functor f => (i -> f a -> b) -> f s -> t) -> Ixgrate i s t a b
ifirst :: Ixlens i i (a , c) (b , c) a b
ifirst = runIx . first' . Ix


-}


{-
--primViewOf :: APrimView r s t a b -> ((i , a) -> r) -> (i , s) -> r
--indexOf :: AIxview i s a -> Index a r i -> Index s r i
indexOf :: AIxview i s a -> Index i a r -> Index i s r
--indexOf :: APrimView r s t a b -> Index i a r -> Index i s r
indexOf o (Index i ar) = Index i $ _ o --primViewOf o undefined -- (\(i , a) iar
-- AIxview i s a -> i -> s -> r

-- @
-- 'view' o ≡ 'iview' o '.' 'const'
-- @
--
-}

-- |
-- @
-- 'ito' :: (s -> (i, a)) -> 'Ixview' i s a
-- @
ito :: (s -> (i , a)) -> Ixview i s a
ito f = to $ f . snd
{-# INLINE ito #-}

kfrom :: ((k -> b) -> t) -> Cxview k t b
kfrom f = from $ \kb _ -> f kb
{-# INLINE kfrom #-}

-- | Bring the index and value of a indexed optic into the current environment as a pair.
--
-- >>> iview ifirst ("foo", 42)
-- (Just (),"foo")
--
-- >>>iview (iat 3 . ifirst) [(0,'f'),(1,'o'),(2,'o'),(3,'b'),(4,'a'),(5,'r') :: (Int, Char)]
-- (Just 3,3)
--
-- In order to 'iview' a 'Choice' optic (e.g. 'Ixtraversal0', 'Ixtraversal', 'Ixfold', etc),
-- /a/ must have a 'Monoid' instance:
--
-- >>> iview (iat 0) ([] :: [Int])
-- (Nothing,0)
-- >>> iview (iat 0) ([1] :: [Int])
-- (Just 0,1)
--
-- /Note/ when applied to a 'Ixtraversal' or 'Ixfold', then 'iview' will return a monoidal 
-- summary of the indices tupled with a monoidal summary of the values:
--
-- >>> (iview @_ @_ @Int @Int) itraversed [1,2,3,4]
-- (Just 6,10)
--
iview :: MonadReader s m => Monoid i => AIxview i s a -> m (Maybe i , a)
iview o = asks $ primViewOf o (B.first Just) . (mempty,)
{-# INLINE iview #-}

-- | Bring the index and value of an indexed optic into the current environment as a pair.
--
iuse :: MonadState s m => Monoid i => AIxview i s a -> m (Maybe i , a)
iuse o = gets (iview o)

-- | Bring a function of the index and value of an indexed optic into the current environment.
--
-- 'iviews' ≡ 'ifoldMapOf'
--
-- >>> iview (iat 0 . ifirst)
--
-- >>> iviews (iat 2) (-) ([0,1,2] :: [Int])
-- 0
--
-- In order to 'iviews' a 'Choice' optic (e.g. 'Ixtraversal0', 'Ixtraversal', 'Ixfold', etc),
-- /a/ must have a 'Monoid' instance (here from the 'rings' package):
--
-- >>> iviews (iat 3) (flip const) ([1] :: [Int])
-- 0
--
-- Use 'iview' if there is a need to disambiguate between 'mempty' as a miss or as a return value.
--
-- As with 'iview', applying 'iviews' to an 'Ixfold' the result will be a monoidal summary 
-- instead of a single answer.
--
iviews :: MonadReader s m => Monoid i => AIxfold r i s a -> (i -> a -> r) -> m r
iviews o f = asks $ ifoldMapOf o f

-- | Bring a function of the index and value of an indexed optic into the current environment.
--
iuses :: MonadState s m => Monoid i => AIxfold r i s a -> (i -> a -> r) -> m r
iuses o f = gets $ ifoldMapOf o f

-- | Bring a function of the index of a co-indexed optic into the current environment.
--
kreview :: MonadReader b m => ACxview k t b -> m (k -> t)
kreview o = kreviews o id
 
-- | Bring a continuation of the index of a co-indexed optic into the current environment.
--
kreviews :: MonadReader b m => ACxview k t b -> ((k -> t) -> r) -> m r
kreviews o f = asks $ primReviewOf o f . const

coindexes :: ACxview k t b -> Coindex t r k -> Coindex b r k
coindexes o (Coindex f) = Coindex $ primReviewOf o f



win :: Monoid i => Applicative g => Traversable f => (i -> a -> g b) -> f a -> g (f b)
win iab = traverse (iab mempty)

--TODO is this the right function ? useful?
--jfoldMapOf :: CoindexedOptic' (CofoldRep r) j s a -> (i -> s -> r)
jfoldMapOf :: Monoid i => ACofold (i, r) t b -> (i -> r -> b) -> r -> t
jfoldMapOf o f = cofoldMapOf o (uncurry f)  . (mempty,)




-- | Traversal with an index.
--
-- /NB:/ When you don't need access to the index then you can just apply your 'IndexedTraversal'
-- directly as a function!
--
-- @
-- 'itraverseOf' ≡ 'Data.Profunctor.Optic.Indexed.withIndex'
-- 'Data.Profunctor.Optic.Traversal.traverseOf' l = 'itraverseOf' l '.' 'const' = 'id'
-- @
--
-- @
-- 'itraverseOf' :: 'Functor' f     => 'IndexedLens' i s t a b       -> (i -> a -> f b) -> s -> f t
-- 'itraverseOf' :: 'Applicative' f => 'IndexedTraversal' i s t a b  -> (i -> a -> f b) -> s -> f t
-- 'itraverseOf' :: 'Apply' f       => 'IndexedTraversal1' i s t a b -> (i -> a -> f b) -> s -> f t
-- @
--itraverseOf :: (Indexed i a (f b) -> s -> f t) -> (i -> a -> f b) -> s -> f t
--itraverseOf l = l .# Indexed
--{-# INLINE itraverseOf #-}

{-
reindexed' :: Profunctor p => (j -> i) -> (i -> j) -> Iso (Ix p i a b) (Ix p i s t) (Ix p j a b) (Ix p j s t)

foo = reindexed' fromInteger toInteger
ilists (itrav1 . reindex id . itrav1) ["foo", "bar"]
ilists (itrav1 . (reix fromIntegral itrav2)) ["foo", "bar"]

itrav1 :: Ixtraversal Int [a] [b] a b
itrav1 = itraversed @Int

ifoldsr ifolded (<>) 0 

itrav2 :: Ixtraversal Integer [a] [b] a b
itrav2 = itraversed @Integer
itrav1 
ilists itraversed "foobar"
[(0,'f'),(1,'o'),(2,'o'),(3,'b'),(4,'a'),(5,'r')]

ilists (itraversed . itraversed) ["foo", "bar"]
[(0,'f'),(1,'o'),(2,'o'),(0,'b'),(1,'a'),(2,'r')]

ilists (itraversed . reix (+1) (itraversed @Int)) ["foo", "bar"]
[(1,'f'),(2,'o'),(3,'o'),(1,'b'),(2,'a'),(3,'r')]

ilists (itraversed' @Int) "foobar"
[(0,'f'),(0,'o'),(0,'o'),(0,'b'),(0,'a'),(0,'r')] --rings is in scope


ilists (itraversed . itraversalVl' traverse) ["foo", "bar"]
[(0,'f'),(0,'o'),(0,'o'),(0,'b'),(0,'a'),(0,'r')] -- ideally want 000111 here instead but can live w this

ilists (itraversalVl' traverse . itraversed) ["foo", "bar"]
[(0,'f'),(1,'o'),(2,'o'),(0,'b'),(1,'a'),(2,'r')] 



λ>  ilists @Int (ileft . ileft) (Left (Left "hi"))
[(0,"hi")]
λ>  ilists @Int (ileft . ileft) (Left (Right "hi"))
[]

-- | TODO: Document
--
itraversed :: Monoid i => Traversable f => Ixtraversal i (f a) (f b) a b
itraversed = itraversalVl' traverse

(getConst #.) #. runStar #. o .# Star .# (Const #.)
-}

itraversed :: Ixtraversal Int [a] [b] a b
itraversed = itraversalVl itraverseList

{-
jtraversed :: Distributive f => Cxtraversal j (f a) (f b) a b
jtraversed = undefined

fold0 . preview
sel :: Fold0 (Int, a) a
sel = 

preview (fold0 . preview $ selected even) (2, "yes")
Just "yes"
preview (fold0 . preview $ selected even) (3, "no")
Nothing

-}


itraverseList :: Num n => Applicative f => (n -> a -> f b) -> [a] -> f [b]
itraverseList f = go 0
  where
    go _ []     = pure []
    go i (a:as) = (:) <$> f i a <*> go (i Prelude.+ 1) as

itraversedList :: Num n => Ixtraversal n [a] [b] a b
itraversedList = itraversalVl itraverseList



{-
--in Data.Map.Optic
itraversed :: IndexedOptic p i (Map i a) (Map i b) a b
itraversed = itraversalVl Map.traverseWithKey


-}

