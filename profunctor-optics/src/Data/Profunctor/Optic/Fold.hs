module Data.Profunctor.Optic.Fold where

import Data.Foldable (traverse_)
import Data.Profunctor.Optic.Type 
import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Getter (view, to)

import Data.DList (DList)
import qualified Data.DList as L
import Data.DList.NonEmpty (NonEmptyDList)
import Data.List.NonEmpty (NonEmpty(..))
--import qualified Data.List.NonEmpty as NEL
import qualified Data.DList.NonEmpty as NEL

import Data.List (foldr, unfoldr)
import Data.Profunctor.Optic.Review
import Data.Profunctor.Optic.Grate (unfoldMapOf)
import Data.Functor.Foldable
---------------------------------------------------------------------
-- 'Fold'
---------------------------------------------------------------------

{-

A 'Fold' can interpret 'a' in a monoid so long as 's' can also be interpreted that way.

Fold laws:

fold_complete :: Fold s a -> Bool
fold_complete o = tripping o $ folding (toListOf o)
-}

--folded :: Foldable f => Fold (f a) a
--folded = folding id
foldLike :: ((a -> r) -> s -> r) -> FoldLike r s a
foldLike = between (ustar Const) (dstar getConst)

-- recursing :: FoldLike r (Mu []) [r]
recursing :: Recursive s => FoldLike r s (Base s r)
recursing = foldLike fold

-- | Obtain a 'Fold' by lifting an operation that returns a 'Foldable' result.
--
-- This can be useful to lift operations from @Data.List@ and elsewhere into a 'Fold'.
--
-- >>> [1,2,3,4] ^.. folding tail
-- [2,3,4]
--
folding :: Foldable f => (s -> f a) -> Fold s a
folding f = rcoerce . lmap f . wander traverse_
{-# INLINE folding #-}

-- | Obtain a 'Fold' using a 'Traversable' functor.
--
-- @
-- 'folding'' f ≡ 'traverse'' . 'lmap' f . 'rcoerce'
-- 'folding'' f ≡ 'wander' 'traverse' . 'to' f
-- @
--
folding' :: Traversable f => (s -> a) -> Fold (f s) a
folding' f = wander traverse . to f

--type Unfold t b = forall p. Distributive (Corep p) => Contravariant (Corep p) => Recursive (Corep p a1) => Base (Corep p a1) ~ Corep p => Under' p t b

--Found hole: _ :: (b -> Rep p b) -> t -> Rep p b

--Found hole: _ :: (b -> Rep p b) -> t -> Rep p (f b)
--cofolding :: (f b -> t) -> Unfold t b
--
{-
unfoldMapOf :: UnfoldLike r t b -> (r -> b) -> r -> t
unfoldMapOf = between (dcostar Const) (ucostar getConst) 



foo
  :: (Corepresentable p, Contravariant (Corep p), Corecursive b) =>
     p a (Base b (Corep p a)) -> p c b
foo = lcoerce . cowander ana

bar
  :: (Representable p, Contravariant (Rep p), Recursive a) =>
     p (Base a (Rep p b)) b -> p a c
rcoerce . wander cata


-- | Mutumorphism
mutu :: Recursive t => (Base t (b, a) -> b) -> (Base t (b, a) -> a) -> t -> a
mutu f g = snd . cata (f &&& g)

-- | A monadic catamorphism
cataM :: (Recursive t, Traversable (Base t), Monad m) => (Base t a -> m a) -> (t -> m a)
cataM phi = c where c = phi <=< (traverse c . project)

-- | A monadic anamorphism
anaM :: (Corecursive t, Traversable (Base t), Monad m) => (a -> m (Base t a)) -> (a -> m t)
anaM psi = a where a = (fmap embed . traverse a) <=< psi

-- | A monadic hylomorphism
hyloM :: (Functor f, Monad m, Traversable f) => (f b -> m b) -> (a -> m (f a)) -> a -> m b
hyloM phi psi = h where h = phi <=< traverse h <=< psi

cofolding
  :: Contravariant (Corep p)
  => Recursive (Corep p a2)
  => Base (Corep p a2) ~ Corep p
  => (a2 -> b) -> p a2 a2 -> p c b
cofolding f = lcoerce . rmap f . cowander cata

class Unfoldable f where
  fromList :: [a] -> f a
  fromList xs = cofold (\cons unit -> foldr cons unit xs)

  cofold :: (forall b. (a -> b -> b) -> b -> b) -> f a
  cofold g = fromList (g (:) [])

  singleton :: a -> f a
  singleton = fromList . (:[])
-}

foo :: Under p b [t] b (Maybe (t, Corep p b))
foo = cowander unfoldr



--foldr c n (cofold g) === g c n

type FoldList a = forall b. (a -> b -> b) -> b -> b

toFoldList :: [a] -> FoldList a
toFoldList xs = \cons unit -> foldr cons unit xs

fromFoldList :: FoldList a -> [a]
fromFoldList fl = fl (:) []

type Cata s t = forall p. Corecursive t => Under p s t s (Base t (Corep p s))

type Ana s t = forall p. Recursive s => Over p s t (Base s (Rep p t)) t

type AnaFix f a = forall p. Over p (Fix f) a (f (Rep p a)) a

type AnaFix' a = forall p. Over p (Fix (Rep p)) a (Rep p (Rep p a)) a

--folded :: Recursive s => Over p s t (Base s (Rep p t)) t
folded' :: AnaFix' a
folded' = wander fold

folded :: Functor f => AnaFix f a
folded = wander fold

unfolded :: Cata s t
unfolded = cowander unfold

bicata :: Functor f => Bistar Identity f (Identity a) (f a)
bicata = Bistar distCata

biana :: Functor f => Bistar f Identity (f a) (Identity a)
biana = Bistar distAna

biapo :: Recursive t => Bistar (Base t) (Either t) (Base t a) (Either t a)
biapo = Bistar distApo

bipara :: Corecursive t => Bistar ((,) t) (Base t) (t, a) (Base t a)
bipara = Bistar distPara

--bihisto :: Functor f => Bistar (Cofree f) f (Cofree f a) (f a)
--bihisto = Bistar distHisto

--bifutu :: Functor f => Bistar f (Free f) (f a) (Free f a)
--bifutu = Bistar distFutu

unfoldLike :: ((r -> b) -> r -> t) -> UnfoldLike r t b
unfoldLike = between (ucostar getConst) (dcostar Const) 

-- corecursing :: Functor f => UnfoldLike a (Fix f) (f a)
corecursing :: Corecursive t => UnfoldLike a t (Base t a)
corecursing = unfoldLike unfold

unfolding :: Distributive g => (b -> t) -> Unfold (g t) b
unfolding f = cowander cotraverse . unto f

cloneUnfold :: AReview t b -> Unfold t b
cloneUnfold = unto . review

fooOf :: UnfoldLike b (DList t) (DList b) -> b -> [t]
fooOf o = flip L.apply [] . unfoldMapOf o L.singleton 

fromPureOf :: Applicative f => UnfoldLike r t (f r) -> r -> t
fromPureOf = flip unfoldMapOf pure

unfoldOf :: AReview t b -> b -> t
unfoldOf = flip unfoldMapOf id

cloneFold :: FoldLike a s a -> Fold s a
cloneFold = to . view

-- @
-- toPureOf :: Fold s a -> s -> [a]
-- toPureOf :: (Applicative f, Monoid (f a)) => Fold s a -> s -> f a
-- toPureOf :: Applicative f => Setter s t a b -> s -> f a
-- @
toPureOf :: Applicative f => FoldLike (f a) s a -> s -> f a
toPureOf = flip foldMapOf pure

---------------------------------------------------------------------
-- 'Fold1'
---------------------------------------------------------------------

{-
A 'Fold1' can interpret 'a' in a semigroup so long as 's' can also be interpreted that way.


Fold1 laws:

fold_complete :: Fold1 s a -> Bool
fold_complete o = tripping o $ folding1 (toNelOf o)
-}

{-

-- folding1 (0 :|) :: Fold1 [Int] Int
folding1 :: Foldable1 f => (s -> f a) -> Fold1 s a
folding1 f = to f . wander1 traverse1_

-- folding1' First :: Traversable1 f => Fold1 (f a) (First a)
-- folding1' Min :: Traversable1 f => Fold1 (f a) (Min a)
folding1' :: Traversable1 f => (s -> a) -> Fold1 (f s) a
folding1' f = wander1 traverse1 . to f


folded1 :: Foldable1 f => Fold1 (f a) a
folded1 = folding1 id

foldMapping :: ((a -> r) -> s -> r) -> FoldLike r s a
foldMapping = between (ustar Const) (dstar getConst) 

cloneFold1 :: Semigroup a => FoldLike a s a -> Fold1 s a
cloneFold1 = to . view
-}

---------------------------------------------------------------------
-- Primitive Operators
---------------------------------------------------------------------

-- | Map each part of a structure viewed through a 'Lens', 'Getter',
-- 'Fold' or 'Traversal' to a monoid and combine the results.
--
-- >>> foldMapOf both id (["foo"], ["bar", "baz"])
-- ["foo","bar","baz"]
--
-- @
-- 'Data.Foldable.foldMap' = 'foldMapOf' 'folded'
-- @
--
-- @
-- 'foldMapOf' ≡ 'views'
-- @
--
-- @
-- 'foldMapOf' ::                  'Iso'' s a        -> (a -> r) -> s -> r
-- 'foldMapOf' ::                  'Lens'' s a       -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Monoid' r    => 'Prism'' s a      -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Monoid' r    => 'Traversal'' s a  -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Monoid' r    => 'Affine'' s a -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Semigroup' r => 'Traversal1'' s a -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Monoid' r    => 'Fold' s a        -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Semigroup' r => 'Fold1' s a       -> (a -> r) -> s -> r
-- @
--
-- @
-- 'foldMapOf' :: 'AFold' r s a -> (a -> r) -> s -> r
-- @
foldMapOf :: FoldLike r s a -> (a -> r) -> s -> r
foldMapOf = between (dstar getConst) (ustar Const)

-- | Collects the foci of a `Fold` into a list.
toListOf :: FoldLike (DList a) s a -> s -> [a]
toListOf o = flip L.apply [] . foldMapOf o L.singleton 

-- | Extract a 'NonEmpty' of the targets of 'Fold1'.
--
-- >>> toNelOf both1 ("hello", "world")
-- "hello" :| ["world"]
--
-- @
-- 'toNelOf' :: 'Getter' s a        -> s -> NonEmpty a
-- 'toNelOf' :: 'Fold1' s a       -> s -> NonEmpty a
-- 'toNelOf' :: 'Lens'' s a       -> s -> NonEmpty a
-- 'toNelOf' :: 'Iso'' s a        -> s -> NonEmpty a
-- 'toNelOf' :: 'Traversal1'' s a -> s -> NonEmpty a
-- 'toNelOf' :: 'Prism'' s a      -> s -> NonEmpty a
-- @
toNelOf :: FoldLike (NonEmptyDList a) s a -> s -> NonEmpty a
toNelOf o = flip NEL.apply [] . foldMapOf o NEL.singleton

