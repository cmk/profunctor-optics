module Data.Profunctor.Optic.Operators (
    module Data.Profunctor.Optic.Operators
  , swap
) where

import Data.Profunctor.Optic.Types


{-





set :: ((a -> b) -> c) -> b -> c
-- ^ @
-- set :: SEC s t a b -> b -> s -> tb
-- @
set l = l . const


toListOf :: Applicative f => Optical (Star (Const (f a))) s t a b -> s -> f a
-- ^ @
-- toListOf :: Fold s t a b -> s -> [a]
-- toListOf :: (Applicative f, Monoid (f a)) => Fold s t a b -> s -> f a
-- toListOf :: Applicative f => To s t a b -> s -> f a
-- @
toListOf l = gets l pure

firstOf :: Optical (Star (Const (First a))) s t a b -> s -> Maybe a
-- ^ @
-- firstOf :: Fold s t a b -> s -> Maybe a
-- @
firstOf l = getFirst . gets l (First . pure)

un :: Optical (ProProduct (Star (Const tb)) (Costar (Const ta))) b a tb ta -> Iso ta tb a b
-- ^ @
-- un :: Iso b a tb ta -> Iso ta tb a b
-- @
un l = iso (review . Const) (getConst . get)
 where
  ProProduct (Star get) (Costar beget) = l (ProProduct (Star Constant) (Costar getConstant))
-}

re :: Optic (Re p a b) s t a b -> Optic p b a t s
re o = (through Re runRe) o id


-- ^ @
-- over :: Setter s t a b -> (a -> r) -> s -> r
-- over :: Monoid r => Fold s t a b -> (a -> r) -> s -> r
-- @
over :: Optic (->) s t a b -> (a -> b) -> s -> t
over = id


-- ^ @
-- review :: Fro s t a b -> b -> tb
-- @
review' :: Optic (Costar (Const b)) s t a b -> b -> t
review' o = h . Const where Costar h = o (Costar getConst)

review :: Optic Tagged s t a b -> b -> t
review = through Tagged unTagged


-- | 'view o == foldMapOf o id'
--view :: Optic (Forget a) s t a b -> s -> a
view o = foldMapOf o id


-- ^ @
-- match :: Traversal s t a b -> s -> Either t a
-- @
match' :: Optic (Star (Either a)) s t a b -> s -> Either t a
match' o = switch . h where Star h = o (Star Left)

match :: Optic (Matched a) s t a b -> s -> Either t a
match o = (through Matched runMatched) o Right



preview :: Optic (Previewed a) s t a b -> s -> Maybe a
preview o = (through Previewed runPreviewed) o Just


foldMapOf :: Optic (Star (Const r)) s t a b -> (a -> r) -> s -> r
foldMapOf o f = getConst . h where Star h = o (Star (Const . f))

foldMapOf' :: Optic (Forget r) s t a b -> (a -> r) -> s -> r
foldMapOf' = through Forget runForget



zipWithOf :: Optic Zipped s t a b -> (a -> a -> b) -> s -> s -> t
zipWithOf = through Zipped runZipped 


-- ^ @
-- traverseOf :: Functor f => Lens s t a b -> (a -> f b) -> s -> f tb
-- traverseOf :: Applicative f => Traversal s t a b -> (a -> f b) -> s -> f tb
-- @
traverseOf' :: Optic (Star f) s t a b -> (a -> f b) -> s -> f t
traverseOf' o f = tf where Star tf = o (Star f)

-- | 'traverseOf' can be used to convert 'Strong' optics to their
-- van Laarhoven equivalents.
traverseOf :: Optic (Star f) s t a b -> (a -> f b) -> s -> f t
traverseOf = through Star runStar

cotraverseOf :: Optic (Costar f) s t a b -> (f a -> b) -> (f s -> t)
cotraverseOf = through Costar runCostar

-- | Box up a profunctor, map it through an optic, then unbox.
through :: (t1 -> t2) -> (t3 -> t4) -> (t2 -> t3) -> t1 -> t4
through up down optic a = down (optic $ up a)


