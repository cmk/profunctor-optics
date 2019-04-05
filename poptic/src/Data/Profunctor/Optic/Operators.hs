module Data.Profunctor.Optic.Operators (
    module Data.Profunctor.Optic.Operators
  , swap
) where

import Data.Profunctor.Optic.Types
import Data.Validation

import Control.Monad.Reader as Reader
import Control.Monad.State as State









re :: Optic (Re p a b) s t a b -> Optic p b a t s
re o = (through Re runRe) o id


-- ^ @
-- over :: Setter s t a b -> (a -> r) -> s -> r
-- over :: Monoid r => Fold s t a b -> (a -> r) -> s -> r
-- @
over :: Optic (->) s t a b -> (a -> b) -> s -> t
over = id


-- ^ @
-- review :: Review s t a b -> b -> tb
-- @
--
review :: Optic (Costar (Const b)) s t a b -> b -> t
review o = h . Const where Costar h = o (Costar getConst)



-- | 'view o == foldMapOf o id'
view :: MonadReader s m => Optic (Star (Const a)) s t a b -> m a
view o = Reader.asks $ foldMapOf o id


-- ^ @
-- match :: Traversal s t a b -> s -> Either t a
-- @
match :: Optic (Star (Either a)) s t a b -> s -> Either t a
match o = switch . h where Star h = o (Star Left)

-- | A more restrictive variant of 'match'.
match' :: Optic (Matched a) s t a b -> s -> Either t a
match' o = (through Matched runMatched) o Right




previewOf :: Optic (Star (Pre a)) s t a b -> s -> Maybe a
previewOf o = runPre . h where Star h = o (Star (Pre . Just))

foldMapOf :: Optic (Star (Const r)) s t a b -> (a -> r) -> s -> r
foldMapOf o f = getConst . h where Star h = o (Star (Const . f))

foldMapOf' :: Optic (Forget r) s t a b -> (a -> r) -> s -> r
foldMapOf' = through Forget runForget

-- ^ @
-- traverseOf :: Functor f => Lens s t a b -> (a -> f b) -> s -> f t
-- traverseOf :: Applicative f => Traversal s t a b -> (a -> f b) -> s -> f t
-- @
traverseOf :: Optic (Star f) s t a b -> (a -> f b) -> s -> f t
traverseOf o f = tf where Star tf = o (Star f)

cotraverseOf :: Optic (Costar f) s t a b -> (f a -> b) -> (f s -> t)
cotraverseOf o f = tf where Costar tf = o (Costar f) -- = through Costar runCostar

validateOf
  :: Optic (Star (Validation a)) s t a b 
  -> s 
  -> Validation t a
validateOf o = switch' . h where Star h = o (Star Failure)


zipWithOf :: Optic Zipped s t a b -> (a -> a -> b) -> s -> s -> t
zipWithOf = through Zipped runZipped 


switch'  :: Validation e a -> Validation a e
switch' v = case v of
  Failure e -> Success e
  Success a -> Failure a


-- | Box up a profunctor, map it through an optic, then unbox.
through :: (t1 -> t2) -> (t3 -> t4) -> (t2 -> t3) -> t1 -> t4
through up down optic a = down (optic $ up a)


