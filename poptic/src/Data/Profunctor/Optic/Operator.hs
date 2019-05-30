module Data.Profunctor.Optic.Operator (
    module Data.Profunctor.Optic.Operator
  , swap
) where

import Data.Profunctor.Types
import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Type
import Data.Either.Validation

import Control.Monad.Reader as Reader
import Control.Monad.State as State

import Control.Monad
--import Control.Monad.Reader.Class as Reader




re :: Optic (Re p a b) s t a b -> Optic p b a t s
re o = (between runRe Re) o id


preview :: Previewing s a -> s -> Maybe a
--previewOf' o = runPre . getConst . h where Star h = o (Star $ Const . Pre . Just)
preview o = h where Previewed h = o (Previewed Just)

-- ^ @
-- match :: Traversal s t a b -> s -> Either t a
-- @
match :: Matching a s t a b -> s -> Either t a
match o = h where Matched h = o (Matched Right )

--match o = swap . h where Star h = o (Star Left)
--match = between (extract swap) (insert id Left)

-- | A more restrictive variant of 'match'.
--match' :: Optic (Matched a) s t a b -> s -> Either t a
--match' o = (between Matched runMatched) o Right

validate :: Validating a s t a b -> s -> Validation t a
validate o = swap . h where Star h = o (Star Failure)


previewOf :: AFolding r s a -> (a -> r) -> s -> Maybe r
previewOf = between (extract runPre) (insert $ Pre . Just)

foldMapOf :: Folding r s a -> (a -> r) -> s -> r
foldMapOf = between (extract getConst) (insert Const)

unfoldMapOf :: Unfolding r t b -> (r -> b) -> r -> t
unfoldMapOf = between (coextract Const) (coinsert getConst) 

--getConst . h where Star h = o . forget $ f

--foldMapMOf = (betweenM unforget forget)

--foldMapOf' :: Optic (Forget r) s t a b -> (a -> r) -> s -> r
--foldMapOf' = between runForget Forget






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

traverseOf :: Optic (Star f) s t a b -> (a -> f b) -> s -> f t
traverseOf o f = tf where Star tf = o (Star f)

-- cotraverseOf == between runCostar Costar 
cotraverseOf :: Optic (Costar f) s t a b -> (f a -> b) -> (f s -> t)
cotraverseOf o f = tf where Costar tf = o (Costar f)

zipWithOf :: Optic Zipped s t a b -> (a -> a -> b) -> s -> s -> t
zipWithOf = between runZipped Zipped




