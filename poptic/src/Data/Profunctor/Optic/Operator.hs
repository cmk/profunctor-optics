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


-- over l id ≡ id
-- over l f . over l g ≡ over l (f . g)
--
-- ^ @
-- over :: Setter s t a b -> (a -> r) -> s -> r
-- over :: Monoid r => Fold s t a b -> (a -> r) -> s -> r
-- @
over :: Optic (->) s t a b -> (a -> b) -> s -> t
over = id


pre :: Previewing s a -> s -> Maybe a
--previewOf' o = runPre . getConst . h where Star h = o (Star $ Const . Pre . Just)
pre o = h where Previewed h = o (Previewed Just)

--between (extract $ runPre . getConst) (insert $ Const . Pre . Just) o id

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


{-
afolding :: (s -> Maybe a) -> AffineFold s a
afolding f = cimap (\s -> maybe (Left s) Right (f s)) Left . right'

folding :: Foldable f => (s -> f a) -> Fold s a
folding f = cimap f (const ()) . wander traverse_

folding' :: Traversable f => (s -> a) -> Fold (f s) a
folding' f = traverse' . cimap f f


-- | Folds over a `Foldable` container.
folded :: Foldable f => Monoid r => Getting r (f a) a
folded (Star Const) = undefined --Star $ Const . foldMap a

-- | Replicates the elements of a fold.
replicated :: Monoid r => Int -> Getting r s a
replicated i (Star (Const a)) = Star (Const (go i a))
  where go 0 _ = mempty
        go n x = x <> go (n - 1) x

-- | Builds a `Fold` using an unfold.
unfolded :: Monoid r => (s -> Maybe (a, s)) -> Getting r s a
unfolded f p = Star (Const go)
  where
  go = maybe mempty (\(a, sn) -> runStar (Const p a <> go sn) . f)

toPureOf
  :: Applicative f 
  => Getting (f a) s a -> s -> f a
toPureOf o = foldMapOf o pure

-- | Collects the foci of a `Fold` into a list.
--toListOf :: Fold (Endo [a]) s t a b -> s -> [a]
toListOf :: Getting (Endo [a]) s a -> s -> [a]
toListOf o = foldrOf o (:) []

(^..) :: s -> Getting (Endo [a]) s a -> [a]
(^..) = flip toListOf

(^?) :: s -> Getting (First a) s a -> Maybe a
(^?) = flip firstOf

-- | The first focus of a `Fold`, if there is any. Synonym for `preview`.
firstOf :: Getting (First a) s a -> s -> Maybe a
firstOf l = getFirst . foldMapOf l (First . pure)

-- | The last focus of a `Fold`, if there is any.
lastOf :: Getting (Last a) s a -> s -> Maybe a
lastOf p = getLast . foldMapOf p (Last . Just)

-- | We can freely convert a 'Getter s (Maybe a)' into an 'AffineFold s a'.
-- getJust :: Getting (Maybe a) s (Maybe a) -> AffineFold s a
getJust :: Choice p => (p (Maybe a) (Maybe b) -> c) -> p a b -> c
getJust o = o . _Just

{-
firstOf
lastOf
previewOf

λ> preview traverse' ["foo", "bar"]
Just "foo"
λ> preview' traverse' ["foo", "bar"]
Just "foobar"

λ> preview traverse' ['a', 'b']
Just 'a'
λ> preview' traverse' ['a', 'b']

<interactive>:262:10: error:
    • No instance for (Semigroup Char)
        arising from a use of ‘traverse'’
-}
preview' :: MonadReader s m => Getting (Maybe a) s a -> m (Maybe a)
preview' = Reader.asks . (`previewOf` id)
-}


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




