module Data.Profunctor.Optic.Operator (
    module Data.Profunctor.Optic.Operator
  , swap
) where

import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Type
import Data.Either.Validation

import Control.Monad.Reader as Reader
import Control.Monad.State as State


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






-- ^ @
-- match :: Traversal s t a b -> s -> Either t a
-- @
match :: Optic (Star (Either a)) s t a b -> s -> Either t a
match o = swap . h where Star h = o (Star Left)
--match = between (extract swap) (insert id Left)

-- | A more restrictive variant of 'match'.
--match' :: Optic (Matched a) s t a b -> s -> Either t a
--match' o = (between Matched runMatched) o Right

validate :: Optic (Star (Validation a)) s t a b -> s -> Validation t a
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
-}

--previewOf :: Optic (Star (Pre a)) s t a b -> s -> Maybe a
--previewOf o = between ((runPre .) . runStar) (Star . ((Pre . Just) .)) o id
--previewOf o = runPre . h where Star h = o (Star (Pre . Just))

previewOf :: Semigroup r => Getting (Maybe r) s a -> (a -> r) -> s -> Maybe r
previewOf = between (extract getConst) (insert Const Just)

reviewOf :: Reviewing (Maybe r) t b -> (Maybe r -> b) -> r -> t
reviewOf = between (coextract Just) (coinsert id)

foldMapOf :: Getting r s a -> (a -> r) -> s -> r
foldMapOf = between (extract getConst) (insert Const id)

unfoldMapOf :: Reviewing r t b -> (r -> b) -> r -> t
unfoldMapOf = between (coextract id) (coinsert id) 

--getConst . h where Star h = o . forget $ f

--foldMapMOf = (betweenM unforget forget)

--foldMapOf' :: Optic (Forget r) s t a b -> (a -> r) -> s -> r
--foldMapOf' = between runForget Forget

forget :: (a -> r) -> Star (Const r) a b
forget = insert Const id

unforget :: Star (Const r) a b -> a -> r
unforget = extract getConst

insert :: (a -> f d) -> (b -> a) -> (c -> b) -> Star f c d
insert g f = Star . (g .) . (f .)

extract :: (f c1 -> b) -> Star f a c1 -> a -> b
extract g = (g .) . runStar

coinsert :: (b1 -> b2) -> (b2 -> c) -> Costar (Const b1) d c
coinsert g = Costar . (. getConst) . (. g)


coextract :: (a -> b1) -> Costar (Const b1) b2 c -> a -> c
coextract g = (. g) . (. Const) . runCostar




foo :: Getting r s a -> (a -> r) -> s -> Const r s
foo o = between runStar forget o



{-
The laws for a 'Traversal' follow from the laws for 'Traversable' as stated in "The Essence of the Iterator Pattern".

Identity:

traverseOf t (Identity . f) ≡  Identity (fmap f)

Composition:

Compose . fmap (traverseOf t f) . traverseOf t g ≡ traverseOf t (Compose . fmap f . g)
-}
-- ^ @
-- traverseOf :: Functor f => Lens s t a b -> (a -> f b) -> s -> f t
-- traverseOf :: Applicative f => Traversal s t a b -> (a -> f b) -> s -> f t
-- traverseOf $ _1 . _R :: Applicative f => (a -> f b) -> (Either c a, d) -> f (Either c b, d)
-- @
traverseOf :: Optic (Star f) s t a b -> (a -> f b) -> s -> f t
traverseOf = between runStar Star -- tf where Star tf = o (Star f)

cotraverseOf :: Optic (Costar f) s t a b -> (f a -> b) -> (f s -> t)
cotraverseOf = between runCostar Costar -- o f = tf where Costar tf = o (Costar f) -- = between Costar runCostar

zipWithOf :: Optic Zipped s t a b -> (a -> a -> b) -> s -> s -> t
zipWithOf = between runZipped Zipped








