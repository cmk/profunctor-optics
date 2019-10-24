{-# LANGUAGE TupleSections #-}

module Data.Profunctor.Optic.Traversal.Affine where

import Data.Bitraversable 
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Prelude

import Data.Profunctor.Optic.Prism
import Data.Maybe (fromMaybe)
import Data.Functor.Base (NonEmptyF(..))

---------------------------------------------------------------------
-- 'Traversal0'
---------------------------------------------------------------------


-- | Create a 'Traversal0' from a constructor and a matcher.
--
-- \( \quad \mathsf{Traversal0}\;S\;A =\exists C, D, S \cong D + C \times A \)
--
-- /Caution/: In order for the generated affine family to be well-defined,
-- you must ensure that the three lens affine traversal laws hold:
--
-- * @seta (sbt (a, s)) ≡ either (Left . const a) Right (seta s)@
--
-- * @either (\a -> sbt (a, s)) id (seta s) ≡ s@
--
-- * @sbt (a2, (sbt (a1, s))) ≡ sbt (a2, s)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
traversal0 :: (s -> t + a) -> (s -> b -> t) -> Traversal0 s t a b
traversal0 seta sbt = dimap f g . pright . pfirst
  where f s = (,s) <$> seta s
        g = id ||| (uncurry . flip $ sbt)

-- | Create a 'Traversal0'' from a constructor and a matcher function.
--
traversal0' :: (s -> Maybe a) -> (s -> a -> s) -> Traversal0' s a
traversal0' sma sas = flip traversal0 sas $ \s -> maybe (Left s) Right (sma s)

-- | TODO: Document
--
traversing0 :: (forall f. Functor f => (forall r. r -> f r) -> (a -> f b) -> s -> f t) -> Traversal0 s t a b
traversing0 f = dimap (\s -> (match s, s)) (\(ebt, s) -> either (update s) id ebt) . pfirst . pleft
  where
    --match :: s -> Either a t
    match s = f Right Left s
    --update :: s -> b -> t
    update s b = runIdentity $ f Identity (\_ -> Identity b) s



{-
-- https://r6research.livejournal.com/28338.html
class Functor f => Pointed f where
  point :: a -> f a
  point = fmap (id ||| absurd) . distr . Left

  distr :: Either a (f b) -> f (Either a b)
  distr = either (fmap Left . point) (fmap Right)

  distl :: Either (f a) b -> f (Either a b)
  distl = fmap coswp . distr . coswp

distl' :: Traversable f => f (Either b1 b2) -> Either (f b1) b2
distl' = coswp . traverse coswp
-}

---------------------------------------------------------------------
-- 'Traversal0Rep'
---------------------------------------------------------------------

-- | The `Traversal0Rep` profunctor precisely characterizes an 'Traversal0'.
data Traversal0Rep a b s t = Traversal0Rep (s -> t + a) (s -> b -> t)

type ATraversal0 s t a b = Optic (Traversal0Rep a b) s t a b

type ATraversal0' s a = ATraversal0 s s a a

type ARetraversal0 s t a b = Optic (Re (Traversal0Rep t s) a b) s t a b

idTraversal0Rep :: Traversal0Rep a b a b
idTraversal0Rep = Traversal0Rep Right (\_ -> id)

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
        (\eca -> assocl (second getter eca))
        (\eca v -> second (`setter` v) eca)

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | TODO: Document
--
withTraversal0 :: ATraversal0 s t a b -> ((s -> t + a) -> (s -> b -> t) -> r) -> r
withTraversal0 o f = case o (Traversal0Rep Right $ const id) of Traversal0Rep x y -> f x y

-- | Retrieve the value targeted by a 'Traversal0' or return the original
-- value while allowing the type to change if it does not match.
--
-- @
-- 'preview' o ≡ 'either' ('const' 'Nothing') 'id' . 'matching' o
-- @
--
matching :: ATraversal0 s t a b -> s -> t + a
matching o = withTraversal0 o $ \match _ -> match

-- | Test whether the optic matches or not.
--
isMatched :: ATraversal0 s t a b -> s -> Bool
isMatched o = either (const False) (const True) . matching o

-- | Reverse match on a 'Reprism' or similar.
--
-- * @rematching . re $ prism _ sa ≡ sa@
--
rematching :: ARetraversal0 s t a b -> b -> a + t
rematching o = matching (re o)

---------------------------------------------------------------------
-- Common traversing0 traversals
---------------------------------------------------------------------

nulled :: Traversal0' s a
nulled = traversal0 Left const 

-- | Obtain a 'Traversal0' that can be composed with to filter another 'Lens', 'Iso', 'View', 'Fold' (or 'Traversal').
--
-- >>> [1..10] ^.. folding id . filtering even
-- [2,4,6,8,10]
--
filtering :: (s -> Bool) -> Traversal0' s s
filtering p = traversal0 (branch' p) (flip const)

selecting :: (k -> Bool) -> Traversal0' (k, v) v
selecting p = traversal0 (\kv@(k,v) -> branch p kv v k) (\kv@(k,_) v' -> if p k then (k,v') else kv)
