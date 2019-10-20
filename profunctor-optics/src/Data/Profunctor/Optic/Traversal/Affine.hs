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
-- * @seta (sbt (a, s)) === either (Left . const a) Right (seta s)@
--
-- * @either (\a -> sbt (a, s)) id (seta s) === s@
--
-- * @sbt (a2, (sbt (a1, s))) === sbt (a2, s)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
atraversing :: (s -> t + a) -> (s -> b -> t) -> Traversal0 s t a b
atraversing seta sbt = dimap f g . right' . first'
  where f s = (,s) <$> seta s
        g = id ||| (uncurry . flip $ sbt)

-- | Create a 'Traversal0'' from a constructor and a matcher function.
--
atraversing' :: (s -> Maybe a) -> (s -> a -> s) -> Traversal0' s a
atraversing' sma sas = flip atraversing sas $ \s -> maybe (Left s) Right (sma s)

---------------------------------------------------------------------
-- 'Traversal0Rep'
---------------------------------------------------------------------

-- | The `Traversal0Rep` profunctor precisely characterizes an 'Traversal0'.
data Traversal0Rep a b s t = Traversal0Rep (s -> t + a) (s -> b -> t)

type ATraversal0 s t a b = Optic (Traversal0Rep a b) s t a b

type ATraversal0' s a = ATraversal0 s s a a

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

-- ^ @
-- matchOf :: Traversal0 s t a b -> s -> Either t a
-- matchOf :: Traversal s t a b -> s -> Either t a
-- @
--
matchOf :: AMatch a s t a b -> s -> Either t a
matchOf o = between (dstar coswp) (ustar Left) o id

-- | Test whether the optic matches or not.
isMatched :: AMatch a s t a b -> s -> Bool
isMatched o = either (const False) (const True) . matchOf o

-- | Test whether the optic matches or not.
isntMatched :: AMatch a s t a b -> s -> Bool
isntMatched o = not . isMatched o

---------------------------------------------------------------------
-- Common atraversing traversals
---------------------------------------------------------------------

nulled :: Traversal0' s a
nulled = atraversing Left const 

-- | Obtain a 'Traversal0' that can be composed with to filter another 'Lens', 'Iso', 'Getter', 'Fold' (or 'Traversal').
--
-- >>> [1..10] ^.. folding id . filtering even
-- [2,4,6,8,10]
--
filtering :: (s -> Bool) -> Traversal0' s s
filtering p = atraversing (branch' p) (flip const)
{-# INLINE filtering #-}

selecting :: (k -> Bool) -> Traversal0' (k, v) v
selecting p = atraversing (\kv@(k,v) -> branch p kv v k) (\kv@(k,_) v' -> if p k then (k,v') else kv)
