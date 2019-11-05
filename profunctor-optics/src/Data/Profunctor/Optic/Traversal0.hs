{-# LANGUAGE TupleSections #-}
module Data.Profunctor.Optic.Traversal0 where

import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Prelude

---------------------------------------------------------------------
-- 'Traversal0'
---------------------------------------------------------------------

-- | Create a 'Traversal0' from a constructor and a matcher.
--
-- \( \quad \mathsf{Traversal0}\;S\;A =\exists C, D, S \cong D + C \times A \)
--
-- /Caution/: In order for the 'Traversal0' to be well-defined,
-- you must ensure that the three affine traversal laws hold:
--
-- * @sta (sbt (a, s)) ≡ either (Left . const a) Right (sta s)@
--
-- * @either (\a -> sbt (a, s)) id (sta s) ≡ s@
--
-- * @sbt (a2, (sbt (a1, s))) ≡ sbt (a2, s)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
traversal0 :: (s -> t + a) -> (s -> b -> t) -> Traversal0 s t a b
traversal0 sta sbt = dimap f g . pright . pfirst
  where f s = (,s) <$> sta s
        g = id ||| (uncurry . flip $ sbt)

-- | Create a 'Traversal0'' from a constructor and a matcher function.
--
traversal0' :: (s -> Maybe a) -> (s -> a -> s) -> Traversal0' s a
traversal0' sa sas = flip traversal0 sas $ \s -> maybe (Left s) Right (sa s)

-- | Transform a Van Laarhoven 'Traversal0' into a profunctor 'Traversal0'.
--
traversal0VL :: (forall f. Functor f => (forall r. r -> f r) -> (a -> f b) -> s -> f t) -> Traversal0 s t a b
traversal0VL f = dimap (\s -> (match s, s)) (\(ebt, s) -> either (update s) id ebt) . pfirst . pleft
  where
    match s = f Right Left s
    update s b = runIdentity $ f Identity (\_ -> Identity b) s

---------------------------------------------------------------------
-- 'Traversal0Rep'
---------------------------------------------------------------------

-- | The `Traversal0Rep` profunctor precisely characterizes an 'Traversal0'.
data Traversal0Rep a b s t = Traversal0Rep (s -> t + a) (s -> b -> t)

type ATraversal0 s t a b = Optic (Traversal0Rep a b) s t a b

type ATraversal0' s a = ATraversal0 s s a a

type ARetraversal0 s t a b = Optic (Re (Traversal0Rep t s) a b) s t a b

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
      (\eca -> assocl' (second getter eca))
      (\eca v -> second (`setter` v) eca)

instance Sieve (Traversal0Rep a b) (PStore0 a b) where
  sieve (Traversal0Rep sta sbt) s = PStore0 (sbt s) (sta s)

instance Representable (Traversal0Rep a b) where
  type Rep (Traversal0Rep a b) = PStore0 a b

  tabulate f = Traversal0Rep (\s -> info0 (f s)) (\s -> values0 (f s))

data PStore0 a b t = PStore0 (b -> t) (t + a)

values0 :: PStore0 a b t -> b -> t
values0 (PStore0 bt _) = bt

info0 :: PStore0 a b t -> t + a
info0 (PStore0 _ a) = a

instance Functor (PStore0 a b) where
  fmap f (PStore0 bt ta) = PStore0 (f . bt) (first f ta)
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

-- | Reverse match on a 'Reprism' or similar.
--
-- * @rematching . re $ prism _ sa ≡ sa@
--
rematchOf :: ARetraversal0 s t a b -> b -> a + t
rematchOf o = matchOf (re o)

-- | Test whether the optic matches or not.
--
-- >>> isMatched _Just Nothing
-- False
--
isMatched :: ATraversal0 s t a b -> s -> Bool
isMatched o = either (const False) (const True) . matchOf o

-- | Test whether the optic matches or not.
--
-- >>> isntMatched _Just Nothing
-- True
--
isntMatched :: ATraversal0 s t a b -> s -> Bool
isntMatched o = either (const True) (const False) . matchOf o

---------------------------------------------------------------------
-- Common affine traversals
---------------------------------------------------------------------

-- | TODO: Document
--
nulled :: Traversal0' s a
nulled = traversal0 Left const 

-- | Filter result(s) that don't satisfy a predicate.
--
-- /Caution/: While this is a valid 'Traversal0', it is only a valid 'Traversal'
-- if the predicate always evaluates to 'True' on the targets of the 'Traversal'.
--
-- @
-- 'filtered0' p ≡ 'vltraversal0' $ \point f a -> if p a then f a else point a
-- @
--
-- >>> [1..10] ^.. fold id . filtered0 even
-- [2,4,6,8,10]
--
filtered0 :: (a -> Bool) -> Traversal0' a a
filtered0 p = traversal0 (branch' p) (flip const)

-- | TODO: Document
--
selected0 :: (a -> Bool) -> Traversal0' (a, b) b
selected0 p = traversal0 (\kv@(k,v) -> branch p kv v k) (\kv@(k,_) v' -> if p k then (k,v') else kv)
