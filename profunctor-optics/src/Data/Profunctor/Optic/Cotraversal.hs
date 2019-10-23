module Data.Profunctor.Optic.Cotraversal where

import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Prelude

{-
-- | TODO: Document
--
cotraversing0 :: (forall f. Functor f => (forall r. f r -> r) -> (f a -> b) -> f s -> t) -> Cotraversal0 s t a b
cotraversing0 f = dimap (\s -> (match s, s)) (\(ebt, s) -> either (update s) id ebt) . closed . pleft
  where
    --match :: (b, s) -> t
    match s = f snd fst s
    --update :: Identity s -> Identity b -> Identity a
    update s b = Identity $ f runIdentity (\_ -> runIdentity b) s

dimap (\s -> (match s, s))
  :: Profunctor p => (c -> d) -> p (a, (b, s)) c -> p (b, s) d
-}
---------------------------------------------------------------------
-- 'Cotraversal'
---------------------------------------------------------------------

cotraversed :: Distributive f => Cotraversal (f a) (f b) a b 
cotraversed = lower cotraverse

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- @ cotraverseOf $ grate (flip cotraverse id) == cotraverse @
cotraverseOf :: Optic (Costar f) s t a b -> (f a -> b) -> (f s -> t)
cotraverseOf = between runCostar Costar
