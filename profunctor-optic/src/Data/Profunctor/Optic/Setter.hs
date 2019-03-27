{-# LANGUAGE DeriveFunctor #-}

module Data.Profunctor.Optic.Setter where

import Data.Profunctor.Optic.Types -- (Setter, star)
import Data.Profunctor.Optic.Operators

--setting :: ((a -> b) -> s -> t) -> Setter s t a b
--setting f = roam $ \g s -> tabulate $ \idx -> f (flip index idx . g) s

data Context a b t = Context (b -> t) a deriving Functor

setting :: ((a -> b) -> s -> t) -> Setter s t a b
setting f = dimap (Context id) (\(Context g s) -> f g s) . map'

mapped :: Functor f => Setter (f a) (f b) a b
mapped = setting fmap


{-
    • Couldn't match type ‘Star Data.Functor.Identity.Identity s t’
                     with ‘s -> t’
      Expected type: (a -> b) -> s -> t

-- | Apply a function to the foci of a `Setter` that may vary with the index.
iover :: forall i s t a b. IndexedSetter i s t a b -> (i -> a -> b) -> s -> t
iover l f = l (Indexed $ uncurry f)
-}



{-
set :: ((a -> b) -> c) -> b -> c
-- ^ @
-- set :: Setter s t a b -> b -> s -> t
-- @
set l = l . const
-}

appendOver :: Semigroup a => Setter s t a a -> a -> s -> t
appendOver p = over p . (<>)

--setJust :: Optic (->) s t a (Maybe b) -> b -> s -> t
--setJust :: Setter s t a (Maybe b) -> b -> s -> t
--setJust p = set p . Just

