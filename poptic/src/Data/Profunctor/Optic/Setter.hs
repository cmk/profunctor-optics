{-# LANGUAGE DeriveFunctor #-}

module Data.Profunctor.Optic.Setter (
    module Data.Profunctor.Optic.Setter 
  , module Export
) where


import Data.Profunctor.Optic.Types 
import Data.Profunctor.Optic.Operators

import Data.Profunctor.Mapping as Export

---------------------------------------------------------------------
-- Setter
---------------------------------------------------------------------

--setting :: ((a -> b) -> s -> t) -> Setter s t a b
--setting f = roam $ \g s -> tabulate $ \idx -> f (flip index idx . g) s

data Context a b t = Context (b -> t) a deriving Functor

-- See http://conal.net/blog/posts/semantic-editor-combinators
setting :: ((a -> b) -> s -> t) -> Setter s t a b
setting f = dimap (Context id) (\(Context g s) -> f g s) . map'

---------------------------------------------------------------------
-- Common setters
---------------------------------------------------------------------

mapped :: Functor f => Setter (f a) (f b) a b
mapped = setting fmap

---------------------------------------------------------------------
-- Derived operators
---------------------------------------------------------------------

reover :: Optic (Re (->) a b) s t a b -> (t -> s) -> (b -> a)
reover = over . re

set :: Optic (->) s t a b -> s -> b -> t
set o s b = over o (const b) s

set' :: ((a -> b) -> t) -> b -> t
set' o = o . const

reset :: Optic (Re (->) a b) s t a b -> b -> s -> a
reset = set . re

appendOver :: Semigroup a => Setter s t a a -> a -> s -> t
appendOver p = over p . (<>)

--setJust :: Optic (->) s t a (Maybe b) -> b -> s -> t
--setJust :: Setter s t a (Maybe b) -> b -> s -> t
--setJust p = set p . Just
