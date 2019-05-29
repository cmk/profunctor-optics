
module Data.Profunctor.Optic.Closure (
    module Data.Profunctor.Optic.Closure
  , module Export
  , Costar (..)
) where

import Data.Distributive
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Prelude

import Data.Profunctor.Closed as Export hiding (Closure)

closure :: (((s -> a) -> b) -> t) -> Closure s t a b
closure f pab = dimap (flip ($)) f (closed pab)

closure' :: (s -> a) -> (b -> t) -> Closure s t a b
closure' sa bt = closure $ closureMod sa bt

modClosure :: (((s -> a) -> b) -> t) -> (a -> b) -> s -> t
modClosure sabt ab s = sabt (\get -> ab (get s))

-- Every isomorphism is a closure.
closureMod :: (s -> a) -> (b -> t) -> ((s -> a) -> b) -> t
closureMod sa bt sab = bt (sab sa)

withClosure :: AClosure s t a b -> ((s -> a) -> b) -> t
withClosure g =
 let ClosureRep h = (g (ClosureRep $ \f -> f id))

  in h

cloneClosure :: AClosure s t a b -> Closure s t a b
cloneClosure g = closure (withClosure g)

cotraversed :: Distributive f => Closure (f a) (f b) a b
cotraversed = closure $ \f -> cotraverse f id




