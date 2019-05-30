
module Data.Profunctor.Optic.Closure (
    module Data.Profunctor.Optic.Closure
  , module Export
  , Costar (..)
) where

import Data.Distributive
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Operator
import Data.Profunctor.Optic.Prelude

import Data.Profunctor.Closed as Export hiding (Closure)

closure :: (((s -> a) -> b) -> t) -> Closure s t a b
closure f pab = dimap (flip ($)) f (closed pab)

closure' :: (s -> a) -> (b -> t) -> Closure s t a b
closure' sa bt = closure $ closureMod sa bt


---------------------------------------------------------------------
-- 
---------------------------------------------------------------------

-- | The 'ClosureRep' profunctor precisely characterizes 'Closure'.

newtype ClosureRep a b s t = ClosureRep { unClosureRep :: ((s -> a) -> b) -> t }

instance Profunctor (ClosureRep a b) where
  dimap f g (ClosureRep z) = ClosureRep $ \d -> g (z $ \k -> d (k . f))

instance Closed (ClosureRep a b) where
  -- closed :: p a b -> p (x -> a) (x -> b)
  closed (ClosureRep z) = ClosureRep $ \f x -> z $ \k -> f $ \g -> k (g x)

type AClosure s t a b = Optic (ClosureRep a b) s t a b

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

modClosure :: (((s -> a) -> b) -> t) -> (a -> b) -> s -> t
modClosure sabt ab s = sabt (\get -> ab (get s))

-- Every isomorphism is a closure.
closureMod :: (s -> a) -> (b -> t) -> ((s -> a) -> b) -> t
closureMod sa bt sab = bt (sab sa)

withClosure :: AClosure s t a b -> ((s -> a) -> b) -> t
withClosure g = h where ClosureRep h = (g (ClosureRep $ \f -> f id))

cloneClosure :: AClosure s t a b -> Closure s t a b
cloneClosure g = closure (withClosure g)

cotraversed :: Distributive f => Closure (f a) (f b) a b
cotraversed = closure $ \f -> cotraverse f id

cotraversing :: (Distributive f1, Functor f2) => (f2 a -> b) -> f2 (f1 a) -> f1 b
cotraversing = cotraverseOf cotraversed
