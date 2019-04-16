{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE TypeOperators             #-}
-- {-# LANGUAGE GADTs             #-}

module Data.Profunctor.Reference.Types (
    -- module Data.Profunctor.Reference.Types
    X(..), type (+), (>+<), (>*<)
  , get, (=$), ($=), (!=$), ($=!), (~$), ($~), (!~$), ($~!)
  , HasGetter, HasSetter, HasUpdate
  , GettableStateVar, SettableStateVar, StateVar
  , makeGettableStateVar
  , pstate, pmaybe
) where

import Control.Applicative
import Control.Exception (Exception(..))
import Control.Monad.IO.Unlift
import Data.Functor.Contravariant.Divisible
import Data.Profunctor.Optic
import Data.StateVar 
import Data.Void
import Data.Monoid

class X x
instance X x

instance (Exception e1, Exception e2) => Exception (Either e1 e2) where

  toException = either toException toException

  fromException s = (fmap Left $ fromException s) <|> (fmap Right $ fromException s) 

type (+) = Either
infixr 5 +

type (*) = (,)
infixl 6 *

infixr 3 >*<

(>*<) :: Divisible f => f a -> f b -> f (a , b)
(>*<) = divided

infixr 3 >+<

(>+<) :: Decidable f => f a -> f b -> f (a + b)
(>+<) = chosen

newtype Settable m a = Settable (a -> m ())

type Gettable m a = m a

infixl 2 =$, !=$, ~$, !~$
(=$) :: (MonadIO m, HasSetter t a) => a -> t -> m ()
(=$) = flip ($=)

(!=$) :: (MonadIO m, HasSetter t a) => a -> t -> m () 
(!=$) = flip ($=!)

(~$) :: (MonadIO m, HasUpdate t a b) => (a -> b) -> t -> m ()
(~$) = flip ($~)

(!~$) :: (MonadIO m, HasUpdate t a b) => (a -> b) -> t -> m ()
(!~$) = flip ($~!)


pstate 
  :: Optic (Star ((,) a)) s t a b
  -> (a -> (a, b)) -> s -> t
pstate o f = star o snd f id

pmaybe
  :: Optic (Costar Maybe) s t a b 
  -> a -> (a -> b) -> Maybe s -> t
pmaybe o a ab = costar' o ab (maybe a id)

into :: ((a -> b) -> c) -> (r -> b) -> (a -> r) -> c
into up f = up . (f .)

outof :: (c -> a -> b) -> (b -> r) -> c -> a -> r
outof down g = (g .) . down

star
  :: Optic (Star f) s t a b
  -> (f t -> r)
  -> (c -> f b)
  -> (a -> c)
  -> s
  -> r
star o down up f = outof runStar down (o . into Star up $ f)

star' :: Optic (Star f) s t a b -> (f t -> r) -> (a -> f b) -> s -> r
star' o f g = star o f g id

costar
  :: (t -> d)
  -> Optic (Costar f) s t a b
  -> (c -> b)
  -> (f a -> c)
  -> f s
  -> d
costar down o up f = outof runCostar down (o . into Costar up $ f)

costar'
  :: Optic (Costar f) s t a b
  -> (c -> b)
  -> (f a -> c)
  -> f s
  -> t
costar' = costar id
