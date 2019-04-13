{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE QuantifiedConstraints, ConstraintKinds     #-}

{-# OPTIONS_GHC -w #-}
module Data.Profunctor.Reference.PError where

import Control.Applicative
import Control.Exception.Optic
import Control.Monad.IO.Unlift

import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible

import Data.Profunctor.Reference.Types
import Data.Profunctor.Reference.PRefs
--import Data.Profunctor.Reference.PRef 
import Data.Void

import Data.Maybe (listToMaybe)
import Data.Monoid

import UnliftIO.Exception hiding (Handler)


data Handler m e = Handler { runHandler :: forall a. e -> m a }

instance Contravariant (Handler m) where
  
  contramap f (Handler h) = Handler $ h . f

instance Applicative m => Divisible (Handler m) where
  
  divide f (Handler h) (Handler h') = 
    Handler $ \e -> case f e of (e1, e2) -> h e1 *> h' e2
  
  conquer = Handler $ const undefined

instance MonadUnliftIO m => Decidable (Handler m) where

  lose f = Handler $ \a -> absurd (f a)

  choose f (Handler h) (Handler h') = Handler $ either h h' . f


-- | Create a new 'PError'.

{-# INLINE newPError #-}

newPError :: MonadIO m => Exception a => Handler m SomeException -> PError m Choice a a
newPError h = PRef exception h




--TODO: push this upstream, demonstrate use case w/ +$+
data PRef c cs rs b a = forall x . cs x => PRef (Optical c x x a b) (rs x)

type PError m c b a = PRef c Exception (Handler m) b a

perror :: Exception a => PError IO Choice a a
perror = PRef exception (Handler throwIO)

tryPError :: MonadUnliftIO m => c (Star (Const (First a))) => PError m c b a -> m r -> m (Either a r)
tryPError (PRef o _) m = tryJust (preview o) m

throwPError :: MonadUnliftIO m => c (Costar (Const b)) => PError m c b a -> b -> m r
throwPError (PRef o _) b = throwing o b

catchPError :: MonadUnliftIO m => c (Star (Either a)) => PError m c b a -> m r -> (a -> m r) -> m r
catchPError (PRef o (Handler ht)) m ha = m `catch` \e -> either ht ha $ match o e

handlePError :: MonadUnliftIO m => c (Star (Either a)) => PError m c b a -> (a -> m r) -> m r -> m r
handlePError perr = flip $ catchPError perr





{-
data Catch m a b = forall e . Exception e => Catch (b -> Maybe e) (e -> m a)


instance Contravariant (Catch m a) where
  
  contramap f (Catch emt tma) = Catch (emt . f) tma

instance MonadThrow m => Divisible (Catch m a) where
  
  divide f (Catch g g') (Catch h h') = 
    Catch (\e -> case f e of (e1, e2) -> g e1 <|> h e2) (\t -> g' t >> h' t) --TODO 
  
  conquer = Catch (const Nothing) throwM

instance MonadThrow m => Decidable (Catch m a) where

  lose _ = Catch (const Nothing) throwM

  choose f (Catch g g') (Catch h _) = Catch (either g h . f) g' --TODO left-biased ?

data PRefs'' c rt rs b a = forall x y . Exception x => PRefs'' (Optical c x y a b) (rs x) (rt y)
--type PError c rt rs b a = PRefs c X Exception rt rs b a 

tryFoo :: MonadUnliftIO m => c (Star (Const (First a))) => PRefs'' c rt rs b a -> m r -> m (Either a r)
tryFoo (PRefs'' o _ _ ) m = tryJust (preview o) m


-- | Type alias for 'PRefs' constructed from @m s@, @(t -> Maybe e)@, and @(e -> m a)@.

type PCatch m c b a = PRefs' c (Catch m a) m b a

data PRefs' c rt rs b a = forall x y . Exception y => PRefs' (Optical c x y a b) (rs x) (rt y)

--type PCatch c rt rs b a = PRefs c Exception X rt rs b a 

tryPCatch :: MonadUnliftIO m => c (Star (Const a)) => PCatch m c b a -> m a
tryPCatch (PRefs' o m (Catch f g)) = catchJust f (view o <$> m) g

throwPCatch :: MonadUnliftIO m => c (Costar (Const b)) => PCatch m c b a -> b -> m a
throwPCatch (PRefs' o _ (Catch f g)) b = catchJust f (throwing o $ b) g
-}


