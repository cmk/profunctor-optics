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
import Control.Monad (MonadPlus(..))
import Control.Monad.IO.Unlift

import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible

import Data.Profunctor.Reference.Types
import Data.Profunctor.Reference.PRef
import Data.Void

import Data.Monoid

import UnliftIO.Exception (Exception(..), SomeException)

import qualified UnliftIO.Exception as Ex hiding (Handler)
import qualified Control.Exception.Optic as O (exception, throwing, trying)





data Handler m e = Handler { runHandler :: forall a. e -> m a }

instance Contravariant (Handler m) where
  
  contramap f (Handler h) = Handler $ h . f

instance MonadPlus m => Divisible (Handler m) where
  
  divide f (Handler h) (Handler h') = 
    Handler $ \e -> case f e of (e1, e2) -> h e1 >> h' e2
  
  conquer = Handler $ const mzero

instance MonadPlus m => Decidable (Handler m) where

  lose f = Handler $ \a -> absurd (f a)

  choose f (Handler h) (Handler h') = Handler $ either h h' . f


-- | Create a new 'PError'.

{-# INLINE newPError #-}

newPError :: MonadIO m => Exception a => Handler m SomeException -> PError m Choice a
newPError h = PRef O.exception h



{-
-- TODO- you can use these to define domain-level exceptions. e.g.
-- myerr :: PError IO Choice MyDomainException = perror
-- then come back and handle the backend exception hierarchy at a later time
-- 
foo :: PError IO Choice Foo
foo = perror

bar :: PError IO Choice Bar
bar = perror
 
baz :: PError m c a -> PRef c X (Handler m) a a
baz (PRef o h) = (PRef o h)

> :t baz foo +$+ baz bar

  :: PRef
       Choice
       X
       (Handler IO)
       (Either Foo Bar)
       (Either Foo Bar)
-}


type PError m c a = PRef c Exception (Handler m) a a

perror :: MonadIO m => Exception a => PError m Choice a
perror = PRef O.exception (Handler Ex.throwIO)

trying :: MonadUnliftIO m => c (Star (Const (First a))) => PError m c a -> m r -> m (Either a r)
trying (PRef o _) m = O.trying o m

throwing :: MonadUnliftIO m => c (Costar (Const a)) => PError m c a -> a -> m r
throwing (PRef o _) a = O.throwing o a

-- | Runs the hidden 'Handler' or the user-supplied handler, depending on the error.
catching :: MonadUnliftIO m => c (Star (Either a)) => PError m c a -> m r -> (a -> m r) -> m r
catching (PRef o (Handler ht)) m ha = m `Ex.catch` \e -> either ht ha $ match o e

-- | A flipped variant of 'catchPError'.
handling :: MonadUnliftIO m => c (Star (Either a)) => PError m c a -> (a -> m r) -> m r -> m r
handling perr = flip $ catching perr





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


