{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE QuantifiedConstraints  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances   #-}
module Data.Profunctor.Optic.Zoom where

import Control.Monad.Reader as Reader
import Control.Monad.State as State
import Control.Monad.Trans.State.Lazy as Lazy
import Control.Monad.Trans.State.Strict as Strict
import Control.Monad.Trans.RWS.Lazy as Lazy
import Control.Monad.Trans.RWS.Strict as Strict
import Control.Monad.Trans.Identity
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Types

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XFlexibleInstances
-- >>> :set -XRankNTypes
-- >>> import Control.Monad.State
-- >>> :load Data.Profunctor.Optic

infixr 2 `zoom`

type family Zoomed (m :: * -> *) :: * -> * -> *

type instance Zoomed (IdentityT m)         = Zoomed m
type instance Zoomed (ReaderT e m)         = Zoomed m
type instance Zoomed (Strict.StateT s z)   = StateTRep z
type instance Zoomed (Lazy.StateT s z)     = StateTRep z
type instance Zoomed (Strict.RWST r w s z) = RWSTRep w z
type instance Zoomed (Lazy.RWST r w s z)   = RWSTRep w z

class (MonadState s m, MonadState t n) => Zoom m n s t | m -> s, n -> t, m t -> n, n s -> m where

  -- | Run a monadic action in a larger 'State' than it was defined in.
  --
  -- Used to lift actions into a 'State' 'Monad' with a larger 'State' type.
  --
  -- >>> flip evalState (1,"foo") $ zoom first' $ use id
  -- 1
  --
  -- >>> flip evalState [Right "foo", Right "bar"] $ zoom traversed $ use right'
  -- "foobar"
  --
  -- >>> flip execState (1,"foo") $ zoom first' $ id .= 2
  -- (2,"foo")
  --
  -- >>> flip execState [(1,"foo"), (2,"foo")] $ zoom traversed $ second' ..= (<>"bar")
  -- [(1,"foobar"),(2,"foobar")]
  --
  -- >>> flip execState [Left "foo", Right "bar"] $ zoom traversed $ right' ..= (<>"baz")
  -- [Left "foo",Right "barbaz"]
  --
  -- >>> flip evalState ("foo","bar") $ zoom both (use id)
  -- "foobar"
  --
  zoom :: Optic' (Star (Zoomed m c)) t s -> m c -> n c

instance Zoom m n s t => Zoom (IdentityT m) (IdentityT n) s t where
  zoom l (IdentityT m) = IdentityT (zoom l m)
  {-# INLINE zoom #-}

instance Zoom m n s t => Zoom (ReaderT e m) (ReaderT e n) s t where
  zoom l (ReaderT m) = ReaderT (zoom l . m)
  {-# INLINE zoom #-}

instance Monad z => Zoom (Strict.StateT s z) (Strict.StateT t z) s t where
  zoom o m = Strict.StateT $ unStateTRep #. (runStar #. o .# Star) (StateTRep #. (Strict.runStateT m))
  {-# INLINE zoom #-}

instance Monad z => Zoom (Lazy.StateT s z) (Lazy.StateT t z) s t where
  zoom o m = Lazy.StateT $ unStateTRep #. (runStar #. o .# Star) (StateTRep #. (Lazy.runStateT m))
  {-# INLINE zoom #-}

instance (Monoid w, Monad z) => Zoom (Strict.RWST r w s z) (Strict.RWST r w t z) s t where
  zoom o m = Strict.RWST $ \r -> unRWSTRep #. (runStar #. o .# Star) (RWSTRep #. (Strict.runRWST m r))
  {-# INLINE zoom #-}

instance (Monoid w, Monad z) => Zoom (Lazy.RWST r w s z) (Lazy.RWST r w t z) s t where
  zoom o m = Lazy.RWST $ \r -> unRWSTRep #. (runStar #. o .# Star) (RWSTRep #. (Lazy.runRWST m r))
  {-# INLINE zoom #-}

----------------------------------------------------------------------
-- StateTRep
----------------------------------------------------------------------

newtype StateTRep m s a = StateTRep { unStateTRep :: m (s, a) }

instance Monad m => Functor (StateTRep m s) where
  fmap f (StateTRep m) = StateTRep $ do
     (s, a) <- m
     return (s, f a)
  {-# INLINE fmap #-}

instance (Monad m, Semigroup s) => Apply (StateTRep m s) where
  StateTRep mf <.> StateTRep ma = StateTRep $ do
    (s, f) <- mf
    (s', a) <- ma
    return (s <> s', f a)
  {-# INLINE (<.>) #-}

instance (Monad m, Monoid s) => Applicative (StateTRep m s) where
  pure a = StateTRep (return (mempty, a))
  {-# INLINE pure #-}
  StateTRep mf <*> StateTRep ma = StateTRep $ do
    (s, f) <- mf
    (s', a) <- ma
    return (mappend s s', f a)
  {-# INLINE (<*>) #-}

------------------------------------------------------------------------------
-- RWSTRep
------------------------------------------------------------------------------

newtype RWSTRep w m s a = RWSTRep { unRWSTRep :: m (s, a, w) }

instance Monad m => Functor (RWSTRep w m s) where
  fmap f (RWSTRep m) = RWSTRep $ do
     (s, a, w) <- m
     return (s, f a, w)
  {-# INLINE fmap #-}

instance (Monad m, Semigroup s, Semigroup w) => Apply (RWSTRep w m s) where
  RWSTRep mf <.> RWSTRep ma = RWSTRep $ do
    (s, f, w) <- mf
    (s', a, w') <- ma
    return (s <> s', f a, w <> w')
  {-# INLINE (<.>) #-}

instance (Monad m, Monoid s, Monoid w) => Applicative (RWSTRep w m s) where
  pure a = RWSTRep (return (mempty, a, mempty))
  {-# INLINE pure #-}
  RWSTRep mf <*> RWSTRep ma = RWSTRep $ do
    (s, f, w) <- mf
    (s', a, w') <- ma
    return (mappend s s', f a, mappend w w')
  {-# INLINE (<*>) #-}
