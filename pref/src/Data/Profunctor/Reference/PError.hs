{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE QuantifiedConstraints     #-}

{-# OPTIONS_GHC -w #-}
module Data.Profunctor.Reference.PError where

import Control.Applicative
import Control.Monad.Error.Class
import Control.Monad.IO.Unlift

import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
import Data.Profunctor.Optic hiding (has)
import Data.Profunctor.Reference.Types
import Data.Profunctor.Reference.PRefs
import Data.Void

import Data.Maybe (listToMaybe)
import Data.Monoid

--data Catch a m e = forall t . Exception e => Catch (e -> Maybe t) (t -> m a)
--TODO: profunctor instance
data Catch e m a b = Catch (b -> Maybe e) (e -> m a)

instance Contravariant (Catch e m a) where
  
  contramap f (Catch emt tma) = Catch (emt . f) tma


instance MonadError e m => Divisible (Catch e m a) where
  
  divide f (Catch g g') (Catch h h') = Catch (\e -> case f e of (e1, e2) -> g e1 <|> h e2) (\t -> g' t >> h' t) --TODO 
  
  conquer = Catch (const Nothing) throwError

instance MonadError e m => Decidable (Catch e m a) where

  lose _ = Catch (const Nothing) throwError

  choose f (Catch g g') (Catch h _) = Catch (either g h . f) g' --TODO left-biased ?



{-




instance Monad m => Decidable (Catch a m) where
  lose f = Catch $ \a -> absurd (f a)
  choose f (Catch g) (Catch h) = Catch $ either g h . f


-- | You need this when using 'catches'.

data Error m e where
  Error :: Exception e => (e -> m a) -> Error m e

data Throw a m e where
  Throw :: Exception e => (e -> m a) -> Throw a m e

error :: (Exception e, MonadThrow m) => Error m e
error = Error throwM

instance Monad m => Functor (Handler e m) where
  fmap f (Handler ema amr) = Handler ema $ \a -> do
     r <- amr a
     return (f r)
  {-# INLINE fmap #-}

instance Monad m => Semigroup (Handler e m a) where
  (<>) = M.mappend
  {-# INLINE (<>) #-}

instance Monad m => Alt (Handler e m) where
  Handler ema amr <!> Handler emb bmr = Handler emab abmr where
    emab e = Left <$> ema e <|> Right <$> emb e
    abmr = either amr bmr
  {-# INLINE (<!>) #-}

instance Monad m => Plus (Handler e m) where
  zero = Handler (const Nothing) undefined
  {-# INLINE zero #-}

instance Monad m => M.Monoid (Handler e m a) where
  mempty = zero
  {-# INLINE mempty #-}
  mappend = (<!>)
  {-# INLINE mappend #-}

instance Handleable e m (Handler e m) where
  handler = Handler . preview
  {-# INLINE handler #-}

-}



-- | Helper function to provide conditional catch behavior.
catchJust :: MonadError e m => (e -> Maybe t) -> m a -> (t -> m a) -> m a
catchJust f m k = catchError m $ \ e -> case f e of
  Nothing -> throwError e
  Just x  -> k x
{-# INLINE catchJust #-}

--catching :: MonadCatch m => Getting (First a) SomeException a -> m r -> (a -> m r) -> m r
catching :: MonadError e m => AGetter (First a) e t a b -> m r -> (a -> m r) -> m r
--catching :: MonadError e m => Getting (M.First a) e a -> m r -> (a -> m r) -> m r
catching l = catchJust (preview l)

{-
--tryN (PRefs o rs (Error f)) = try rs >>= either (f >> return undefined) (return . view o)
exception :: Exception a => Prism' SomeException a
exception = prism' toException fromException

--catching :: MonadCatch m => Getting (First a) SomeException a -> m r -> (a -> m r) -> m r
catching :: Exception s => AGetter (First a) s t a b -> IO r -> (a -> IO r) -> IO r
catching l = catchJust (preview l)

-- catching_ :: MonadCatch m => Getting (First a) SomeException a -> m r -> m r -> m r
catching_ :: Exception s => AGetter (First a) s t a b -> IO r -> IO r -> IO r
catching_ l a b = catchJust (preview l) a (const b)

-- handling :: MonadCatch m => Getting (First a) SomeException a -> (a -> m r) -> m r -> m r
handling :: Exception s => AGetter (First a) s t a b -> (a -> IO r) -> IO r -> IO r
handling l = flip (catching l)

--trying :: MonadCatch m => Getting (First a) SomeException a -> m r -> m (Either a r)
trying :: Exception s => AGetter (First a) s t a b -> IO r -> IO (Either a r)
trying l = tryJust (preview l)

--throwing :: AReview SomeException b -> b -> r
--throwing :: (MonadReader b1 m, Exception e) => Optic (Costar (Const b1)) s e a1 b1 -> m a2
--throwing l = reviews l throw
-}

-- | Maybe produce a 'Left', otherwise produce a 'Right'.
--
-- >>> maybeToRight "default" (Just 12)
-- Left 12
--
-- >>> maybeToRight "default" Nothing
-- Right "default"
maybeToLeft :: b -> Maybe a -> Either a b
maybeToLeft _ (Just x) = Left x
maybeToLeft y Nothing  = Right y

-- | Maybe produce a 'Right', otherwise produce a 'Left'.
--
-- >>> maybeToRight "default" (Just 12)
-- Right 12
--
-- >>> maybeToRight "default" Nothing
-- Left "default"
maybeToRight :: b -> Maybe a -> Either b a
maybeToRight _ (Just x) = Right x
maybeToRight y Nothing  = Left y

-- | Generalize @Either e@ as @MonadError e m@.
--
-- If the argument has form @Left e@, an error is produced in the monad via
-- 'throwError'. Otherwise, the @Right a@ part is forwarded.
eitherToError :: (MonadError e m) => Either e a -> m a
eitherToError = either throwError return

--try :: (MonadCatch m, Exception e) => m a -> m (Either e a)

--tryJust :: (MonadCatch m, Exception e) => (e -> Maybe b) -> m a -> m (Either b a)
--trying :: MonadCatch m => c (Star (Const (First a))) => PRefs c (Error m) m b a
--
{-
e -> Either t a
PThrow m e = PRef Reviewing (Error m) e ()
PHandle e m a = PRefs Choice m (Error m) e a -- 

PTry e m a = PRefs Choice (Error m) m e a
catchJust :: MonadError t m => (t -> Maybe e) -> m a -> (e -> m a) -> m a
-}

--tryP :: (c (Star (Const (m a))), MonadCatch m) => PRefs c (Error m) m b (m a) -> m a
--tryP :: (c (Star (Const a)), MonadCatch rs) => PRefs c (Error m) rs b a -> rs a
--tryP (PRefs o rs (Error f)) = try rs >>= either (f >> return undefined) (return . view o)

-- | Type alias for 'PRefs' constructed from @m s@, @(t -> Maybe e)@, and @(e -> m a)@.
type PError e m c b a = PRefs c (Catch e m a) m b a

--tryPError' :: (forall e . MonadError e m) => c (Star (Either a)) => PError e m c b a -> m (Either e a)
--tryPError' (PRefs o m (Catch f g)) = catchJust f (match o <$> m) g

--https://lukajcb.github.io/blog/functional/2018/04/15/rethinking-monaderror.html
tryPError :: (forall e . MonadError e m) => c (Star (Const a)) => PError e m c b a -> m a
tryPError (PRefs o m (Catch f g)) = catchJust f (view o <$> m) g

--TODO try this with simple Either
throwPError :: (forall e . MonadError e m) => c (Costar (Const b)) => PError e m c b a -> b -> m a
throwPError (PRefs o _ (Catch f g)) b = catchJust f (throwError . review o $ b) g

