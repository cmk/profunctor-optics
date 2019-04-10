{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE QuantifiedConstraints     #-}

{-# OPTIONS_GHC -w #-}
module Data.Profunctor.Reference.PRefs (
    PVars, PRefs(..), readRef, writeRef, has, withPRefs
  , (<$<), (>$>), (*$*)
  , ($=), ($=!), ($~), ($~!)
  , SettableStateVar(..), GettableStateVar(..)
) where

import Control.Arrow
import Control.Category (Category)
import Control.Applicative
import Control.Monad.Reader (MonadReader(..), asks)
import Control.Monad.Writer (MonadWriter(..))
import Control.Monad.IO.Unlift

import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
import Data.Profunctor.Optic hiding (has)
import Data.Profunctor.Reference.Types
-- (HasGetter(..), HasSetter(..), HasUpdate(..), ($=), ($=!), ($~), ($~!))
import Data.Void
import System.IO.Streams (InputStream, OutputStream)

import qualified Data.StateVar as SV
import qualified Control.Category as C
import qualified Data.IORef as IOR

import Data.Maybe (listToMaybe)
import Data.Monoid
--import Control.Exception.Safe hiding (Handler)
import Control.Monad.Error.Class
---------------------------------------------------------------------
--  PRef
---------------------------------------------------------------------


{- | A profunctor reference is a pair of mutable references bound 

together with a profunctor optic by existentializing over the types
 
in the read and write references.

The type variables signify:

  * @c@ - The profunctor constraint determining which operations may be performed.

  * @rt@ - The contravariant write-only reference.

  * @rs@ - The covariant read-only reference.

  * @b@ - The contravariant write-only type.

  * @a@ - The covariant read-only type.

-}

-- TODO: consider adding some version of PRefs'
-- data PRefs' c rs rt b a = forall x . PRefs' (Optical c x x a b) !(rs x) !(rt x)
-- data PRefs' c rs b a = forall x . PRefs' (Optical c x x a b) !(rs x) !(rs x)
data PRefs c rt rs b a = forall x y . PRefs (Optical c x y a b) !(rs x) !(rt y)

-- | Type alias for 'PRefs' constructed from @IO s@ and @t -> IO ()@.
type PVars c b a = PRefs c SettableStateVar GettableStateVar b a

-- | Type alias for 'PRefs' constructed from @m s@, @(a -> Maybe e)@, and @(e -> m a)@.
type PError m e c b a = PRefs c (Catch m e a) m b a

-- | Extract the covariant read reference.
readRef :: Functor rs => c (Star (Const a)) => PRefs c rt rs b a -> rs a
readRef (PRefs o rs _) = view o <$> rs

-- (>$) :: b -> f b -> f a
-- | Extract the contravariant write reference.
writeRef :: Contravariant rt => c (Costar (Const b)) => PRefs c rt rs b a -> b -> rt r
writeRef (PRefs o _ rt) b = review o b >$ rt

--TODO : fills the (read-side) role of the lens in a Has type class
-- you can have your has-pattern using the raw accessor functions of your caps type,
-- or just use 'rs = id' if you want 'o' to be your accessor.  write this up.

-- | A substitute for the 'Has' typeclass pattern.
has :: MonadReader r m => c (Star (Const a)) => PRefs c rt ((->) r) b a -> m a
has (PRefs o rs _) = view o <$> asks rs

-- | Unbox a 'PRefs' by providing an existentially quantified continuation.
withPRefs 
  :: PRefs c rt rs b a 
  -> (forall x y. Optical c x y a b -> rs x -> rt y -> r) 
  -> r
withPRefs (PRefs o sx ty) f = f o sx ty

instance (forall s . HasGetter (rs s) s, c (Star (Const a))) => HasGetter (PRefs c rt rs b a) a where

  get (PRefs o rs _) = liftIO $ view o <$> SV.get rs
  {-# INLINE get #-}

instance (forall s. HasGetter (rs s) s, forall t. HasSetter (rt t) t, c (->)) => HasSetter (PRefs c rt rs b a) b where

  (PRefs o rs rt) $= b = liftIO $ SV.get rs >>= \s -> rt $= over o (const b) s
  {-# INLINE ($=) #-}

instance (forall s. HasGetter (rs s) s, forall t. HasSetter (rt t) t, c (->)) => HasUpdate (PRefs c rt rs b a) a b where

  (PRefs o rs rt) $~ f  = liftIO $ SV.get rs >>= \s -> rt $= over o f s

  (PRefs o rs rt) $~! f = liftIO $ SV.get rs >>= \s -> rt $=! over o f s

-- TODO c :- Profunctor
instance Profunctor (PRefs Profunctor rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt 

instance Profunctor (PRefs Strong rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Profunctor (PRefs Costrong rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Profunctor (PRefs Choice rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Profunctor (PRefs Cochoice rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Profunctor (PRefs Closed rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Profunctor (PRefs Mapping rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Profunctor (PRefs Traversing rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Profunctor (PRefs AffineTraversing rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Profunctor (PRefs Folding rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Profunctor (PRefs AffineFolding rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Profunctor (PRefs Getting rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Profunctor (PRefs Reviewing rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Strong (PRefs Costrong rt rs) where first' (PRefs o rs rt) = PRefs (o . unfirst) rs rt

instance Costrong (PRefs Strong rt rs) where unfirst (PRefs o rs rt) = PRefs (o . first') rs rt

instance Choice (PRefs Cochoice rt rs) where right' (PRefs o rs rt) = PRefs (o . unright) rs rt

instance Cochoice (PRefs Choice rt rs) where unright (PRefs o rs rt) = PRefs (o . right') rs rt

instance (Alternative f, Divisible g) => Category (PRefs Profunctor g f) where 
  id =  PRefs (dimap id id) empty conquer
  (PRefs oab sx _) . (PRefs obc _ ty) = PRefs (compose_iso oab obc) sx ty

compose_iso :: AnIso s y a b -> AnIso x t b c -> Iso s t a c
compose_iso o o' = withIso o $ \ sa _ -> withIso o' $ \ _ b't' -> iso sa b't'

instance (Alternative f, Divisible g) => Category (PRefs Strong g f) where 
  id =  PRefs (dimap id id) empty conquer
  (PRefs oab sx _) . (PRefs obc _ ty) = undefined 


--try :: (MonadCatch m, Exception e) => m a -> m (Either e a)

--tryJust :: (MonadCatch m, Exception e) => (e -> Maybe b) -> m a -> m (Either b a)
--trying :: MonadCatch m => c (Star (Const (First a))) => PRefs c (Error m) m b a
--
{-
tryJust :: (MonadCatch m, Exception e) => (e -> Maybe b) -> m a -> m (Either b a)
tryJust f a = catch (Right `liftM` a) (\e -> maybe (throwM e) (return . Left) (f e))

catchJust :: (MonadCatch m, Exception e) => (e -> Maybe b) -> m a -> (b -> m a) -> m a
catchJust f a b = a `catch` \e -> maybe (throwM e) b $ f e

catch :: (MonadCatch m, Exception e) => m a -> (e -> m a) -> m a
-- | Generalized version of 'Control.Exception.Handler'
data Handler m a = forall e . Control.Exception.Exception e => Handler (e -> m a)


data Catch a m e = forall t . Exception e => Catch (e -> Maybe t) (t -> m a)

e -> Either t a
PThrow m e = PRef Reviewing (Error m) e ()
PHandle e m a = PRefs Choice m (Error m) e a -- 

PTry e m a = PRefs Choice (Error m) m e a
-}

--tryP :: (c (Star (Const (m a))), MonadCatch m) => PRefs c (Error m) m b (m a) -> m a
--tryP :: (c (Star (Const a)), MonadCatch rs) => PRefs c (Error m) rs b a -> rs a
--tryP (PRefs o rs (Error f)) = try rs >>= either (f >> return undefined) (return . view o)


--https://lukajcb.github.io/blog/functional/2018/04/15/rethinking-monaderror.html
tryPError :: (forall e . MonadError e m) => c (Star (Const a)) => PRefs c (Catch m e a) m b a -> m a
tryPError (PRefs o m (Catch f g)) = catchJust f (view o <$> m) g

throwPError :: (forall e . MonadError e m) => c (Costar (Const b)) => PRefs c (Catch m e a) m b a -> b -> m a
throwPError (PRefs o _ (Catch f g)) b = catchJust f (throwError . review o $ b) g

--compose_lens :: ALens s y a b -> ALens x t b c -> Lens s t a c
--compose_lens o o' = withLens o $ \ sa sbt -> withLens o' $ \ s'a' s'b't' -> lens sa sb't'
-- newtype Yoneda p a b = Yoneda { runYoneda :: forall x y. (x -> a) -> (b -> y) -> p x y }

-- | Compose two 'PRefs' from left to right:
--
-- @
-- (>$>) :: 'PVars' 'Profunctor' String Int -> 'PVars' 'Profunctor' Text String -> 'PVars' 'Profunctor' Text Int
-- @
(>$>) :: PRefs Profunctor rx rs b a -> PRefs Profunctor rt ry c b -> PRefs Profunctor rt rs c a
(PRefs oab rs _) >$> (PRefs obc _ rt) = (PRefs (compose_iso oab obc) rs rt)


-- | Compose two 'PRefs' from right to left:
--
-- @
-- (<$<) :: 'PVars' 'Profunctor' Text String -> 'PVars' 'Profunctor' String Int -> 'PVars' 'Profunctor' Text Int
-- @
(<$<) = flip (>$>)

instance (Alternative f, Divisible g) => Arrow (PRefs Profunctor g f) where 
  arr f = PRefs (dimap f f) empty conquer

  (PRefs o f g) *** (PRefs o' f' g') = PRefs (paired o o') (liftA2 (,) f f') (divided g g') 


-- | Combine two 'PRefs' with profunctorial strength:
-- 
-- @
-- (*$*) :: 'PVars' 'Strong' String Int -> 'PVars' 'Strong' [a] a -> 'PVars' 'Strong' (String, [a]) (Int, a)
-- @
(*$*) :: (Applicative f, Divisible g) => PRefs Strong g f b1 a1 -> PRefs Strong g f b2 a2 -> PRefs Strong g f (b1,b2) (a1,a2)
(*$*) (PRefs o f g) (PRefs o' f' g') = PRefs (paired o o') (liftA2 (,) f f') (divided g g')


-- | Combine two 'PRefs' with profunctorial choice:
-- 
-- @
-- (+$+) :: 'PVars' 'Choice' String Int -> 'PVars' 'Choice' [a] a -> 'PVars' 'Choice' (Either String [a]) (Either Int a)
-- @
(+$+) :: (Alternative f, Decidable g) => PRefs Choice g f b1 a1 -> PRefs Choice g f b2 a2 -> PRefs Choice g f (Either b1 b2) (Either a1 a2)
(+$+) (PRefs o f g) (PRefs o' f' g') = PRefs (split o o') (fmap Left f <|> fmap Right f')  (chosen g g')
