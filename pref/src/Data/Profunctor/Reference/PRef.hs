{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE QuantifiedConstraints     #-}

{-# OPTIONS_GHC -w #-}
{-# LANGUAGE TemplateHaskell, CPP #-}
module Data.Profunctor.Reference.PRef (
    module Data.Profunctor.Reference.PRef 
  , ($=), ($=!), ($~), ($~!)
  , StateVar(..)
) where

import Control.Category (Category)
import Control.Monad.Reader (MonadReader(..), asks)
import Control.Monad.IO.Unlift
import Data.Functor.Contravariant.Divisible
import Data.Profunctor.Optic hiding (has)
import Data.Profunctor.Reference.Global
import Data.Profunctor.Reference.Types as Export

import qualified Data.IORef as IOR
import qualified Data.StateVar as SV
import qualified Control.Monad.Trans.Reader as R


import Control.Applicative (liftA2)
import Data.IORef (IORef(..))
---------------------------------------------------------------------
--  PRef
---------------------------------------------------------------------


-- | A 'PRef' is a mutable reference bound together with a profunctor
-- optic by existentializing over the 's' and 't' variables and setting 
-- them equal to one another. See also 'Data.Profunctor.Reference.PRef'.
--
-- The type variables signify:
-- 
-- * @c@ - The constraint determining which operations may be performed.
-- * @rs@ - The read / write container reference.
-- * @a@ - The read / write type.

data PRef c rs b a = forall x . PRef (Optical c x x a b) !(rs x)

-- | Type alias for 'PRefs' constructed from @IO s@ and @s -> IO ()@.
type PVar c b a = PRef c StateVar b a


-- | Unbox a 'PRef' by providing an existentially quantified continuation.
withPRef
  :: PRef c rs b a 
  -> (forall x . Optical c x x a b -> rs x -> r) 
  -> r
withPRef (PRef o rs) f = f o rs

{-

newtype LocalRef c s a = 
  LocalRef { unLocalRef :: Ref m r => forall r. ReaderT (PRef STRef c s) (ST r) a }

-}


instance (forall s . HasGetter (rs s) s, c (Star (Const a))) => HasGetter (PRef c rs b a) a where

  get (PRef o rs) = liftIO $ view o <$> SV.get rs
  {-# INLINE get #-}

instance (forall s. HasUpdate (rs s) s s, c (->)) => HasSetter (PRef c rs b a) b where

  (PRef o rs) $= b = liftIO $ rs $~ over o (const b)
  {-# INLINE ($=) #-}

instance (forall s. HasUpdate (rs s) s s, c (->)) => HasUpdate (PRef c rs b a) a b where

  (PRef o rs) $~ f  = liftIO $ rs $~ over o f

  (PRef o rs) $~! f = liftIO $ rs $~! over o f

instance Profunctor (PRef Profunctor rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Profunctor (PRef Strong rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Profunctor (PRef Costrong rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Profunctor (PRef Choice rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Profunctor (PRef Cochoice rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Profunctor (PRef Closed rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Profunctor (PRef Mapping rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Profunctor (PRef Traversing rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Profunctor (PRef AffineTraversing rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Profunctor (PRef Folding rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Profunctor (PRef AffineFolding rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Profunctor (PRef Getting rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Profunctor (PRef Reviewing rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Strong (PRef Costrong rs) where first' (PRef o rs) = PRef (o . unfirst) rs

instance Costrong (PRef Strong rs) where unfirst (PRef o rs) = PRef (o . first') rs

instance Choice (PRef Cochoice rs) where right' (PRef o rs) = PRef (o . unright) rs

instance Cochoice (PRef Choice rs) where unright (PRef o rs) = PRef (o . right') rs

(*$*) :: Applicative f => PRef Strong f b1 a1 -> PRef Strong f b2 a2 -> PRef Strong f (b1,b2) (a1,a2)
(*$*) (PRef o f) (PRef o' f') = PRef (paired o o') (liftA2 (,) f f')

-- TODO: could use these w/ & an 'Error m e = Error { forall a. e -> m a }' the 'Decidable' instance for exceptions
(+$+) :: Decidable f => PRef Choice f b1 a1 -> PRef Choice f b2 a2 -> PRef Choice f (Either b1 b2) (Either a1 a2)
(+$+) (PRef o f) (PRef o' f') = PRef (split o o') (chosen f f')


has :: MonadReader r m => c (Star (Const a)) => PRef c ((->) r) b a -> m a
has (PRef o rs) = view o <$> asks rs

{-
hasBoth  
  :: c1 (Star (Const (PRef Strong m b1 a1)))
  => c2 (Star (Const (PRef Strong m b2 a2)))
  => MonadReader r m
  => PRef c1 ((->) r) b4 (PRef Strong m b1 a1)
  -> PRef c2 ((->) r) b5 (PRef Strong m b2 a2)
  -> m (PRef Strong m (b1, b2) (a1, a2))
hasBoth r s = liftA2 (*$*) (has r) (has s)
-}
asksBoth
  :: (MonadReader r m, Applicative m) 
  => (r -> PRef Strong m b1 a1)
  -> (r -> PRef Strong m b2 a2)
  -> m (PRef Strong m (b1, b2) (a1, a2))
asksBoth r s = liftA2 (*$*) (asks r) (asks s)
