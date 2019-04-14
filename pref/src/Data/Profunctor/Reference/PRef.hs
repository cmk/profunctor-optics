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

import Control.Applicative (liftA2)
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

{-

import Data.Constraint
import Data.Constraint.Forall

-- (\\) :: a => (b => r) -> (a :- b) -> r 

-- nice to haves:

--withPRef' :: (cs s :- cs' s) -> PRef c cs rs a b -> (cs' s => PRef c cs' rs a b -> x) -> x
--withPRef' r f = undefined

--withEntailment :: c (PRef r d) => (d p :- c p) -> (c (PRef r c) => x) -> x
--withEntailment = undefined

withEntailment :: a => (a :- b) -> (b => c) -> c
withEntailment p q = q \\ p

-}

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
-- * @rs@ - The read / write reference.
-- * @a@ - The read / write type.

--data PRef c cs rs b a = forall x . PRef (Optical c x x a b) !(rs x)

data PRef c cs rs b a = forall x . cs x => PRef (Optical c x x a b) (rs x)

-- | Type alias for a 'PRef' constructed from @IO s@ and @s -> IO ()@.
type PVar c cs b a = PRef c cs StateVar b a


instance (forall s . HasGetter (rs s) s, c (Star (Const a))) => HasGetter (PRef c cs rs b a) a where

  get (PRef o rs) = liftIO $ view o <$> SV.get rs
  {-# INLINE get #-}

instance (forall s. HasUpdate (rs s) s s, c (->)) => HasSetter (PRef c cs rs b a) b where

  (PRef o rs) $= b = liftIO $ rs $~ over o (const b)
  {-# INLINE ($=) #-}

instance (forall s. HasUpdate (rs s) s s, c (->)) => HasUpdate (PRef c cs rs b a) a b where

  (PRef o rs) $~ f  = liftIO $ rs $~ over o f

  (PRef o rs) $~! f = liftIO $ rs $~! over o f

instance Profunctor (PRef Profunctor cs rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Profunctor (PRef Strong cs rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Profunctor (PRef Costrong cs rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Profunctor (PRef Choice cs rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Profunctor (PRef Cochoice cs rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Profunctor (PRef Closed cs rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Profunctor (PRef Mapping cs rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Profunctor (PRef Traversing cs rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Profunctor (PRef AffineTraversing cs rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Profunctor (PRef Folding cs rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Profunctor (PRef AffineFolding cs rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Profunctor (PRef Getting cs rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Profunctor (PRef Reviewing cs rs) where dimap bt sa (PRef o rs) = PRef (o . dimap sa bt) rs

instance Strong (PRef Costrong cs rs) where first' (PRef o rs) = PRef (o . unfirst) rs

instance Costrong (PRef Strong cs rs) where unfirst (PRef o rs) = PRef (o . first') rs

instance Choice (PRef Cochoice cs rs) where right' (PRef o rs) = PRef (o . unright) rs

instance Cochoice (PRef Choice cs rs) where unright (PRef o rs) = PRef (o . right') rs

infixr 3 *|*

(*|*) :: Applicative f => PRef Strong X f b1 a1 -> PRef Strong X f b2 a2 -> PRef Strong X f (b1,b2) (a1,a2)
(*|*) (PRef o f) (PRef o' f') = PRef (paired o o') (liftA2 (,) f f')

infixr 2 +|+

(+|+) :: Decidable f => PRef Choice X f b1 a1 -> PRef Choice X f b2 a2 -> PRef Choice X f (Either b1 b2) (Either a1 a2)
(+|+) (PRef o f) (PRef o' f') = PRef (split o o') (chosen f f')


has :: MonadReader r m => c (Star (Const a)) => PRef c cs ((->) r) b a -> m a
has (PRef o rs) = view o <$> asks rs

asksBoth :: (MonadReader r m, Applicative m) => (r -> PRef Strong X m b1 a1) -> (r -> PRef Strong X m b2 a2) -> m (PRef Strong X m (b1, b2) (a1, a2))
asksBoth r s = liftA2 (*|*) (asks r) (asks s)

asksEither
  :: (MonadReader r m, Decidable m) 
  => (r -> PRef Choice X m b1 a1)
  -> (r -> PRef Choice X m b2 a2)
  -> m (PRef Choice X m (Either b1 b2) (Either a1 a2))
asksEither r s = liftA2 (+|+) (asks r) (asks s)


-- | Unbox a 'PRef' by providing an existentially quantified continuation.
withPRef
  :: PRef c cs rs b a 
  -> (forall x . Optical c x x a b -> rs x -> r) 
  -> r
withPRef (PRef o rs) f = f o rs
