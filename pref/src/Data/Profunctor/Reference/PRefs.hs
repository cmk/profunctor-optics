{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE QuantifiedConstraints     #-}

{-# OPTIONS_GHC -w #-}
module Data.Profunctor.Reference.PRefs where

import Control.Arrow
import Control.Category (Category)
import Control.Applicative
import Control.Monad.Reader (MonadReader(..), asks)
import Control.Monad.Writer (MonadWriter(..))
import Control.Monad.IO.Unlift

import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
import Data.Profunctor.Optic
import Data.Profunctor.Reference.Types
-- (HasGetter(..), HasSetter(..), HasUpdate(..), ($=), ($=!), ($~), ($~!))
import Data.Void
import System.IO.Streams (InputStream, OutputStream)

import qualified Data.StateVar as SV
import qualified Control.Category as C
import qualified Data.IORef as IOR


---------------------------------------------------------------------
--  PRef
---------------------------------------------------------------------


{- | A profunctor reference is a pair of mutable references bound 

together with a profunctor optic by existentializing over the types
 
in the read and write references.

The type variables signify:

  * @c@ - The profunctor constraint determining which operations can be performed.

  * @rt@ - The write container reference (e.g. 'MVar', 'IORef' etc.).

  * @rs@ - The read container reference (e.g. '(-> r)', 'MVar', 'IORef' etc.).

  * @b@ - The exposed (contravariant) write-only type.

  * @a@ - The exposed (covariant) read-only type.

-}

-- TODO: consider adding some version of PRefs'
-- data PRefs' c rs rt b a = forall x . PRefs' (Optical c x x a b) !(rs x) !(rt x)
-- data PRefs' c rs b a = forall x . PRefs' (Optical c x x a b) !(rs x) !(rs x)
data PRefs c rt rs b a = forall x y . PRefs (Optical c x y a b) !(rs x) !(rt y)

type PVars c b a = PRefs c SettableStateVar GettableStateVar b a

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
dimap' :: (b' -> b) -> (a -> a') -> PRefs Profunctor rt rs b a -> PRefs Profunctor rt rs b' a'
dimap' bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

instance Profunctor (PRefs Profunctor rt rs) where dimap = dimap'

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


-- PRefs c SettableStateVar GettableStateVar
instance (Alternative f, Divisible g) => Category (PRefs Profunctor g f) where 
  id =  PRefs (dimap id id) empty conquer
  (PRefs oab sx _) . (PRefs obc _ ty) = (PRefs (compose_iso oab obc) sx ty) 

compose_iso :: AnIso s y a b -> AnIso x t b c -> Iso s t a c
compose_iso o o' = withIso o $ \ sa _ -> withIso o' $ \ _ b't' -> iso sa b't'

--compose_lens :: ALens s y a b -> ALens x t b c -> Lens s t a c
--compose_lens o o' = withLens o $ \ sa sbt -> withLens o' $ \ s'a' s'b't' -> lens sa sb't'
-- newtype Yoneda p a b = Yoneda { runYoneda :: forall x y. (x -> a) -> (b -> y) -> p x y }



instance (Alternative f, Divisible g) => Arrow (PRefs Profunctor g f) where 
  arr f = PRefs (dimap f f) empty conquer

  (PRefs o f g) *** (PRefs o' f' g') = PRefs (paired o o') (liftA2 (,) f f') (divided g g') 


(*$*) :: Applicative f => Divisible g => PRefs Strong g f b1 a1 -> PRefs Strong g f b2 a2 -> PRefs Strong g f (b1,b2) (a1,a2)
(*$*) (PRefs o f g) (PRefs o' f' g') = PRefs (paired o o') (liftA2 (,) f f') (divided g g')

-- TODO 'Decidable f' seems like the wrong constraint here.
-- (+$+) :: Decidable f => Decidable g => PRefs Choice g f b1 a1 -> PRefs Choice g f b2 a2 -> PRefs Choice g f (Either b1 b2) (Either a1 a2)
-- (+$+) (PRefs o f g) (PRefs o' f' g') = PRefs (split o o') (chosen f f') (chosen g g')



-- | Unbox a 'Pxy' by providing an existentially quantified continuation.
withPRefs 
  :: PRefs c rt rs b a 
  -> (forall x y. Optical c x y a b -> rs x -> rt y -> r) 
  -> r
withPRefs (PRefs o sx ty) f = f o sx ty





--TODO : this is the key function. fills the (read-side) role of the lens in a Has type class
-- you can have your has-pattern using the raw accessor functions of your caps type,
-- or just use 'rs = id' if you want 'o' to be your accessor.  write this up.
has :: MonadReader r m => c (Star (Const a)) => PRefs c rt ((->) r) b a -> m a
has (PRefs o rs _) = view o <$> asks rs

read :: Functor rs => c (Star (Const a)) => PRefs c rt rs b a -> rs a
read (PRefs o rs _) = view o <$> rs

-- (>$) :: b -> f b -> f a
write :: Contravariant rt => c (Costar (Const b)) => PRefs c rt rs b a -> b -> rt r
write (PRefs o _ rt) b = review o b >$ rt

--update :: Functor rs => Contravariant rt => c (->) => PRefs c rt rs b a -> (a -> b) -> rt a
--update (PRefs o rs rt) f = contramap (over o f) rt

{-
debug :: Show a => SettableStateVar a
debug = SettableStateVar print




pstate 
  :: Optic (Star ((,) a)) s t a b
  -> (a -> (a, b)) -> s -> t
pstate o f = star o snd f id

pmaybe
  :: Optic (Costar Maybe) s t a b 
  -> a -> (a -> b) -> Maybe s -> t
pmaybe o a ab = costar' o ab (maybe a id)

--star' up down o f = outof runStar up (o . into Star down $ f)


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
-}
