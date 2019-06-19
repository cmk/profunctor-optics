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
module Data.Profunctor.Reference.PRefs (
    PVars, PRefs(..), readRefs, writeRefs, has, withPRefs
  , (<.<), (>.>), (*$$*), (+$$+)
  , SettableStateVar(..), GettableStateVar(..)
) where

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

import Data.Monoid
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

data PRefs c rt rs b a = forall x y . PRefs (Optical c x y a b) !(rs x) !(rt y)

-- | Type alias for 'PRefs' constructed from @IO s@ and @t -> IO ()@.
type PVars c b a = PRefs c SettableStateVar GettableStateVar b a

-- | Extract the covariant read reference.
readRefs :: Functor rs => c (Star (Const a)) => PRefs c rt rs b a -> rs a
readRefs (PRefs o rs _) = view o <$> rs

-- | Extract the contravariant write reference.
writeRefs :: Contravariant rt => c (Costar (Const b)) => PRefs c rt rs b a -> b -> rt r
writeRefs (PRefs o _ rt) b = review o b >$ rt

-- @
--'readPure' ::  'Monoid' r => (s -> a) -> 'PRefs' 'Profunctor' ('Op' r) ((->) s) b a
-- @
readPure :: Divisible g => (s -> a) -> PRefs Profunctor g ((->) s) b a
readPure f = PRefs (dimap f id) id conquer

-- @
-- 'writePure' :: (b -> t) -> 'PRefs' 'Profunctor' ('Op' t) 'Maybe' b a
-- @
writePure :: Alternative f => (b -> t) -> PRefs Profunctor (Op t) f b a
writePure g = PRefs (dimap id g) empty (Op id) 

readVars :: (s -> a) -> PVars Profunctor b a
readVars f = PRefs (dimap f id) empty conquer

writeVars :: (b -> t) -> PVars Profunctor b a
writeVars g = PRefs (dimap id g) empty conquer


{-
> :t readRef simple
readRef simple :: a -> a
> :t writeRef simple
writeRef simple :: a -> Op a r
-}
simple :: PRefs Profunctor (Op a) ((->) a) a a
simple = readPure @(Op ()) id >.> writePure @Maybe id


-- | A substitute for the 'Has' typeclass pattern.
has :: MonadReader r m => c (Star (Const a)) => PRefs c rt ((->) r) b a -> m a
has (PRefs o rs _) = view o <$> asks rs


-- | Unbox a 'PRefs' by providing an existentially quantified continuation.
withPRefs 
  :: PRefs c rt rs b a 
  -> (forall x y. Optical c x y a b -> rs x -> rt y -> r) 
  -> r
withPRefs (PRefs o sx ty) f = f o sx ty

instance (c (Star (Const a)), forall s . HasGetter (rs s) s) => HasGetter (PRefs c rt rs b a) a where

  get (PRefs o rs _) = liftIO $ view o <$> SV.get rs
  {-# INLINE get #-}

instance (c (->), forall s. HasGetter (rs s) s, forall t. HasSetter (rt t) t) => HasSetter (PRefs c rt rs b a) b where

  (PRefs o rs rt) $= b = liftIO $ SV.get rs >>= \s -> rt $= over o (const b) s
  {-# INLINE ($=) #-}

instance (c (->), forall s. HasGetter (rs s) s, forall t. HasSetter (rt t) t) => HasUpdate (PRefs c rt rs b a) a b where

  (PRefs o rs rt) $~ f  = liftIO $ SV.get rs >>= \s -> rt $= over o f s

  (PRefs o rs rt) $~! f = liftIO $ SV.get rs >>= \s -> rt $=! over o f s

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

instance Profunctor (PRefs Fold0ing rt rs) where dimap bt sa (PRefs o rs rt) = PRefs (o . dimap sa bt) rs rt

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



infixr 1 >.>, <.<


-- | Compose two 'PRefs' from left to right:
--
-- @
-- (>$>) :: 'PVars' 'Profunctor' String Int -> 'PVars' 'Profunctor' Text String -> 'PVars' 'Profunctor' Text Int
-- @
(>.>) :: PRefs Profunctor rx rs b a -> PRefs Profunctor rt ry c b -> PRefs Profunctor rt rs c a
(PRefs oab rs _) >.> (PRefs obc _ rt) = (PRefs (compose_iso oab obc) rs rt)


-- | Compose two 'PRefs' from right to left:
--
(<.<) = flip (>.>)


infixr 3 *$$*
-- | Combine two 'PRefs' with profunctorial strength:
-- 
-- @
-- (*$$*) :: 'PVars' 'Strong' String Int -> 'PVars' 'Strong' [a] a -> 'PVars' 'Strong' (String, [a]) (Int, a)
-- @
(*$$*) :: (Applicative f, Divisible g) => PRefs Strong g f b1 a1 -> PRefs Strong g f b2 a2 -> PRefs Strong g f (b1,b2) (a1,a2)
(*$$*) (PRefs o f g) (PRefs o' f' g') = PRefs (o *** o') (liftA2 (,) f f') (g >*< g')


infixr 2 +$$+
-- | Combine two 'PRefs' with profunctorial choice:
-- 
-- @
-- (+$$+) :: 'PVars' 'Choice' String Int -> 'PVars' 'Choice' [a] a -> 'PVars' 'Choice' (Either String [a]) (Either Int a)
-- @
(+$$+) :: (Alternative f, Decidable g) => PRefs Choice g f b1 a1 -> PRefs Choice g f b2 a2 -> PRefs Choice g f (Either b1 b2) (Either a1 a2)
(+$$+) (PRefs o f g) (PRefs o' f' g') = PRefs (o +++ o') (fmap Left f <|> fmap Right f')  (g >+< g')
