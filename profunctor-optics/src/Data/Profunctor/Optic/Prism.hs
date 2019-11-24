{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Prism (
    -- * Types
    Prism
  , Prism'
  , APrism
  , APrism'
  , Reprism
  , Reprism'
  , AReprism
  , AReprism'
    -- * Indexed Types
  , Ixprism
  , Ixprism'
  , Rxprism
  , Rxprism'
    -- * Constructors
  , prism
  , prism'
  , reprism
  , reprism'
  , handling
  , rehandling
  , aside
  , without
  , below
  , toPastroSum
  , toTambaraSum
  , clonePrism
  , cloneReprism
    -- * Indexed Constructors
  , iprism
  , iprism'
  , rprism
  , rprism'
    -- * Representatives
  , PrismRep(..)
  , ReprismRep(..)
    -- * Primitive operators
  , withPrism
  , withReprism
    -- * Optics
  , left
  , right
  , releft
  , reright
  , just
  , nothing
  , keyed
  , filtered
  , compared
  , prefixed
  , only
  , nearly
  , nthbit
  , sync
  , async
  , exception
  , asyncException
    -- * Indexed optics
  , ileft
  , iright
  , rleft
  , rright
    -- * Classes
  , Choice(..)
  , Cochoice(..)
) where

import Control.Exception
import Control.Monad (guard)
import Data.Bifunctor as B
import Data.Bits (Bits, bit, testBit)
import Data.List (stripPrefix)
import Data.Prd
import Data.Profunctor.Choice
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Import 
import Data.Profunctor.Optic.Type

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- 'Prism'
---------------------------------------------------------------------

-- | Obtain a 'Prism' from a constructor and a matcher function.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input functions satisfy the following
-- properties:
--
-- * @sta (bt b) ≡ Right b@
--
-- * @(id ||| bt) (sta s) ≡ s@
--
-- * @left sta (sta s) ≡ left Left (sta s)@
--
-- More generally, a profunctor optic must be monoidal as a natural 
-- transformation:
-- 
-- * @o id ≡ id@
--
-- * @o ('Data.Profunctor.Composition.Procompose' p q) ≡ 'Data.Profunctor.Composition.Procompose' (o p) (o q)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
prism :: (s -> t + a) -> (b -> t) -> Prism s t a b
prism sta bt = dimap sta (id ||| bt) . right'

-- | Obtain a 'Prism'' from a reviewer and a matcher function that produces a 'Maybe'.
--
prism' :: (s -> Maybe a) -> (a -> s) -> Prism' s a
prism' sa as = flip prism as $ \s -> maybe (Left s) Right (sa s)

-- | Obtain a 'Cochoice' optic from a constructor and a matcher function.
--
-- @
-- reprism f g ≡ \f g -> re (prism f g)
-- @
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input functions satisfy the following
-- properties:
--
-- * @bat (bt b) ≡ Right b@
--
-- * @(id ||| bt) (bat b) ≡ b@
--
-- * @left bat (bat b) ≡ left Left (bat b)@
--
-- A 'Reprism' is a 'View', so you can specialise types to obtain:
--
-- @ view :: 'Reprism'' s a -> s -> a @
--
reprism :: (s -> a) -> (b -> a + t) -> Reprism s t a b
reprism sa bat = unright . dimap (id ||| sa) bat

-- | Create a 'Reprism' from a reviewer and a matcher function that produces a 'Maybe'.
--
reprism' :: (s -> a) -> (a -> Maybe s) -> Reprism' s a
reprism' tb bt = reprism tb $ \b -> maybe (Left b) Right (bt b)

-- | Obtain a 'Prism' from its free tensor representation.
--
-- Useful for constructing prisms from try and handle functions.
--
handling :: (s -> c + a) -> (c + b -> t) -> Prism s t a b
handling sca cbt = dimap sca cbt . right'

-- | Obtain a 'Reprism' from its free tensor representation.
--
rehandling :: (c + s -> a) -> (b -> c + t) -> Reprism s t a b
rehandling csa bct = unright . dimap csa bct

-- | Use a 'Prism' to lift part of a structure.
--
aside :: APrism s t a b -> Prism (e , s) (e , t) (e , a) (e , b)
aside k =
  withPrism k $ \sta bt ->
    flip prism (fmap bt) $ \(e,s) ->
      case sta s of
        Left t  -> Left  (e,t)
        Right a -> Right (e,a)
{-# INLINE aside #-}

-- | Given a pair of prisms, project sums.
without :: APrism s t a b -> APrism u v c d -> Prism (s + u) (t + v) (a + c) (b + d)
without k =
  withPrism k $ \sta bt k' ->
    withPrism k' $ \uevc dv ->
      flip prism (bimap bt dv) $ \su ->
        case su of
          Left s  -> bimap Left Left (sta s)
          Right u -> bimap Right Right (uevc u)
{-# INLINE without #-}

-- | Lift a 'Prism' through a 'Traversable' functor.
-- 
-- Returns a 'Prism' that matches only if each element matches the original 'Prism'.
--
-- >>> [Left 1, Right "foo", Left 4, Right "woot"] ^.. below right
-- []
--
-- >>> [Right "hail hydra!", Right "foo", Right "blah", Right "woot"] ^.. below right
-- [["hail hydra!","foo","blah","woot"]]
--
below :: Traversable f => APrism' s a -> Prism' (f s) (f a)
below k =
  withPrism k $ \sta bt ->
    flip prism (fmap bt) $ \s ->
      case traverse sta s of
        Left _  -> Left s
        Right t -> Right t
{-# INLINE below #-}

-- | Use a 'Prism' to construct a 'PastroSum'.
--
toPastroSum :: APrism s t a b -> p a b -> PastroSum p s t
toPastroSum o p = withPrism o $ \sta bt -> PastroSum (join . B.first bt) p (eswap . sta)

-- | Use a 'Prism' to construct a 'TambaraSum'.
--
toTambaraSum :: Choice p => APrism s t a b -> p a b -> TambaraSum p s t
toTambaraSum o p = withPrism o $ \sta bt -> TambaraSum (left . prism sta bt $ p)

-- | TODO: Document
--
clonePrism :: APrism s t a b -> Prism s t a b
clonePrism o = withPrism o prism

-- | TODO: Document
--
cloneReprism :: AReprism s t a b -> Reprism s t a b
cloneReprism o = withReprism o reprism

---------------------------------------------------------------------
-- 'Ixprism' & 'Rxprism'
---------------------------------------------------------------------

-- | Obtain an 'Ixprism'' from a reviewer and an indexed matcher function.
--
jprism :: (i -> s -> t + a) -> (b -> t) -> Ixprism i s t a b
jprism ista = prism $ \(i,s) -> fmap (i,) (ista i s)

iprism :: (s -> t + (i , a)) -> (b -> t) -> Ixprism i s t a b
iprism stia = prism $ stia . snd

iprism' :: (s -> Maybe (i , a)) -> (a -> s) -> Ixprism' i s a
iprism' sia = iprism $ \s -> maybe (Left s) Right (sia s)

-- | Obtain an 'Ixprism'' from a reviewer and an indexed matcher function that produces a 'Maybe'.
--
jprism' :: (i -> s -> Maybe a) -> (a -> s) -> Ixprism' i s a
jprism' isa = prism $ \(i,s) -> maybe (Left s) (Right . (i,)) (isa i s)

-- | Obtain an 'Rxprism' from an indexed reviewer and a matcher function.
--
rprism :: Monoid r => (r -> s -> a) -> (b -> a + t) -> Rxprism r s t a b
rprism rsa bat = reprism (const mempty &&& uncurry rsa) (B.first (mempty,) . bat)

-- | Obtain an 'Rxprism'' from an indexed reviewer and a matcher function that produces a 'Maybe'.
--
rprism' :: Monoid r => (r -> s -> a) -> (a -> Maybe s) -> Rxprism' r s a
rprism' rsa = reprism' (rsa mempty)

---------------------------------------------------------------------
-- 'PrismRep' & 'ReprismRep'
---------------------------------------------------------------------

type APrism s t a b = Optic (PrismRep a b) s t a b

type APrism' s a = APrism s s a a

-- | The 'PrismRep' profunctor precisely characterizes a 'Prism'.
--
data PrismRep a b s t = PrismRep (s -> t + a) (b -> t)

instance Functor (PrismRep a b s) where
  fmap f (PrismRep sta bt) = PrismRep (first f . sta) (f . bt)
  {-# INLINE fmap #-}

instance Profunctor (PrismRep a b) where
  dimap f g (PrismRep sta bt) = PrismRep (first g . sta . f) (g . bt)
  {-# INLINE dimap #-}

  lmap f (PrismRep sta bt) = PrismRep (sta . f) bt
  {-# INLINE lmap #-}

  rmap = fmap
  {-# INLINE rmap #-}

instance Choice (PrismRep a b) where
  left' (PrismRep sta bt) = PrismRep (either (first Left . sta) (Left . Right)) (Left . bt)
  {-# INLINE left' #-}

  right' (PrismRep sta bt) = PrismRep (either (Left . Left) (first Right . sta)) (Right . bt)
  {-# INLINE right' #-}

type AReprism s t a b = Optic (ReprismRep a b) s t a b

type AReprism' s a = AReprism s s a a

data ReprismRep a b s t = ReprismRep (s -> a) (b -> a + t) 

instance Functor (ReprismRep a b s) where
  fmap f (ReprismRep sa bat) = ReprismRep sa (second f . bat)
  {-# INLINE fmap #-}

instance Profunctor (ReprismRep a b) where
  lmap f (ReprismRep sa bat) = ReprismRep (sa . f) bat
  {-# INLINE lmap #-}

  rmap = fmap
  {-# INLINE rmap #-}

instance Cochoice (ReprismRep a b) where
  unleft (ReprismRep sca batc) = ReprismRep (sca . Left) (forgetr $ either (eassocl . batc) Right)
  {-# INLINE unleft #-}

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Extract the two functions that characterize a 'Prism'.
--
withPrism :: APrism s t a b -> ((s -> t + a) -> (b -> t) -> r) -> r
withPrism o f = case o (PrismRep Right id) of PrismRep g h -> f g h

-- | Extract the two functions that characterize a 'Reprism'.
--
withReprism :: AReprism s t a b -> ((s -> a) -> (b -> a + t) -> r) -> r
withReprism o f = case o (ReprismRep id Right) of ReprismRep g h -> f g h

---------------------------------------------------------------------
-- Common 'Prism's and 'Reprism's
---------------------------------------------------------------------

-- | 'Prism' into the `Left` constructor of `Either`.
--
left :: Prism (a + c) (b + c) a b
left = left'

-- | 'Prism' into the `Right` constructor of `Either`.
--
right :: Prism (c + a) (c + b) a b
right = right'

-- | 'Reprism' out of the `Left` constructor of `Either`.
--
releft :: Reprism a b (a + c) (b + c)
releft = unleft

-- | 'Reprism' out of the `Right` constructor of `Either`.
--
reright :: Reprism a b (c + a) (c + b)
reright = unright

-- | 'Prism' into the `Just` constructor of `Maybe`.
--
just :: Prism (Maybe a) (Maybe b) a b
just = flip prism Just $ maybe (Left Nothing) Right

-- | 'Prism' into the `Nothing` constructor of `Maybe`.
--
nothing :: Prism (Maybe a) (Maybe b) () ()
nothing = flip prism  (const Nothing) $ maybe (Right ()) (const $ Left Nothing)

-- | Match a given key to obtain the associated value. 
--
keyed :: Eq a => a -> Prism' (a , b) b
keyed x = flip prism ((,) x) $ \kv@(k,v) -> branch (==x) kv v k

-- | Filter another optic.
--
-- >>> [1..10] ^.. folded . filtered even
-- [2,4,6,8,10]
--
filtered :: (a -> Bool) -> Prism' a a
filtered f = iso (branch' f) join . right 

-- | Focus on comparability to a given element of a partial order.
--
compared :: Eq a => Prd a => a -> Prism' a Ordering
compared x = flip prism' (const x) (pcompare x)

-- | 'Prism' into the remainder of a list with a given prefix.
--
prefixed :: Eq a => [a] -> Prism' [a] [a]
prefixed ps = prism' (stripPrefix ps) (ps ++)

-- | Focus not just on a case, but a specific value of that case.
--
only :: Eq a => a -> Prism' a ()
only x = nearly x (x==)

-- | Create a 'Prism' from a value and a predicate.
--
nearly :: a -> (a -> Bool) -> Prism' a ()
nearly x f = prism' (guard . f) (const x)

-- | Focus on the truth value of the nth bit in a bit array.
--
nthbit :: Bits s => Int -> Prism' s ()
nthbit n = prism' (guard . (flip testBit n)) (const $ bit n)

-- | Check whether an exception is synchronous.
--
sync :: Exception e => Prism' e e 
sync = filtered $ \e -> case fromException (toException e) of
  Just (SomeAsyncException _) -> False
  Nothing -> True

-- | Check whether an exception is asynchronous.
--
async :: Exception e => Prism' e e 
async = filtered $ \e -> case fromException (toException e) of
  Just (SomeAsyncException _) -> True
  Nothing -> False

-- | TODO: Document
--
exception :: Exception e => Prism' SomeException e
exception = prism' fromException toException

-- | TODO: Document
--
asyncException :: Exception e => Prism' SomeException e
asyncException = prism' asyncExceptionFromException asyncExceptionToException

---------------------------------------------------------------------
-- Indexed 'Prism's and 'Reprism's
---------------------------------------------------------------------

-- | Indexed 'Prism' into the `Left` constructor of `Either`.
--
ileft :: Ixprism i (a + c) (b + c) a b
ileft = lmap assocl' . left'

-- | Indexed 'Prism' into the `Right` constructor of `Either`.
--
iright :: Ixprism i (c + a) (c + b) a b
iright = lmap (traverse eswap . fmap eswap) . right'

-- | Indexed 'Rxprism' out of the `Left` constructor of `Either`.
--
rleft :: Monoid r => Rxprism r a b (a + c) (b + c)
rleft = unleft . lmap (either (fmap Left) ((mempty,) . Right))

-- | Indexed 'Rxprism' out of the `Right` constructor of `Either`.
--
rright :: Monoid r => Rxprism r a b (c + a) (c + b)
rright = unright . lmap (either ((mempty,) . Left) (fmap Right))
