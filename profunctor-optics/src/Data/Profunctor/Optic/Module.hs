{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ExistentialQuantification #-}

module Data.Profunctor.Optic.Module where

import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Combinator
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.Prism
import Data.Profunctor.Optic.Types
import Data.Tuple.Optic

import Data.Kind (Type)

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XTypeOperators
-- >>> :set -XRankNTypes
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- Module
---------------------------------------------------------------------

type Is = Module Tagged

type As = Module (+)

type Has = Module (,)

type With = Module (->)

-- | A (right) Tambara module on the tensor /o/.
--
class Module (o :: Type -> Type -> Type) a s where
  optic :: FreeTambara o a a s s

-- | Obtain an iso from an 'Is' instance.
--
-- >>> view (is @Int @Int) 4
-- 4
--
is :: Is a s => Iso' s a
is = lowerIso optic

-- | Obtain a prism from an 'As' instance.
--
-- >>> review (as @Int @Int) 4
-- 4
-- >>> Left "oops" ^? as @String @(String + Int)
-- Just "oops"
--
as :: As a s => Prism' s a
as = handling' optic

-- | Obtain a coprism from an 'As' instance.
--
-- >>> 4 ^. coas @Int @(String + Int)
-- Right 4
--
coas :: As t b => Coprism' t b
coas = re $ handling' optic

-- | Obtain a lens from a 'Has' instance.
--
-- >>> (1,2,"foo") ^. has @String @(Int,Int,String)
-- "foo"
--
has :: Has a s => Lens' s a
has = matching' optic

-- | Obtain a colens from a 'Has' instance.
--
-- >>> review (cohas @Int @(Int,String)) (2, "two")
-- 2
-- >>> zipsWith2 (cohas @Int @Int) (+) 2 2
-- 4
--
cohas :: Has t b => Colens' t b
cohas = re $ matching' optic

-- | Obtain a grate from a 'With' instance.
--
-- >>> review (with @Int @Int) 4
-- 4
-- >>> zipsWith2 (with @String @String) (++) "foo" "bar" 
-- "foobar"
--
with :: With a s => Grate' s a
with = inverting' optic

-- | Obtain a traversal from a 'Has' instance.
--
-- >>> foldsr (have @Int @Int @[]) (\i -> (show i ++)) [] [1..5]
-- "12345"
--
have :: Has a s => Traversable f => Traversal' (f s) a
have = repn traverse . has

-- | Obtain a non-empty traversal from a 'Has' instance.
-- 
have1 :: Has a s => Traversable1 f => Traversal1' (f s) a
have1 = repn traverse1 . has

-- | Obtain a cotraversal from a 'Has' instance.
--
cohave :: Has t b => Distributive g => Cotraversal' (g t) b
cohave = corepn cotraverse . cohas

-- | Obtain a partial cotraversal from a 'Has' instance.
--
cohave1 :: Has t b => Distributive1 g => Cotraversal1' (g t) b
cohave1 = corepn cotraverse1 . cohas

---------------------------------------------------------------------
-- FreeTambara
---------------------------------------------------------------------

type FreeIso s t a b = FreeTambara Tagged a b s t

type FreeIso' s a = FreeIso s s a a

type FreeLens s t a b = FreeTambara (,) a b s t

type FreeLens' s a = FreeLens s s a a

type FreeGrate s t a b = FreeTambara (->) a b s t

type FreeGrate' s a = FreeGrate s s a a

type FreeColens s t a b = FreeTambara (,) t s b a

type FreeColens' t b = FreeColens b b t t

type FreePrism s t a b = FreeTambara (+) a b s t

type FreePrism' s a = FreePrism s s a a

type FreeCoprism s t a b = FreeTambara (+) t s b a

type FreeCoprism' t b = FreeCoprism t t b b

type FreeTambara' o a s = FreeTambara o a a s s

data FreeTambara o a b s t = forall x. FreeTambara (s -> x `o` a) (x `o` b -> t)

lowerIso :: FreeIso s t a b -> Iso s t a b
lowerIso (FreeTambara f g) = iso (unTagged . f) (g . Tagged)

handling' :: FreePrism s t a b -> Prism s t a b
handling' (FreeTambara f g) = handling f g

cohandling' :: FreeCoprism s t a b -> Coprism s t a b
cohandling' (FreeTambara f g) = cohandling g f

matching' :: FreeLens s t a b -> Lens s t a b
matching' (FreeTambara f g) = matching f g

comatching' :: FreeColens s t a b -> Colens s t a b
comatching' (FreeTambara f g) = comatching g f

inverting' :: FreeGrate s t a b -> Grate s t a b
inverting' (FreeTambara l r) = dimap l r . closed

liftIso :: Is a1 a2 => Iso' s a2 -> FreeIso' s a1
liftIso o = withIso (o . is) $ \ba ab -> FreeTambara (Tagged . ba) (ab . unTagged)

liftPrism :: As a1 a2 => Prism' s a2 -> FreePrism' s a1 
liftPrism o = withPrism o liftChoice

liftCoprism :: As b1 b2 => Coprism' b2 t -> FreeCoprism' b1 t
liftCoprism o = withPrism (re o) liftChoice

liftLens :: Has a1 a2 => Lens' s a2 -> FreeLens' s a1
liftLens o = withLens o liftStrong

liftColens :: Has b1 b2 => Colens' b2 t -> FreeColens' t b1
liftColens o = withLens (re o) liftStrong

liftGrate :: With a1 a2 => Grate' s a2 -> FreeGrate' s a1
liftGrate o = withGrate (o . with) $ \sabt -> FreeTambara (curry eval) sabt

liftChoice :: As a1 a2 => (s -> s + a2) -> (a2 -> s) -> FreeTambara' (+) a1 s
liftChoice ssb bs = withPrism as $ \bba ab ->
  FreeTambara (first (either id bs) . eassocl . fmap bba . ssb) (either id (bs.ab) )

liftStrong :: Has a1 a2 => (s -> a2) -> (s -> a2 -> s) -> FreeTambara' (,) a1 s
liftStrong sb sbs = withLens has $ \ba bab ->
  FreeTambara (\s -> (s, ba.sb $ s)) (\(s,a) -> sbs s (bab (sb s) a))

---------------------------------------------------------------------
-- FreeTambara instances
---------------------------------------------------------------------

instance Profunctor (FreeTambara o a b) where
  dimap f g (FreeTambara l r) = FreeTambara (l . f) (g . r) 

instance Strong (FreeTambara (,) a b) where
  second' (FreeTambara l r) = FreeTambara l' r' where
    l' (d,s) = ((d , fst (l s)), snd (l s))
    r' ((d,c),b) = (d,r (c,b))

instance Choice (FreeTambara (+) a b) where
  right' (FreeTambara l r) = FreeTambara l' r' where
    l' = (either (Left . Left) (either (Left . Right) Right . l))
    r' = (either (either Left (Right . r . Left)) (Right . r . Right))

instance Closed (FreeTambara (->) a b) where
  closed (FreeTambara l r) = FreeTambara l' r' where
    l' f (d , c) = l (f d) c
    r' = (r .) . curry

---------------------------------------------------------------------
-- Is instances
---------------------------------------------------------------------

instance Module Tagged a a where
  optic = FreeTambara Tagged unTagged 

---------------------------------------------------------------------
-- As instances
---------------------------------------------------------------------

instance Module (+) a a where
  optic = FreeTambara Right rgt'

instance Module (+) a (a + b) where
  optic = liftPrism left'

instance Module (+) b (a + b) where
  optic = liftPrism right'

instance Module (+) a (Maybe a) where
  optic = liftPrism just

instance Module (+) () (Maybe a) where
  optic = liftPrism nothing

---------------------------------------------------------------------
-- Has instances
---------------------------------------------------------------------

instance Module (,) a a where
  optic = FreeTambara ((,) ()) snd

instance Module (,) a (a , b) where
  optic = liftLens t21 

instance Module (,) b (a , b) where
  optic = liftLens t22

instance Module (,) a (a,b,c) where
  optic = liftLens t31

instance Module (,) b (a,b,c) where
  optic = liftLens t32

instance Module (,) c (a,b,c) where
  optic = liftLens t33

instance Module (,) a (a,b,c,d) where
  optic = liftLens t41

instance Module (,) b (a,b,c,d) where
  optic = liftLens t42

instance Module (,) c (a,b,c,d) where
  optic = liftLens t43

instance Module (,) d (a,b,c,d) where
  optic = liftLens t44

instance Module (,) a (a,b,c,d,e) where
  optic = liftLens t51

instance Module (,) b (a,b,c,d,e) where
  optic = liftLens t52

instance Module (,) c (a,b,c,d,e) where
  optic = liftLens t53

instance Module (,) d (a,b,c,d,e) where
  optic = liftLens t54

instance Module (,) e (a,b,c,d,e) where
  optic = liftLens t55

---------------------------------------------------------------------
-- With instances
---------------------------------------------------------------------

instance Module (->) a a where
  optic = FreeTambara const ($ ())

instance Distributive f => Module (->) a (f a) where
  optic = liftGrate distributed
