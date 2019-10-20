{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | A collection of properties that can be tested with QuickCheck, to guarantee
-- that you are working with valid 'Lens'es, 'Setter's, 'Traversal's, 'Iso's and
-- 'Prism's.
module Data.Profunctor.Optic.Property where

import Control.Applicative
--import Data.Functor.Compose
--import Data.Functor.Identity

import Data.Profunctor.Optic

import Test.QuickCheck
import Test.QuickCheck.Function
--import Test.QuickCheck.Instances
import Data.Tagged
data FreeTambaraR ten s t a b = forall x. FreeTambaraR (s -> x `ten` a) (x `ten` b -> t)


---------------------------------------------------------------------
-- 'Iso'
---------------------------------------------------------------------

--isIso :: (Arbitrary s, Arbitrary a, CoArbitrary s, CoArbitrary a, Show s, Show a, Eq s, Eq a, Function s, Function a) => Iso' s a -> Property
--isIso o = iso_fromto o .&. iso_2 o .&. isLens o .&. isLens (from l)


iso_fromto' :: Eq s => Iso' s a -> s -> Bool
iso_fromto' o = withIso o iso_fromto

iso_tofrom' :: Eq a => Iso' s a -> a -> Bool
iso_tofrom' o = withIso o iso_tofrom

iso_fromto :: Eq s => (s -> a) -> (a -> s) -> s -> Bool
iso_fromto sa as s = as (sa s) == s

iso_tofrom :: Eq a => (s -> a) -> (a -> s) -> a -> Bool
iso_tofrom sa as a = sa (as a) == a

---------------------------------------------------------------------
-- 'Prism'
---------------------------------------------------------------------


{- prism laws:

Prism is the characterization of a Choice profunctor. It identifies 
objects as consisting of a sum of two components.

prism_complete :: Prism s t a b -> Bool
prism_complete p = tripping p $ prism (preview p) (matching p)

They have two operations: matchOf and build. The first one tries to extract the focus value from the whole one, but if it's not possible, it provides the final value for t. On the other hand, build is always able to construct the whole value, given the focus one. As expected, this optic should hold the following properties.


First, if I review a value with a Prism and then preview, I will get it back:

preview o (review o b) ≡ Just b

If you can extract a value a using a Prism o from a value s, then the value s is completely described by o and a:
preview o s ≡ Just a ⇒ review o a ≡ s

-}

--isPrism :: (Arbitrary s, Arbitrary a, CoArbitrary a, Show s, Show a, Eq s, Eq a, Function a) => Prism' s a -> Property
--isPrism o = isTraversal o .&. prism_fromto o .&. prism_2 l


-- If we are able to view an existing focus, then building it will return the original structure. 
prism_tofrom :: Eq s => (s -> s + a) -> (a -> s) -> s -> Bool
prism_tofrom seta bt s = either id bt (seta s) == s

-- If we build a whole from any focus, that whole must contain a focus.
prism_fromto :: Eq s => Eq a => (s -> s + a) -> (a -> s) -> a -> Bool
prism_fromto seta bt a = seta (bt a) == Right a

prism_tofrom' :: Eq s => Prism' s a -> s -> Bool
prism_tofrom' o = withPrism o prism_tofrom

-- Reviewing a value with a 'Prism' and then previewing returns the value.
prism_fromto' :: Eq s => Eq a => Prism' s a -> a -> Bool
prism_fromto' o = withPrism o prism_fromto

---------------------------------------------------------------------
-- 'Lens'
---------------------------------------------------------------------


-- | A 'Lens' is only legal if it is a valid 'Traversal' (see 'isTraversal' for
-- what this means), and if the following laws hold:
--
-- 1. @view o (set o b a)  ≡ b@
--
-- 2. @set o (view o a) a  ≡ a@
--
-- 3. @set o c (set o b a) ≡ set o c a@
--isLens :: (Arbitrary s, Arbitrary a, CoArbitrary a, Show s, Show a, Eq s, Eq a, Function a) => Lens' s a -> Property
--isLens o = lens_fromto o .&. lens_2 o .&. isTraversal l

lens_tofrom :: Eq s => (s -> a) -> (s -> a -> s) -> s -> Bool
lens_tofrom sa sas s = sas s (sa s) == s

lens_fromto :: Eq a => (s -> a) -> (s -> a -> s) -> s -> a -> Bool
lens_fromto sa sas s a = sa (sas s a) == a

lens_idempotent :: Eq s => (s -> a -> s) -> s -> a -> a -> Bool
lens_idempotent sas s a1 a2 = sas (sas s a1) a2 == sas s a2 

-- | Putting back what you got doesn't change anything.
lens_tofrom' :: Eq s => Lens' s a -> s -> Bool
lens_tofrom' o = withLens o lens_tofrom

-- | You get back what you put in.
lens_fromto' :: Eq a => Lens' s a -> s -> a -> Bool
lens_fromto' o = withLens o lens_fromto

-- | Setting twice is the same as setting once.
lens_idempotent' :: Eq s => Lens' s a -> s -> a -> a -> Bool
lens_idempotent' o = withLens o $ const lens_idempotent

---------------------------------------------------------------------
-- 'Grate'
---------------------------------------------------------------------

-- | The 'grate' laws are that of an algebra for a parameterised continuation monad.
--
-- * @grate ($ s) === s@
--
-- * @grate (\k -> h (k . sabt)) === sabt (\k -> h ($ k))@
--
grate_pure :: Eq s => (((s -> a) -> a) -> s) -> s -> Bool
grate_pure sabt s = sabt ($ s) == s 

grate_pure' :: Eq s => (((s -> a) -> a) -> s) -> s -> a -> Bool
grate_pure' sabt s a = sabt (const a) == s

--grate_compose :: Eq s => (((s -> a) -> a) -> s) -> (a -> a) -> Bool
--grate_compose sabt h = \k -> h (k . sabt) == sabt (\k -> h ($ k)) 

--grate_compose :: Eq s => GrateRep a a s s -> (s -> a) ->  (s -> c0) -> Bool
grate_compose (GrateRep sabt) h = \k1 -> h (k1 . sabt) == sabt (\k2 -> h ($ k2)) 

--foo p = (id *** p) . _Just

---------------------------------------------------------------------
-- 'Traversal0'
---------------------------------------------------------------------

atraversal_tofrom :: Eq a => Eq s => (s -> s + a) -> (s -> a -> s) -> s -> a -> Bool
atraversal_tofrom seta sbt s a = seta (sbt s a) == either (Left . flip const a) Right (seta s)

atraversal_fromto :: Eq s => (s -> s + a) -> (s -> a -> s) -> s -> Bool
atraversal_fromto seta sbt s = either id (sbt s) (seta s) == s

atraversal_idempotent :: Eq s => (s -> a -> s) -> s -> a -> a -> Bool
atraversal_idempotent sbt s a1 a2 = sbt (sbt s a1) a2 == sbt s a2

atraversal_tofrom' :: Eq a => Eq s => Traversal0' s a -> s -> a -> Bool
atraversal_tofrom' o = withTraversal0 o atraversal_tofrom

atraversal_fromto' :: Eq s => Traversal0' s a -> s -> Bool
atraversal_fromto' o = withTraversal0 o atraversal_fromto

atraversal_idempotent' :: Eq s => Traversal0' s a -> s -> a -> a -> Bool
atraversal_idempotent' o = withTraversal0 o $ const atraversal_idempotent

---------------------------------------------------------------------
-- 'Traversal'
---------------------------------------------------------------------

{-

-- | A 'Traversal' is only legal if it is a valid 'Setter' (see 'isSetter' for
-- what makes a 'Setter' valid), and the following laws hold:
--
-- 1. @t pure ≡ pure@
--
-- 2. @fmap (t f) . t g ≡ getCompose . t (Compose . fmap f . g)@
isTraversal :: (Arbitrary s, Arbitrary a, CoArbitrary a, Show s, Show a, Eq s, Function a)
         => Traversal' s a -> Property
isTraversal o = isSetter o .&. traverse_pureMaybe o .&. traverse_pureList l
                  .&. do as <- arbitrary
                         bs <- arbitrary
                         t <- arbitrary
                         return $ traverse_compose o (\x -> as++[x]++bs)
                                                     (\x -> if t then Just x else Nothing)

--traverse_pure :: forall f s a. (Applicative f, Eq (f s)) => LensLike' f s a -> s -> Bool
traverse_pure o s = o pure s == (pure s :: f s)

--traverse_pureMaybe :: Eq s => LensLike' Maybe s a -> s -> Bool
traverse_pureMaybe = traverse_pure

--traverse_pureList :: Eq s => LensLike' [] s a -> s -> Bool
traverse_pureList = traverse_pure

--traverse_compose :: (Applicative f, Applicative g, Eq (f (g s))) => Traversal' s a -> (a -> g a) -> (a -> f a) -> s -> Bool
traverse_compose t f g s = (fmap (t f) . t g) s == (getCompose . t (Compose . fmap f . g)) s
-}

---------------------------------------------------------------------
-- 'Getter'
---------------------------------------------------------------------

-- laws 
-- view_complete :: Getter s a -> Bool
-- view_complete o = tripping o $ to (view o)


---------------------------------------------------------------------
-- 'Setter'
---------------------------------------------------------------------

-- | A 'Setter' is only legal if the following 3 laws hold:
--
-- 1. @set o y (set o x a) ≡ set o y a@
--
-- 2. @over o id ≡ id@
--
-- 3. @over o f . over o g ≡ over o (f . g)@

setter_id :: Eq s => Setter' s a -> s -> Bool
setter_id o s = over o id s == s

setter_compose :: Eq s => Setter' s a -> (a -> a) -> (a -> a) -> s -> Bool
setter_compose o f g s = (over o f . over o g) s == over o (f . g) s

setter_idempotent :: Eq s => Setter' s a -> s -> a -> a -> Bool
setter_idempotent o s a b = set o b (set o a s) == set o b s
