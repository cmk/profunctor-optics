{-# LANGUAGE DeriveFunctor #-}

module Data.Profunctor.Optic.Setter where


import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Review (re)
import Data.Profunctor.Task
import Data.Profunctor.Optic.Prelude hiding (Bifunctor(..))
import Data.Profunctor.Optic.Grate -- (withGrate, forgotten)

import Control.Applicative (liftA)
import Control.Monad.State as State hiding (lift)
import Control.Monad.Writer as Writer hiding (lift)
import Control.Monad.Reader as Reader hiding (lift)

import qualified Control.Exception as Ex

import Data.Profunctor.Optic.Prism



import qualified Data.Functor.Rep as F


---------------------------------------------------------------------
-- Setter
---------------------------------------------------------------------


-- | Promote a <http://conal.net/blog/posts/semantic-editor-combinators semantic editor combinator> to a modify-only optic.
--
-- To demote an optic to a semantic edit combinator, use the section @(l %~)@ or @over l@.
--
-- >>> [("The",0),("quick",1),("brown",1),("fox",2)] & setting map . _1 %~ length
-- [(3,0),(5,1),(5,1),(3,2)]
--
-- /Caution/: In order for the generated family to be well-defined, you must ensure that the two functor laws hold:
--
-- * @sec id ≡ id@
--
-- * @sec f . sec g ≡ sec (f . g)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
setting :: ((a -> b) -> s -> t) -> Setter s t a b 
setting f = dimap (\s -> Bar $ \ab -> f ab s) lent . map'

-- | TODO: Document
--
lifting :: F.Representable (Rep p) => ((a -> b) -> s -> t) -> Over p s t a b
lifting f = lift $ genMap' f

-- | SEC on each value of a functor
mapping :: Functor f => Setter (f a) (f b) a b
mapping = map'

-- | TODO: Document
--
grating :: Functor f => (((s -> f a) -> f b) -> t) -> Setter s t a b
grating f = dimap pureTaskF (f . runTask) . map' 

-- | Every 'Grate' is a 'Setter'.
--
grated :: (((s -> a) -> b) -> t) -> Setter s t a b
grated sabt = setting $ lowerGrate sabt
  where lowerGrate sabt ab s = sabt $ \sa -> ab (sa s)

---------------------------------------------------------------------
-- 'SetterRep'
---------------------------------------------------------------------

genMap :: Distributive f => ((a -> b) -> s -> t) -> (a -> f b) -> s -> f t
genMap abst afb s = fmap (\ab -> abst ab s) (distribute afb)

genMap' :: F.Representable f => ((a -> b) -> s -> t) -> (a -> f b) -> s -> f t
genMap' f afb s = F.tabulate $ \i -> f (flip F.index i . afb) s

--roam :: ((i -> Store i v v) -> s -> Store a b t) -> Setter s t a b --Like p s t a b
--roam l = dimap ((values &&& info) . l (Store id)) eval . map'



newtype Bar t b a = Bar
  { runBar :: (a -> b) -> t }
  deriving Functor

lent :: Bar t a a -> t
lent m = runBar m id

--prim_setter :: Choice p => (forall x. Applicative (p x)) => p a b -> p (Store a c t) (Store b c t)

--prim_setter p = pure (\c -> (undefined, c)) <*> (puncurry . closed $ p)

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- mapOf l id ≡ id
-- mapOf l f . mapOf l g ≡ mapOf l (f . g)
--
-- 'mapOf' ('cayley' a) ('Data.Semiring.one' <>) 'Data.Semiring.zero' ≡ a
--
-- ^ @
-- mapOf :: Setter s t a b -> (a -> r) -> s -> r
-- mapOf :: Monoid r => Fold s t a b -> (a -> r) -> s -> r
-- @
mapOf :: Optic (->) s t a b -> (a -> b) -> s -> t
mapOf = over 

-- | TODO: Document
--
remapOf :: Optic (Re (->) a b) s t a b -> (t -> s) -> (b -> a)
remapOf = re

-- | Modify the target of a 'Lens' or all the targets of a 'Setter' or 'Traversal'.
--
-- @
-- 'over' l f '.' 'over' l g = 'over' l (f '.' g)
-- @
--
--
-- >>> over mapped f (over mapped g [a,b,c]) == over mapped (f . g) [a,b,c]
-- True
--
-- >>> over mapped f (Just a)
-- Just (f a)
--
-- >>> over mapped (*10) [1,2,3]
-- [10,20,30]
--
-- >>> over _1 f (a,b)
-- (f a,b)
--
-- >>> over _1 show (10,20)
-- ("10",20)
--
-- @
-- 'fmap' ≡ 'over' 'mapped'
-- 'setting' '.' 'over' ≡ 'id'
-- 'over' '.' 'setting' ≡ 'id'
-- @
--
over :: Optic (->) s t a b -> (a -> b) -> s -> t
over = id

infixr 4 %~

-- | TODO: Document
--
(%~) :: Optic (->) s t a b -> (a -> b) -> s -> t
(%~) = id
{-# INLINE (%~) #-}

infixr 4 .~

-- | TODO: Document
--
(.~) :: Optic (->) s t a b -> b -> s -> t
(.~) = set
{-# INLINE (.~) #-}

-- set l y (set l x a) ≡ set l y a
-- \c -> set (setting . runCayley $ c) zero one ≡ lowerCayey c

-- | Set all referenced fields to the given value.
--
set :: Optic (->) s t a b -> b -> s -> t
set o b s = o (const b) s

--set . re :: Colens s t a b -> s -> b -> a
--reset :: Optic (Re (->) a b) s t a b -> b -> s -> a
--reset o = set o . re

-- | Set all referenced fields to the given value.
--reset :: AResetter s t a b -> b -> s -> t
--reset l b = under l (const b)

appendSetter :: Semigroup a => Setter s t a a -> a -> s -> t
appendSetter o = o . (<>)

---------------------------------------------------------------------
-- Common setters
---------------------------------------------------------------------

-- | Map contravariantly by setting the input of a 'Profunctor'.
--
--
-- The most common profunctor to use this with is @(->)@.
--
-- >>> (dom %~ f) g x
-- g (f x)
--
-- >>> (dom %~ show) length [1,2,3]
-- 7
--
-- >>> (dom %~ f) h x y
-- h (f x) y
--
-- Map setting the second arg of a function:
--
-- >>> (mapped . dom %~ f) h x y
-- h x (f y)
--
dom :: Profunctor p => Setter (p b r) (p a r) a b
dom = setting lmap
{-# INLINE dom #-}

-- | A grate accessing the codomain of a function.
--
-- @
-- cod @(->) == lowerGrate range
-- @
--
cod :: Profunctor p => Setter (p r a) (p r b) a b
cod = setting rmap

-- | TODO: Document
--
masking :: Setter (IO a) (IO b) a b
masking = grating Ex.mask

-- | SEC for monadically transforming a monadic value
binding :: Monad m => Setter (m a) (m b) a (m b)
binding = setting (=<<)

-- | TODO: Document
--
foldMapped :: Foldable f => Monoid m => Setter (f a) m a m
foldMapped = setting foldMap

-- | This 'setter' can be used to modify all of the values in an 'Applicative'.
--
-- @
-- 'liftA' ≡ 'setting' 'liftedA'
-- @
--
-- >>> setting liftedA f [a,b,c]
-- [f a,f b,f c]
--
-- >>> set liftedA b (Just a)
-- Just b
liftedA :: Applicative f => Setter (f a) (f b) a b
liftedA = setting liftA

-- | TODO: Document
--
liftedM :: Monad m => Setter (m a) (m b) a b
liftedM = setting liftM

-- | Set a value using an SEC.
--
sets :: Setter b (a -> c) a c
sets = setting const

-- | TODO: Document
--
zipped :: Setter (u -> v -> a) (u -> v -> b) a b
zipped = setting ((.)(.)(.))

-- | TODO: Document
--
modded :: Setter (b -> t) (((s -> a) -> b) -> t) s a
modded = setting $ \sa bt sab -> bt (sab sa)

-- | TODO: Document
--
composed :: Setter (s -> a) ((a -> b) -> s -> t) b t
composed = setting between

-- | SEC applying the given function only when the given predicate
--  yields true for an input value.
branching :: (a -> Bool) -> Setter' a a
branching p = setting $ \f a -> if p a then f a else a

branching' :: (k -> Bool) -> Setter' (k -> v) v
branching' p = setting $ \mod f a -> if p a then mod (f a) else f a
