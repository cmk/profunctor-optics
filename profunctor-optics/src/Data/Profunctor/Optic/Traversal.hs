{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Traversal (
    -- * Traversal & Ixtraversal
    Traversal
  , Traversal'
  , Ixtraversal
  , Ixtraversal'
  , traversing
  , itraversing
  , traversalVl
  , itraversalVl
  , noix
  , ix
    -- * Cotraversal & Cxtraversal
  , Cotraversal
  , Cotraversal'
  , retraversing
  , cotraversing
  , cotraversalVl
  , retraversing
    -- * Optics
  , traversed
  , itraversedRep
  , both
  , duplicated
  , bitraversed
  , cotraversed
    -- * Primitive operators
  , withTraversal
  , withCotraversal
    -- * Operators
  , sequences
  , distributes 
    -- * Carriers
  , ATraversal
  , ATraversal'
  , ACotraversal
  , ACotraversal'
) where

import Control.Category
import Control.Arrow
import Data.Bitraversable
import Data.List.NonEmpty as NonEmpty
import Data.Profunctor.Optic.Grate
import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.Import hiding (id,(.))
import Data.Profunctor.Optic.Types
import Data.Semigroupoid
import Data.Semiring
import Control.Monad.Trans.State
import Prelude (Foldable(..), reverse)
import qualified Data.Functor.Rep as F

import Control.Applicative
import Control.Comonad
import Control.Monad.Reader.Class
import Control.Monad.Fix
import Control.Monad.Zip
import Data.Distributive
import Data.Foldable
import Data.Profunctor.Closed
import Data.Profunctor
import Data.Profunctor.Sieve
import Data.Profunctor.Rep as Profunctor
import Data.Profunctor.Unsafe
import Unsafe.Coerce

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XFlexibleContexts
-- >>> :set -XTypeApplications
-- >>> :set -XTupleSections
-- >>> :set -XRankNTypes
-- >>> import Data.Maybe
-- >>> import Data.Int.Instance ()
-- >>> import Data.List.NonEmpty (NonEmpty(..))
-- >>> import qualified Data.List.NonEmpty as NE
-- >>> import Data.Functor.Identity
-- >>> import Data.List.Index
-- >>> :load Data.Profunctor.Optic
-- >>> let catchOn :: Int -> Cxprism' Int (Maybe String) String ; catchOn n = kjust $ \k -> if k==n then Just "caught" else Nothing
-- >>> let itraversed :: Ixtraversal Int [a] [b] a b ; itraversed = itraversalVl itraverse

type ATraversal f s t a b = Applicative f => ARepn f s t a b

type ATraversal' f s a = ATraversal f s s a a

type ACotraversal f s t a b = Coapplicative f => ACorepn f s t a b

type ACotraversal' f s a = ACotraversal f s s a a

---------------------------------------------------------------------
-- 'Traversal' & 'Ixtraversal'
---------------------------------------------------------------------

-- | Obtain a 'Traversal' by lifting a lens getter and setter into a 'Traversable' functor.
--
-- @
--  'withLens' o 'traversing' ≡ 'traversed' . o
-- @
--
-- Compare 'Data.Profunctor.Optic.Moore.folding'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input functions constitute a legal lens:
--
-- * @sa (sbt s a) ≡ a@
--
-- * @sbt s (sa s) ≡ s@
--
-- * @sbt (sbt s a1) a2 ≡ sbt s a2@
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- The resulting optic can detect copies of the lens stucture inside
-- any 'Traversable' container. For example:
--
-- >>> lists (traversing snd $ \(s,_) b -> (s,b)) [(0,'f'),(1,'o'),(2,'o'),(3,'b'),(4,'a'),(5,'r')]
-- "foobar"
--
traversing :: Traversable f => (s -> a) -> (s -> b -> t) -> Traversal (f s) (f t) a b
traversing sa sbt = repn traverse . lens sa sbt

-- | Obtain a 'Ixtraversal' by lifting an indexed lens getter and setter into a 'Traversable' functor.
--
-- @
--  'withIxlens' o 'itraversing' ≡ 'itraversed' . o
-- @
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input functions constitute a legal 
-- indexed lens:
--
-- * @snd . sia (sbt s a) ≡ a@
--
-- * @sbt s (snd $ sia s) ≡ s@
--
-- * @sbt (sbt s a1) a2 ≡ sbt s a2@
--
-- See 'Data.Profunctor.Optic.Property'.
--
itraversing :: Monoid i => Traversable f => (s -> (i , a)) -> (s -> b -> t) -> Ixtraversal i (f s) (f t) a b
itraversing sia sbt = repn (\iab -> traverse (curry iab mempty) . snd) . ilens sia sbt 

-- | Obtain a profunctor 'Traversal' from a Van Laarhoven 'Traversal'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @abst pure ≡ pure@
--
-- * @fmap (abst f) . abst g ≡ getCompose . abst (Compose . fmap f . g)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
traversalVl :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> Traversal s t a b
traversalVl abst = tabulate . abst . sieve

-- | Lift an indexed VL traversal into an indexed profunctor traversal.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @iabst (const pure) ≡ pure@
--
-- * @fmap (iabst $ const f) . (iabst $ const g) ≡ getCompose . iabst (const $ Compose . fmap f . g)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
itraversalVl :: (forall f. Applicative f => (i -> a -> f b) -> s -> f t) -> Ixtraversal i s t a b
itraversalVl f = traversalVl $ \iab -> f (curry iab) . snd

-- | Lift a VL traversal into an indexed profunctor traversal that ignores its input.
--
-- Useful as the first optic in a chain when no indexed equivalent is at hand.
--
-- >>> ilists (noix traversed . itraversed) ["foo", "bar"]
-- [(0,'f'),(1,'o'),(2,'o'),(0,'b'),(1,'a'),(2,'r')]
--
-- >>> ilists (itraversed . noix traversed) ["foo", "bar"]
-- [(0,'f'),(0,'o'),(0,'o'),(0,'b'),(0,'a'),(0,'r')]
--
noix :: Monoid i => Traversal s t a b -> Ixtraversal i s t a b
noix o = itraversalVl $ \iab s -> flip runStar s . o . Star $ iab mempty

-- | Index a traversal with a 'Data.Semiring'.
--
-- >>> ilists (ix traversed . ix traversed) ["foo", "bar"]
-- [((),'f'),((),'o'),((),'o'),((),'b'),((),'a'),((),'r')]
--
-- >>> ilists (ix @Int traversed . ix traversed) ["foo", "bar"]
-- [(0,'f'),(1,'o'),(2,'o'),(0,'b'),(1,'a'),(2,'r')]
--
-- >>> ilists (ix @[()] traversed . ix traversed) ["foo", "bar"]
-- [([],'f'),([()],'o'),([(),()],'o'),([],'b'),([()],'a'),([(),()],'r')]
--
-- >>> ilists (ix @[()] traversed % ix traversed) ["foo", "bar"]
-- [([],'f'),([()],'o'),([(),()],'o'),([()],'b'),([(),()],'a'),([(),(),()],'r')]
--
ix :: Monoid i => Semiring i => Traversal s t a b -> Ixtraversal i s t a b
ix o = itraversalVl $ \f s ->
  flip evalState mempty . getCompose . flip runStar s . o . Star $ \a ->
    Compose $ (f <$> get <*> pure a) <* modify (<> sunit) 

---------------------------------------------------------------------
-- 'Cotraversal' & 'Cxtraversal'
---------------------------------------------------------------------

-- | Obtain a 'Cotraversal' by embedding a continuation into a 'Distributive' functor. 
--
-- @
--  'withGrate' o 'cotraversing' ≡ 'cotraversed' . o
-- @
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input function satisfies the following
-- properties:
--
-- * @sabt ($ s) ≡ s@
--
-- * @sabt (\k -> f (k . sabt)) ≡ sabt (\k -> f ($ k))@
--
cotraversing :: Distributive g => (((s -> a) -> b) -> t) -> Cotraversal (g s) (g t) a b
cotraversing sabt = corepn cotraverse . grate sabt

-- | Obtain a profunctor 'Cotraversal' from a Van Laarhoven 'Cotraversal'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @abst runIdentity ≡ runIdentity@
--
-- * @abst f . fmap (abst g) ≡ abst (f . fmap g . getCompose) . Compose@
--
-- See 'Data.Profunctor.Optic.Property'.
--
cotraversalVl :: (forall f. Coapplicative f => (f a -> b) -> f s -> t) -> Cotraversal s t a b
cotraversalVl abst = cotabulate . abst . cosieve 

-- | Obtain a 'Cotraversal' by embedding a reversed lens getter and setter into a 'Distributive' functor.
--
-- @
--  'withLens' ('re' o) 'cotraversing' ≡ 'cotraversed' . o
-- @
--
retraversing :: Distributive g => (b -> t) -> (b -> s -> a) -> Cotraversal (g s) (g t) a b
retraversing bsa bt = corepn cotraverse . (re $ lens bsa bt)

---------------------------------------------------------------------
-- Optics
---------------------------------------------------------------------

-- | TODO: Document
--
traversed :: Traversable f => Traversal (f a) (f b) a b
traversed = traversalVl traverse

-- | TODO: Document
--
itraversedRep :: F.Representable f => Traversable f => Ixtraversal (F.Rep f) (f a) (f b) a b
itraversedRep = itraversalVl F.itraverseRep

-- | TODO: Document
--
-- >>> withTraversal both (pure . length) ("hello","world")
-- (5,5)
--
both :: Traversal (a , a) (b , b) a b
both p = p **** p

-- | Duplicate the results of any 'Moore'. 
--
-- >>> lists (both . duplicated) ("hello","world")
-- ["hello","hello","world","world"]
--
duplicated :: Traversal a b a b
duplicated p = pappend p p

-- | Traverse both parts of a 'Bitraversable' container with matching types.
--
-- >>> withTraversal bitraversed (pure . length) (Right "hello")
-- Right 5
--
-- >>> withTraversal bitraversed (pure . length) ("hello","world")
-- (5,5)
--
-- >>> ("hello","world") ^. bitraversed
-- "helloworld"
--
-- @
-- 'bitraversed' :: 'Traversal' (a , a) (b , b) a b
-- 'bitraversed' :: 'Traversal' (a + a) (b + b) a b
-- @
--
bitraversed :: Bitraversable f => Traversal (f a a) (f b b) a b
bitraversed = repn $ \f -> bitraverse f f
{-# INLINE bitraversed #-}

-- | TODO: Document
--
cotraversed :: Distributive f => Cotraversal (f a) (f b) a b 
cotraversed = cotraversalVl cotraverse
{-# INLINE cotraversed #-}

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | 
--
-- The traversal laws can be stated in terms of 'withTraversal':
-- 
-- * @withTraversal t (pure . f) ≡  pure (fmap f)@
--
-- * @Compose . fmap (withTraversal t f) . withTraversal t g ≡ withTraversal t (Compose . fmap f . g)@
--
withTraversal :: Applicative f => ATraversal f s t a b -> (a -> f b) -> s -> f t
withTraversal o = runStar #. o .# Star

-- |
--
-- @
-- 'withCotraversal' $ 'Data.Profuncto.Optic.Grate.grate' (flip 'Data.Distributive.cotraverse' id) ≡ 'Data.Distributive.cotraverse'
-- @
--
-- The cotraversal laws can be restated in terms of 'withCotraversal':
--
-- * @withCotraversal o (f . runIdentity) ≡  fmap f . runIdentity@
--
-- * @withCotraversal o f . fmap (withCotraversal o g) == withCotraversal o (f . fmap g . getCompose) . Compose@
--
-- See also < https://www.cs.ox.ac.uk/jeremy.gibbons/publications/iterator.pdf >
--
withCotraversal :: Coapplicative f => ACotraversal f s t a b -> (f a -> b) -> (f s -> t)
withCotraversal o = runCokleisli #. o .# Cokleisli

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | TODO: Document
--
sequences :: Applicative f => ATraversal f s t (f a) a -> s -> f t
sequences o = withTraversal o id
{-# INLINE sequences #-}

-- | TODO: Document
--
-- >>> distributes left' (1, Left "foo")
-- Left (1,"foo")
--
-- >>> distributes left' (1, Right "foo")
-- Right "foo"
--
distributes :: Coapplicative f => ACotraversal f s t a (f a) -> f s -> t
distributes o = withCotraversal o id
{-# INLINE distributes #-}
