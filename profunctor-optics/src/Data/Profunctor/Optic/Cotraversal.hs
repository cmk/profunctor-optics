{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Cotraversal (
    -- * Cotraversal & Cxtraversal
    Cotraversal
  , Cotraversal'
  , cotraversing
  , retraversing
  , cotraversalVl
    -- * Optics
  , cotraversed
    -- * Operators
  , (/~)
  , (//~)
  , withCotraversal
  , distributes 
) where

import Data.Bitraversable
import Data.List.NonEmpty as NonEmpty
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Grate
import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.Import hiding (id,(.))
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Operator
import Data.Semigroupoid
import Data.Semiring
import Control.Monad.Trans.State
import Prelude (Foldable(..), reverse)
import qualified Data.Functor.Rep as F

import Control.Applicative
import Data.Ord
import Data.Function
import Prelude
import Data.Semigroup.Foldable as F1
import Data.Foldable as F
import Data.List as L
import Data.List.NonEmpty as L1

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XFlexibleContexts
-- >>> :set -XTypeApplications
-- >>> :set -XTupleSections
-- >>> :set -XRankNTypes
-- >>> import Data.Maybe
-- >>> import Data.Int.Instance ()
-- >>> import Data.List.NonEmpty (NonEmpty(..))
-- >>> import Data.Functor.Identity
-- >>> import Data.List.Index
-- >>> :load Data.Profunctor.Optic
-- >>> let catchOn :: Int -> Cxprism' Int (Maybe String) String ; catchOn n = kjust $ \k -> if k==n then Just "caught" else Nothing

---------------------------------------------------------------------
-- 'Cotraversal'
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

-- | Obtain a 'Cotraversal' by embedding a reversed lens getter and setter into a 'Distributive' functor.
--
-- @
--  'withLens' ('re' o) 'cotraversing' ≡ 'cotraversed' . o
-- @
--
retraversing :: Distributive g => (b -> t) -> (b -> s -> a) -> Cotraversal (g s) (g t) a b
retraversing bsa bt = corepn cotraverse . (re $ lens bsa bt)

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

---------------------------------------------------------------------
-- Optics
---------------------------------------------------------------------

-- | TODO: Document
--
cotraversed :: Distributive f => Cotraversal (f a) (f b) a b 
cotraversed = cotraversalVl cotraverse
{-# INLINE cotraversed #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

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
withCotraversal = withCostar
{-# INLINE withCotraversal #-}

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
