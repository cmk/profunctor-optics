{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE Trustworthy           #-}

module Data.Profunctor.Optic.Traversal1 (
    -- * Traversal1
    Traversal1
  , Traversal1'
  , Ixtraversal1
  , Ixtraversal1'
  , traversing1
  , traversal1Vl
  , itraversal1Vl
    -- * Optics
  , traversed1
  , both1
  , bitraversed1
  , repeated 
  , iterated
  , cycled
    -- * Primitive operators
  , withTraversal1
    -- * Operators
  , sequences1
    -- * Carriers
  , ATraversal1
  , ATraversal1'
) where

import Control.Category
import Control.Monad.Fix
import Control.Monad.Reader.Class
import Control.Monad.Zip
import Data.List.NonEmpty as NonEmpty
import Data.Semigroup.Bitraversable
import Data.Semigroupoid
import Data.Semiring
import Data.Profunctor.Rep as Profunctor
import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.Import hiding (id,(.))
import Data.Profunctor.Optic.Grate
import Data.Profunctor.Optic.Types
import Prelude (Foldable(..), reverse)
import Unsafe.Coerce

import qualified Data.Functor.Rep as F

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XFlexibleContexts
-- >>> :set -XTypeApplications
-- >>> :set -XTupleSections
-- >>> :set -XRankNTypes
-- >>> import Data.Complex
-- >>> import Data.Maybe
-- >>> import Data.List.NonEmpty (NonEmpty(..))
-- >>> import qualified Data.List.NonEmpty as NE
-- >>> import Data.Functor.Identity
-- >>> import Data.List.Index
-- >>> :load Data.Profunctor.Optic Data.Either.Optic Data.Tuple.Optic
-- >>> let catchOn :: Int -> Cxprism' Int (Maybe String) String ; catchOn n = kjust $ \k -> if k==n then Just "caught" else Nothing
-- >>> let itraversed :: Ixtraversal Int [a] [b] a b ; itraversed = itraversalVl itraverse


type ATraversal1 f s t a b = Apply f => ARepn f s t a b

type ATraversal1' f s a = ATraversal1 f s s a a

---------------------------------------------------------------------
-- 'Traversal1'
---------------------------------------------------------------------

-- | Obtain a 'Traversal' by lifting a lens getter and setter into a 'Traversable' functor.
--
-- @
--  'withLens' o 'traversing' ≡ 'traversed' . o
-- @
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
-- Compare 'Data.Profunctor.Optic.Fold.folding'.
--
traversing1 :: Traversable1 f => (s -> a) -> (s -> b -> t) -> Traversal1 (f s) (f t) a b
traversing1 sa sbt = repn traverse1 . lens sa sbt

-- | Obtain a profunctor 'Traversal1' from a Van Laarhoven 'Traversal1'.
--
-- /Caution/: In order for the generated family to be well-defined,
-- you must ensure that the traversal1 law holds for the input function:
--
-- * @fmap (abst f) . abst g ≡ getCompose . abst (Compose . fmap f . g)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
traversal1Vl :: (forall f. Apply f => (a -> f b) -> s -> f t) -> Traversal1 s t a b
traversal1Vl abst = tabulate . abst . sieve 

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
itraversal1Vl :: (forall f. Apply f => (i -> a -> f b) -> s -> f t) -> Ixtraversal1 i s t a b
itraversal1Vl f = traversal1Vl $ \iab -> f (curry iab) . snd



---------------------------------------------------------------------
-- Optics
---------------------------------------------------------------------

-- | Obtain a 'Traversal1' from a 'Traversable1' functor.
--
traversed1 :: Traversable1 t => Traversal1 (t a) (t b) a b
traversed1 = traversal1Vl traverse1
{-# INLINE traversed1 #-}

-- | TODO: Document
--
-- >>> withTraversal1 both1 (pure . NE.length) ('h' :| "ello", 'w' :| "orld")
-- (5,5)
--
both1 :: Traversal1 (a , a) (b , b) a b
both1 p = tabulate $ \s -> liftF2 ($) (flip sieve s $ dimap fst (,) p) (flip sieve s $ lmap snd p)
{-# INLINE both1 #-}

-- | Traverse both parts of a 'Bitraversable1' container with matching types.
--
-- >>> withTraversal1 bitraversed1 (pure . NE.length) ('h' :| "ello", 'w' :| "orld")
-- (5,5)
--
bitraversed1 :: Bitraversable1 r => Traversal1 (r a a) (r b b) a b
bitraversed1 = repn $ \f -> bitraverse1 f f
{-# INLINE bitraversed1 #-}

-- | Obtain a 'Traversal1'' by repeating the input forever.
--
-- @
-- 'repeat' ≡ 'lists' 'repeated'
-- @
--
-- >>> take 5 $ 5 ^.. repeated
-- [5,5,5,5,5]
--
-- @
-- repeated :: Fold1 a a
-- @
--
repeated :: Traversal1' a a
repeated = repn $ \g a -> go g a where go g a = g a .> go g a
{-# INLINE repeated #-}

-- | @x '^.' 'iterated' f@ returns an infinite 'Traversal1'' of repeated applications of @f@ to @x@.
--
-- @
-- 'lists' ('iterated' f) a ≡ 'iterate' f a
-- @
--
-- >>> take 3 $ (1 :: Int) ^.. iterated (+1)
-- [1,2,3]
--
-- @
-- iterated :: (a -> a) -> 'Fold1' a a
-- @
--
iterated :: (a -> a) -> Traversal1' a a
iterated f = repn $ \g a0 -> go g a0 where go g a = g a .> go g (f a)
{-# INLINE iterated #-}

-- | Transform a 'Traversal1'' into a 'Traversal1'' that loops over its elements repeatedly.
--
-- >>> take 7 $ (1 :| [2,3]) ^.. cycled traversed1
-- [1,2,3,1,2,3,1]
--
-- @
-- cycled :: 'Fold1' s a -> 'Fold1' s a
-- @
--
cycled :: Apply f => ATraversal1' f s a -> ATraversal1' f s a
cycled o = repn $ \g a -> go g a where go g a = (withTraversal1 o g) a .> go g a
{-# INLINE cycled #-}

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- |
--
-- The traversal laws can be stated in terms of 'withTraversal1':
-- 
-- * @withTraversal1 t (Identity . f) ≡  Identity (fmap f)@
--
-- * @Compose . fmap (withTraversal1 t f) . withTraversal1 t g ≡ withTraversal1 t (Compose . fmap f . g)@
--
-- @
-- withTraversal1 :: Functor f => Lens s t a b -> (a -> f b) -> s -> f t
-- withTraversal1 :: Apply f => Traversal1 s t a b -> (a -> f b) -> s -> f t
-- @
--
withTraversal1 :: Apply f => ATraversal1 f s t a b -> (a -> f b) -> s -> f t
withTraversal1 o = runStar #. o .# Star

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | TODO: Document
--
sequences1 :: Apply f => ATraversal1 f s t (f a) a -> s -> f t
sequences1 o = withTraversal1 o id
{-# INLINE sequences1 #-}

