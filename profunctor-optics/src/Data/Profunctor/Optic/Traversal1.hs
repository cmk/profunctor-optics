{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Traversal1 (
    -- * Traversal1
    Traversal1
  , Traversal1'
  , Ixtraversal1
  , Ixtraversal1'
  , traversing1
  , traversal1Vl
  , itraversal1Vl
    -- * Cotraversal1 & Cxtraversal1
  , Cotraversal1
  , Cotraversal1'
  , Cxtraversal1
  , Cxtraversal1'
  , ACotraversal1
  , ACotraversal1'
  , cotraversal1
  , cotraversing1
  , retraversing1
  , cotraversal1Vl
  , ktraversal1Vl
  , nocx1
    -- * Optics
  , traversed1
  , cotraversed1
  , both1
  , bitraversed1
  , repeated 
  , iterated
  , cycled
    -- * Primitive operators
  , withTraversal1
  , withCotraversal1
    -- * Operators
  , sequences1
  , distributes1
    -- * Carriers
 -- , Star()
 -- , Costar()
  , ATraversal1
  , ATraversal1'
    -- * Classes
  , Representable(..)
  , Corepresentable(..)
) where

import Data.Semigroup.Bitraversable
import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Grate
import Data.Profunctor.Optic.Types

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XFlexibleContexts
-- >>> :set -XTypeApplications
-- >>> :set -XTupleSections
-- >>> :set -XRankNTypes
-- >>> import Data.Maybe
-- >>> import Data.List.NonEmpty (NonEmpty(..))
-- >>> import qualified Data.List.NonEmpty as NE
-- >>> import Data.Functor.Identity
-- >>> import Data.List.Index
-- >>> :load Data.Profunctor.Optic Data.Either.Optic Data.Tuple.Optic
-- >>> let catchOn :: Int -> Cxprism' Int (Maybe String) String ; catchOn n = kjust $ \k -> if k==n then Just "caught" else Nothing
-- >>> let itraversed :: Ixtraversal Int [a] [b] a b ; itraversed = itraversalVl itraverse

---------------------------------------------------------------------
-- 'Traversal1'
---------------------------------------------------------------------

type ATraversal1 f s t a b = Apply f => ARepn f s t a b

type ATraversal1' f s a = ATraversal1 f s s a a

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
-- 'Cotraversal1' & 'Cxtraversal11'
---------------------------------------------------------------------

type ACotraversal1 f s t a b = Apply f => ACorepn f s t a b

type ACotraversal1' f s a = ACotraversal1 f s s a a

-- | Obtain a 'Cotraversal1' directly. 
--
cotraversal1 :: Distributive g => (g b -> s -> g a) -> (g b -> t) -> Cotraversal1 s t a b
cotraversal1 bsa bt = colens bsa bt . corepn cotraverse

-- | Obtain a 'Cotraversal1' by embedding a reversed lens getter and setter into a 'Distributive' functor.
--
-- @
--  'withColens' o 'cotraversing' ≡ 'cotraversed' . o
-- @
--
cotraversing1 :: Distributive g => (b -> s -> a) -> (b -> t) -> Cotraversal1 (g s) (g t) a b
cotraversing1 bsa bt = corepn cotraverse . colens bsa bt 

-- | Obtain a 'Cotraversal1' by embedding a grate continuation into a 'Distributive' functor. 
--
-- @
--  'withGrate' o 'retraversing' ≡ 'cotraversed' . o
-- @
--
retraversing1 :: Distributive g => (((s -> a) -> b) -> t) -> Cotraversal1 (g s) (g t) a b
retraversing1 sabt = corepn cotraverse . grate sabt

-- | Obtain a profunctor 'Cotraversal1' from a Van Laarhoven 'Cotraversal1'.
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
cotraversal1Vl :: (forall f. Apply f => (f a -> b) -> f s -> t) -> Cotraversal1 s t a b
cotraversal1Vl abst = cotabulate . abst . cosieve 

-- | Lift an indexed VL cotraversal into a (co-)indexed profunctor cotraversal.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @kabst (const extract) ≡ extract@
--
-- * @kabst (const f) . fmap (kabst $ const g) ≡ kabst ((const f) . fmap (const g) . getCompose) . Compose@
--
-- See 'Data.Profunctor.Optic.Property'.
--
ktraversal1Vl :: (forall f. Apply f => (k -> f a -> b) -> f s -> t) -> Cxtraversal1 k s t a b
ktraversal1Vl kabst = cotraversal1Vl $ \kab -> const . kabst (flip kab)

-- | Lift a VL cotraversal into an (co-)indexed profunctor cotraversal that ignores its input.
--
-- Useful as the first optic in a chain when no indexed equivalent is at hand.
--
nocx1 :: Monoid k => Cotraversal1 s t a b -> Cxtraversal1 k s t a b
nocx1 o = ktraversal1Vl $ \kab s -> flip runCostar s . o . Costar $ kab mempty

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

-- |
--
-- @
-- 'withCotraversal1' $ 'Data.Profuncto.Optic.Grate.grate' (flip 'Data.Distributive.cotraverse' id) ≡ 'Data.Distributive.cotraverse'
-- @
--
-- The cotraversal laws can be restated in terms of 'cowithTraversal1':
--
-- * @withCotraversal1 o (f . runIdentity) ≡  fmap f . runIdentity @
--
-- * @withCotraversal1 o f . fmap (withCotraversal1 o g) == withCotraversal1 o (f . fmap g . getCompose) . Compose@
--
-- See also < https://www.cs.ox.ac.uk/jeremy.gibbons/publications/iterator.pdf >
--
withCotraversal1 :: Apply f => ACotraversal1 f s t a b -> (f a -> b) -> (f s -> t)
withCotraversal1 o = runCostar #. o .# Costar

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
cotraversed1 :: Distributive f => Cotraversal1 (f a) (f b) a b 
cotraversed1 = cotraversal1Vl cotraverse
{-# INLINE cotraversed1 #-}

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
iterated :: (a -> a) -> Traversal1' a a
iterated f = repn $ \g a0 -> go g a0 where go g a = g a .> go g (f a)
{-# INLINE iterated #-}

-- | Transform a 'Traversal1'' into a 'Traversal1'' that loops repn its elements repeatedly.
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
-- Operators
---------------------------------------------------------------------

-- | TODO: Document
--
sequences1 :: Apply f => ATraversal1 f s t (f a) a -> s -> f t
sequences1 o = withTraversal1 o id
{-# INLINE sequences1 #-}

-- | TODO: Document
--
distributes1 :: Apply f => ACotraversal1 f s t a (f a) -> f s -> t
distributes1 o = withCotraversal1 o id
{-# INLINE distributes1 #-}
