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
    -- * Traversal1
  , Traversal1
  , Traversal1'
  , Ixtraversal1
  , Ixtraversal1'
  , traversing1
  , traversal1Vl
  , itraversal1Vl
    -- * Optics
  , traversed
  , traversed1
  , both
  , both1
  , duplicated
  , beside
  , bitraversed
  , bitraversed1
  , repeated 
  , iterated
  , cycled
    -- * Indexed optics
  , itraversed
  , itraversed1
  , itraversedRep
    -- * Operators
  , withTraversal
  , withTraversal1
    -- * Operators
  , (*~)
  , (**~)
  , sequences
  , sequences1
) where

import Control.Category
import Control.Arrow
import Data.Bitraversable
import Data.Key as K
import Data.List.NonEmpty as NonEmpty
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.Import hiding (id,(.))
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Operator
import Data.Semigroup.Bitraversable
import Data.Semiring
import Control.Monad.Trans.State
import Prelude (Foldable(..), reverse)
import qualified Data.Functor.Rep as F

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

-- | TODO: Document
--
traversed :: Traversable f => Traversal (f a) (f b) a b
traversed = traversalVl traverse

-- | Obtain a 'Traversal1' from a 'Traversable1' functor.
--
traversed1 :: Traversable1 t => Traversal1 (t a) (t b) a b
traversed1 = traversal1Vl traverse1
{-# INLINE traversed1 #-}

-- | TODO: Document
--
-- >>> withTraversal both (pure . length) ("hello","world")
-- (5,5)
--
both :: Traversal (a , a) (b , b) a b
both p = p **** p

-- | TODO: Document
--
-- >>> withTraversal1 both1 (pure . NE.length) ('h' :| "ello", 'w' :| "orld")
-- (5,5)
--
both1 :: Traversal1 (a , a) (b , b) a b
both1 p = tabulate $ \s -> liftF2 ($) (flip sieve s $ dimap fst (,) p) (flip sieve s $ lmap snd p)
{-# INLINE both1 #-}

-- | Duplicate the results of any 'Moore'. 
--
-- >>> lists (both . duplicated) ("hello","world")
-- ["hello","hello","world","world"]
--
duplicated :: Traversal a b a b
duplicated p = pappend p p

-- | TODO: Document
--
beside :: Bitraversable r => Traversal s1 t1 a b -> Traversal s2 t2 a b -> Traversal (r s1 s2) (r t1 t2) a b
beside x y p = tabulate go where go rss = bitraverse (sieve $ x p) (sieve $ y p) rss

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
-- Indexed optics 
---------------------------------------------------------------------

-- | TODO: Document
--
itraversed :: TraversableWithKey f => Traversable f => Ixtraversal (Key f) (f a) (f b) a b
itraversed = itraversalVl K.traverseWithKey

-- | TODO: Document
--
itraversed1 :: TraversableWithKey1 f => Traversable1 f => Ixtraversal1 (Key f) (f a) (f b) a b
itraversed1 = itraversal1Vl K.traverseWithKey1

-- | TODO: Document
--
itraversedRep :: F.Representable f => Traversable f => Ixtraversal (F.Rep f) (f a) (f b) a b
itraversedRep = itraversalVl F.itraverseRep

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | 
--
-- The traversal laws can be stated in terms of 'withTraversal':
-- 
-- * @withTraversal t (Identity . f) ≡ Identity (fmap f)@
--
-- * @Compose . fmap (withTraversal t f) . withTraversal t g ≡ withTraversal t (Compose . fmap f . g)@
--
withTraversal :: Applicative f => ATraversal f s t a b -> (a -> f b) -> s -> f t
withTraversal = withStar
{-# INLINE withTraversal #-}

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
withTraversal1 = withStar
{-# INLINE withTraversal1 #-}

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
sequences1 :: Apply f => ATraversal1 f s t (f a) a -> s -> f t
sequences1 o = withTraversal1 o id
{-# INLINE sequences1 #-}
