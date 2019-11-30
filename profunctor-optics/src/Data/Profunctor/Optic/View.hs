{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TupleSections         #-}
module Data.Profunctor.Optic.View (
    -- * Types
    View
  , AView
  , Ixview
  , AIxview
  , PrimView
  , Review
  , AReview
  , Cxview
  , ACxview
  , PrimReview
    -- * Constructors
  , to
  , ixto
  , from
  , cxfrom
  , cloneView
  , cloneReview
    -- * Carriers
  , Tagged(..)
    -- * Primitive operators
  , primViewOf
  , primReviewOf
    -- * Optics
  , like
  , ixlike
  , relike
  , cxlike
  , toProduct
  , fromSum
    -- * Operators
  , (^.)
  , (^%)
  , view
  , ixview
  , views
  , ixviews
  , use
  , ixuse
  , uses
  , ixuses
  , (#^)
  , review
  , cxview
  , reviews
  , cxviews
  , reuse
  , reuses
  , cxuse
  , cxuses
    -- * MonadIO
  , throws
  , throws_
  , throwsTo
) where

import Control.Exception (Exception)
import Control.Monad.IO.Class
import Control.Monad.Reader as Reader
import Control.Monad.Writer as Writer hiding (Sum(..))
import Control.Monad.State as State
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Index
import GHC.Conc (ThreadId)
import qualified Control.Exception as Ex
import qualified Data.Bifunctor as B

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> import Data.Either
-- >>> import Control.Monad.State
-- >>> import Control.Monad.Writer
-- >>> import Data.List.Index as LI
-- >>> :load Data.Profunctor.Optic
-- >>> let catchOn :: Int -> Cxprism' Int (Maybe String) String ; catchOn n = cxjust $ \k -> if k==n then Just "caught" else Nothing
-- >>> let ixtraversed :: Ixtraversal Int [a] [b] a b ; ixtraversed = ixtraversalVl LI.itraverse
-- >>> let ixat :: Int -> Ixtraversal0' Int [a] a; ixat = inserted (\i s -> flip LI.ifind s $ \n _ -> n == i) (\i a s -> LI.modifyAt i (const a) s)

type APrimView r s t a b = Optic (Star (Const r)) s t a b

type AView s a = Optic' (Star (Const a)) s a

type AIxview r i s a = IndexedOptic' (Star (Const (Maybe i , r))) i s a

type APrimReview s t a b = Optic Tagged s t a b

type AReview t b = Optic' Tagged t b

type ACxview k t b = CoindexedOptic' Tagged k t b

---------------------------------------------------------------------
-- 'View' & 'Review'
---------------------------------------------------------------------


-- | Obtain a 'View' from an arbitrary function.
--
-- @
-- 'to' f '.' 'to' g ≡ 'to' (g '.' f)
-- a '^.' 'to' f ≡ f a
-- @
--
-- >>> ("hello","world") ^. to snd
-- "world"
--
-- >>> 5 ^. to succ
-- 6
--
-- >>> (0, -5) ^. second . to abs
-- 5
--
-- @
-- 'to' :: (s -> a) -> 'View' s a
-- @
--
to :: (s -> a) -> PrimView s t a b
to f = coercer . lmap f
{-# INLINE to #-}

-- | TODO: Document
--
ixto :: (s -> (i , a)) -> Ixview i s a
ixto f = to $ f . snd
{-# INLINE ixto #-}

-- | Obtain a 'Review' from an arbitrary function.
--
-- @
-- 'from' ≡ 're' . 'to'
-- @
--
-- >>> (from Prelude.length) #^ [1,2,3]
-- 3
--
-- @
-- 'from' :: (b -> t) -> 'Review' t b
-- @
--
from :: (b -> t) -> PrimReview s t a b 
from f = coercel . rmap f
{-# INLINE from #-}

-- | TODO: Document
--
cxfrom :: ((k -> b) -> t) -> Cxview k t b
cxfrom f = from $ \kb _ -> f kb
{-# INLINE cxfrom #-}

-- | TODO: Document
--
-- @
-- 'cloneView' ::             'AView' s a -> 'View' s a
-- 'cloneView' :: 'Monoid' a => 'AView' s a -> 'Fold' s a
-- @
--
cloneView :: AView s a -> PrimView s s a a
cloneView = to . view
{-# INLINE cloneView #-}

-- | TODO: Document
--
cloneReview :: AReview t b -> PrimReview t t b b
cloneReview = from . review
{-# INLINE cloneReview #-}

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | TODO: Document
--
primViewOf :: APrimView r s t a b -> (a -> r) -> s -> r
primViewOf o = (getConst #.) #. runStar #. o .# Star .# (Const #.)
{-# INLINE primViewOf #-}

-- | TODO: Document
--
primReviewOf :: APrimReview s t a b -> (t -> r) -> b -> r
primReviewOf o f = f . unTagged #. o .# Tagged
{-# INLINE primReviewOf #-}

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

-- | Obtain a constant-valued (index-preserving) 'View' from an arbitrary value.
--
-- This can be useful as a second case 'failing' a 'Fold'
-- e.g. @foo `failing` 'like' 0@
--
-- @
-- 'like' a '.' 'like' b ≡ 'like' b
-- a '^.' 'like' b ≡ b
-- a '^.' 'like' b ≡ a '^.' 'to' ('const' b)
-- @
--
--
-- @
-- 'like' :: a -> 'View' s a
-- @
--
like :: a -> PrimView s t a b
like = to . const
{-# INLINE like #-}

-- | TODO: Document
--
ixlike :: i -> a -> Ixview i s a
ixlike i a = ixto (const (i, a))
{-# INLINE ixlike #-}

-- | Obtain a constant-valued (index-preserving) 'Review' from an arbitrary value.
--
-- @
-- 'relike' a '.' 'relike' b ≡ 'relike' a
-- 'relike' a '#' b ≡ a
-- 'relike' a '#' b ≡ 'from' ('const' a) '#' b
-- @
--
relike :: t -> PrimReview s t a b
relike = from . const
{-# INLINE relike #-}

-- | Obtain a constant-valued 'Cxview' from an arbitrary value. 
--
cxlike :: t -> Cxview k t b
cxlike = cxfrom . const
{-# INLINE cxlike #-}

-- | Combine two 'View's into a 'View' to a product.
--
-- @
-- 'toProduct' :: 'View' s a1 -> 'View' s a2 -> 'View' s (a1 , a2)
-- @
--
toProduct :: AView s a1 -> AView s a2 -> PrimView s t (a1 , a2) b
toProduct l r = to (view l &&& view r)
{-# INLINE toProduct #-}

-- | Combine two 'Review's into a 'Review' from a sum.
--
-- @
-- 'fromSum' :: 'Review' t b1 -> 'Review' t b2 -> 'Review' t (b1 + b2)
-- @
--
fromSum :: AReview t b1 -> AReview t b2 -> PrimReview s t a (b1 + b2)
fromSum l r = from (review l ||| review r)
{-# INLINE fromSum #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

infixl 8 ^.

-- | An infix alias for 'view'. Dual to '#'.
--
-- Fixity and semantics are such that subsequent field accesses can be
-- performed with ('Prelude..').
--
-- >>> ("hello","world") ^. second
-- "world"
--
-- >>> import Data.Complex
-- >>> ((0, 1 :+ 2), 3) ^. first . second . to magnitude
-- 2.23606797749979
--
-- @
-- ('^.') ::             s -> 'View' s a       -> a
-- ('^.') :: 'Data.Monoid.Monoid' m => s -> 'Data.Profunctor.Optic.Fold.Fold' s m       -> m
-- ('^.') ::             s -> 'Data.Profunctor.Optic.Iso.Iso'' s a       -> a
-- ('^.') ::             s -> 'Data.Profunctor.Optic.Lens.Lens'' s a      -> a
-- ('^.') ::             s -> 'Data.Profunctor.Optic.Prism.Coprism'' s a   -> a
-- ('^.') :: 'Data.Monoid.Monoid' m => s -> 'Data.Profunctor.Optic.Traversal.Traversal'' s m -> m
-- @
--
(^.) :: s -> AView s a -> a
(^.) = flip view
{-# INLINE ( ^. ) #-}

infixl 8 ^%

-- | Bring the index and value of a indexed optic into the current environment as a pair.
--
-- This a flipped, infix variant of 'ixview' and an indexed variant of '^.'.
--
-- The fixity and semantics are such that subsequent field accesses can be
-- performed with ('Prelude..').
--
-- The result probably doesn't have much meaning when applied to an 'Ixfold'.
--
(^%) ::  Monoid i => s -> AIxview a i s a -> (Maybe i , a)
(^%) = flip ixview 
{-# INLINE (^%) #-}

-- | View the value pointed to by a 'View', 'Data.Profunctor.Optic.Iso.Iso' or
-- 'Lens' or the result of folding over all the results of a
-- 'Data.Profunctor.Optic.Fold.Fold' or 'Data.Profunctor.Optic.Traversal.Traversal' that points
-- at a monoidal value.
--
-- @
-- 'view' '.' 'to' ≡ 'id'
-- @
--
-- >>> view second (1, "hello")
-- "hello"
--
-- >>> view (to succ) 5
-- 6
--
-- >>> view (second . first) ("hello",("world","!!!"))
-- "world"
--
view :: MonadReader s m => AView s a -> m a
view o = views o id
{-# INLINE view #-}

-- | Bring the index and value of a indexed optic into the current environment as a pair.
--
-- >>> ixview ixfirst ("foo", 42)
-- (Just (),"foo")
--
-- >>> ixview (ixat 3 . ixfirst) [(0,'f'),(1,'o'),(2,'o'),(3,'b'),(4,'a'),(5,'r') :: (Int, Char)]
-- (Just 3,3)
--
-- In order to 'ixview' a 'Choice' optic (e.g. 'Ixtraversal0', 'Ixtraversal', 'Ixfold', etc),
-- /a/ must have a 'Monoid' instance:
--
-- >>> ixview (ixat 0) ([] :: [Int])
-- (Nothing,0)
-- >>> ixview (ixat 0) ([1] :: [Int])
-- (Just 0,1)
--
-- /Note/ when applied to a 'Ixtraversal' or 'Ixfold', then 'ixview' will return a monoidal 
-- summary of the indices tupled with a monoidal summary of the values:
--
-- >>> (ixview @_ @_ @Int @Int) ixtraversed [1,2,3,4]
-- (Just 6,10)
--
ixview :: MonadReader s m => Monoid i => AIxview a i s a -> m (Maybe i , a)
ixview o = asks $ primViewOf o (B.first Just) . (mempty,)
{-# INLINE ixview #-}

-- | Map each part of a structure viewed to a semantic edixtor combinator.
--
-- @
-- 'views o f ≡ foldMapOf o f'
-- 'Data.Foldable.foldMap' = 'views' 'folding''
-- @
--
-- >>> views both id (["foo"], ["bar", "baz"])
-- ["foo","bar","baz"]
--
-- @
-- 'views' ::                'AView' s a       -> (a -> r) -> s -> r
-- 'views' ::                'Iso'' s a        -> (a -> r) -> s -> r
-- 'views' ::                'Lens'' s a       -> (a -> r) -> s -> r
-- 'views' ::                'Coprism'' s a    -> (a -> r) -> s -> r
-- 'views' :: 'Monoid' r    => 'Traversal'' s a  -> (a -> r) -> s -> r
-- 'views' :: 'Semigroup' r => 'Traversal1'' s a -> (a -> r) -> s -> r
-- 'views' :: 'Monoid' r    => 'Fold' s a        -> (a -> r) -> s -> r
-- 'views' :: 'Semigroup' r => 'Fold1' s a       -> (a -> r) -> s -> r
-- @
--
views :: MonadReader s m => Optic' (Star (Const r)) s a -> (a -> r) -> m r
views o f = asks $ primViewOf o f
{-# INLINE views #-}

-- | Bring a function of the index and value of an indexed optic into the current environment.
--
-- 'ixviews' ≡ 'ifoldMapOf'
--
-- >>> ixviews (ixat 2) (-) ([0,1,2] :: [Int])
-- 0
--
-- In order to 'ixviews' a 'Choice' optic (e.g. 'Ixtraversal0', 'Ixtraversal', 'Ixfold', etc),
-- /a/ must have a 'Monoid' instance (here from the 'rings' package):
--
-- >>> ixviews (ixat 3) (flip const) ([1] :: [Int])
-- 0
--
-- Use 'ixview' if there is a need to disambiguate between 'mempty' as a miss vs. as a return value.
--
ixviews :: MonadReader s m => Monoid i => IndexedOptic' (Star (Const r)) i s a -> (i -> a -> r) -> m r
ixviews o f = asks $ primViewOf o (uncurry f) . (mempty,) 

-- | TODO: Document
--
use :: MonadState s m => AView s a -> m a
use o = gets (view o)
{-# INLINE use #-}

-- | Bring the index and value of an indexed optic into the current environment as a pair.
--
ixuse :: MonadState s m => Monoid i => AIxview a i s a -> m (Maybe i , a)
ixuse o = gets (ixview o)

-- | Use the target of a 'Lens', 'Data.Profunctor.Optic.Iso.Iso' or
-- 'View' in the current state, or use a summary of a
-- 'Data.Profunctor.Optic.Fold.Fold' or 'Data.Profunctor.Optic.Traversal.Traversal' that
-- points to a monoidal value.
--
-- >>> evalState (uses first length) ("hello","world")
-- 5
--
-- @
-- 'uses' :: 'MonadState' s m             => 'Data.Profunctor.Optic.Iso.Iso'' s a       -> (a -> r) -> m r
-- 'uses' :: 'MonadState' s m             => 'Data.Profunctor.Optic.View.View' s a     -> (a -> r) -> m r
-- 'uses' :: 'MonadState' s m             => 'Data.Profunctor.Optic.Lens.Lens'' s a      -> (a -> r) -> m r
-- 'uses' :: 'MonadState' s m             => 'Data.Profunctor.Optic.Prism.Coprism'' s a      -> (a -> r) -> m r
-- 'uses' :: 'MonadState' s m => 'Data.Monoid.Monoid' r => 'Data.Profunctor.Optic.Traversal.Traversal'' s a -> (a -> r) -> m r
-- 'uses' :: 'MonadState' s m => 'Data.Monoid.Monoid' r => 'Data.Profunctor.Optic.Fold.Fold' s a       -> (a -> r) -> m r
-- @
--
-- @
-- 'uses' :: 'MonadState' s m => 'Getting' r s t a b -> (a -> r) -> m r
-- @
--
uses :: MonadState s m => Optic' (Star (Const r)) s a -> (a -> r) -> m r
uses l f = gets (views l f)
{-# INLINE uses #-}

-- | Bring a function of the index and value of an indexed optic into the current environment.
--
ixuses :: MonadState s m => Monoid i => IndexedOptic' (Star (Const r)) i s a -> (i -> a -> r) -> m r
ixuses o f = gets $ primViewOf o (uncurry f) . (mempty,)

infixr 8 #^

-- | An infix variant of 'review'. Dual to '^.'.
--
-- @
-- 'from' f #^ x ≡ f x
-- o #^ x ≡ x '^.' 're' o
-- @
--
-- This is commonly used when using a 'Prism' as a smart constructor.
--
-- >>> left #^ 4
-- Left 4
--
-- @
-- (#^) :: 'Iso''      s a -> a -> s
-- (#^) :: 'Prism''    s a -> a -> s
-- (#^) :: 'Colens''   s a -> a -> s
-- (#^) :: 'Review'    s a -> a -> s
-- (#^) :: 'Equality'' s a -> a -> s
-- @
--
(#^) :: AReview t b -> b -> t
o #^ b = review o b
{-# INLINE (#^) #-}

-- | Turn an optic around and look through the other end.
--
-- @
-- 'review' ≡ 'view' '.' 're'
-- 'review' . 'from' ≡ 'id'
-- @
--
-- >>> review (from succ) 5
-- 6
--
-- @
-- 'review' :: 'Iso'' s a   -> a -> s
-- 'review' :: 'Prism'' s a -> a -> s
-- 'review' :: 'Colens'' s a -> a -> s
-- @
--
review :: MonadReader b m => AReview t b -> m t
review o = reviews o id
{-# INLINE review #-}

-- | Bring a function of the index of a co-indexed optic into the current environment.
--
cxview :: MonadReader b m => ACxview k t b -> m (k -> t)
cxview o = cxviews o id
{-# INLINE cxview #-}

-- | Turn an optic around and look through the other end, applying a function.
--
-- @
-- 'reviews' ≡ 'views' '.' 're'
-- 'reviews' ('from' f) g ≡ g '.' f
-- @
--
-- >>> reviews left isRight "mustard"
-- False
--
-- >>> reviews (from succ) (*2) 3
-- 8
--
-- @
-- 'reviews' :: 'Iso'' t b -> (t -> r) -> b -> r
-- 'reviews' :: 'Prism'' t b -> (t -> r) -> b -> r
-- 'reviews' :: 'Colens'' t b -> (t -> r) -> b -> r
-- @
--
reviews :: MonadReader b m => AReview t b -> (t -> r) -> m r
reviews o f = asks $ primReviewOf o f
{-# INLINE reviews #-}

-- | Bring a continuation of the index of a co-indexed optic into the current environment.
--
-- @
-- cxviews :: ACxview k t b -> ((k -> t) -> r) -> b -> r
-- @
--
cxviews :: MonadReader b m => ACxview k t b -> ((k -> t) -> r) -> m r
cxviews o f = asks $ primReviewOf o f . const

-- | Turn an optic around and 'use' a value (or the current environment) through it the other way.
--
-- @
-- 'reuse' ≡ 'use' '.' 're'
-- 'reuse' '.' 'from' ≡ 'gets'
-- @
--
-- >>> evalState (reuse left) 5
-- Left 5
--
-- >>> evalState (reuse (from succ)) 5
-- 6
--
-- @
-- 'reuse' :: 'MonadState' a m => 'Iso'' s a   -> m s
-- 'reuse' :: 'MonadState' a m => 'Prism'' s a -> m s
-- 'reuse' :: 'MonadState' a m => 'Colens'' s a -> m s
-- @
--
reuse :: MonadState b m => AReview t b -> m t
reuse o = gets (unTagged #. o .# Tagged)
{-# INLINE reuse #-}

-- | TODO: Document
--
cxuse :: MonadState b m => ACxview k t b -> m (k -> t)
cxuse o = gets (cxview o)
{-# INLINE cxuse #-}

-- | Turn an optic around and 'use' the current state through it the other way, applying a function.
--
-- @
-- 'reuses' ≡ 'uses' '.' 're'
-- 'reuses' ('from' f) g ≡ 'gets' (g '.' f)
-- @
--
-- >>> evalState (reuses left isLeft) (5 :: Int)
-- True
--
-- @
-- 'reuses' :: 'MonadState' a m => 'Iso'' s a   -> (s -> r) -> m r
-- 'reuses' :: 'MonadState' a m => 'Prism'' s a -> (s -> r) -> m r
-- 'reuses' :: 'MonadState' a m => 'Prism'' s a -> (s -> r) -> m r
-- @
--
reuses :: MonadState b m => AReview t b -> (t -> r) -> m r
reuses o tr = gets (tr . unTagged #. o .# Tagged)
{-# INLINE reuses #-}

-- | TODO: Document
--
cxuses :: MonadState b m => ACxview k t b -> ((k -> t) -> r) -> m r
cxuses o f = gets (cxviews o f)
{-# INLINE cxuses #-}

---------------------------------------------------------------------
-- 'MonadIO'
---------------------------------------------------------------------

-- | Throw an exception described by an optic.
--
-- @
-- 'throws' o e \`seq\` x  ≡ 'throws' o e
-- @
--
throws :: MonadIO m => Exception e => AReview e b -> b -> m r
throws o = reviews o $ liftIO . Ex.throwIO
{-# INLINE throws #-}

-- | Variant of 'throws' for error constructors with no arguments.
--
throws_ :: MonadIO m => Exception e => AReview e () -> m r
throws_ o = throws o ()

-- | Raise an 'Exception' specified by an optic in the target thread.
--
-- @
-- 'throwsTo' thread o ≡ 'throwTo' thread . 'review' o
-- @
--
throwsTo :: MonadIO m => Exception e => ThreadId -> AReview e b -> b -> m ()
throwsTo tid o = reviews o (liftIO . Ex.throwTo tid)
