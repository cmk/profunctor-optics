{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE PackageImports        #-}
module Data.Profunctor.Optic.Traversal (
    -- * Traversal0
    Traversal0
  , Traversal0'
  , Cotraversal0
  , Cotraversal0'
  , traversal0
  , traversal0'
  , traversalVl0
    -- * Traversal
  , Traversal
  , Traversal'
  , Cotraversal
  , Cotraversal'
  , traversing
  , traversalVl
  , cotraversing
  , retraversing
  , cotraversalVl
  , beside
    -- * Traversal1
  , Traversal1
  , Traversal1'
  , Cotraversal
  , Cotraversal'
  , traversing1
  , traversalVl1
  , cotraversing1
  , retraversing1
  , cotraversalVl1
  , beside1
  , pappend
  , divide
  , cochoose
  , codivide
  , choose
  , (<<*>>)
  , (****)
  , (&&&&)
  , (++++)
  , (||||)
    -- * Optics
  , affine
  , nulled
  , traversed
  , cotraversed
  , traversed1
  , cotraversed1
  , bitraversed
  , bitraversed1
  , forked
  , coforked
  , duplicated
  , repeated 
  , iterated
  , cycled
    -- * Operators
  , matches
  , sequences
  , collects 
  , backwards
  --, mapAccumsL
  --, mapAccumsR
  --, scansl1
  --, scansr1
    -- * Classes
  , Strong(..)
  , Choice(..)
  , Closed(..)
  , Representable(..)
  , Corepresentable(..)
) where

import Control.Monad.State.Strict
import Control.Applicative.Backwards
import Data.Function
import Data.Bitraversable
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.Prism
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Combinator
import Data.Semigroup.Bitraversable
import qualified Data.Bifunctor as B

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XFlexibleContexts
-- >>> :set -XTypeApplications
-- >>> :set -XTupleSections
-- >>> :set -XRankNTypes
-- >>> import Data.Char
-- >>> import Data.Function ((&))
-- >>> import Data.Int
-- >>> import Data.List.NonEmpty (NonEmpty(..))
-- >>> import Data.Maybe
-- >>> import Data.String
-- >>> import Data.Semigroup
-- >>> import qualified Data.Bifunctor as B
-- >>> import qualified Data.List.NonEmpty as NE
-- >>> import Data.Functor.Identity
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- 'Traversal0'
---------------------------------------------------------------------

-- | Obtain a 'Traversal0' from match and constructor functions.
--
-- /Caution/: In order for the 'Traversal0' to be well-defined,
-- you must ensure that the input functions satisfy the following
-- properties:
--
-- * @sta (sbt a s) ≡ either (Left . const a) Right (sta s)@
--
-- * @either id (sbt s) (sta s) ≡ s@
--
-- * @sbt (sbt s a1) a2 ≡ sbt s a2@
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
traversal0 :: (s -> t + a) -> (s -> b -> t) -> Traversal0 s t a b
traversal0 sta sbt = dimap (\s -> (s,) <$> sta s) (id ||| uncurry sbt) . right . second
{-# INLINE traversal0 #-}

-- | Obtain a 'Traversal0'' from match and constructor functions.
--
traversal0' :: (s -> Maybe a) -> (s -> b -> s) -> Traversal0 s s a b
traversal0' sa sas = flip traversal0 sas $ \s -> maybe (Left s) Right (sa s)
{-# INLINE traversal0' #-}

-- | Transform a Van Laarhoven 'Traversal0' into a profunctor 'Traversal0'.
--
traversalVl0 :: (forall f. Functor f => (forall c. c -> f c) -> (a -> f b) -> s -> f t) -> Traversal0 s t a b
traversalVl0 f = dimap (\s -> (s,) <$> eswap (f Right Left s)) (id ||| uncurry sbt) . right . second
  where
    sbt s b = runIdentity $ f Identity (\_ -> Identity b) s
{-# INLINE traversalVl0 #-}

---------------------------------------------------------------------
-- 'Traversal'
---------------------------------------------------------------------

-- | Obtain a 'Traversal' by lifting a lens getter and setter into a 'Traversable' functor.
--
-- @
--  'withLens' o 'traversing' ≡ 'traversed' . o
-- @
--
-- Compare 'Data.Profunctor.Optic.List.folding'.
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
-- >>> list (traversing snd $ \(s,_) b -> (s,b)) [(0,'f'),(1,'o'),(2,'o'),(3,'b'),(4,'a'),(5,'r')]
-- "foobar"
--
traversing :: Traversable f => (s -> a) -> (s -> b -> t) -> Traversal (f s) (f t) a b
traversing sa sbt = represent traverse . lens sa sbt
{-# INLINE traversing #-}

-- | Obtain a profunctor 'Traversal' from a Van Laarhoven 'Traversal'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @abst pure ≡ pure@
--
-- * @fmap (abst f) . abst g ≡ getCompose . abst (Compose . fmap f . g)@
--
-- The traversal laws can be stated in terms of 'traverses':
-- 
-- * @traverses t (pure . f) ≡ pure (fmap f)@
--
-- * @Compose . fmap (traverses t f) . traverses t g ≡ traverses t (Compose . fmap f . g)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
traversalVl :: (forall f. Applicative' f => (a -> f b) -> s -> f t) -> Traversal s t a b
traversalVl = represent
{-# INLINE traversalVl #-}

-- | Obtain a 'Cotraversal' by embedding a continuation into a 'Distributive' functor. 
--
-- @
--  'withColens' o 'cotraversing' ≡ 'cotraversed' . o
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
cotraversing sabt = corepresent cotraverse . colens sabt

-- | Obtain a 'Cotraversal' by embedding a reversed lens getter and setter into a 'Distributive' functor.
--
-- @
--  'withLens' ('re' o) 'retraversing' ≡ 'cotraversed' . o
-- @
--
retraversing :: Distributive g => (b -> t) -> (b -> s -> a) -> Cotraversal (g s) (g t) a b
retraversing bt bsa = corepresent cotraverse . relens bsa bt

-- | Obtain a profunctor 'Cotraversal' from a Van Laarhoven 'Cotraversal'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @abst f . fmap (abst g) ≡ abst (f . fmap g . getCompose) . Compose@
--
-- The cotraversal laws can be restated in terms of 'costar':
--
-- * @costar o f . fmap (costar o g) == costar o (f . fmap g . getCompose) . Compose@
--
-- See 'Data.Profunctor.Optic.Property'.
--
cotraversalVl :: (forall f. Coapply f => (f a -> b) -> f s -> t) -> Cotraversal s t a b
cotraversalVl = corepresent

-- | TODO: Document
--
beside :: Bitraversable r => Traversal s1 t1 a b -> Traversal s2 t2 a b -> Traversal (r s1 s2) (r t1 t2) a b
beside x y p = tabulate go where go rss = bitraverse (sieve $ x p) (sieve $ y p) rss
{-# INLINE beside #-}

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
-- >>> list (traversing snd $ \(s,_) b -> (s,b)) [(0,'f'),(1,'o'),(2,'o'),(3,'b'),(4,'a'),(5,'r')]
-- "foobar"
--
-- Compare 'Data.Profunctor.Optic.Fold.folding'.
--
traversing1 :: Traversable1 f => (s -> a) -> (s -> b -> t) -> Traversal1 (f s) (f t) a b
traversing1 sa sbt = represent traverse1 . lens sa sbt
{-# INLINE traversing1 #-}

-- | Obtain a profunctor 'Traversal1' from a Van Laarhoven 'Traversal1'.
--
-- /Caution/: In order for the generated family to be well-defined,
-- you must ensure that the traversal1 law holds for the input function:
--
-- * @fmap (abst f) . abst g ≡ getCompose . abst (Compose . fmap f . g)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
traversalVl1 :: (forall f. Apply f => (a -> f b) -> s -> f t) -> Traversal1 s t a b
traversalVl1 abst = tabulate . abst . sieve 
{-# INLINE traversalVl1 #-}

-- | Obtain a 'Cotraversal' by embedding a continuation into a 'Distributive1' functor. 
--
-- @
--  'withColens' o 'cotraversing1' ≡ 'cotraversed1' . o
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
cotraversing1 :: Distributive1 g => (((s -> a) -> b) -> t) -> Cotraversal1 (g s) (g t) a b
cotraversing1 sabt = corepresent cotraverse1 . colens sabt

-- | Obtain a 'Cotraversal' by embedding a reversed lens getter and setter into a 'Distributive1' functor.
--
-- @
--  'withLens' ('re' o) 'retraversing1' ≡ 'cotraversed1' . o
-- @
--
retraversing1 :: Distributive1 g => (b -> t) -> (b -> s -> a) -> Cotraversal1 (g s) (g t) a b
retraversing1 bt bsa = corepresent cotraverse1 . relens bsa bt

-- | Obtain a profunctor 'Cotraversal' from a Van Laarhoven 'Cotraversal'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @abst runIdentity ≡ runIdentity@
--
-- * @abst f . fmap (abst g) ≡ abst (f . fmap g . getCompose) . Compose@
--
-- The cotraversal1 laws can be restated in terms of 'costar':
--
-- * @costar o (f . copure) ≡  fmap f . copure@
--
-- * @costar o f . fmap (cotraverses o g) == costar o (f . fmap g . getCompose) . Compose@
--
-- See 'Data.Profunctor.Optic.Property'.
--
cotraversalVl1 :: (forall f. Coapplicative f => (f a -> b) -> f s -> t) -> Cotraversal1 s t a b
cotraversalVl1 = corepresent

-- | TODO: Document
--
beside1 :: Bitraversable1 r => Traversal1 s1 t1 a b -> Traversal1 s2 t2 a b -> Traversal1 (r s1 s2) (r t1 t2) a b
beside1 x y p = tabulate go where go rss = bitraverse1 (sieve $ x p) (sieve $ y p) rss
{-# INLINE beside1 #-}

---------------------------------------------------------------------
-- Optics
---------------------------------------------------------------------

-- | The identity for affine optics.
--
affine :: Traversal0 a b a b
affine = traversal0 Right $ flip const
{-# INLINE affine #-}

-- | TODO: Document
--
nulled :: Traversal0' s a
nulled = traversal0 Left const 
{-# INLINE nulled #-}

-- | TODO: Document
--
traversed :: Traversable f => Traversal (f a) (f b) a b
traversed = traversalVl traverse
{-# INLINE traversed #-}

-- | TODO: Document
--
-- Ideally we would have this:
--
-- > 'cotraversed' :: 'Cotraversal' [a] [b] a b
--
cotraversed :: Distributive1 f => Cotraversal (f a) (f b) a b 
cotraversed = cotraversalVl cotraverse1
{-# INLINE cotraversed #-}

-- | Obtain a 'Traversal1' from a 'Traversable1' functor.
--
traversed1 :: Traversable1 t => Traversal1 (t a) (t b) a b
traversed1 = traversalVl1 traverse1
{-# INLINE traversed1 #-}

-- | TODO: Document
--
-- > 'cotraversed' :: 'Cotraversal' (NonEmpty a) (NonEmpty b) a b
--
cotraversed1 :: Distributive1 f => Cotraversal1 (f a) (f b) a b
cotraversed1 = cotraversalVl1 cotraverse1
{-# INLINE cotraversed1 #-}

-- | Traverse both parts of a 'Bitraversable' container with matching types.
--
-- >>> traverses bitraversed (pure . length) (Right "hello")
-- Right 5
-- >>> traverses bitraversed (pure . length) ("hello","world")
-- (5,5)
-- >>> ("hello","world") ^. bitraversed
-- "helloworld"
--
-- @
-- 'bitraversed' :: 'Traversal' (a , a) (b , b) a b
-- 'bitraversed' :: 'Traversal' (a + a) (b + b) a b
-- @
--
bitraversed :: Bitraversable f => Traversal (f a a) (f b b) a b
bitraversed = represent $ \f -> bitraverse f f
{-# INLINE bitraversed #-}

-- | Traverse both parts of a 'Bitraversable1' container with matching types.
--
-- >>> ('h' :| "ello", 'w' :| "orld") & bitraversed1 **~ pure . NE.length 
-- (5,5)
--
bitraversed1 :: Bitraversable1 r => Traversal1 (r a a) (r b b) a b
bitraversed1 = represent $ \f -> bitraverse1 f f
{-# INLINE bitraversed1 #-}

-- | TODO: Document
--
-- @since 0.0.3
forked :: Traversal (a , a) (b , b) a b
forked p = p **** p
{-# INLINE forked #-}

-- | TODO: Document
--
-- >>> Left "foo" :| [Left "bar"] & coforked //~ fold
-- Left "foobar"
-- >>> Right "foo" :| [Right "bar"] & coforked //~ fold
-- Right "foobar"
-- 
-- @since 0.0.3
coforked :: Cotraversal (a + a) (b + b) a b
coforked p = p ++++ p
{-# INLINE coforked #-}

-- | Duplicate the results of a 'Traversal'. 
--
-- >>> list (bitraversed . duplicated) ("hello","world")
-- ["hello","hello","world","world"]
--
duplicated :: Traversal a b a b
duplicated p = pappend p p
{-# INLINE duplicated #-}

-- | Obtain a 'Traversal1'' by repeating the input forever.
--
-- @
-- 'repeat' ≡ 'list' 'repeated'
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
repeated = represent $ \g a -> go g a where go g a = g a .> go g a
{-# INLINE repeated #-}

-- | @x '^.' 'iterated' f@ returns an infinite 'Traversal1'' of repeated applications of @f@ to @x@.
--
-- @
-- 'list' ('iterated' f) a ≡ 'iterate' f a
-- @
--
-- >>> take 3 $ (1 :: Int) ^.. iterated (+1)
-- [1,2,3]
--
iterated :: (a -> a) -> Traversal1' a a
iterated f = represent $ \g a0 -> go g a0 where go g a = g a .> go g (f a)
{-# INLINE iterated #-}

-- | Transform a 'Traversal1'' into a 'Traversal1'' that loops over its elements repeatedly.
--
-- >>> take 7 $ (1 :| [2,3]) ^.. cycled traversed1
-- [1,2,3,1,2,3,1]
--
cycled :: Apply f => ATraversal' f s a -> ATraversal' f s a
cycled o = represent $ \g a -> go g a where go g a = (stars o g) a .> go g a
{-# INLINE cycled #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Test whether the optic matches or not.
--
-- >>> matches just (Just 2)
-- Right 2
-- >>> matches just (Nothing :: Maybe Int) :: Either (Maybe Bool) Int
-- Left Nothing
--
matches :: ATraversal0 s t a b -> s -> t + a
matches o = withAffine o $ \sta _ -> sta
{-# INLINE matches #-}

-- | TODO: Document
--
sequences :: Applicative f => ATraversal f s t (f a) a -> s -> f t
sequences o = stars o id
{-# INLINE sequences #-}

-- | TODO: Document
--
-- >>> collects cotraversed ["xxx","ooo"]
-- ["xo","xo","xo"]
-- >>> collects left' (1, Left "foo") :: Either (Int8, String) String
-- Left (1,"foo")
-- >>> collects left' (1, Right "foo")
-- Right "foo"
--
collects :: Coapply f => ACotraversal f s t a (f a) -> f s -> t
collects o = costars o id
{-# INLINE collects #-}

-- | This allows you to 'Control.Traversable.traverse' the elements of a 'Traversing' or 'Traversing1' optic in the opposite order.
--
-- This will preserve indexes on 'Indexed' types and for example will give you the elements of a (finite) 'Fold' or 'Traversal' in the opposite order.
--
-- This has no practical effect on a 'View', 'Setter', 'Lens' or 'Iso'.
--
-- @since 0.0.3
backwards :: ATraversal (Backwards f) s t a b -> (a -> f b) -> s -> f t
backwards o = (forwards #.) #. stars o .# (Backwards #.)
{-# INLINE backwards #-}

{-
-- | Generalize 'Data.Traversable.mapAccumL' to a 'Traversing' or 'Traversing1' optic.
--
-- @
-- 'mapAccumL' ≡ 'mapAccumsL' 'traverse'
-- @
--
-- 'mapAccumsL' accumulates 'State' from left to right.
--
-- @since 0.0.3
mapAccumsL :: ATraversal (State r) s t a b -> (r -> a -> (r, b)) -> r -> s -> (r, t)
mapAccumsL o f acc0 s = swap (runState (stars o g s) acc0) where
   g a = state $ \acc -> swap (f acc a)

-- | Generalize 'Data.Traversable.mapAccumR' to a 'Traversing' or 'Traversing1' optic.
--
-- @
-- 'mapAccumR' ≡ 'mapAccumsR' 'traverse'
-- @
--
-- 'mapAccumsR' accumulates 'State' from right to left.
--
-- @since 0.0.3
mapAccumsR :: ATraversal (Backwards (State r)) s t a b -> (r -> a -> (r, b)) -> r -> s -> (r, t)
mapAccumsR = mapAccumsL . astar . backwards
{-# INLINE mapAccumsR #-}


-- | Scan left over a 'Traversing' or 'Traversing1' optic.
--
-- @
-- 'scanl1' ≡ 'scansl1' 'traverse'
-- @
--
-- @since 0.0.3
scansl1 :: ATraversal (State (Maybe a)) s t a a -> (a -> a -> a) -> s -> t
scansl1 o f = snd . mapAccumsL o step Nothing where
  step Nothing a  = (Just a, a)
  step (Just s) a = (Just r, r) where r = f s a
{-# INLINE scansl1 #-}

-- | Scan left over a 'Traversing' or 'Traversing1' optic.
--
-- @
-- 'scanr1' ≡ 'scansr1' 'traverse'
-- @
--
-- @since 0.0.3
scansr1 :: ATraversal (Backwards (State (Maybe a))) s t a a -> (a -> a -> a) -> s -> t
scansr1 o f = snd . mapAccumsR o step Nothing where
  step Nothing a  = (Just a, a)
  step (Just s) a = (Just r, r) where r = f a s
{-# INLINE scansr1 #-}
-}
