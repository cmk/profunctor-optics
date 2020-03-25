{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE PolyKinds             #-}
module Data.Profunctor.Optic.Traversal (
    -- * At
    At
    -- * Traversal0
  , Traversal0, Ixtraversal0
  , Cotraversal0
  , Traversal0', Ixtraversal0'
  , Cotraversal0'
  , traversal0, itraversal0
  , traversal0', itraversal0'
  , traversal0Vl, itraversal0Vl
    -- * Traversal
  , Traversal, Ixtraversal
  , Cotraversal
  , Traversal', Ixtraversal'
  , Cotraversal'
  , traversing, itraversing
  , cotraversing, retraversing
  , traversalVl, itraversalVl
  , cotraversalVl
  , atraversal
  , acotraversal
    -- * Traversal1
  , Traversal1, Ixtraversal1
  , Cotraversal1
  , Traversal1', Ixtraversal1'
  , Cotraversal1'
  , traversing1
  , cotraversing1, retraversing1
  , traversal1Vl, itraversal1Vl
  , cotraversal1Vl
  , pappend
  , divide
  , divide'
  , cochoose
  , cochoose'
  , codivide
  , codivide'
  , choose
  , choose'
  , (<<*>>)
  , (****)
  , (&&&&)
  , (++++)
  , (||||)
    -- * Optics
  , at
  , anulled
  , selected
  , traversed
  , cotraversed
  , traversed1
  , cotraversed1
  , bitraversed
  , bitraversed1
  , both
  , coboth
  , duplicated
  , beside
  , repeated 
  , iterated
  , cycled
    -- * Indexed optics
  , itraversed
  , itraversed1
  , itraversedRep
    -- * Operators
  , matches
  , (*~)
  , (**~)
  , sequences
  , traverses
  , (/~)
  , (//~)
  , collects 
  , cotraverses
  , withAffine
  , withCoaffine
    -- * Indexed operators
  , iat
  , (%~)
  , (%%~)
  , itraverses
    -- * Classes
  , Strong(..)
  , Choice(..)
  , Closed(..)
  , Representable(..)
  , Corepresentable(..)
) where

import Control.Monad.State
import Data.Key as K
import Data.Function
import Data.Bitraversable
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Prism
import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Combinator
import Data.Semigroup.Bitraversable
import qualified Data.Functor.Rep as F

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XFlexibleContexts
-- >>> :set -XTypeApplications
-- >>> :set -XTupleSections
-- >>> :set -XRankNTypes
-- >>> import Data.Int
-- >>> import Data.String
-- >>> import Data.Maybe
-- >>> import Data.List.NonEmpty (NonEmpty(..))
-- >>> import qualified Data.List.NonEmpty as NE
-- >>> import Data.Functor.Identity
-- >>> :load Data.Profunctor.Optic

type At f = (Lookup f, Adjustable f)

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
traversal0 sta sbt = dimap (\s -> (s,) <$> sta s) (id ||| uncurry sbt) . right' . second'
{-# INLINE traversal0 #-}

-- | TODO: Document
--
itraversal0 :: (s -> t + (i , a)) -> (s -> b -> t) -> Ixtraversal0 i s t a b
itraversal0 stia sbt = itraversal0Vl $ \point f s -> either point (fmap (sbt s) . uncurry f) (stia s)
{-# INLINE itraversal0 #-}

-- | Obtain a 'Traversal0'' from match and constructor functions.
--
traversal0' :: (s -> Maybe a) -> (s -> a -> s) -> Traversal0' s a
traversal0' sa sas = flip traversal0 sas $ \s -> maybe (Left s) Right (sa s)
{-# INLINE traversal0' #-}

-- | TODO: Document
--
itraversal0' :: (s -> Maybe (i , a)) -> (s -> a -> s) -> Ixtraversal0' i s a
itraversal0' sia = itraversal0 $ \s -> maybe (Left s) Right (sia s) 
{-# INLINE itraversal0' #-}

-- | Transform a Van Laarhoven 'Traversal0' into a profunctor 'Traversal0'.
--
traversal0Vl :: (forall f. Functor f => (forall c. c -> f c) -> (a -> f b) -> s -> f t) -> Traversal0 s t a b
traversal0Vl f = dimap (\s -> (s,) <$> eswap (sat s)) (id ||| uncurry sbt) . right' . second'
  where
    sat = f Right Left
    sbt s b = runIdentity $ f Identity (\_ -> Identity b) s
{-# INLINE traversal0Vl #-}

-- | Transform an indexed Van Laarhoven 'Traversal0' into an indexed profunctor 'Traversal0'.
--
itraversal0Vl :: (forall f. Functor f => (forall c. c -> f c) -> (i -> a -> f b) -> s -> f t) -> Ixtraversal0 i s t a b
itraversal0Vl f = traversal0Vl $ \cc iab -> f cc (curry iab) . snd
{-# INLINE itraversal0Vl #-}

---------------------------------------------------------------------
-- 'Traversal'
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
traversing sa sbt = represent traverse . lens sa sbt
{-# INLINE traversing #-}

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
itraversing :: (Sum-Monoid) i => Traversable f => (s -> (i , a)) -> (s -> b -> t) -> Ixtraversal i (f s) (f t) a b
itraversing sia sbt = represent (\iab -> traverse (curry iab zero) . snd) . ilens sia sbt 

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
traversalVl abst = tabulate . abst . sieve
{-# INLINE traversalVl #-}

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
{-# INLINE itraversalVl #-}

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
cotraversing sabt = corepresent cotraverse . grate sabt

-- | Obtain a 'Cotraversal' by embedding a reversed lens getter and setter into a 'Distributive' functor.
--
-- @
--  'withLens' ('re' o) 'cotraversing' ≡ 'cotraversed' . o
-- @
--
retraversing :: Distributive g => (b -> t) -> (b -> s -> a) -> Cotraversal (g s) (g t) a b
retraversing bsa bt = corepresent cotraverse . (re $ lens bsa bt)

-- | Obtain a profunctor 'Cotraversal' from a Van Laarhoven 'Cotraversal'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @abst copure ≡ copure@
--
-- * @abst f . fmap (abst g) ≡ abst (f . fmap g . getCompose) . Compose@
--
-- The cotraversal laws can be restated in terms of 'cotraverses':
--
-- * @cotraverses o (f . copure) ≡  fmap f . copure@
--
-- * @cotraverses o f . fmap (cotraverses o g) == cotraverses o (f . fmap g . getCompose) . Compose@
--
-- See 'Data.Profunctor.Optic.Property'.
--
cotraversalVl :: (forall f. Coapplicative f => (f a -> b) -> f s -> t) -> Cotraversal s t a b
cotraversalVl abst = cotabulate . abst . cosieve 

-- | TODO: Document
--
atraversal :: ((a -> f b) -> s -> f t) -> ATraversal f s t a b
atraversal f = Star #. f .# runStar
{-# INLINE atraversal #-}

-- | TODO: Document
--
acotraversal :: ((f a -> b) -> f s -> t) -> ACotraversal f s t a b
acotraversal f = Costar #. f .# runCostar
{-# INLINE acotraversal #-}

{-
-- | Lift a VL traversal into an indexed profunctor traversal that ignores its input.
--
-- Useful as the first optic in a chain when no indexed equivalent is at hand.
--
-- >>> ilists (noix traversed . itraversed) ["foo", "bar"]
-- [(0,'f'),(1,'o'),(2,'o'),(0,'b'),(1,'a'),(2,'r')]
-- >>> ilists (itraversed . noix traversed) ["foo", "bar"]
-- [(0,'f'),(0,'o'),(0,'o'),(0,'b'),(0,'a'),(0,'r')]
--
noix :: (Sum-Monoid) i => Traversal s t a b -> Ixtraversal i s t a b
noix o = itraversalVl $ \iab s -> flip runStar s . o . Star $ iab zero

-- | Index a traversal with a 'Data.Semiring'.
--
-- >>> ilists (ix traversed . ix traversed) ["foo", "bar"]
-- [((),'f'),((),'o'),((),'o'),((),'b'),((),'a'),((),'r')]
-- >>> ilists (ix @Int traversed . ix traversed) ["foo", "bar"]
-- [(0,'f'),(1,'o'),(2,'o'),(0,'b'),(1,'a'),(2,'r')]
-- >>> ilists (ix @[()] traversed . ix traversed) ["foo", "bar"]
-- [([],'f'),([()],'o'),([(),()],'o'),([],'b'),([()],'a'),([(),()],'r')]
-- >>> ilists (ix @[()] traversed % ix traversed) ["foo", "bar"]
-- [([],'f'),([()],'o'),([(),()],'o'),([()],'b'),([(),()],'a'),([(),(),()],'r')]
--
ix :: Semiring i => Traversal s t a b -> Ixtraversal i s t a b
ix o = itraversalVl $ \f s ->
  flip evalState zero . getCompose . flip runStar s . o . Star $ \a ->
    Compose $ (f <$> get <*> pure a) <* modify (+ one) 
-}

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
traversing1 sa sbt = represent traverse1 . lens sa sbt
{-# INLINE traversing1 #-}

-- | Obtain a 'Cotraversal1' by embedding a continuation into a 'Distributive1' functor. 
--
-- @
--  'withGrate' o 'cotraversing1' ≡ 'cotraversed1' . o
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
cotraversing1 sabt = corepresent cotraverse1 . grate sabt

-- | Obtain a 'Cotraversal1' by embedding a reversed lens getter and setter into a 'Distributive1' functor.
--
-- @
--  'withLens' ('re' o) 'cotraversing' ≡ 'cotraversed' . o
-- @
--
retraversing1 :: Distributive1 g => (b -> t) -> (b -> s -> a) -> Cotraversal1 (g s) (g t) a b
retraversing1 bsa bt = corepresent cotraverse1 . (re $ lens bsa bt)

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
{-# INLINE traversal1Vl #-}

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

-- | Obtain a profunctor 'Cotraversal1' from a Van Laarhoven 'Cotraversal1'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @abst runIdentity ≡ runIdentity@
--
-- * @abst f . fmap (abst g) ≡ abst (f . fmap g . getCompose) . Compose@
--
-- The cotraversal1 laws can be restated in terms of 'cotraverses':
--
-- * @cotraverses o (f . runIdentity) ≡  fmap f . runIdentity@
--
-- * @cotraverses o f . fmap (cotraverses o g) == cotraverses o (f . fmap g . getCompose) . Compose@
--
-- See 'Data.Profunctor.Optic.Property'.
--
cotraversal1Vl :: (forall f. Coapply f => (f a -> b) -> f s -> t) -> Cotraversal1 s t a b
cotraversal1Vl abst = cotabulate . abst . cosieve 

---------------------------------------------------------------------
-- Optics
---------------------------------------------------------------------

-- | /O(log n)/. Affine traversal into the value at a key of a 'Map.Map'.
--
-- >>> Map.fromList [(1,"world")] ^. at 0
-- ""
-- >>> Map.fromList [(1,"world")] ^. at 1
-- "world"
-- >>> Map.fromList [(67,'C')] & at 99 ..~ toLower
-- fromList [(67,'C')]
-- >>> Map.fromList [(67,'C')] & at 67 ..~ toLower
-- fromList [(67,'c')]
--
at :: At f => Key f -> Traversal0' (f a) a
at k = traversal0' (K.lookup k) (flip $ K.replace k)
{-# INLINE at #-}

-- | TODO: Document
--
anulled :: Traversal0' s a
anulled = traversal0 Left const 
{-# INLINE anulled #-}

-- | TODO: Document
--
selected :: (a -> Bool) -> Traversal0' (a, b) b
selected p = traversal0 (\kv@(k,v) -> branch p kv v k) (\kv@(k,_) v' -> if p k then (k,v') else kv)
{-# INLINE selected #-}

-- | TODO: Document
--
traversed :: Traversable f => Traversal (f a) (f b) a b
traversed = traversalVl traverse
{-# INLINE traversed #-}

-- | TODO: Document
--
cotraversed :: Distributive f => Cotraversal (f a) (f b) a b 
cotraversed = cotraversalVl cotraverse
{-# INLINE cotraversed #-}

-- | Obtain a 'Traversal1' from a 'Traversable1' functor.
--
traversed1 :: Traversable1 t => Traversal1 (t a) (t b) a b
traversed1 = traversal1Vl traverse1
{-# INLINE traversed1 #-}

-- | TODO: Document
--
-- > 'cotraversed1' :: 'Cotraversal1' [a] [b] a b
--
cotraversed1 :: Distributive1 f => Cotraversal1 (f a) (f b) a b
cotraversed1 = cotraversal1Vl cotraverse1
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
-- >>> traverses bitraversed1 (pure . NE.length) ('h' :| "ello", 'w' :| "orld")
-- (5,5)
--
bitraversed1 :: Bitraversable1 r => Traversal1 (r a a) (r b b) a b
bitraversed1 = represent $ \f -> bitraverse1 f f
{-# INLINE bitraversed1 #-}

-- | TODO: Document
--
-- >>> traverses both (pure . length) ("hello","world")
-- (5,5)
-- >>> traverses both (pure . NE.length) ('h' :| "ello", 'w' :| "orld")
-- (5,5)
--
both :: Traversal1 (a , a) (b , b) a b
both p = p **** p
{-# INLINE both #-}

-- | TODO: Document
--
-- >>> cotraverses coboth (foldMap id) $ Left "foo" :| [Right "bar"]
-- Left "foo"
-- >>> cotraverses coboth (foldMap id) $ Right "foo" :| [Right "bar"]
-- Right "foobar"
-- 
coboth :: Cotraversal1 (a + a) (b + b) a b
coboth p = p ++++ p
{-# INLINE coboth #-}

-- | Duplicate the results of a 'Traversal'. 
--
-- >>> lists (both . duplicated) ("hello","world")
-- ["hello","hello","world","world"]
--
duplicated :: Traversal a b a b
duplicated p = pappend p p
{-# INLINE duplicated #-}

-- | TODO: Document
--
beside :: Bitraversable r => Traversal s1 t1 a b -> Traversal s2 t2 a b -> Traversal (r s1 s2) (r t1 t2) a b
beside x y p = tabulate go where go rss = bitraverse (sieve $ x p) (sieve $ y p) rss
{-# INLINE beside #-}

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
repeated = represent $ \g a -> go g a where go g a = g a .> go g a
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
iterated :: (a -> a) -> Traversal1' a a
iterated f = represent $ \g a0 -> go g a0 where go g a = g a .> go g (f a)
{-# INLINE iterated #-}

-- | Transform a 'Traversal1'' into a 'Traversal1'' that loops over its elements repeatedly.
--
-- >>> take 7 $ (1 :| [2,3]) ^.. cycled traversed1
-- [1,2,3,1,2,3,1]
--
cycled :: Apply f => ATraversal' f s a -> ATraversal' f s a
cycled o = represent $ \g a -> go g a where go g a = (traverses o g) a .> go g a
{-# INLINE cycled #-}

---------------------------------------------------------------------
-- Indexed optics 
---------------------------------------------------------------------

-- | TODO: Document
--
itraversed :: TraversableWithKey f => Traversable f => Ixtraversal (Key f) (f a) (f b) a b
itraversed = itraversalVl K.traverseWithKey
{-# INLINE itraversed #-}

-- | TODO: Document
--
itraversed1 :: TraversableWithKey1 f => Traversable1 f => Ixtraversal1 (Key f) (f a) (f b) a b
itraversed1 = itraversal1Vl K.traverseWithKey1
{-# INLINE itraversed1 #-}

-- | TODO: Document
--
itraversedRep :: F.Representable f => Traversable f => Ixtraversal (F.Rep f) (f a) (f b) a b
itraversedRep = itraversalVl F.itraverseRep
{-# INLINE itraversedRep #-}

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

infixr 4 *~, **~, /~, //~ --, %~, %%~, #~, ##~

-- | Set the focus of a representable optic.
--
(*~) :: ATraversal f s t a b -> f b -> s -> f t
(*~) o b = traverses o (const b)
{-# INLINE (*~) #-}

-- | Map over a representable optic.
--
(**~) :: ATraversal f s t a b -> (a -> f b) -> s -> f t
(**~) = traverses
{-# INLINE (**~) #-}

-- | TODO: Document
--
sequences :: Applicative f => ATraversal f s t (f a) a -> s -> f t
sequences o = traverses o id
{-# INLINE sequences #-}

-- | TODO: Document
--
traverses :: ATraversal f s t a b -> (a -> f b) -> s -> f t
traverses o = runStar #. o .# Star
{-# INLINE traverses #-}

-- | Set the focus of a co-representable optic.
--
(/~) :: ACotraversal f s t a b -> b -> f s -> t
(/~) o b = cotraverses o (const b)
{-# INLINE (/~) #-}

-- | Map over a co-representable optic.
--
(//~) :: ACotraversal f s t a b -> (f a -> b) -> f s -> t
(//~) = cotraverses
{-# INLINE (//~) #-}

-- | TODO: Document
--
-- >>> collects cotraversed1 ["xxx","ooo"]
-- ["xo","xo","xo"]
-- >>> collects left' (1, Left "foo") :: Either (Int8, String) String
-- Left (1,"foo")
-- >>> collects left' (1, Right "foo")
-- Right "foo"
--
collects :: Coapply f => ACotraversal f s t a (f a) -> f s -> t
collects o = cotraverses o id
{-# INLINE collects #-}

-- | TODO: Document
--
cotraverses :: ACotraversal f s t a b -> (f a -> b) -> (f s -> t)
cotraverses o = runCostar #. o .# Costar
{-# INLINE cotraverses #-}

---------------------------------------------------------------------
-- Indexed operators
---------------------------------------------------------------------

-- | /O(log n)/. Indexed affine traversal into the value at a key of a 'Map.Map'.
--
-- >>> Map.fromList [(1,"world")] ^% iat 0 
-- (Nothing,"")
-- >>> Map.fromList [(1,"world")] ^% iat 1
-- (Just 1,"world")
-- >>> Map.fromList [(67,'C')] & iat 99 %~ chr
-- fromList [(67,'C')]
-- >>> Map.fromList [(67,'C')] & iat 67 %%~ const toLower
-- fromList [(67,'c')]
-- >>> iat 2 %%~ (\i x -> if odd i then not x else x) $ Map.fromList [(1,True),(2,False)]
-- fromList [(1,True),(2,False)]
--
iat :: At f => Key f -> Ixtraversal0' (Key f) (f a) a; 
iat k = itraversal0' (\s -> (k,) <$> K.lookup k s) (flip $ K.replace k) 
{-# INLINE iat #-}

infixr 4 %~, %%~

-- | Set the focus of an indexed optic.
--
--  See also '#~'.
--
-- /Note/ if you're looking for the infix 'over' it is '..~'.
--
(%~) :: (Sum-Monoid) i => AIxtraversal f i s t a b -> (i -> f b) -> s -> f t
(%~) o = (%%~) o . (const .)
{-# INLINE (%~) #-}

-- | Map over an indexed optic.
--
-- See also '##~'.
--
(%%~) :: (Sum-Monoid) i => AIxtraversal f i s t a b -> (i -> a -> f b) -> s -> f t
(%%~) = itraverses
{-# INLINE (%%~) #-}

-- | TODO: Document
--
itraverses :: (Sum-Monoid) i => AIxtraversal f i s t a b -> (i -> a -> f b) -> s -> f t
itraverses o f = curry (traverses o $ uncurry f) zero
{-# INLINE itraverses #-}
