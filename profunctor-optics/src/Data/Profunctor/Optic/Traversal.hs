{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}

-- | Left and right carriers are characterized by their representation
-- functors ('Rep' and 'Corep'). 'Iso' sits at the top where both
-- are trivial ('Identity'). 'Adjoint' sits at the bottom where they
-- form a full adjunction (@'Corep' p ⊣ 'Rep' p@). A left-indexed
-- ('Ix') optic threads an index through the left adjoint functor
-- @(,) k@, while a right-indexed ('Cx') optic threads a coindex
-- through the right adjoint functor @(->) k@.
module Data.Profunctor.Optic.Traversal (
    -- * Constructors
    -- ** Traversal, Ixtraversal
    Traversal, Traversal'
  , Ixtraversal, Ixtraversal'
  , atraversal
  , traversing
  , ixtraversing
  , traversalVl
  , ixtraversalVl
  , beside
  , reversing
  , ix, noix
  , cloneTraversalVl
  , cloneTraversal1Vl
    -- ** Traversal0, Ixtraversal0
  , Traversal0, Traversal0'
  , Ixtraversal0, Ixtraversal0'
  , traversal0
  , ixtraversal0
  , traversal0'
  , ixtraversal0'
  , traversalVl0
  , ixtraversalVl0
  , cloneTraversal0
    -- ** Traversal1, Ixtraversal1
  , Traversal1, Traversal1'
  , Ixtraversal1, Ixtraversal1'
  , traversing1
  , ixtraversing1
  , traversalVl1
  , ixtraversalVl1
  , beside1
    -- * Dual Constructors
    -- ** Cotraversal, Cxtraversal
  , Cotraversal, Cotraversal'
  , Cxtraversal, Cxtraversal'
  , acotraversal
  , cotraversing
  , retraversing
  , cotraversalVl
  , cxtraversalVl
  , cloneCotraversalVl
    -- ** Cotraversal0, Cxtraversal0
  , Cotraversal0
  , Cotraversal0'
  , cotraversal0
  , cloneCotraversal0
    -- ** Cotraversal1, Cxtraversal1
  , Cotraversal1, Cotraversal1'
  , Cxtraversal1, Cxtraversal1'
  , cotraversing1
  , retraversing1
  , cotraversalVl1
  , cxtraversalVl1
  , cloneCotraversal1Vl
    -- * Optics
    -- ** Traversal, Ixtraversal
  , traversed
  , itraversedRep
  , bitraversed
  , anulled
  , selected
  , duplicated
  , repeated
  , iterated
  , cycling
    -- ** Traversal1, Ixtraversal1
  , traversed1
  , bitraversed1
  , forked
    -- * Dual Optics
    -- ** Cotraversal, Cxtraversal
  , cotraversed
  , coforked
    -- ** Cotraversal1, Cxtraversal1
  , cotraversed1
    -- * Operators
    -- ** Traversal, Ixtraversal
  , traverseOf
  , ixtraverseOf
  , sequenceOf
  , ixsequenceOf
  , reverseOf
  , mapAccumLOf
  , mapAccumROf
  , ixmapAccumLOf
  , ixmapAccumROf
  , scanl1Of
  , scanr1Of
    -- ** Traversal0, Ixtraversal0
  , matches
  , ixmatches
    -- ** Traversal1, Ixtraversal1
    -- * Dual Operators
    -- ** Cotraversal, Cxtraversal
  , cotraverseOf
  , cxtraverseOf
  , collectOf
  , cxcollectOf
    -- * Reexports
  , Strong(..)
  , Choice(..)
  , Closed(..)
  , Representable(..)
  , Corepresentable(..)
) where

import Control.Monad.State
import Control.Applicative.Backwards
import Data.Bitraversable
import Data.Profunctor.Optic.Arrow
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Dual
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Index
import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.Prism
import Data.Profunctor.Optic.Types
import Data.Semigroup.Bitraversable
import qualified Data.Bifunctor as B
import qualified Data.Functor.Rep as F

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
-- >>> import Prelude

---------------------------------------------------------------------
-- Constructors
---------------------------------------------------------------------

-- | TODO: Document
--
atraversal :: ((a -> f b) -> s -> f t) -> ATraversal f s t a b
atraversal f = Star #. f .# runStar
{-# INLINE atraversal #-}

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
-- The resulting optic can detect copies of the lens structure inside
-- any 'Traversable' container. For example:
--
-- >>> toListOf (traversing snd $ \(s,_) b -> (s,b)) [(0,'f'),(1,'o'),(2,'o'),(3,'b'),(4,'a'),(5,'r')]
-- "foobar"
--
traversing :: Traversable f => (s -> a) -> (s -> b -> t) -> Traversal (f s) (f t) a b
traversing sa sbt = representing traverse . lens sa sbt
{-# INLINE traversing #-}

---------------------------------------------------------------------
-- Indexed Constructors
---------------------------------------------------------------------

-- | Obtain a 'Ixtraversal' by lifting an indexed lens getter and setter into a 'Traversable' functor.
--
-- @
--  'withIxlens' o 'ixtraversing' ≡ 'ixtraversed' . o
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
-- @since 0.0.3
ixtraversing :: Monoid k => Traversable f => (s -> (k , a)) -> (s -> b -> t) -> Ixtraversal k (f s) (f t) a b
ixtraversing sia sbt = representing (\kab -> traverse (curry kab mempty) . snd) . ixlens sia sbt

-- | Obtain a profunctor 'Traversal' from a Van Laarhoven 'Traversal'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @abst pure ≡ pure@
--
-- * @fmap (abst f) . abst g ≡ getCompose . abst (Compose . fmap f . g)@
--
-- The traversal laws can be stated in terms of 'traverseOf':
--
-- * @traverseOf t (pure . f) ≡ pure (fmap f)@
--
-- * @Compose . fmap (traverseOf t f) . traverseOf t g ≡ traverseOf t (Compose . fmap f . g)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
traversalVl :: (forall f. Applicative' f => (a -> f b) -> s -> f t) -> Traversal s t a b
traversalVl f pab = representing f pab
{-# INLINE traversalVl #-}

-- | Lift an indexed VL traversal into an indexed profunctor traversal.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @kabst (const pure) ≡ pure@
--
-- * @fmap (kabst $ const f) . (kabst $ const g) ≡ getCompose . kabst (const $ Compose . fmap f . g)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- @since 0.0.3
ixtraversalVl :: (forall f. Applicative f => (k -> a -> f b) -> k -> s -> f t) -> Ixtraversal k s t a b
ixtraversalVl f = traversalVl $ \kab -> uncurry (f (curry kab))
{-# INLINE ixtraversalVl #-}

-- | TODO: Document
--
beside :: Bitraversable r => Traversal s1 t1 a b -> Traversal s2 t2 a b -> Traversal (r s1 s2) (r t1 t2) a b
beside x y p = tabulate go where go rss = bitraverse (sieve $ x p) (sieve $ y p) rss
{-# INLINE beside #-}

-- | TODO: Document
--
-- @since 0.0.3
reversing :: ATraversal (Backwards f) s t a b -> ATraversal f s t a b
reversing = atraversal . reverseOf
{-# INLINE reversing #-}

-- | Iteratively index a traversal with an incrementing value.
--
-- The incoming index from outer composition is used as the initial
-- accumulator, so @('.')@ threads indices through chains of 'ix'.
--
-- >>> B.first getSum <$> ixtoListOf (ix (Sum 1) traversed) "foobar"
-- [(0,'f'),(1,'o'),(2,'o'),(3,'b'),(4,'a'),(5,'r')]
-- >>> ixtoListOf (noix traversed . ix "o" traversed) ["foo", "bar"]
-- [("",'f'),("o",'o'),("oo",'o'),("",'b'),("o",'a'),("oo",'r')]
-- >>> ixtoListOf (ix "x" traversed . ix "o" traversed) ["foo", "bar"]
-- [("",'f'),("o",'o'),("oo",'o'),("x",'b'),("xo",'a'),("xoo",'r')]
-- >>> B.first getSum <$> ixtoListOf (ix (Sum 3) traversed . ix (Sum 1) traversed) ["foo", "bar"]
-- [(0,'f'),(1,'o'),(2,'o'),(3,'b'),(4,'a'),(5,'r')]
--
-- @since 0.0.3
ix :: Semigroup k => k -> Traversal s t a b -> Ixtraversal k s t a b
ix k o = ixrepresenting $ \f k_in s ->
  flip evalState k_in . getCompose . flip runStar s . o . Star $ \a ->
    Compose $ (f <$> get <*> pure a) <* modify (<> k)

-- | Lift a non-indexed traversal into an indexed one that passes
-- through the incoming index without modification.
--
-- @since 0.0.3
noix :: Traversal s t a b -> Ixtraversal k s t a b
noix o = ixrepresenting $ \iab k_in s -> flip runStar s . o . Star $ iab k_in

-- | Extract the Van Laarhoven function that characterizes a 'Traversal'.
--
-- @since 0.0.3
cloneTraversalVl :: Applicative f => ATraversal f s t a b -> (a -> f b) -> s -> f t
cloneTraversalVl = traverseOf
{-# INLINE cloneTraversalVl #-}

-- | Extract the Van Laarhoven function that characterizes a 'Traversal1'.
--
-- @since 0.0.3
cloneTraversal1Vl :: Apply f => ATraversal1 f s t a b -> (a -> f b) -> s -> f t
cloneTraversal1Vl = traverseOf
{-# INLINE cloneTraversal1Vl #-}

---------------------------------------------------------------------
-- Traversal0 Constructors
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
traversal0 sta sbt = dimap (\s -> (s,) <$> sta s) (either id (uncurry sbt)) . right' . second'
{-# INLINE traversal0 #-}

---------------------------------------------------------------------
-- Indexed Traversal0 Constructors
---------------------------------------------------------------------

-- | TODO: Document
--
-- @since 0.0.3
ixtraversal0 :: (s -> t + (k , a)) -> (s -> b -> t) -> Ixtraversal0 k s t a b
ixtraversal0 stia sbt = ixtraversalVl0 $ \point f _k s -> either point (fmap (sbt s) . uncurry f) (stia s)
{-# INLINE ixtraversal0 #-}

-- | Obtain a 'Traversal0'' from match and constructor functions.
--
traversal0' :: (s -> Maybe a) -> (s -> b -> s) -> Traversal0 s s a b
traversal0' sa sas = traversal0 (\s -> maybe (Left s) Right (sa s)) sas
{-# INLINE traversal0' #-}

-- | TODO: Document
--
-- @since 0.0.3
ixtraversal0' :: (s -> Maybe (k , a)) -> (s -> a -> s) -> Ixtraversal0' k s a
ixtraversal0' sia = ixtraversal0 $ \s -> maybe (Left s) Right (sia s)
{-# INLINE ixtraversal0' #-}

-- | Transform a Van Laarhoven 'Traversal0' into a profunctor 'Traversal0'.
--
traversalVl0 :: (forall f. Functor f => (forall c. c -> f c) -> (a -> f b) -> s -> f t) -> Traversal0 s t a b
traversalVl0 f = dimap (\s -> (s,) <$> eswap (f Right Left s)) (either id (uncurry sbt)) . right' . second'
  where
    sbt s b = runIdentity $ f Identity (\_ -> Identity b) s
{-# INLINE traversalVl0 #-}

-- | Transform an indexed Van Laarhoven 'Traversal0' into an indexed profunctor 'Traversal0'.
--
-- @since 0.0.3
ixtraversalVl0 :: (forall f. Functor f => (forall c. c -> f c) -> (k -> a -> f b) -> k -> s -> f t) -> Ixtraversal0 k s t a b
ixtraversalVl0 f = traversalVl0 $ \cc kab -> uncurry (f cc (curry kab))
{-# INLINE ixtraversalVl0 #-}

-- | Clone a 'Traversal0'.
--
-- @since 0.0.3
cloneTraversal0 :: ATraversal0 s t a b -> Traversal0 s t a b
cloneTraversal0 o = withTraversal0 o traversal0
{-# INLINE cloneTraversal0 #-}

---------------------------------------------------------------------
-- Traversal1 Constructors
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
-- The resulting optic can detect copies of the lens structure inside
-- any 'Traversable' container. For example:
--
-- >>> toListOf (traversing snd $ \(s,_) b -> (s,b)) [(0,'f'),(1,'o'),(2,'o'),(3,'b'),(4,'a'),(5,'r')]
-- "foobar"
--
-- Compare 'Data.Profunctor.Optic.Fold.folding'.
--
traversing1 :: Traversable1 f => (s -> a) -> (s -> b -> t) -> Traversal1 (f s) (f t) a b
traversing1 sa sbt = representing traverse1 . lens sa sbt
{-# INLINE traversing1 #-}

---------------------------------------------------------------------
-- Indexed Traversal1 Constructors
---------------------------------------------------------------------

-- | Obtain a 'Ixtraversal' by lifting an indexed lens getter and setter into a 'Traversable' functor.
--
-- @
--  'withIxlens' o 'ixtraversing' ≡ 'ixtraversed' . o
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
-- @since 0.0.3
ixtraversing1 :: Monoid k => Traversable1 f => (s -> (k , a)) -> (s -> b -> t) -> Ixtraversal1 k (f s) (f t) a b
ixtraversing1 sia sbt = representing (\kab -> traverse1 (curry kab mempty) . snd) . ixlens sia sbt

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

-- | Obtain a profunctor 'Ixtraversal1' from a Van Laarhoven 'Ixtraversal1'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @kabst (const Identity) ≡ Identity@
--
-- * @fmap (kabst $ const f) . (kabst $ const g) ≡ getCompose . kabst (const $ Compose . fmap f . g)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- @since 0.0.3
ixtraversalVl1 :: (forall f. Apply f => (k -> a -> f b) -> k -> s -> f t) -> Ixtraversal1 k s t a b
ixtraversalVl1 f = traversalVl1 $ \kab -> uncurry (f (curry kab))
{-# INLINE ixtraversalVl1 #-}

-- | TODO: Document
--
beside1 :: Bitraversable1 r => Traversal1 s1 t1 a b -> Traversal1 s2 t2 a b -> Traversal1 (r s1 s2) (r t1 t2) a b
beside1 x y p = tabulate go where go rss = bitraverse1 (sieve $ x p) (sieve $ y p) rss
{-# INLINE beside1 #-}

---------------------------------------------------------------------
-- Dual Constructors
---------------------------------------------------------------------

-- | TODO: Document
--
acotraversal :: ((f a -> b) -> f s -> t) -> ACotraversal f s t a b
acotraversal f = Costar #. f .# runCostar
{-# INLINE acotraversal #-}

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
cotraversing sabt = corepresenting cotraverse . grate sabt

-- | Obtain a 'Cotraversal' by embedding a reversed lens getter and setter into a 'Distributive' functor.
--
-- @
--  'withLens' ('re' o) 'retraversing' ≡ 'cotraversed' . o
-- @
--
retraversing :: Distributive g => (b -> t) -> (b -> s -> a) -> Cotraversal (g s) (g t) a b
retraversing bt bsa = corepresenting cotraverse . (re $ lens bt bsa)

-- | Obtain a profunctor 'Cotraversal' from a Van Laarhoven 'Cotraversal'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @abst copure ≡ copure@
--
-- * @abst f . fmap (abst g) ≡ abst (f . fmap g . getCompose) . Compose@
--
-- The cotraversal laws can be restated in terms of 'cotraverseOf':
--
-- * @cotraverseOf o (f . copure) ≡  fmap f . copure@
--
-- * @cotraverseOf o f . fmap (cotraverseOf o g) == cotraverseOf o (f . fmap g . getCompose) . Compose@
--
-- See 'Data.Profunctor.Optic.Property'.
--
cotraversalVl :: (forall f. Coapplicative f => (f a -> b) -> f s -> t) -> Cotraversal s t a b
cotraversalVl f pab = corepresenting f pab

---------------------------------------------------------------------
-- Coindexed Constructors
---------------------------------------------------------------------

-- | Lift a coindexed VL cotraversal into a coindexed profunctor cotraversal.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @aibst (const . copure) ≡ copure@
--
-- * @(aibst $ const . f) . fmap (aibst $ const . g) ≡ aibst (const . f . fmap g . getCompose) . Compose@
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- @since 0.0.3
cxtraversalVl :: (forall f. Coapplicative f => (f a -> k -> b) -> k -> f s -> t) -> Cxtraversal k s t a b
cxtraversalVl f = cotraversalVl $ \akb fs k -> f akb k fs
{-# INLINE cxtraversalVl #-}

-- | Extract the Van Laarhoven function that characterizes a 'Cotraversal'.
--
-- @since 0.0.3
cloneCotraversalVl :: Coapplicative f => ACotraversal f s t a b -> (f a -> b) -> f s -> t
cloneCotraversalVl = cotraverseOf
{-# INLINE cloneCotraversalVl #-}

---------------------------------------------------------------------
-- Cotraversal0 Constructors
---------------------------------------------------------------------

---------------------------------------------------------------------
-- Cotraversal0 Constructors
---------------------------------------------------------------------

-- | Obtain a 'Cotraversal0' from its CPS representation.
--
-- The construction uses @closed . right'@ (the dual of @second' . right'@
-- used by 'traversal0'). After @closed@, the profunctor type is
-- @p ((s -> t + a) -> t + a) ((s -> t + a) -> t + b)@. The right @dimap@
-- uses 'stabt' to reconstruct @t@, relying on the CPS guarantee that
-- when @sta s = Left t@, 'stabt' short-circuits without evaluating
-- the callback result (lazy evaluation).
--
-- @since 0.0.3
cotraversal0 :: (((s -> t + a) -> b) -> t) -> Cotraversal0 s t a b
cotraversal0 stabt =
  dimap (flip ($))
        (\stab -> stabt $ \sta -> case stab sta of
           Right b -> b
           Left  _ -> error "cotraversal0: impossible — CPS short-circuits on Left")
  . closed . right'
{-# INLINE cotraversal0 #-}

-- TODO S17.23: cotraversalVl0 and cxtraversalVl0
-- The VL-to-profunctor bridge for Coaffine (Closed + Choice) is
-- non-trivial. The extraction witness (forall c. f c -> c) needs
-- to be threaded through both closed and right' in a way that
-- preserves the functor parameter. Deferred to sprint 20 for
-- careful implementation and verification.

-- | Clone a 'Cotraversal0'.
--
-- @since 0.0.3
cloneCotraversal0 :: ACotraversal0 s t a b -> Cotraversal0 s t a b
cloneCotraversal0 o = withCotraversal0 o cotraversal0
{-# INLINE cloneCotraversal0 #-}

---------------------------------------------------------------------
-- Dual Traversal1 Constructors
---------------------------------------------------------------------

-- | Obtain a 'Cotraversal1' by embedding a continuation into a 'Distributive1' functor.
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
cotraversing1 sabt = corepresenting cotraverse1 . grate sabt

-- | Obtain a 'Cotraversal1' by embedding a reversed lens getter and setter into a 'Distributive1' functor.
--
-- @
--  'withLens' ('re' o) 'retraversing1' ≡ 'cotraversed1' . o
-- @
--
retraversing1 :: Distributive1 g => (b -> t) -> (b -> s -> a) -> Cotraversal1 (g s) (g t) a b
retraversing1 bt bsa = corepresenting cotraverse1 . (re $ lens bt bsa)

-- | Obtain a profunctor 'Cotraversal1' from a Van Laarhoven 'Cotraversal1'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @abst runIdentity ≡ runIdentity@
--
-- * @abst f . fmap (abst g) ≡ abst (f . fmap g . getCompose) . Compose@
--
-- The cotraversal1 laws can be restated in terms of 'cotraverseOf':
--
-- * @cotraverseOf o (f . runIdentity) ≡  fmap f . runIdentity@
--
-- * @cotraverseOf o f . fmap (cotraverseOf o g) == cotraverseOf o (f . fmap g . getCompose) . Compose@
--
-- See 'Data.Profunctor.Optic.Property'.
--
cotraversalVl1 :: (forall f. Coapply f => (f a -> b) -> f s -> t) -> Cotraversal1 s t a b
cotraversalVl1 abst = cotabulate . abst . cosieve

---------------------------------------------------------------------
-- Coindexed Traversal1 Constructors
---------------------------------------------------------------------

-- | Obtain a profunctor 'Cxtraversal1' from a Van Laarhoven 'Cxtraversal1'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @aibst (const . runIdentity) ≡ runIdentity@
--
-- * @(aibst $ const . f) . fmap (aibst $ const . g) ≡ aibst (const . f . fmap g . getCompose) . Compose@
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- @since 0.0.3
cxtraversalVl1 :: (forall f. Coapply f => (f a -> k -> b) -> k -> f s -> t) -> Cxtraversal1 k s t a b
cxtraversalVl1 f = cotraversalVl1 $ \akb fs k -> f akb k fs
{-# INLINE cxtraversalVl1 #-}

-- | Extract the Van Laarhoven function that characterizes a 'Cotraversal1'.
--
-- @since 0.0.3
cloneCotraversal1Vl :: Coapply f => ACotraversal1 f s t a b -> (f a -> b) -> f s -> t
cloneCotraversal1Vl = cotraverseOf
{-# INLINE cloneCotraversal1Vl #-}

---------------------------------------------------------------------
-- Optics
---------------------------------------------------------------------

-- | TODO: Document
--
traversed :: Traversable f => Traversal (f a) (f b) a b
traversed = traversalVl traverse
{-# INLINE traversed #-}

---------------------------------------------------------------------
-- Indexed Optics
---------------------------------------------------------------------

-- | TODO: Document
--
itraversedRep :: F.Representable f => Traversable f => Ixtraversal (F.Rep f) (f a) (f b) a b
itraversedRep = ixtraversalVl $ \f _k -> F.itraverseRep f
{-# INLINE itraversedRep #-}

-- | Traverse both parts of a 'Bitraversable' container with matching types.
--
-- >>> traverseOf bitraversed (pure . length) (Right "hello")
-- Right 5
-- >>> traverseOf bitraversed (pure . length) ("hello","world")
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
bitraversed = representing $ \f -> bitraverse f f
{-# INLINE bitraversed #-}

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

-- | Duplicate the results of a 'Traversal'.
--
-- >>> toListOf (bitraversed . duplicated) ("hello","world")
-- ["hello","hello","world","world"]
--
duplicated :: Traversal1 a b a b
duplicated p = pappend p p
{-# INLINE duplicated #-}

-- | Obtain a 'Traversal1'' by repeating the input forever.
--
-- @
-- 'repeat' ≡ 'toListOf' 'repeated'
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
repeated = representing $ \g a -> go g a where go g a = g a .> go g a
{-# INLINE repeated #-}

-- | @x '^.' 'iterated' f@ returns an infinite 'Traversal1'' of repeated applications of @f@ to @x@.
--
-- @
-- 'toListOf' ('iterated' f) a ≡ 'iterate' f a
-- @
--
-- >>> take 3 $ (1 :: Int) ^.. iterated (+1)
-- [1,2,3]
--
iterated :: (a -> a) -> Traversal1' a a
iterated f = representing $ \g a0 -> go g a0 where go g a = g a .> go g (f a)
{-# INLINE iterated #-}

-- | Transform a 'Traversal1'' into a 'Traversal1'' that loops over its elements repeatedly.
--
-- >>> take 7 $ (1 :| [2,3]) ^.. cycling traversed1
-- [1,2,3,1,2,3,1]
--
cycling :: Apply f => ATraversal' f s a -> ATraversal' f s a
cycling o = representing $ \g a -> go g a where go g a = (traverseOf o g) a .> go g a
{-# INLINE cycling #-}

---------------------------------------------------------------------
-- Traversal1 Optics
---------------------------------------------------------------------

-- | Obtain a 'Traversal1' from a 'Traversable1' functor.
--
traversed1 :: Traversable1 t => Traversal1 (t a) (t b) a b
traversed1 = traversalVl1 traverse1
{-# INLINE traversed1 #-}

-- | Traverse both parts of a 'Bitraversable1' container with matching types.
--
-- >>> ('h' :| "ello", 'w' :| "orld") & bitraversed1 **~ pure . NE.length
-- (5,5)
--
bitraversed1 :: Bitraversable1 r => Traversal1 (r a a) (r b b) a b
bitraversed1 = representing $ \f -> bitraverse1 f f
{-# INLINE bitraversed1 #-}

-- | TODO: Document
--
-- @since 1.0.0
forked :: Traversal1 (a , a) (b , b) a b 
forked p = p *** p
{-# INLINE forked #-}

---------------------------------------------------------------------
-- Dual Optics
---------------------------------------------------------------------

-- | TODO: Document
--
cotraversed :: Distributive f => Cotraversal (f a) (f b) a b
cotraversed = cotraversalVl cotraverse
{-# INLINE cotraversed #-}

-- | TODO: Document
--
-- >>> cotraverseOf coforked (foldMap id) $ Left "foo" :| [Right "bar"]
-- Left "foo"
-- >>> cotraverseOf coforked (foldMap id) $ Right "foo" :| [Right "bar"]
-- Right "foobar"
--
-- @since 1.0.0
coforked :: Cotraversal1 (a + a) (b + b) a b
coforked p = p +++ p
{-# INLINE coforked #-}

---------------------------------------------------------------------
-- Dual Traversal1 Optics
---------------------------------------------------------------------

-- | TODO: Document
--
-- > 'cotraversed1' :: 'Cotraversal1' [a] [b] a b
--
cotraversed1 :: Distributive1 f => Cotraversal1 (f a) (f b) a b
cotraversed1 = cotraversalVl1 cotraverse1
{-# INLINE cotraversed1 #-}

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
matches o = withTraversal0 o $ \sta _ -> sta
{-# INLINE matches #-}

-- | Indexed 'matches'. Returns the index along with the matched value.
--
-- @since 0.0.3
ixmatches :: Monoid k => AIxtraversal0 k s t a b -> s -> t + (k, a)
ixmatches o s = case o (Traversal0Rep (\(_k, a) -> Right a) (\_ b -> b)) of
  Traversal0Rep sta _ -> fmap (mempty,) (sta (mempty, s))
{-# INLINE ixmatches #-}

-- | Traverse over a 'Traversal'.
--
-- /Benchmark: 0.89x vs direct fmap — GHC optimizes Star carrier well. See "Data.Profunctor.Optic.Bench"./
--
traverseOf :: ATraversal f s t a b -> (a -> f b) -> s -> f t
traverseOf o = runStar #. o .# Star
{-# INLINE traverseOf #-}

-- | Traverse over an 'Ixtraversal'.
--
-- @
-- 'ixtraverseOf' o f = 'curry' ('traverseOf' o '$' 'uncurry' f) 'mempty'
-- @
--
-- @since 0.0.3
ixtraverseOf :: Monoid k => AIxtraversal f k s t a b -> (k -> a -> f b) -> s -> f t
ixtraverseOf o f = curry (traverseOf o $ uncurry f) mempty
{-# INLINE ixtraverseOf #-}

-- | TODO: Document
--
sequenceOf :: Applicative f => ATraversal f s t (f a) a -> s -> f t
sequenceOf o = traverseOf o id
{-# INLINE sequenceOf #-}

-- | Indexed 'sequenceOf'.
--
-- @since 0.0.3
ixsequenceOf :: Monoid k => Applicative f => AIxtraversal f k s t (f a) a -> s -> f t
ixsequenceOf o = ixtraverseOf o (const id)
{-# INLINE ixsequenceOf #-}

-- | This allows you to 'Control.Traversable.traverse' the elements of a 'Traversing' or 'Traversing1' optic in the opposite order.
--
-- This will preserve indexes on 'Indexed' types and for example will give you the elements of a (finite) 'Fold' or 'Traversal' in the opposite order.
--
-- This has no practical effect on a 'View', 'Setter', 'Lens' or 'Iso'.
--
-- @since 0.0.3
reverseOf :: ATraversal (Backwards f) s t a b -> (a -> f b) -> s -> f t
reverseOf o = (forwards #.) #. traverseOf o .# (Backwards #.)
{-# INLINE reverseOf #-}

-- | Generalize 'Data.Traversable.mapAccumL' to a 'Traversing' or 'Traversing1' optic.
--
-- @
-- 'mapAccumL' ≡ 'mapAccumLOf' 'traverse'
-- @
--
-- 'mapAccumLOf' accumulates 'State' from left to right.
--
-- @since 0.0.3
mapAccumLOf :: ATraversal (State r) s t a b -> (r -> a -> (r, b)) -> r -> s -> (r, t)
mapAccumLOf o f acc0 s = swap (runState (traverseOf o g s) acc0) where
   g a = state $ \acc -> swap (f acc a)

-- | Generalize 'Data.Traversable.mapAccumR' to a 'Traversing' or 'Traversing1' optic.
--
-- @
-- 'mapAccumR' ≡ 'mapAccumROf' 'traverse'
-- @
--
-- 'mapAccumROf' accumulates 'State' from right to left.
--
-- @since 0.0.3
mapAccumROf :: ATraversal (Backwards (State r)) s t a b -> (r -> a -> (r, b)) -> r -> s -> (r, t)
mapAccumROf = mapAccumLOf . reversing
{-# INLINE mapAccumROf #-}

-- | Indexed 'mapAccumLOf'. Accumulates state from left to right,
-- threading the index.
--
-- @since 0.0.3
ixmapAccumLOf :: Monoid k => AIxtraversal (State r) k s t a b -> (k -> r -> a -> (r, b)) -> r -> s -> (r, t)
ixmapAccumLOf o f acc0 s = swap (runState (ixtraverseOf o g s) acc0) where
  g k a = state $ \acc -> swap (f k acc a)

-- | Indexed 'mapAccumROf'. Accumulates state from right to left,
-- threading the index.
--
-- @since 0.0.3
ixmapAccumROf :: Monoid k => AIxtraversal (Backwards (State r)) k s t a b -> (k -> r -> a -> (r, b)) -> r -> s -> (r, t)
ixmapAccumROf o f acc0 s = swap (runState (forwards (ixtraverseOf o g s)) acc0) where
  g k a = Backwards . state $ \acc -> swap (f k acc a)

-- | Scan left over a 'Traversing' or 'Traversing1' optic.
--
-- @
-- 'scanl1' ≡ 'scanl1Of' 'traverse'
-- @
--
-- @since 0.0.3
scanl1Of :: ATraversal (State (Maybe a)) s t a a -> (a -> a -> a) -> s -> t
scanl1Of o f = snd . mapAccumLOf o step Nothing where
  step Nothing a  = (Just a, a)
  step (Just s) a = (Just r, r) where r = f s a
{-# INLINE scanl1Of #-}

-- | Scan left over a 'Traversing' or 'Traversing1' optic.
--
-- @
-- 'scanr1' ≡ 'scanr1Of' 'traverse'
-- @
--
-- @since 0.0.3
scanr1Of :: ATraversal (Backwards (State (Maybe a))) s t a a -> (a -> a -> a) -> s -> t
scanr1Of o f = snd . mapAccumROf o step Nothing where
  step Nothing a  = (Just a, a)
  step (Just s) a = (Just r, r) where r = f a s
{-# INLINE scanr1Of #-}

-- | Cotraverse over a 'Cotraversal'.
--
cotraverseOf :: ACotraversal f s t a b -> (f a -> b) -> (f s -> t)
cotraverseOf o = runCostar #. o .# Costar
{-# INLINE cotraverseOf #-}

-- | Cotraverse over a 'Cxtraversal'.
--
-- @
-- 'cxtraverseOf' o f = 'flip' ('cotraverseOf' o '$' 'flip' f) 'mempty'
-- @
--
-- @since 0.0.3
cxtraverseOf :: Monoid k => ACxtraversal f k s t a b -> (k -> f a -> b) -> f s -> t
cxtraverseOf o f = flip (cotraverseOf o $ flip f) mempty
{-# INLINE cxtraverseOf #-}

-- | TODO: Document
--
-- >>> collectOf cotraversed1 ["xxx","ooo"]
-- ["xo","xo","xo"]
-- >>> collectOf left' (1, Left "foo") :: Either (Int8, String) String
-- Left (1,"foo")
-- >>> collectOf left' (1, Right "foo")
-- Right "foo"
--
collectOf :: Coapply f => ACotraversal f s t a (f a) -> f s -> t
collectOf o = cotraverseOf o id
{-# INLINE collectOf #-}

-- | Coindexed 'collectOf'.
--
-- @since 0.0.3
cxcollectOf :: Monoid k => Coapply f => ACxtraversal f k s t a (f a) -> f s -> t
cxcollectOf o = cxtraverseOf o (const id)
{-# INLINE cxcollectOf #-}
