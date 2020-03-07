{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Cotraversal (
    -- * Cotraversal
    Cotraversal
  , Cotraversal'
  , cotraversing
  , retraversing
  , cotraversalVl
    -- * Cotraversal1
  , Cotraversal1
  , Cotraversal1'
  , cotraversing1
  , retraversing1
  , cotraversal1Vl
  , (++++)
  , (||||)
  , codivide
  , codivide'
  , choose
  , choose'
    -- * Optics
  , cotraversed
  , cotraversed1
  , coboth
  , coboth1
    -- * Operators
  , cotraverses
  , cotraverses1
  , collects 
  , collects1
    -- * Classes
  , Choice(..)
  , Closed(..)
  , Corepresentable(..)
) where

import Data.Function
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Grate
import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.Import hiding (id,(.))
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Combinator

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XFlexibleContexts
-- >>> :set -XTypeApplications
-- >>> :set -XTupleSections
-- >>> :set -XRankNTypes
-- >>> import Data.Int
-- >>> import Data.String
-- >>> import Data.List.NonEmpty (NonEmpty(..))
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- Cotraversal0
---------------------------------------------------------------------

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
-- * @abst copure ≡ copure@
--
-- * @abst f . fmap (abst g) ≡ abst (f . fmap g . getCompose) . Compose@
--
-- The cotraversal laws can be restated in terms of 'withCostar':
--
-- * @withCostar o (f . copure) ≡  fmap f . copure@
--
-- * @withCostar o f . fmap (withCostar o g) == withCostar o (f . fmap g . getCompose) . Compose@
--
-- See 'Data.Profunctor.Optic.Property'.
--
cotraversalVl :: (forall f. Coapplicative f => (f a -> b) -> f s -> t) -> Cotraversal s t a b
cotraversalVl abst = cotabulate . abst . cosieve 

---------------------------------------------------------------------
-- 'Cotraversal1'
---------------------------------------------------------------------

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
cotraversing1 sabt = corepn cotraverse1 . grate sabt

-- | Obtain a 'Cotraversal1' by embedding a reversed lens getter and setter into a 'Distributive1' functor.
--
-- @
--  'withLens' ('re' o) 'cotraversing' ≡ 'cotraversed' . o
-- @
--
retraversing1 :: Distributive1 g => (b -> t) -> (b -> s -> a) -> Cotraversal1 (g s) (g t) a b
retraversing1 bsa bt = corepn cotraverse1 . (re $ lens bsa bt)

-- | Obtain a profunctor 'Cotraversal1' from a Van Laarhoven 'Cotraversal1'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @abst runIdentity ≡ runIdentity@
--
-- * @abst f . fmap (abst g) ≡ abst (f . fmap g . getCompose) . Compose@
--
-- The cotraversal1 laws can be restated in terms of 'withCostar':
--
-- * @withCostar o (f . runIdentity) ≡  fmap f . runIdentity@
--
-- * @withCostar o f . fmap (withCostar o g) == withCostar o (f . fmap g . getCompose) . Compose@
--
-- See 'Data.Profunctor.Optic.Property'.
--
cotraversal1Vl :: (forall f. Coapply f => (f a -> b) -> f s -> t) -> Cotraversal1 s t a b
cotraversal1Vl abst = cotabulate . abst . cosieve 

---------------------------------------------------------------------
-- Optics
---------------------------------------------------------------------

-- | TODO: Document
--
cotraversed :: Distributive f => Cotraversal (f a) (f b) a b 
cotraversed = cotraversalVl cotraverse
{-# INLINE cotraversed #-}

-- | TODO: Document
--
cotraversed1 :: Distributive1 f => Cotraversal1 (f a) (f b) a b 
cotraversed1 = cotraversal1Vl cotraverse1
{-# INLINE cotraversed1 #-}

-- | TODO: Document
--
coboth :: Cotraversal (a + a) (b + b) a b
coboth p = p ++++ p
{-# INLINE coboth #-}

-- | TODO: Document
--
-- >>> cotraverses1 coboth1 (foldMap id) $ Left "foo" :| [Right "bar"]
-- Left "foo"
-- >>> cotraverses1 coboth1 (foldMap id) $ Right "foo" :| [Right "bar"]
-- Right "foobar"
-- 
coboth1 :: Cotraversal1 (a + a) (b + b) a b
coboth1 p = p ++++ p
{-# INLINE coboth1 #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | TODO: Document
--
cotraverses :: Coapplicative f => ACotraversal f s t a b -> (f a -> b) -> f s -> t 
cotraverses = withCostar
{-# INLINE cotraverses #-}

-- | TODO: Document
--
cotraverses1 :: Coapply f => ACotraversal1 f s t a b -> (f a -> b) -> f s -> t
cotraverses1 = withCostar
{-# INLINE cotraverses1 #-}

-- | TODO: Document
--
-- >>> collects left' (1, Left "foo") :: Either (Int8, String) String
-- Left (1,"foo")
-- >>> collects left' (1, Right "foo")
-- Right "foo"
--
collects :: Coapplicative f => ACotraversal f s t a (f a) -> f s -> t
collects o = cotraverses o id
{-# INLINE collects #-}

-- | TODO: Document
--
-- >>> collects1 cotraversed1 ["xxx","ooo"] :: [String]
-- ["xo","xo","xo"]
--
collects1 :: Coapply f => ACotraversal1 f s t a (f a) -> f s -> t
collects1 o = cotraverses1 o id
{-# INLINE collects1 #-}


