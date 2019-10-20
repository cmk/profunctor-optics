{-# LANGUAGE UndecidableInstances, UndecidableSuperClasses, TypeOperators , GADTs, DataKinds, KindSignatures, TypeFamilies #-}

{-# LANGUAGE ExistentialQuantification #-}

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE QuantifiedConstraints #-}
-- {-# LANGUAGE IncoherentInstances #-}
-- {-# LANGUAGE OverlappingInstances #-}


module Data.Profunctor.Optic.Type (
    module Data.Profunctor.Optic.Type
  , module VL
  , module Export
) where

import Data.Semigroup (First, Last)
import Data.Profunctor.Optic.Prelude

import qualified Data.Profunctor.Optic.Type.VL as VL
import           Control.Applicative
import           Control.Monad
import           Control.Monad.Fix
import           Data.Bifoldable
import Data.Bifunctor as Export (Bifunctor (..))
import           Data.Bitraversable
import           Data.Coerce
import           Data.Data
import           Data.Distributive
import Data.Functor.Classes
import Data.Functor.Apply (Apply(..))

import GHC.Generics (Generic)
import Data.Int
import Data.Word
import Linear.V2
import Linear.V3
import Linear.V4
import Pipes
import qualified Pipes.Prelude as Pipes

import Data.Functor.Base (NonEmptyF(..))
import Data.Traversable

-- * 'Optic'

--type Optic p s t a b = Profunctor p => p a b -> p s t
--type Optical p s t a b = p a b -> p s t

type Optic p s t a b = p a b -> p s t

type Optic' p s a = Optic p s s a a

-- * 'Iso'

type Equality s t a b = forall p. Optic p s t a b 

type Equality' s a = Equality s s a a

type Iso s t a b = forall p. Profunctor p => Optic p s t a b

type Iso' s a = Iso s s a a

-- * 'Over/Under'

type Over p s t a b = Representable p => Optic p s t a b

type Over' p s a = Representable p => Optic p s s a a

type Under p s t a b = Corepresentable p => Optic p s t a b

type Under' p s a = Under p s s a a

-- * 'Lens'

--type LensPrim p c a b = Optic p (c , a) (c , b) a b

type LensLike p s t a b = Strong p => Optic p s t a b

type LensLike' p s a = LensLike p s s a a

type Lens s t a b = forall p. LensLike p s t a b

type Lens' s a = Lens s s a a

type ColensLike p s t a b = Costrong p => Optic p s t a b

type Colens s t a b = forall p. ColensLike p s t a b

type Colens' s a = Colens s s a a

-- * 'Prism'

type PrismLike p s t a b = Choice p => Optic p s t a b

type Prism s t a b = forall p. PrismLike p s t a b

type Prism' s a = Prism s s a a

type CoprismLike p s t a b = Cochoice p => Optic p s t a b

type Coprism s t a b = forall p. CoprismLike p s t a b

type Coprism' s a = Coprism s s a a

-- * 'Grate'

type GrateLike p s t a b = Closed p => Optic p s t a b

type GrateLike' p s a = GrateLike p s s a a

type Grate s t a b = forall p. GrateLike p s t a b

type Grate' s a = Grate s s a a

-- * 'Grid'

type GridLike p s t a b = Closed p => LensLike p s t a b

-- | \( \quad \mathsf{Grid}\;S\;A = \exists C,I, S \cong C \times (I \to A) \)
type Grid s t a b = forall p. GridLike p s t a b

-- * 'Glass'

type GlassLike p s t a b = Closed p => PrismLike p s t a b

-- | \( \quad \mathsf{Glass}\;S\;A = \exists D,I, S \cong D + (I \to A) \)
type Glass s t a b = forall p. GlassLike p s t a b
{- 
FreeGrid:
∃ c,d .  (s -> (c × (d -> a))) × (c × (d -> b) -> t)  ≅
∃ c,d .  (s -> c) × (s -> (d -> a)) × (c × (d -> b) -> t)  ≅
∃ d   .  (s -> (d -> a)) × (s × (d -> b) -> t)  ≅
∃ d   .  (d -> (s -> a)) × (s × (d -> b) -> t)  ≅
(s × ((s -> a) -> b) -> t)  ≅
((s -> a) -> b) -> s -> t

FreeGlass:
∃ c,d .  (s -> (c + (d -> a))) × (c + (d -> b) -> t)  ≅
(s + ((s -> a) -> b) -> t)  ≅


right' . closed
  :: (Choice p, Closed p) =>
     p a b -> p (Either c (x -> a)) (Either c (x -> b))


\begin{aligned} 
\quad \mathsf{Iso}\;S\;A  =&&  S &\cong A  \\   \quad 
\mathsf{Lens}\;S\;A    =&& \exists C, S &\cong C \times A \\   
\quad \mathsf{Prism}\;S\;A   =&& \exists D, S &\cong D + A \\   
\quad \mathsf{Affine}\;S\;A  =&& \exists C, D, S &\cong D + C \times A \\   
\quad \mathsf{Grate}\;S\;A   =&& \exists I, S &\cong I \to A \\   
\quad \mathsf{Achroma}\;S\;A =&& \exists C, S &\cong 1 + C \times A 
\quad \mathsf{Setter}\;S\;A =&& \exists F : \mathsf{Functor}, S \equiv F\,A

\end{aligned}

Hopefully the pattern stands out, namely S is isomorphic to F\,A for some endofunctor F:




-}


-- * 'Traversal0' extracts at most one result, with no monoidal interactions.

type Traversal0Like p s t a b = Choice p => LensLike p s t a b

type Traversal0 s t a b = forall p. Traversal0Like p s t a b

type Traversal0' s a = Traversal0 s s a a

-- * 'Traversal' extracts 0 or more results, with monoidal interactions.

type TraversalLike p s t a b = (forall x. Applicative (p x)) => Traversal0Like p s t a b

--type Traversal s t a b = forall p. Applicative (Rep p) => Over p s t a b
type Traversal s t a b = forall p. TraversalLike p s t a b

type ATraversal f s t a b = Applicative f => Optic (Star f) s t a b

type Traversal' s a = Traversal s s a a

-- * A 'Traversal1' extracts 1 or more results, with monoidal interactions.

--type Traversal1 s t a b = forall p. Apply (Rep p) => Over p s t a b
type Traversal1Like p s t a b = (forall x. Apply (p x)) => Traversal0Like p s t a b

type Traversal1 s t a b = forall p. Traversal1Like p s t a b

type Traversal1' s a = Traversal1 s s a a


-- * 'Cotraversal' 

--(forall x. Coapplicative (p x))
type CotraversalLike p s t a b = (forall x. Distributive (p x)) => GridLike p s t a b

--type Cotraversal s t a b = forall p. Distributive (Corep p) => Under p s t a b
type Cotraversal s t a b = forall p. CotraversalLike p s t a b

-- * A 'Fold0' extracts at most one result.

--type FoldRep0 r = Star ?

type Fold0Like p s a = (forall x. Contravariant (p x)) => Traversal0Like p s s a a

type Fold0 s a = forall p. Fold0Like p s a

-- * A 'Fold1' extracts a semigroupal summary from a non-empty container

type AFold1 r s a = Semigroup r => Optic' (FoldRep r) s a

--type Fold1 s a = forall p. Apply (Rep p) => Contravariant (Rep p) => Over' p s a
type Fold1 s a = forall p. (forall x. Contravariant (p x)) => Traversal1Like p s s a a 


-- * A 'Fold' extracts a monoidal summary from a container.

type FoldRep r = Star (Const r)

type AFold r s a = Monoid r => Optic' (FoldRep r) s a

--type Fold s a = forall p. Applicative (Rep p) => Contravariant (Rep p) => Over' p s a
type Fold s a = forall p. (forall x. Contravariant (p x)) => TraversalLike p s s a a



-- * A 'Unfold'

type UnfoldRep r = Costar (Const r)

type AUnfold r t b = Optic' (UnfoldRep r) t b

--type Unfold t b = forall p. Distributive (Corep p) => Contravariant (Corep p) => Under' p t b
type Unfold t b = forall p. Bifunctor p => CotraversalLike p t t b b

--

-- * A 'Getter' extracts exactly one result.

--type PrimGetter s t a b = forall p. Contravariant (Rep p) => Over p s t a b
type PrimGetter s t a b = forall p. Profunctor p => (forall x. Contravariant (p x)) => Optic p s t a b

type AGetter s a = Optic' (FoldRep a) s a

--type Getter s a = forall p. Contravariant (Rep p) => Over' p s a
type Getter s a = forall p. (forall x. Contravariant (p x)) => LensLike p s s a a


-- * A 'Review' produces a result.

type PrimReviewLike p s t a b = Profunctor p => Bifunctor p => Optic p s t a b 

--type PrimReview s t a b = forall p. Contravariant (Corep p) => Under p s t a b
type PrimReview s t a b = forall p. PrimReviewLike p s t a b

--type AReview t b = forall r. AUnfold r t b
type AReview t b = Optic' (UnfoldRep b) t b

--type Review t b = forall p. Contravariant (Corep p) => Under' p t b
type Review t b = forall p. Bifunctor p => PrismLike p t t b b


-- * Setter
-- type Setter s t a b = Closed p => Strong p => Choice p => (forall x. Applicative (p x)) => (forall x. Distributive (p x)) => Optic p s t a b
type Setter s t a b = forall p. Distributive (Rep p) => Over p s t a b

type Setter' s a = Setter s s a a

type AMatch e s t a b = Optic (Star (Either e)) s t a b

type ASetter s t a b = Optic (Star Identity) s t a b

type AResetter s t a b = Optic (Costar Identity) s t a b

overLike :: ((a -> b) -> s -> t) -> ASetter s t a b
overLike sec = between Star runStar $ \f -> Identity . sec (runIdentity . f)

-- | TODO: Document
--
underLike :: ((a -> b) -> s -> t) -> AResetter s t a b
underLike sec = between Costar runCostar $ \f -> sec (f . Identity) . runIdentity

-- | TODO: Document
--
cloneOver :: Optic (Star (Rep p)) s t a b -> Over p s t a b
cloneOver = between fromStar star 

-- | TODO: Document
--
cloneUnder :: Optic (Costar (Corep p)) s t a b -> Under p s t a b
cloneUnder = between fromCostar costar 

closed' :: Under p (c -> a) (c -> b) a b
closed' = lower cotraverse

class Profunctor p => Pointing p where
  point :: p a b -> p (Maybe a) (Maybe b)


-- Using the free applicative construction from Capriotti-Kaposi, we can show their concrete representation is the following.
-- aka kaleidoscope == resetter?
-- (Vector n a -> b) -> (Vector n s -> t)
--type LaxLike f s t a b = Distributive f => GrateLike f s t a b

--List-lenses (unlike general lenses) compose with Kaleidoscopes
--type ListLens (view :: s -> a, classify :: Distributive f => f s -> b -> t)



type SLens s t a b = forall p. Strong p => PSemigroup (,) p => Optic p s t a b
type SLens' s a = SLens s s a a
--v2 :: Semigroupal p => Optic p (V2 a) (V2 b) a b
v2 :: SLens (V2 a) (V2 b) a b
v2 p = dimap (\(V2 x y) -> (x, y)) (\(x, y) -> V2 x y) (p *** p)

-- >>>  contents skipLast (1,2,3)
-- [1,2]
skipLast :: SLens (a, a, c) (b, b, c) a b
skipLast p = dimap group ungroup (first' (p *** p)) where
  group  (x, y, z) = ((x, y), z)
  ungroup ((x, y), z) = (x, y, z)

skipLast' :: SLens' (V3 a) a
skipLast' p = dimap group ungroup (first' (p *** p)) where
  group  (V3 x y z) = ((x, y), z)
  ungroup ((x, y), z) = V3 x y z


v4 :: SLens (V4 a) (V4 b) a b
v4 p = dimap (\(V4 x y z w) -> (x, (y, (z, w)))) (\(x, (y, (z, w))) -> V4 x y z w) (p *** p *** p *** p)


{-λ> review (v2 . right' . _V2) 1 :: V2 (Either Bool (V2 Int))
V2 (Right (V2 1 1)) (Right (V2 1 1))
and zipWithOf:

λ> let as = V2 (Left ())     (Right (1,2))
λ> let bs = V2 (Right (3,4)) (Right (5,6))
λ> zipWithOf (v2 . right' . first') (,) as bs
V2 (Left ()) (Right ((1,5),2))
But also traverseOf:

λ> let f x = state (\s -> (x + s, s +1))
λ> evalState (traverseOf v2 f (V2 5 7)) 1
V2 6 9
and toListOf:

λ> toListOf (v2 . v2) (V2 (V2 1 2) (V2 3 4))
[1,2,3,4]

-}


--v4' :: Grate (V4 a) (V4 b) a b
--v4' = grate $ \f -> cotraverse f id

--v4'' :: Cotraversal (V4 a) (V4 b) a b
--v4'' = cotraversed

type Motors = V4

-- factor out common substructures where possible
data Controller a b
  = Controller
    { cMeta :: a
    , cMotors :: Motors b
    } deriving Generic

data GainsMeta
  = GainsMeta
    { kValue :: Double
    , kCount :: V4 Word8
    } deriving Generic

type ControlGains = Controller GainsMeta MotorGains

type ControlState = Controller Double MotorState

type ControlOutputs = Controller Double MotorOutputs

type ControlMessage = Controller Bool MotorMessage

data ControllerGains
  = ControllerGains
    { kMotors :: Motors MotorGains
    , kSomething :: Double
    , kWat :: V4 Word8
    } deriving Generic

data ControllerOutputs
  = ControllerOutputs
    { oMotors :: Motors MotorOutputs
    , oSomething :: Double
    } deriving Generic

data ControllerState
  = ControllerState
    { sMotors :: Motors MotorState
    , sSomething :: Double
    } deriving Generic

data Sensors
  = Sensors
    { yMotors :: Motors MotorMessage
    , yDiskLoggingFull :: Bool
    } deriving Generic

-- motor subsystem
data MotorGains
  = MotorGains
    { kA :: Int64
    , kB :: Double
    } deriving Generic

data MotorState
  = MotorState
    { sA :: Double
    , sB :: Int64
    } deriving Generic

data MotorMessage
  = MotorMessage
    { yA :: Double
    , yB :: Int64
    } deriving Generic

data MotorOutputs
  = MotorOutputs
    { oA :: Double
    , oB :: Int64
    } deriving Generic


flightController
  :: ControllerGains -> ControllerState -> Sensors -> (ControllerState, ControllerOutputs)
flightController gains oldState messages = (newState, outputs)
 where
  outputs =
    ControllerOutputs { oMotors = motorOutputs, oSomething = maximum (oA <$> motorOutputs) }

  newState = ControllerState
    { sMotors    = motorNewState
    , sSomething = if abs (sSomething oldState) > 22
      then 2 * sSomething oldState
      else sSomething oldState / 3
    }

  motorOutputs :: Motors MotorOutputs
  motorOutputs = fmap snd motorNewStateAndOutputs

  motorNewState :: Motors MotorState
  motorNewState = fmap fst motorNewStateAndOutputs

  motorNewStateAndOutputs :: Motors (MotorState, MotorOutputs)
  motorNewStateAndOutputs = motorFilter <$> kMotors gains <*> sMotors oldState <*> yMotors messages


-- TODO: use the one from GHC but not necessarily fromIntegral.
intToDouble :: Int64 -> Double
intToDouble = undefined

arctan2 = (+)
-- ∃ c,d .  (s -> (c × (d -> a))) × (c × (d -> b) -> t) 

motorFilter :: MotorGains -> MotorState -> MotorMessage -> (MotorState, MotorOutputs)
motorFilter gains oldState msg = (newState, outputs)
 where
  newState = MotorState
    { sA = 0.2 * sA oldState + intToDouble (sB oldState) + yA msg
    , sB = if sB oldState == 22 then 0 else 1 + sB oldState
    }

  outputs = MotorOutputs { oA = arctan2 (sA oldState) (sA newState), oB = 32 `div` kA gains }



{-



toLensLike :: AdapterLike f Identity s t a b -> LensLike f s t a b
toLensLike o h = lower' o h runIdentity Identity -- l f = l (f . runIdentity) . Identity 

toGrateLike :: AdapterLike Identity g s t a b -> GrateLike g s t a b
toGrateLike o h = colower o h runIdentity Identity

lift :: LensLike f s t a b -> AdapterLike f Identity s t a b
lift l f = l (f . Identity) . runIdentity
-}



---------------------------------------------------------------------
-- 'Re'
---------------------------------------------------------------------


--The 'Re' type, and its instances witness the symmetry of 'Profunctor' 

newtype Re p s t a b = Re { runRe :: p b a -> p t s }

instance Profunctor p => Profunctor (Re p s t) where
    dimap f g (Re p) = Re (p . dimap g f)

instance Cochoice p => Choice (Re p s t) where
    right' (Re p) = Re (p . unright)

instance Costrong p => Strong (Re p s t) where
    first' (Re p) = Re (p . unfirst)

instance Choice p => Cochoice (Re p s t) where
    unright (Re p) = Re (p . right')

instance Strong p => Costrong (Re p s t) where
    unfirst (Re p) = Re (p . first')
