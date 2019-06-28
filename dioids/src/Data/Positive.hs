{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
module Data.Positive where

import Data.Semiring
import Data.Dioid
import Data.Typeable (Typeable)
import Data.Validity
import Data.Validity.Map
import Data.GenValidity
import Data.GenValidity.Map
import GHC.Generics (Generic, Generic1)

import P
import Orphans ()

import           Data.Data (Data, cast)
import qualified Data.Text as T

import           Language.Haskell.TH.Syntax (Q, Exp(..), lift, liftData, dataToExpQ)
import           Language.Haskell.TH.Quote (QuasiQuoter (..))



-- | Newtype representing a non-negative real number. 
--
-- Morally equivalent to 'Maybe Positive'.
newtype NonNegative a = NonNegative { unNonNegative :: a }
  deriving Num via (N (NonNegative a))
  deriving (Eq, Ord, Show, Data, Generic, GenUnchecked, GenValid, Typeable, Validity)

instance Num a => Semigroup (NonNegative a) where
  NonNegative a <> NonNegative b  = NonNegative $ a + b


instance Num a => Monoid (NonNegative a) where
  mempty = NonNegative 0


instance Num a => Semiring (NonNegative a) where
  NonNegative a >< NonNegative b  = NonNegative $ a * b
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ NonNegative 1


instance (Ord a, Num a) => Dioid (NonNegative a) where
  NonNegative a <~ NonNegative b = a <= b

nonNegative :: (Ord a, Num a) => a -> Maybe (NonNegative a)
nonNegative = bool Nothing <$> Just . NonNegative <*> (0 <=)


-- | A quasiquoter for safely constructing a 'NonNegative Float' from a constant.
--
-- >>> [nnf|1.0|]
-- NonNegative {unNonNegative = 1.0}
nnf :: QuasiQuoter
nnf = let
    msg = "Invalid non-negative (must be >= 0)"
    mk s = readMaybe @Float s >>= nonNegative
    in qq $ justErr msg . mk

-- | A quasiquoter for safely constructing a 'NonNegative Double' from a constant.
--
-- >>> [nnd|1.0|]
-- NonNegative {unNonNegative = 1.0}
nnd :: QuasiQuoter
nnd = let
    msg = "Invalid non-negative (must be >= 0)"
    mk s = readMaybe @Double s >>= nonNegative
    in qq $ justErr msg . mk

-- ----------------------------------------------------------------------------

-- | Newtype representing a strictly positive number.
newtype Positive a = Positive { unPositive :: a } 
  deriving (Eq, Ord, Show, Data, Generic, GenUnchecked, GenValid, Typeable, Validity)


instance Num a => Semigroup (Positive a) where
  Positive a <> Positive b  = Positive $ a + b


instance Num a => Semiring (Positive a) where
  Positive a >< Positive b  = Positive $ a * b
  {-# INLINE (><) #-}


instance (Ord a, Num a) => Dioid (Positive a) where
  Positive a <~ Positive b = a <= b


positive :: (Ord a, Num a) => a -> Maybe (Positive a)
positive = bool Nothing <$> Just . Positive <*> (0 <)

-- | A quasiquoter for safely constructing a 'Positive Float' from a constant.
--
-- >>> [pf|1.0|]
-- Positive {unPositive = 1.0}
pf :: QuasiQuoter
pf = let
    msg = "Invalid positive (must be > 0)"
    mk s = readMaybe @Float s >>= positive
    in qq $ justErr msg . mk


-- | A quasiquoter for safely constructing a 'Positive Double' from a constant.
--
-- >>> [pd|1.0|]
-- Positive {unPositive = 1.0}
pd :: QuasiQuoter
pd = let
    msg = "Invalid positive (must be >= 0)"
    mk s = readMaybe @Double s >>= positive
    in qq $ justErr msg . mk

-- | A quasiquoter for safely constructing a 'Positive Natural' from a constant.
--
-- >>> [pn|1.0|]
-- Positive {unPositive = 1.0}
pn :: QuasiQuoter
pn = let
    msg = "Invalid positive (must be >= 0)"
    mk s = readMaybe @Natural s >>= positive
    in qq $ justErr msg . mk

-------------------------------------------------------------------------------
-- 'Unit'
-------------------------------------------------------------------------------


-- | The unit interval dioid.
newtype Unit a = Unit { unUnit :: a }
  deriving (Eq, Ord, Show, Data, Generic, GenUnchecked, GenValid, Typeable, Validity)

instance Num a => Bounded (Unit a) where
  minBound = Unit 0
  maxBound = Unit 1

instance Ord a => Semigroup (Unit a) where
  Unit a <> Unit b  = Unit $ max a b


instance (Ord a, Num a) => Monoid (Unit a) where
  mempty = Unit 0


instance (Ord a, Num a) => Semiring (Unit a) where
  Unit a >< Unit b  = Unit $ a * b
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ Unit 1

instance (Ord a, Num a) => Dioid (Unit a) where
  Unit a <~ Unit b = a <= b


instance (Ord a, Num a) => Closed (Unit a) where
  star _ = one
  plus = id

inRange :: Ord a => a -> a -> a -> Bool
inRange low high = (&&) <$> (low <=) <*> (<= high)

unit :: (Ord a, Num a) => a -> Maybe (Unit a)
unit = bool Nothing <$> (Just . Unit) <*> inRange 0 1


-- | A quasiquoter for safely constructing a 'Unit Float' from a constant.
--
-- >>> [uf|1.0|]
-- Unit {unUnit = 1.0}
uf :: QuasiQuoter
uf = let
    msg = "Invalid unit (must be in [0,1])"
    mk s = readMaybe @Float s >>= unit
    in qq $ justErr msg . mk

-- | A quasiquoter for safely constructing a 'Unit Double' from a constant.
--
-- >>> [ud|1.0|]
-- Unit {unUnit = 1.0}
ud :: QuasiQuoter
ud = let
    msg = "Invalid unit (must be in [0,1])"
    mk s = readMaybe @Double s >>= unit
    in qq $ justErr msg . mk


-- | Safe `Unit` complement
complement :: Num a => Unit a -> Unit a
complement (Unit a) = Unit $ 1 - a

-- | Safe `Unit` division
--div' :: Unit a -> Positive Natural -> Unit a
--div' (Unit n) (Positive d) = Unit $ n / fromIntegral d

-------------------------------------------------------------------------------
-- Internal
-------------------------------------------------------------------------------

qq :: Data a => ([Char] -> Either [Char] a) -> QuasiQuoter
qq = qqLift liftData

-- Necessary when `Text` is involved, https://stackoverflow.com/q/38143464
qqText :: Data a => ([Char] -> Either [Char] a) -> QuasiQuoter
qqText = qqLift liftDataWithText
  where
    liftText :: T.Text -> Q Exp
    liftText = fmap (AppE $ VarE 'T.pack) . lift . T.unpack

    liftDataWithText :: Data a => a -> Q Exp
    liftDataWithText = dataToExpQ (fmap liftText . cast)

qqLift :: (a -> Q Exp) -> ([Char] -> Either [Char] a) -> QuasiQuoter
qqLift l f = QuasiQuoter {
    quoteExp = either fail l . f
  , quotePat = no "patterns"
  , quoteType = no "types"
  , quoteDec = no "declarations"
  }
  where no c = const (fail ("This QQ produces expressions, not " <> c))

