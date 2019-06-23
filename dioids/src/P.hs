{-# LANGUAGE CPP #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
module P (

  -- * Primitive types
  -- ** Unit
   -- ()

  -- ** Bool
    Bool (..), bool
  , (&&), (||), not
  , (==>), implies
  , xor, xnor
  , otherwise

  -- ** Char
  , Char

  -- ** Natural
  , Natural
  , Word8, Word16, Word32, Word64

  -- ** Integer
  , Integer
  , Int, Int8, Int16, Int32, Int64

  -- ** Rational
  , Ratio, Rational
  , numerator, denominator

  -- ** Real
  , Floating, Double
  , fromIntegral
  , fromRational
  , realToFrac
  , div
  , floor, ceiling

  -- * Combinators
  , id, (.), ($), ($!), (&)
  , (***), (&&&), (+++), (|||)
  , const, flip
  , on, onr
  , fix
  , seq

  -- * Data structures
  -- ** Tuple
  , fst, snd
  , curry, uncurry
  , dup, eval

  -- ** Maybe
  , Maybe (..)
  , fromMaybe
  , maybe
  , liftMay

  -- ** Either
  , Either (..)
  , either
  , note
  , dedup
  , module ErrorS

  -- * Typeclasses
  -- ** Eq
  , Eq (..)

  -- ** Ord
  , Ord (..)
  , Ordering (..)
  , comparing

  -- ** Bounded
  , Bounded (..)

  -- ** Semigroup
  , Semigroup (..)

  -- ** Monoid
  , Monoid (..)

  -- ** Ring
  , Num (..)

  -- ** Foldable
  , Foldable (..)
  , Foldable1 (..)
  , for_
  , all
  , endo, endoM
  , module SafeF

  -- ** Traversable
  , Traversable (..)
  , Traversable1 (..)
  , for
  , traverse_

  -- ** Functor
  , Functor (..)
  , (<$>), ($>)
  , void
  , with

  -- ** Bifunctor
  , Bifunctor (..)
  , Assoc (..), Swap (..)

  -- ** Applicative
  , Applicative (..)
  , collect

  -- ** Selective
  , Selective (..)
  , branch

  -- ** Alternative
  , Alternative (..)
  , asum
  , guard
  , when
  , (<||>) 

  -- ** Monad
  , Monad (..), MonadPlus (..)
  , (=<<), (>>=), (>>)
  , join
  , forM
  , forM_
  , mapM_
  , module ErrorU

  -- * Typeclasses-Unsafe
  -- ** Enum
  , Enum (..)
  , succSafe
  , predSafe
  , toEnumMay

  -- ** Read
  , Read (..)
  , readEither
  , readMaybe

  -- ** Show
  , Show (..)

  -- *** ShowS
  , ShowS
  , showString

  -- * System
  -- ** IO
  , IO
  , FilePath

  -- * Partial functions
  , undefined
  , error

  -- * Debugging facilities
  , trace
  , traceM
  , traceIO

  ) where

import Control.Applicative as Applicative (Applicative (..), Alternative (..))
import Control.Arrow as Arrow ((***),(&&&),(+++),(|||))
import Control.Error.Safe as ErrorS
import Control.Error.Util as ErrorU hiding (bool)
import Control.Monad as Monad (Monad (..), MonadPlus (..), (=<<), (>>=), (<=<), guard, join, forM, forM_, mapM, mapM_, when)
import Control.Selective as Selective (Selective (..), branch)
import Data.Bifunctor as Bifunctor (Bifunctor (..))
import Data.Bifunctor.Assoc as Bifunctor (Assoc (..))
import Data.Bifunctor.Swap as Bifunctor (Swap (..))
import Data.Bool as Bool (Bool (..), bool, (&&), (||), not, otherwise)
import Data.Char as Char (Char)
import Data.Either as Either (Either (..), either)
import Data.Eq as Eq (Eq (..))
import Data.Foldable as Foldable (Foldable (..), asum, traverse_, for_, all)
import Data.Function as Function (id, (.), ($), (&), const, flip, fix, on)
import Data.Functor as Functor (Functor (..), (<$>), ($>), void)
import Data.Int as Int (Int, Int8, Int16, Int32, Int64)
import Data.Maybe as Maybe (Maybe (..), fromMaybe, maybe)
import Data.Monoid as Monoid (Monoid (..))
import Data.Ord as Ord ( Ord (..), Ordering (..), comparing)
import Data.Semigroup as Semigroup (Semigroup(..))
import Data.Semigroup.Bifoldable as Bifoldable1 (Bifoldable1 (..))
import Data.Semigroup.Bitraversable as Bitraversable1 (Bitraversable1 (..))
import Data.Semigroup.Foldable as Foldable1 (Foldable1 (..))
import Data.Semigroup.Traversable as Traversable1 (Traversable1 (..))
import Data.Traversable as Traversable (Traversable (..), for)
import Data.Tuple as Tuple (fst, snd, curry, uncurry)
import Data.Word as Word ( Word8, Word16, Word32, Word64)
import GHC.Real as Real (Ratio, Rational, numerator, denominator, fromIntegral, fromRational, realToFrac, mod, div, floor, ceiling)
import Numeric.Natural as Natural
import Prelude as Prelude (Bounded (..), Enum (..), Num (..), Floating, Double, Integer, seq, ($!))
import Safe.Foldable as SafeF (foldl1Def, foldr1Def, findJustDef, minimumDef, maximumDef, minimumByDef, maximumByDef)
import Safe as SafeE (headMay, tailMay, initMay, lastMay)
import Safe (succSafe, predSafe, toEnumMay)
import System.IO as IO ( FilePath, IO)
import Text.Read as Read (Read (..), readEither, readMaybe)
import Text.Show as Show (Show (..), ShowS, showString)
#if MIN_VERSION_base(4,9,0)
import GHC.Stack (HasCallStack)
#endif

import qualified Prelude as Unsafe
import qualified Debug.Trace as Trace



import Control.Selective hiding ((<||>))

{-
type (+) = Either
infixr 5 +

type (*) = (,)
infixl 6 *

(.+++) :: a + b + c + d + e -> (((a + b) + c) + d) + e
(.+++) = x . x . x where x = unassoc @(+)

(+++.) :: (((a + b) + c) + d) + e -> a + b + c + d + e 
(+++.) = x . x . x where x = assoc @(+)

infixr 4 >*<

(>*<) :: Divisible f => f a -> f b -> f (a , b)
(>*<) = divided

infixr 3 >+<

(>+<) :: Decidable f => f a -> f b -> f (a + b)
(>+<) = chosen

strong :: Apply f => f a -> f b -> f (a, b)
strong = liftF2 (,)

costrong :: Divisible f => f a -> f b -> f (a, b)
costrong = divide id

choice :: Decidable f => f a -> f b -> f (Either a b)
choice = choose id

-}


-- | Counterpart to 'on'.
onr :: (a -> b -> c) -> (c -> d) -> a -> b -> d
onr f g = \x y -> g (f x y)

xor :: Bool -> Bool -> Bool
xor a b = (a || b) && (not a || not b)

xnor :: Bool -> Bool -> Bool
xnor = xor `onr` not

implies :: Bool -> Bool -> Bool
implies a b = not a || b
{-# INLINEABLE implies #-}

infixr 0 ==>

(==>) :: Bool -> Bool -> Bool
(==>) = implies

with :: Functor f => f a -> (a -> b) -> f b
with = flip fmap
{-# INLINEABLE with #-}

collect :: Applicative f => ((a, b) -> c) -> f a -> f b -> f c
collect = liftA2 . curry
{-# INLINEABLE collect #-}

dup :: a -> (a, a)
dup = join (,)

dedup :: Either a a -> a
dedup = join either id

eval :: (b -> c, b) -> c
eval (f, b) = f b

liftMay :: (a -> Bool) -> (a -> b) -> (a -> Maybe b)
liftMay test func val = if test val then Nothing else Just $ func val

-- | Function application with lifted parameter
($<) :: Applicative f => f (a -> b) -> a -> f b
($<) f a = f <*> pure a

infixr 2 <||>

-- | @|||@ for 'Alternative's
(<||>) :: Alternative f => (a -> f b) -> (a -> f b) -> a -> f b
(<||>) f g s = fmap dedup $ (fmap Left $ f s) <|> (fmap Right $ g s)

-- A functor from @Kleisli Maybe@ to @Hask@.
-- [/identity/]
--   @'mapMaybe' Just ≡ id@
--
-- [/composition/]
--   @'mapMaybe' f . 'mapMaybe' g ≡ 'mapMaybe' (f <=< g)@
--
mapMaybe :: (Selective f, Alternative f) => (s -> Maybe a) -> f s -> f a
mapMaybe f = fromMaybeS empty . fmap f

filter' :: (Selective f, Alternative f) => (a -> Bool) -> f a -> f a
filter' f = mapMaybe $ \a -> if f a then Just a else Nothing


{-# RULES
    "endo" forall f g.   endo [f, g]    = f . g;
    "endo" forall f g h. endo [f, g, h] = f . g . h;
    "endo" forall f fs.  endo (f:fs)    = f . endo fs
  #-}

endo :: Foldable t => t (a -> a) -> a -> a
endo = foldr (.) id

{-# INLINE [1] endo #-}

endoM :: (Monad m, Foldable t) => t (a -> m a) -> a -> m a

endoM = foldr (<=<) return

{-# INLINE [1] endoM #-}

{-# RULES
    "endoM" forall f g.   endoM [f, g]    = f <=< g;
    "endoM" forall f g h. endoM [f, g, h] = f <=< g <=< h;
    "endoM" forall f fs.  endoM (f:fs)    = f <=< endoM fs
  #-}

#if MIN_VERSION_base(4,9,0)
undefined :: HasCallStack => a
#else
undefined :: a
#endif
undefined =
  Unsafe.undefined
{-# WARNING undefined "'undefined' is unsafe" #-}

#if MIN_VERSION_base(4,9,0)
error :: HasCallStack => [Char] -> a
#else
error :: [Char] -> a
#endif
error =
  Unsafe.error
{-# WARNING error "'error' is unsafe" #-}

trace :: [Char] -> a -> a
trace =
  Trace.trace
{-# WARNING trace "'trace' should only be used while debugging" #-}

#if MIN_VERSION_base(4,9,0)
traceM :: Applicative f => [Char] -> f ()
#else
traceM :: Monad m => [Char] -> m ()
#endif
traceM =
  Trace.traceM
{-# WARNING traceM "'traceM' should only be used while debugging" #-}

traceIO :: [Char] -> IO ()
traceIO =
  Trace.traceIO
{-# WARNING traceIO "'traceIO' should only be used while debugging" #-}


