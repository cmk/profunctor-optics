{-# LANGUAGE CPP #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
module P (
  -- * Primitive types

  -- ** Bool
    Bool (..), bool
  , (&&), (||), not
  , (==>), implies
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

  -- * Typeclasses-Unsafe
  -- ** Enum
  , Enum (..)
  -- ** Read
  , Read (..)
  , readEither
  , readMaybe
  -- ** Show
  , Show (..)
  -- *** ShowS
  , ShowS
  , showString

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
  -- ** Semiring
  --, Semiring (..)
  -- ** Dioid
  --, Dioid (..)
  -- ** Ring
  --, Ring (..)
  , Num (..)
  -- ** Foldable
  , Foldable (..)
  , Foldable1 (..)
  , for_
  , all
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
  , asum                 --TODO improve
  , guard
  -- ** Monad
  , Monad (..)
  , (=<<)
  , join
  , forM
  , forM_
  , mapM_
  , when

  -- * Data structures
  -- ** Either
  , Either (..)
  , either
  , note
  -- ** Maybe
  , Maybe (..)
  , fromMaybe
  , maybe
  -- ** Tuple
  , fst, snd
  , curry, uncurry

  -- * Combinators
  , id, (.), ($), ($!), (&)
  , (***), (&&&), (+++), (|||)
  , const, flip
  , on
  , fix
  , seq

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

  -- * Misc
  , module P
  , module Export
  ) where





import Data.Bool as Bool (
           Bool (..)
         , bool
         , (&&)
         , (||)
         , not
         , otherwise
         )
import           Data.Char as Char (
           Char
         )

import Numeric.Natural as Natural

import           Data.Word as Word (
           Word8
         , Word16
         , Word32
         , Word64
         )

import           Data.Int as Int (
           Int
         , Int8
         , Int16
         , Int32
         , Int64
         )

import GHC.Real as Real (
           Ratio, Rational, numerator, denominator
         , fromIntegral
         , fromRational
         , realToFrac
         , div
         , floor
         , ceiling
         )

import Data.Semigroup as Semigroup (Semigroup(..))
import Data.Monoid as Monoid (Monoid (..))
--import Data.Semiring as Semiring (Semiring(..))
--import Data.Ring as Ring (Ring(..))
--import Data.Dioid as Dioid (Dioid(..))

import           Data.Foldable as Foldable (
           Foldable (..)
         , asum -- TODO replace?
         , traverse_
         , for_
         , all
         )

import Data.Semigroup.Foldable as Foldable1 (Foldable1 (..))

import Data.Semigroup.Bifoldable as Bifoldable1 (Bifoldable1 (..))

import Data.Semigroup.Bitraversable as Bitraversable1 (Bitraversable1 (..))

import Data.Traversable as Traversable (Traversable (..), for)

import Data.Semigroup.Traversable as Traversable1 (Traversable1 (..))

import           Data.Functor as Functor (
           Functor (..)
         , (<$>)
         , ($>)
         , void
         )
import Data.Bifunctor as Bifunctor (Bifunctor (..))
import Data.Bifunctor.Assoc as Bifunctor (Assoc (..))
import Data.Bifunctor.Swap as Bifunctor (Swap (..))

import Control.Applicative as Applicative (Applicative (..), Alternative (..))

import           Control.Selective as Selective (
           Selective (..)
         , branch
         )

import           Control.Monad as Monad (
           Monad (..)
         , MonadPlus (..)
         , (=<<)
         , (>>=)
         , (<=<)
         , (>>)
         , guard
         , join
         , msum
         , forM
         , forM_
         , mapM
         , mapM_
         , when
         )

import Control.Arrow as Arrow ((***), (&&&), (+++), (|||))

import           Data.Function as Function (
           id
         , (.)
         , ($)
         , (&)
         , const
         , flip
         , fix
         , on
         )

import           Data.Maybe as Maybe (
           Maybe (..)
         , fromMaybe
         , maybe
         )

import           Data.Either as Either (
           Either (..)
         , either
         )

import           Data.Tuple as Tuple (
           fst
         , snd
         , curry
         , uncurry
         )




import qualified Debug.Trace as Trace

#if MIN_VERSION_base(4,9,0)
import           GHC.Stack (HasCallStack)
#endif

import qualified Prelude as Unsafe

import           Data.Eq as Eq (
           Eq (..)
         )
import           Data.Ord as Ord (
           Ord (..)
         , Ordering (..)
         , comparing
         )
import           Text.Show as Show (
           Show (..)
         , ShowS
         , showString
         )
import           Text.Read as Read (
           Read (..)
         , readEither
         , readMaybe
         )
import           Prelude as Prelude (
           Bounded (..)
         , Enum (..)
         , Num (..)
         , Floating
         , Double
         , Integer
         , seq
         , ($!)
         )
import           System.IO as IO (
           FilePath
         , IO
         )

import qualified Control.Category as Cat
import Control.Arrow
--import Data.Functor.Contravariant.Divisible
--import Data.Functor.Contravariant

import Control.Error as Export hiding (bool, mapMaybe)
import Control.Selective 

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

-}


{-

-- | Backwards function application. This is an infix synonym for 'flip'
(-$) :: (a -> b -> c) -> b -> a -> c
(-$) = flip


strong :: Apply f => f a -> f b -> f (a, b)
strong = liftF2 (,)

costrong :: Divisible f => f a -> f b -> f (a, b)
costrong = divide id

choice :: Decidable f => f a -> f b -> f (Either a b)
choice = choose id
-}

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


