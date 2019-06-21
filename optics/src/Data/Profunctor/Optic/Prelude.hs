{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE TypeFamilies     #-}

module Data.Profunctor.Optic.Prelude (
    module Data.Profunctor.Optic.Prelude
  , module Export
) where

import Data.Bifunctor                  as Export hiding (Product(..))
--import Data.Either.Combinators         as Export hiding (whenLeft, eitherToError)
import Data.Function                   as Export
import Data.Functor                    as Export
import Data.Functor.Apply              as Export
import Data.Functor.Compose            as Export
import Data.Functor.Const              as Export
import Data.Functor.Contravariant      as Export hiding (($<))
import Data.Functor.Contravariant.Divisible      as Export
import Data.Functor.Identity           as Export
import Data.Semigroup.Traversable      as Export
import Data.Semigroup.Foldable         as Export
import Data.Profunctor                 as Export
import Data.Void                       as Export
import Control.Arrow                   as Export ((+++),(***),(|||),(&&&)) 
import Control.Applicative             as Export hiding (WrappedArrow(..))
import Control.Monad                   as Export

import P as Export hiding (Num(..))


import Data.Bifunctor (Bifunctor (..))
import Data.Bifunctor.Flip (Flip (..))
import Data.Bifunctor.Product (Product (..))
import Data.Bifunctor.Sum (Sum (..))
import Data.Bifunctor.Tannen (Tannen (..))
import Data.Bifunctor.Biff (Biff (..))
--import Data.Either.Validation (Validation(..), eitherToValidation, validationToEither)

import           Data.Foldable
import           Data.Traversable
import           Prelude             hiding (foldr, filter)

import Control.Selective hiding (Validation(..))
import Data.Bool (bool)
import qualified Data.Tuple 


{-
import Control.Applicative
import Control.Exception (Exception(..))

instance (Exception e1, Exception e2) => Exception (Either e1 e2) where

  toException = either toException toException

  fromException s = (fmap Left $ fromException s) <|> (fmap Right $ fromException s) 


type (+) = Either
infixr 5 +

type (*) = (,)
infixl 6 *

(.+++) :: a + b + c + d + e -> (((a + b) + c) + d) + e
(.+++) = x . x . x where x = unassoc @(+)

(+++.) :: (((a + b) + c) + d) + e -> a + b + c + d + e 
(+++.) = x . x . x where x = assoc @(+)


-}


-- | Can be used to rewrite
--
-- > \g -> f . g . h
--
-- to
--
-- > between f h
--
between :: (c -> d) -> (a -> b) -> (b -> c) -> a -> d
between f g = (f .) . (. g)

-- Equiv to 'ocoerce'. TODO add default instance.
pretagged  :: (Contravariant (p a), Profunctor p) => p a c -> p a d
pretagged = rmap absurd . contramap absurd
{-# INLINE pretagged #-}

-- Equiv to 'icoerce'. TODO add default instance.
retagged :: (Bifunctor p, Profunctor p) => p a c -> p b c
retagged = first absurd . lmap absurd
{-# INLINE retagged #-}

-- | The 'mempty' equivalent for a 'Contravariant' 'Applicative' 'Functor'.
noEffect :: (Contravariant f, Applicative f) => f a
noEffect = phantom $ pure ()
{-# INLINE noEffect #-}

star :: Applicative f => Star f c c
star = Star $ pure

ustar :: (b -> f c) -> (d -> b) -> Star f d c
ustar f = Star . (f .)

dstar :: (f c1 -> b) -> Star f a c1 -> a -> b
dstar f = (f .) . runStar

coUstar :: (f d -> b) -> (b -> c) -> Costar f d c
coUstar g = Costar . (. g)

coDstar :: (a -> f d) -> Costar f d c -> a -> c
coDstar g = (. g) . runCostar

iconst :: Profunctor p => b -> p b c -> p a c
iconst = lmap . const

oconst :: Profunctor p => c -> p a b -> p a c
oconst = rmap . const

_1 :: Strong p => p a b -> p (a,c) (b,c) 
_1 = first'

_2 :: Strong p => p a b -> p (c,a) (c,b)
_2 = second'

_L :: Choice p => p a b -> p (Either a c) (Either b c)
_L = left'

_R :: Choice p => p a b -> p (Either c a) (Either c b)
_R = right'



{-
-- | As an example:
--
-- > λ:> ((*2) .* (+)) 1 3 4
-- > 16
(.*) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(.*) f g = \x y -> f (g x y)

(.**) :: (d -> e) -> (a -> b -> c -> d) -> a -> b -> c -> e
(.**) f g = \x y z -> f (g x y z)

axe :: (Traversable t, Applicative f) => t (a -> f ()) -> a -> f ()
axe = sequenceA_ .* sequenceA

bisequence' :: (Traversable t, Applicative f) => t (a -> b -> f c) -> a -> b -> t (f c)
bisequence' = sequenceA .* sequenceA

biaxe :: (Traversable t, Applicative f) => t (a -> b -> f ()) -> a -> b -> f ()
biaxe = sequenceA_ .** bisequence'
-}

branchOn :: (a -> Bool) -> a -> b -> c -> Either b c
branchOn f a b c = if f a then Right c else Left b

branchOn' :: (a -> Bool) -> a -> Either a a
branchOn' f a = branchOn f a a a




