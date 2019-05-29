{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE TypeFamilies     #-}

module Data.Profunctor.Optic.Prelude (
    module Data.Profunctor.Optic.Prelude
  , module Export
) where

import Data.Bifunctor                  as Export
import Data.Either.Combinators         as Export hiding (eitherToError)
import Data.Function                   as Export
import Data.Functor                    as Export
import Data.Functor.Apply              as Export
import Data.Functor.Compose            as Export
import Data.Functor.Const              as Export
import Data.Functor.Contravariant      as Export
import Data.Functor.Contravariant.Divisible      as Export
import Data.Functor.Identity           as Export
import Data.Semigroup.Traversable      as Export
import Data.Semigroup.Foldable         as Export
import Data.Profunctor                 as Export hiding (Forget(..))
import Data.Void                       as Export
import Control.Arrow                   as Export ((+++),(***),(|||),(&&&)) 
import Control.Applicative             as Export hiding (WrappedArrow(..))


import Data.Bifunctor (Bifunctor (..))
import Data.Bifunctor.Flip (Flip (..))
import Data.Bifunctor.Product (Product (..))
import Data.Bifunctor.Sum (Sum (..))
import Data.Bifunctor.Tannen (Tannen (..))
import Data.Bifunctor.Biff (Biff (..))
import Data.Either.Validation (Validation(..))

import           Control.Monad
import           Data.Foldable
import           Data.Traversable
import           Prelude             hiding (foldr)

import qualified Data.Tuple
{-
import Control.Applicative
import Control.Exception (Exception(..))
import Data.Functor.Contravariant.Divisible

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


infixr 3 >*<

(>*<) :: Divisible f => f a -> f b -> f (a , b)
(>*<) = divided

infixr 3 >+<

(>+<) :: Decidable f => f a -> f b -> f (a + b)
(>+<) = chosen
-}

{-
strong :: Apply f => f a -> f b -> f (a, b)
strong = liftF2 (,)

costrong :: Divisible f => f a -> f b -> f (a, b)
costrong = divide id

choice :: Decidable f => f a -> f b -> f (Either a b)
choice = choose id
-}

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

--both :: (a -> b) -> (a, a) -> (b, b)
--both = join (***)
dup :: a -> (a, a)
dup = join (,)

dedup :: Either a a -> a
dedup = join either id

-- | Infix version of 'join'
--
-- As an example, we could use this to rewrite
--
-- > between (char '"') (char '"')
--
-- to
--
-- > between .$ (char '"')
--
-- @since 2.0.2.0
(.$) :: Monad m => m (m a) -> m a
(.$) = join

-- | Backwards function application. This is an infix synonym for 'flip'
(-$) :: (a -> b -> c) -> b -> a -> c
(-$) = flip

{-# RULES
    "endo" forall f g.   endo [f, g]    = f . g;
    "endo" forall f g h. endo [f, g, h] = f . g . h;
    "endo" forall f fs.  endo (f:fs)    = f . endo fs
  #-}

endo :: Foldable t => t (a -> a) -> a -> a
endo = foldr (.) id

{-# INLINE [1] endo #-}

endoM :: (Monad m, Foldable t, Applicative m) => t (a -> m a) -> a -> m a
endoM = foldr (<=<) pure

{-# INLINE [1] endoM #-}

{-# RULES
    "endoM" forall f g.   endoM [f, g]    = f <=< g;
    "endoM" forall f g h. endoM [f, g, h] = f <=< g <=< h;
    "endoM" forall f fs.  endoM (f:fs)    = f <=< endoM fs
  #-}


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

betweenM :: Monad m => (c -> m d) -> (a -> m b) -> (b -> m c) -> a -> m d
betweenM f g = (f <=<) . (<=< g)

-- Equiv to 'ocoerce'. TODO add default instance.
retagged  :: (Contravariant (p a), Profunctor p) => p a c -> p a d
retagged = rmap absurd . contramap absurd
{-# INLINE retagged #-}

-- Equiv to 'icoerce'. TODO add default instance.
pretagged :: (Bifunctor p, Profunctor p) => p a c -> p b c
pretagged = first absurd . lmap absurd
{-# INLINE pretagged #-}

-- | The 'mempty' equivalent for a 'Contravariant' 'Applicative' 'Functor'.
noEffect :: (Contravariant f, Applicative f) => f a
noEffect = phantom $ pure ()
{-# INLINE noEffect #-}

-- | 'Swap'
--
-- Laws:
-- @
-- 'swap' . 'swap' ≡ 'id'
-- @
--
-- If @p@ is a 'Bifunctor' the following property is assumed to hold:
--
-- @
-- 'swap' . 'bimap' f g ≡ 'bimap' g f . 'swap'
-- @
--
class Swap p where
    swap :: p a b -> p b a

instance Swap (,) where
    swap = Data.Tuple.swap

instance Swap Either where
    swap (Left x) = Right x
    swap (Right x) = Left x

instance Swap p => Swap (Flip p) where
    swap = Flip . swap . runFlip

instance (Swap p, Swap q) => Swap (Product p q) where
    swap (Pair p q) = Pair (swap p) (swap q)

instance (Swap p, Swap q) => Swap (Sum p q) where
    swap (L2 p) = L2 (swap p)
    swap (R2 q) = R2 (swap q)

instance (Functor f, Swap p) => Swap (Tannen f p) where
    swap = Tannen . fmap swap . runTannen

instance (f ~ g, Functor f, Swap p) => Swap (Biff p f g) where
    swap = Biff . swap . runBiff

instance Swap Validation where
    swap (Failure e) = Success e
    swap (Success a) = Failure a

    
-- | 'Assoc' 
--
-- Laws:
-- @
-- 'assoc' . 'unassoc' ≡ 'id'
-- 'unassoc' . 'assoc' ≡ 'id'
-- @
--
-- If @p@ is a 'Bifunctor' the following property is assumed to hold:
--
-- @
-- 'assoc' . 'bimap' ('bimap' f g) h ≡ 'bimap' f ('bimap' g h) . 'assoc'
-- @
--
class Assoc p where
    assoc :: p (p a b) c -> p a (p b c)
    unassoc :: p a (p b c) -> p (p a b) c

instance Assoc (,) where
    assoc ((a, b), c) = (a, (b, c))
    unassoc (a, (b, c)) = ((a, b), c)

instance Assoc Either where
    assoc (Left (Left a))  = Left a
    assoc (Left (Right b)) = Right (Left b)
    assoc (Right c)        = Right (Right c)

    unassoc (Left a)          = Left (Left a)
    unassoc (Right (Left b))  = Left (Right b)
    unassoc (Right (Right c)) = Right c

instance (Assoc p, Bifunctor p) => Assoc (Flip p) where
    assoc   = Flip . first Flip . unassoc . second runFlip . runFlip
    unassoc = Flip . second Flip . assoc . first runFlip . runFlip

-- $setup
--
-- TODO: make proper test-suite
--
-- >>> import Data.Proxy
-- >>> import Test.QuickCheck
-- >>> import Data.Functor.Classes
--
-- >>> :{
--     let assocUnassocLaw :: (Assoc p, Eq2 p) => Proxy p -> p Bool (p Int Char) -> Bool
--         assocUnassocLaw _ x = liftEq2 (==) eq2 (assoc (unassoc x)) x
--     :}
--
-- >>> quickCheck $ assocUnassocLaw (Proxy :: Proxy (,))
-- +++ OK, passed 100 tests.
--
-- >>> quickCheck $ assocUnassocLaw (Proxy :: Proxy Either)
-- +++ OK, passed 100 tests.
--
-- >>> :{
--     let unassocAssocLaw :: (Assoc p, Eq2 p) => Proxy p -> p (p Int Char) Bool -> Bool
--         unassocAssocLaw _ x = liftEq2 eq2 (==) (unassoc (assoc x)) x
--     :}
--
-- >>> quickCheck $ unassocAssocLaw (Proxy :: Proxy (,))
-- +++ OK, passed 100 tests.
--
-- >>> quickCheck $ unassocAssocLaw (Proxy :: Proxy Either)
-- +++ OK, passed 100 tests.
--
-- >>> :{
--     let bimapLaw :: (Assoc p, Eq2 p) => Proxy p
--                  -> Fun Int Char -> Fun Char Bool -> Fun Bool Int
--                  -> p (p Int Char) Bool
--                  -> Bool
--         bimapLaw _ (Fun _ f) (Fun _ g) (Fun _ h) x = liftEq2 (==) eq2
--             (assoc . bimap (bimap f g) h $ x)
--             (bimap f (bimap g h) . assoc $ x)
--     :}
--
-- >>> quickCheck $ bimapLaw (Proxy :: Proxy (,))
-- +++ OK, passed 100 tests.
--
-- >>> quickCheck $ bimapLaw (Proxy :: Proxy Either)
-- +++ OK, passed 100 tests.



