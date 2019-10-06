{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE FlexibleContexts #-}

module Data.Profunctor.Optic.Prelude (
    module Data.Profunctor.Optic.Prelude
  , module Export
) where

import Control.Category.Cartesian as Export
import Control.Category.Braided as Export
import Control.Category  as Export (Category, (>>>), (<<<))
import qualified Control.Category as C
import Control.Category.Associative as Export
import Control.Category.Monoidal as Export

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
import Data.Void                       as Export
import Control.Applicative             as Export
import Control.Monad                   as Export

import Data.Distributive as Export
import Data.Profunctor.Rep
import Data.Profunctor.Sieve

import Data.Profunctor.Types           as Export hiding (WrappedArrow(..), WrapArrow(..))
import Data.Profunctor.Choice          as Export 
import Data.Profunctor.Strong          as Export 
import Data.Profunctor.Closed          as Export
import Data.Profunctor.Adapter as Export
import Data.Profunctor.Rep as Export
import Data.Profunctor.Sieve as Export
--import Data.Profunctor.Mapping         as Export
--import Data.Profunctor.Traversing      as Export

import Data.Bifunctor as Export (Bifunctor (..)) 

{-

import Data.Bifunctor (Bifunctor (..))
import Data.Bifunctor.Flip (Flip (..))
import Data.Bifunctor.Product (Product (..))
import Data.Bifunctor.Sum (Sum (..))
import Data.Bifunctor.Tannen (Tannen (..))
import Data.Bifunctor.Biff (Biff (..))
-}
--import Data.Either.Validation (Validation(..), eitherToValidation, validationToEither)

import           Data.Foldable
import           Data.Traversable
import Prelude as Export            hiding (fst, snd, foldr, filter)

import Data.Bool (bool)
import qualified Data.Tuple 

import qualified Data.Functor.Rep as F
import Control.Monad.Trans.Cont

coidx :: F.Representable f => Cont r (F.Rep f) -> f r -> r
coidx c m = runCont c (F.index m)


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

-- prelude
dup :: a -> (a, a)
dup = join (,)

dedup :: Either a a -> a
dedup = join either id

swp (a,b) = (b,a)

coswp (Left x) = Right x
coswp (Right x) = Left x

assoc :: Associative k1 p1 => k1 (p1 (p1 a b) c) (p1 a (p1 b c))
assoc = associate

unassoc :: Associative k0 p0 => k0 (p0 a (p0 b c)) (p0 (p0 a b) c)
unassoc = disassociate

arr :: Category p => Profunctor p => (a -> b) -> p a b
arr f = dimap id f C.id

unarr :: Sieve p Identity => p a b -> a -> b 
unarr = (runIdentity .) . sieve

returnA :: Category p => Profunctor p => p a a
returnA = arr id

(***) :: Braided a (,) => Strong a => a b c -> a b' c' -> a (b,b') (c,c')
f *** g = first' f >>> braid >>> first' g >>> braid

(+++) :: Braided a Either => Choice a => a b c -> a b' c' -> a (Either b b') (Either c c')
f +++ g = left' f >>> braid >>> left' g >>> braid

eval :: (b -> c, b) -> c
eval (f, b) = f b

coeval :: b -> Either (b -> a) a -> a
coeval b = either ($ b) id

--star :: Applicative f => Star f c c
--star = Star $ pure

recover :: Strong p => p a b -> p a (b, a)
recover = lmap dup . first'

eval' :: Strong p => p a (a -> b) -> p a b
eval' = rmap eval . recover 

--strong :: Applicative f => (f a, f b) -> f (a, b)
--strong = uncurry $ liftA2 (,)

--strong :: Strong p => (a -> b -> c) -> p a b -> p a c
--strong f = dimap dup (Data.Tuple.uncurry f . swp) . first'

choice :: Choice p => (c -> Either a b) -> p a b -> p c b
choice f = dimap f dedup . left'

-- Any 'Corepresentable' profuctor is closed.
--
closed' :: Corepresentable p => p a b -> p (c -> a) (c -> b)
closed' = cowander cotraverse

loop :: Costrong p => p (a, c) (b, c) -> p a b
loop = unfirst




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

wander :: Representable p =>  ((a -> Rep p b) -> s -> Rep p t) -> p a b -> p s t
wander f = tabulate . f . sieve

cowander :: Corepresentable p =>  ((Corep p a -> b) -> Corep p s -> t) -> p a b -> p s t
cowander f = cotabulate . f . cosieve

--https://hackage.haskell.org/package/semialign-1/docs/Data-Align.html
--laligned :: Strong p => Choice p => p a b -> p (These a c) (These b c)
--laligned = error "TODO"

cotraversed :: Corepresentable p => Distributive g => p a b -> p (g a) (g b)
cotraversed = cowander cotraverse

lcoerce :: (Corepresentable p, Contravariant (Corep p)) => p a b -> p c b
lcoerce = cowander (. phantom) --phantom in base's Data.Functor.Contravariant

rcoerce :: (Representable p, Contravariant (Rep p)) => p a b -> p a c
rcoerce = wander (phantom .)

rcoerce'  :: (Contravariant (p a), Profunctor p) => p a c -> p a d
rcoerce' = rmap absurd . contramap absurd

lcoerce' :: (Bifunctor p, Profunctor p) => p a c -> p b c
lcoerce' = first absurd . lmap absurd


-- | The 'mempty' equivalent for a 'Contravariant' 'Applicative' 'Functor'.
noEffect :: (Contravariant f, Applicative f) => f a
noEffect = phantom $ pure ()
{-# INLINE noEffect #-}

lower
  :: ((a1 -> c1) -> b1 -> c2)
  -> (b2 -> c1) -> (a1 -> b2) -> (a2 -> b1) -> a2 -> c2
lower o h f g = o (h . f) . g 

colower o h f g = f . o (g . h)

star :: Sieve p f => p d c -> Star f d c
star = Star . sieve

star' :: Representable p => Star (Rep p) d c -> p d c
star' = tabulate . runStar 

costar :: Cosieve p f => p d c -> Costar f d c
costar = Costar . cosieve

costar' :: Corepresentable p => Costar (Corep p) d c -> p d c
costar' = cotabulate . runCostar

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





branchOn :: (a -> Bool) -> a -> b -> c -> Either b c
branchOn f a b c = if f a then Right c else Left b

branchOn' :: (a -> Bool) -> a -> Either a a
branchOn' f a = branchOn f a a a




