{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Profunctor.Optic.Prelude (
    module Data.Profunctor.Optic.Prelude
  , module Export
) where

import Data.Bifunctor.Assoc as Export
import Data.Bifunctor.Swap as Export
import Data.Bifunctor.Flip as Export (Flip (..))
import Data.Foldable
import Data.Traversable
import Control.Arrow as Export (Kleisli(..))
import Control.Comonad as Export (Cokleisli(..))
import Control.Applicative as Export
import Control.Category  as Export (Category, (>>>), (<<<))
--import Control.Category.Associative as Export
--import Control.Category.Braided as Export
--import Control.Category.Cartesian as Export
--import Control.Category.Monoidal as Export
import Control.Monad as Export hiding (void)
import Control.Comonad as Export
import Data.Bifunctor as Export (Bifunctor (..)) 
import Data.Distributive as Export
import Data.Function as Export
import Data.Functor as Export hiding (void)
import Data.Functor.Compose as Export
import Data.Functor.Const as Export
import Data.Functor.Contravariant as Export hiding (($<), void)
import Data.Functor.Contravariant.Divisible as Export
import Data.Functor.Identity as Export
import Data.Profunctor.Bistar as Export
import Data.Profunctor.Choice as Export 
import Data.Profunctor.Closed as Export
import Data.Profunctor.Rep as Export
import Data.Profunctor.Sieve as Export
import Data.Profunctor.Strong as Export hiding (Tambara(..), Cotambara(..))
import Data.Profunctor.Types as Export hiding (WrappedArrow(..), WrapArrow(..))
import Data.Void as Export
import Prelude as Export hiding (foldr, filter)
import qualified Control.Category as C
import qualified Data.Functor.Rep as F
import qualified Data.Tuple 

import Data.Functor.Apply

type (+) = Either
infixr 5 +

{-
import Control.Applicative
import Control.Exception (Exception(..))

instance (Exception e1, Exception e2) => Exception (Either e1 e2) where

  toException = either toException toException

  fromException s = (fmap Left $ fromException s) <|> (fmap Right $ fromException s) 


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

--coswp = Right ||| Left
coswp (Left x) = Right x
coswp (Right x) = Left x

assocl :: Assoc p => p a (p b c) -> p (p a b) c
assocl = unassoc

assocr :: Assoc p => p (p a b) c -> p a (p b c)
assocr = assoc

--assocr :: Associative p1 => (p1 (p1 a b) c) -> (p1 a (p1 b c))
--assocr = error "TODO"

--assocl :: Associative p0 => (p0 a (p0 b c)) -> (p0 (p0 a b) c)
--assocl = error "TODO"

branch :: (a -> Bool) -> b -> c -> a -> Either b c
branch f y z x = if f x then Right z else Left y

branch' :: (a -> Bool) -> a -> Either a a
branch' f x = branch f x x x

strength :: Functor f => f a -> b -> f (a , b)
strength fa b = fmap (\a -> (a,b)) fa

strengthA :: Applicative f => (f a, f b) -> f (a, b)
strengthA = uncurry $ liftA2 (,)

costrength :: Traversable f => f (a + b) -> (f a) + b
costrength = coswp . traverse coswp

-- Natural laws:
-- distr . right . fmap f = fmap (right f) . distr
-- distr . left f = fmap (left f) . distr
--
-- Other laws:
-- 1. either absurd (fmap Right) = distr :: Either Void (f a) -> f (Either Void a)
-- 2. fmap assocL . distr . right distr . assocR = distr :: Either (Either a b) (f c) -> f (Either (Either a b) c)
--  where
--   assocL :: Either a (Either b c) -> Either (Either a b) c
--   assocL (Left a) = Left (Left a)
--   assocL (Right (Left a)) = Left (Right a)
--   assocL (Right (Right a)) = Right a
--   assocR :: Either (Either a b) c -> Either a (Either b c)
--   assocR (Left (Left a)) = Left a
--   assocR (Left (Right a)) = Right (Left a)
--   assocR (Right a) = Right (Right a)

{-
-- https://r6research.livejournal.com/28338.html
class Functor f => Pointed f where
  point :: a -> f a
  point = fmap (id ||| absurd) . distr . Left

  distr :: Either a (f b) -> f (Either a b)
  distr = either (fmap Left . point) (fmap Right)

  distl :: Either (f a) b -> f (Either a b)
  distl = fmap coswp . distr . coswp

distl' :: Traversable f => f (Either b1 b2) -> Either (f b1) b2
distl' = coswp . traverse coswp
-}

--instance (Functor f, Traversable f) => Pointed f where
--  distr = mapM coswp . coswp


-- | The 'mempty' equivalent for a 'Contravariant' 'Applicative' 'Functor'.
cempty :: Contravariant f => Applicative f => f a
cempty = phantom $ pure ()

infixr 3 >+<

(>+<) :: Decidable f => f a -> f b -> f (a + b)
(>+<) = chosen

infixr 4 >*<
(>*<) :: Divisible f => f a -> f b -> f (a , b)
(>*<) = divided


-- | Lift a function into a profunctor.
arr :: Category p => Profunctor p => (a -> b) -> p a b
arr f = dimap id f C.id

-- | We can convert any 'Conjoined' 'Profunctor' to a function,
-- possibly losing information about an index in the process.
coarr :: (Representable p, Comonad (Rep p)) => p a b -> a -> b
coarr qab = extract . sieve qab
{-# INLINE coarr #-}

returnA :: Category p => Profunctor p => p a a
returnA = arr id

strong :: Strong p => (a -> b -> c) -> p a b -> p a c
strong f = dimap dup (Data.Tuple.uncurry f . swp) . first'

choice :: Choice p => (c -> a + b) -> p a b -> p c b
choice f = dimap f dedup . left'

{-
(***) :: Braided a (,) => Strong a => a b c -> a b' c' -> a (b , b') (c , c')
f *** g = first' f >>> braid >>> first' g >>> braid

(+++) :: Braided a (+) => Choice a => a b c -> a b' c' -> a (b + b') (c + c')
f +++ g = left' f >>> braid >>> left' g >>> braid
-}

eval :: (b -> c, b) -> c
eval = uncurry id

apply :: (a , a -> b) -> b
apply = uncurry $ flip id

coeval :: b -> Either (b -> a) a -> a
coeval b = either ($ b) id

infixr 1 ^>>, >>^, <<^, ^<<

-- | Precomposition with a pure function.
--
(^>>) :: Profunctor p => (a -> b) -> p b c -> p a c
(^>>) = lmap

-- | Postcomposition with a pure function.
--
(>>^) :: Profunctor p => p a b -> (b -> c) -> p a c
(>>^) = flip rmap

-- | Precomposition with a pure function (right-to-left variant).
--
(<<^) :: Profunctor p => p b c -> (a -> b) -> p a c
(<<^) = flip lmap

-- | Postcomposition with a pure function (right-to-left variant).
--
(^<<) :: Profunctor p => (b -> c) -> p a b -> p a c
(^<<) = rmap




recover :: Strong p => p a b -> p a (b , a)
recover = lmap dup . first'

eval' :: Strong p => p a (a -> b) -> p a b
eval' = rmap eval . recover 

loop :: Costrong p => p (a , c) (b , c) -> p a b
loop = unfirst

diag :: Category p => Profunctor p => p a (a, a)
diag = arr dup

codiag :: Category p => Profunctor p => p (Either b b) b
codiag = arr dedup

braid :: Category p => Profunctor p => p (a , b) (b , a)
braid = arr swp

cobraid :: Category p => Profunctor p => p (a + b) (b + a)
cobraid = arr coswp

{-
idl :: Category p => Profunctor p => p (a , b) b
idl = arr snd

idr :: Category p => Profunctor p => p (a , b) a
idr = arr fst

inl :: Category p => Profunctor p => p a (a + b)
inl = arr Left

inr :: Category p => Profunctor p => p b (a + b)
inr = arr Right

inr :: Profunctor p => p a b -> p a (c -> (b , c))
inr = ((,) `rmap`)

inr :: Profunctor p => p a b -> p a ((b + c) -> b)

-}

--select :: Category p => Choice p => p (a + (b, b -> a)) a
--select = id ||| arr apply


-- profunctors
lconst :: Profunctor p => b -> p b c -> p a c
lconst = lmap . const

rconst :: Profunctor p => c -> p a b -> p a c
rconst = rmap . const

--newtype Flip p b a = Flip { unFlip :: p a b }

lcoerce :: (Corepresentable p, Contravariant (Corep p)) => p a b -> p c b
lcoerce = lower (. phantom)

rcoerce :: (Representable p, Contravariant (Rep p)) => p a b -> p a c
rcoerce = lift (phantom .)

rcoerce'  :: (Contravariant (p a), Profunctor p) => p a c -> p a d
rcoerce' = rmap absurd . contramap absurd

lcoerce' :: (Bifunctor p, Profunctor p) => p a c -> p b c
lcoerce' = first absurd . lmap absurd


-- combinators

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

lift :: Representable p => ((a -> Rep p b) -> s -> Rep p t) -> p a b -> p s t
lift f = tabulate . f . sieve

lower :: Corepresentable p => ((Corep p a -> b) -> Corep p s -> t) -> p a b -> p s t
lower f = cotabulate . f . cosieve

--https://hackage.haskell.org/package/semialign-1/docs/Data-Align.html
--laligned :: Strong p => Choice p => p a b -> p (These a c) (These b c)
--laligned = error "TODO"

--foo :: (Corepresentable p, Foldable (Corep p), Monoid t) => p a t -> p (Corep p a) t
--foo = lower foldMap

unarr :: Sieve p Identity => p a b -> a -> b 
unarr = (runIdentity .) . sieve



ustar :: (b -> f c) -> (d -> b) -> Star f d c
ustar f = Star . (f .)

ucostar :: (f d -> b) -> (b -> c) -> Costar f d c
ucostar g = Costar . (. g)

dstar :: (f c1 -> b) -> Star f a c1 -> a -> b
dstar f = (f .) . runStar

dcostar :: (a -> f d) -> Costar f d c -> a -> c
dcostar g = (. g) . runCostar

star :: Sieve p f => p d c -> Star f d c
star = Star . sieve

star' :: Applicative f => Star f a a
star' = Star pure

fromStar :: Representable p => Star (Rep p) a b -> p a b
fromStar = tabulate . runStar 

fromStar' :: F.Representable f => F.Rep f -> Star f a b -> a -> b
fromStar' i (Star f) = flip F.index i . f

costar :: Cosieve p f => p a b -> Costar f a b
costar = Costar . cosieve

costar' :: F.Representable f => F.Rep f -> Costar f a a
costar' i = Costar $ flip F.index i

fromCostar :: Corepresentable p => Costar (Corep p) a b -> p a b
fromCostar = cotabulate . runCostar

fromCostar' :: Applicative f => Costar f a b -> a -> b
fromCostar' f = runCostar f . pure
