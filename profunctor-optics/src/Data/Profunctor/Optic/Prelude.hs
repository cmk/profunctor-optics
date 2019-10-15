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
--import Data.Bifunctor.Flip as Export (Flip (..))
import Data.Foldable
import Data.Traversable
import Control.Arrow as Export (Kleisli(..))
import Control.Comonad as Export (Cokleisli(..))
import Control.Applicative as Export
import Control.Category as Export (Category, (>>>), (<<<))
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
import Data.Profunctor.Arrow as Export hiding ((***), (+++), (&&&), (|||), ($$$), pliftA2, pdivide , pchoose, pselect, pdivided) 
import Data.Profunctor.Choice as Export 
import Data.Profunctor.Closed as Export
import Data.Profunctor.Product as Export
import Data.Profunctor.Rep as Export
import Data.Profunctor.Sieve as Export
import Data.Profunctor.Strong as Export hiding (Tambara(..), Cotambara(..))
import Data.Profunctor.Tambara as Export
import Data.Profunctor.Types as Export hiding (WrappedArrow(..), WrapArrow(..))
import Data.Void as Export
import Prelude as Export hiding (foldr, filter)
import qualified Control.Category as C
import qualified Data.Functor.Rep as F
import qualified Data.Tuple 

import Data.Functor.Apply


{-
import Control.Applicative
import Control.Exception (Exception(..))

instance (Exception e1, Exception e2) => Exception (Either e1 e2) where

  toException = either toException toException

  fromException s = (fmap Left $ fromException s) <|> (fmap Right $ fromException s) 


type (*) = (,)
infixl 6 *





-}



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





{-

yoneda :: F.Representable f => CotambaraR (->) p => p a b -> p (f a) (f b)
yoneda = dimap F.index F.tabulate . embedr

coyoneda :: F.Representable f => CotambaraL (->) p => p (f a) (f a) -> p (F.Rep f) (F.Rep f)
coyoneda = projectl . dimap F.tabulate F.index

ng :: Profunctor p => ((a -> b) -> s -> t) -> p (Store i v2 v2) (Store s a b) -> p i t
ng sec = dimap ((values &&& info)) (\(Store g s) -> sec g s)

vl :: Strong p => ((i -> Store i v v) -> s -> Store a b t) -> p a b -> p s t
vl l = dimap ((values &&& info) . l (Store id)) eval . second'

foo :: ((a -> b) -> s -> t) -> (i -> Store i v v) -> s -> Store a b t
foo abst isivv s = 

bar :: ((a -> b) -> s -> t) -> Store s a b -> t
bar sec (Store g s) = sec g s

bar :: ((i1 -> Store i1 v1 v1) -> a -> Store i2 k v2) -> a -> (k -> v2, i2)
bar l = (values &&& info) . l (Store id)

_Store :: Profunctor p => p (k1 -> v1, i1) (k2 -> v2, i2) -> p (Store i1 k1 v1) (Store i2 k2 v2)
_Store = dimap (values &&& info) (uncurry Store)

data Store s a b = Store {values :: a -> b, info :: s} -- (s, a -> b)


 p a b -> p (Store s v0 v0) (Store s a b)
p a b -> p (s, c -> c) (s, a -> b)

er = embedr @(->)
el = embedl @(->)
pr = projectr @(->)
pl = projectl @(->)

er . pr :: (Closed p, CotambaraR (->) p)        => p (c1 -> a) (c1 -> b) -> p (c2 -> a) (c2 -> b)

el . pl :: (TambaraL (->) p, CotambaraL (->) p) => p (a -> c1) (b -> c1) -> p (a -> c2) (b -> c2)

uncurry' . er :: (Strong p, Closed p) => p a c -> p (b -> a, b) c





er . papply :: (Closed p, Strong p) => p a (a -> b) -> p (c -> a) (c -> b)
-}

braid :: Category p => Profunctor p => Swap o => p (a `o` b) (b `o` a)
braid = arr swap

assocl :: Assoc p => p a (p b c) -> p (p a b) c
assocl = unassoc

assocr :: Assoc p => p (p a b) c -> p a (p b c)
assocr = assoc

assocl4 :: a + b + c + d -> (((a + b) + c) + d)
assocl4 = x . x where x = unassoc @(+)

assocr4 :: (((a + b) + c) + d) -> a + b + c + d 
assocr4 = x . x where x = assoc @(+)

assocl5 :: a + b + c + d + e -> (((a + b) + c) + d) + e
assocl5 = x . x . x where x = unassoc @(+)

assocr5 :: (((a + b) + c) + d) + e -> a + b + c + d + e 
assocr5 = x . x . x where x = assoc @(+)

--assocr :: Associative p1 => (p1 (p1 a b) c) -> (p1 a (p1 b c))
--assocr = error "TODO"

--assocl :: Associative p0 => (p0 a (p0 b c)) -> (p0 (p0 a b) c)
--assocl = error "TODO"

branch :: (a -> Bool) -> b -> c -> a -> Either b c
branch f y z x = if f x then Right z else Left y

branch' :: (a -> Bool) -> a -> Either a a
branch' f x = branch f x x x


-- profunctors
pullback :: Strong p => TambaraL (->) p => p a (a -> b) -> p (a -> b) b
pullback = papply . embedl @(->)

lcoerce :: (Corepresentable p, Contravariant (Corep p)) => p a b -> p c b
lcoerce = lower (. phantom)

rcoerce :: (Representable p, Contravariant (Rep p)) => p a b -> p a c
rcoerce = lift (phantom .)

rcoerce'  :: Profunctor p => Contravariant (p a) => p a c -> p a d
rcoerce' = rmap absurd . contramap absurd

lcoerce' :: Profunctor p => Bifunctor p => p a c -> p b c
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
