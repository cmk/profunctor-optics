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
import Control.Category as Export -- (Category, (>>>), (<<<))
import Control.Monad as Export hiding (void)
import Control.Comonad as Export
import Data.Bifunctor as Export (Bifunctor (..)) 
import Data.Distributive as Export
import Data.Functor as Export hiding (void)
import Data.Functor.Compose as Export
import Data.Functor.Const as Export
import Data.Functor.Contravariant as Export hiding (($<), void)
import Data.Functor.Contravariant.Divisible as Export
import Data.Functor.Identity as Export
import Data.Profunctor.Bistar as Export
import Data.Profunctor.Arrow as Export hiding ((***), (+++), (&&&), (|||), ($$$), pliftA2, pdivide, pchoose, pselect, pdivided) 
import Data.Profunctor.Choice as Export 
import Data.Profunctor.Closed as Export
import Data.Profunctor.Traversing as Export 
import Data.Profunctor.Mapping as Export
import Data.Profunctor.Monoid as Export
import Data.Profunctor.Rep as Export
import Data.Profunctor.Sieve as Export
import Data.Profunctor.Strong as Export hiding (Tambara(..), Cotambara(..))
--import Data.Profunctor.Tambara as Export
import Data.Profunctor.Types as Export hiding (WrappedArrow(..), WrapArrow(..))
import Data.Profunctor.Orphan as Export
import Data.Void as Export
import Prelude as Export hiding (foldr, filter, (.), id, head, tail)
import qualified Data.Functor.Rep as F
import qualified Data.Tuple 

import Control.Monad.Trans.Cont




-- | The 'mempty' equivalent for a 'Contravariant' 'Applicative' 'Functor'.
cempty :: Contravariant f => Applicative f => f a
cempty = phantom $ pure ()

infixr 3 >+<

(>+<) :: Decidable f => f a -> f b -> f (a + b)
(>+<) = chosen

infixr 4 >*<
(>*<) :: Divisible f => f a -> f b -> f (a , b)
(>*<) = divided

env :: F.Representable f => p a b -> Environment p (f a) (f b)
env p = Environment F.tabulate p F.index

{-

yoneda :: F.Representable f => CotambaraR (->) p => p a b -> p (f a) (f b)
yoneda = dimap F.index F.tabulate . embedr

coyoneda :: F.Representable f => CotambaraL (->) p => p (f a) (f a) -> p (F.Rep f) (F.Rep f)
coyoneda = projectl . dimap F.tabulate F.index


bar :: ((a -> b) -> s -> t) -> Store s a b -> t
bar sec (Store g s) = sec g s

bar :: ((i1 -> Store i1 v1 v1) -> a -> Store i2 k v2) -> a -> (k -> v2, i2)
bar l = (values &&& info) . l (Store id)

_Store :: Profunctor p => p (k1 -> v1, i1) (k2 -> v2, i2) -> p (Store i1 k1 v1) (Store i2 k2 v2)
_Store = dimap (values &&& info) (uncurry Store)

data Store s a b = Store {values :: a -> b, info :: s} -- (s, a -> b)


er = embedr @(->)
el = embedl @(->)
pr = projectr @(->)
pl = projectl @(->)

er . pr :: (Closed p, CotambaraR (->) p)        => p (c1 -> a) (c1 -> b) -> p (c2 -> a) (c2 -> b)

el . pl :: (TambaraL (->) p, CotambaraL (->) p) => p (a -> c1) (b -> c1) -> p (a -> c2) (b -> c2)

uncurry' . er :: (Strong p, Closed p) => p a c -> p (b -> a, b) c


er . papply :: (Closed p, Strong p) => p a (a -> b) -> p (c -> a) (c -> b)
-}

(&) :: a -> (a -> c) -> c
(&) = flip ($)

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

branch :: (a -> Bool) -> b -> c -> a -> Either b c
branch f y z x = if f x then Right z else Left y

branch' :: (a -> Bool) -> a -> Either a a
branch' f x = branch f x x x


-- profunctors

pcurry :: Closed p => p (a , b) c -> p a (b -> c)
pcurry = curry'

puncurry :: Strong p => p a (b -> c) -> p (a , b) c
puncurry = uncurry'

pfirst :: Strong p => p a b -> p (a , c) (b , c)
pfirst = first'

psecond :: Strong p => p a b -> p (c , a) (c , b)
psecond = second'

pleft :: Choice p => p a b -> p (a + c) (b + c)
pleft = left'

pright :: Choice p => p a b -> p (c + a) (c + b)
pright = right'

rcoerce  :: Profunctor p => Contravariant (p a) => p a c -> p a d
rcoerce = rmap absurd . contramap absurd

rcoerce' :: (Representable p, Contravariant (Rep p)) => p a b -> p a c
rcoerce' = lift (phantom .)

lcoerce :: Profunctor p => Bifunctor p => p a c -> p b c
lcoerce = first absurd . lmap absurd

lcoerce' :: (Corepresentable p, Contravariant (Corep p)) => p a b -> p c b
lcoerce' = lower (. phantom)

bicoerce :: Strong p => Costrong p => p a a -> p b b
bicoerce = unsecond . first'

bicoerce' :: Choice p => Cochoice p => p a a -> p b b
bicoerce' = unright . left'

infixr 3 &&&

-- | TODO: Document
--
(&&&) :: Profunctor p => (forall x. Applicative (p x)) => p a b1 -> p a b2 -> p a (b1 , b2)
f &&& g = pliftA2 id f g

infixr 3 ***

-- | TODO: Document
--
-- @p <*> x ≡ dimap dup eval (p *** x)@
--
(***) :: Profunctor p => (forall x. Applicative (p x)) => p a1 b1 -> p a2 b2 -> p (a1 , a2) (b1 , b2)
f *** g = dimap fst (,) f <*> lmap snd g

-- | Profunctor equivalent of 'Data.Functor.Divisible.divide'.
--
pdivide :: Profunctor p => (forall x. Applicative (p x)) => (a -> (a1 , a2)) -> p a1 b -> p a2 b -> p a b
pdivide f x y = dimap f fst $ x *** y

-- | Profunctor equivalent of 'Data.Functor.Divisible.divided'.
--
pdivide' :: Profunctor p => (forall x. Applicative (p x)) => p a1 b -> p a2 b -> p (a1 , a2) b
pdivide' = pdivide id

-- | Profunctor equivalent of 'liftA2'.
--
pliftA2 :: Profunctor p => (forall x. Applicative (p x)) => ((b1 , b2) -> b) -> p a b1 -> p a b2 -> p a b
pliftA2 f x y = dimap dup f $ x *** y

pabsurd :: Profunctor p =>  (forall x. Divisible (p x)) => p Void a
pabsurd = rmap absurd $ conquer

ppure :: Profunctor p => (forall x. Applicative (p x)) => b -> p a b
ppure b = dimap (const ()) (const b) $ pure ()



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

fromIdx :: F.Representable f => F.Rep f -> Costar f a a
fromIdx i = Costar $ flip F.index i

fromIdx' :: F.Representable f => Cont a (F.Rep f) -> Costar f a a
fromIdx' c = Costar $ \m -> runCont c (F.index m)

fromCostar :: Corepresentable p => Costar (Corep p) a b -> p a b
fromCostar = cotabulate . runCostar

fromCostar' :: Applicative f => Costar f a b -> a -> b
fromCostar' f = runCostar f . pure

ustar :: (b -> f c) -> (d -> b) -> Star f d c
ustar f = Star . (f .)

ucostar :: (f d -> b) -> (b -> c) -> Costar f d c
ucostar g = Costar . (. g)

dstar :: (f c1 -> b) -> Star f a c1 -> a -> b
dstar f = (f .) . runStar

dcostar :: (a -> f d) -> Costar f d c -> a -> c
dcostar g = (. g) . runCostar
