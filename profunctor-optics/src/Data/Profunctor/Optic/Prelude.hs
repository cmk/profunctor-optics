{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Profunctor.Optic.Prelude (
    module Data.Profunctor.Optic.Prelude
  , module Export
) where

import Data.Foldable
import Data.Traversable
import Control.Arrow as Export ((|||),(&&&),(+++),(***))
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
import Data.Profunctor.Choice as Export
import Data.Profunctor.Closed as Export
import Data.Profunctor.Misc as Export
import Data.Profunctor.Rep as Export
import Data.Profunctor.Sieve as Export
import Data.Profunctor.Strong as Export
import Data.Profunctor.Types as Export hiding (WrappedArrow(..), WrapArrow(..))
import Data.Profunctor.Orphan as Export
import Data.Void as Export
import Prelude as Export hiding (foldr, filter, (.), id, head, tail)
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



star :: Sieve p f => p d c -> Star f d c
star = Star . sieve

star' :: Applicative f => Star f a a
star' = Star pure

fromStar :: Representable p => Star (Rep p) a b -> p a b
fromStar = tabulate . runStar

costar :: Cosieve p f => p a b -> Costar f a b
costar = Costar . cosieve

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
