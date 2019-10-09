{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE FlexibleContexts #-}

module Data.Profunctor.Optic.Prelude (
    module Data.Profunctor.Optic.Prelude
  , module Export
) where

import Data.Foldable
import Data.Traversable
import Control.Applicative as Export
import Control.Category  as Export (Category, (>>>), (<<<))
import Control.Category.Associative as Export
import Control.Category.Braided as Export
import Control.Category.Cartesian as Export
import Control.Category.Monoidal as Export
import Control.Monad as Export hiding (void)
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
import Data.Profunctor.Rep as Export
import Data.Profunctor.Sieve as Export
import Data.Profunctor.Strong as Export 
import Data.Profunctor.Types as Export hiding (WrappedArrow(..), WrapArrow(..))
import Data.Void as Export
import Prelude as Export hiding (fst, snd, foldr, filter)
import qualified Control.Category as C
import qualified Data.Functor.Rep as F
import qualified Data.Tuple 

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

coswp (Left x) = Right x
coswp (Right x) = Left x

assoc :: Associative k1 p1 => k1 (p1 (p1 a b) c) (p1 a (p1 b c))
assoc = associate

unassoc :: Associative k0 p0 => k0 (p0 a (p0 b c)) (p0 (p0 a b) c)
unassoc = disassociate

branch :: (a -> Bool) -> b -> c -> a -> Either b c
branch f y z x = if f x then Right z else Left y

branch' :: (a -> Bool) -> a -> Either a a
branch' f x = branch f x x x


-- arrows
arr :: Category p => Profunctor p => (a -> b) -> p a b
arr f = dimap id f C.id

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

loop :: Costrong p => p (a, c) (b, c) -> p a b
loop = unfirst

-- profunctors
lconst :: Profunctor p => b -> p b c -> p a c
lconst = lmap . const

rconst :: Profunctor p => c -> p a b -> p a c
rconst = rmap . const

lcoerce :: (Corepresentable p, Contravariant (Corep p)) => p a b -> p c b
lcoerce = under (. phantom) --phantom in base's Data.Functor.Contravariant

rcoerce :: (Representable p, Contravariant (Rep p)) => p a b -> p a c
rcoerce = over (phantom .)

rcoerce'  :: (Contravariant (p a), Profunctor p) => p a c -> p a d
rcoerce' = rmap absurd . contramap absurd

lcoerce' :: (Bifunctor p, Profunctor p) => p a c -> p b c
lcoerce' = first absurd . lmap absurd

-- | The 'mempty' equivalent for a 'Contravariant' 'Applicative' 'Functor'.
cempty :: Contravariant f => Applicative f => f a
cempty = phantom $ pure ()

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

over :: Representable p =>  ((a -> Rep p b) -> s -> Rep p t) -> p a b -> p s t
over f = tabulate . f . sieve

under :: Corepresentable p =>  ((Corep p a -> b) -> Corep p s -> t) -> p a b -> p s t
under f = cotabulate . f . cosieve

--https://hackage.haskell.org/package/semialign-1/docs/Data-Align.html
--laligned :: Strong p => Choice p => p a b -> p (These a c) (These b c)
--laligned = error "TODO"

--foo :: (Corepresentable p, Foldable (Corep p), Monoid t) => p a t -> p (Corep p a) t
--foo = under foldMap

unarr :: Sieve p Identity => p a b -> a -> b 
unarr = (runIdentity .) . sieve

lower
  :: ((a1 -> c1) -> b1 -> c2)
  -> (b2 -> c1) -> (a1 -> b2) -> (a2 -> b1) -> a2 -> c2
lower o h f g = o (h . f) . g 

colower o h f g = f . o (g . h)

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
