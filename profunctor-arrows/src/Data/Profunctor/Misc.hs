module Data.Profunctor.Misc where

import Control.Arrow ((|||),(&&&))
import Control.Category (Category)
import Control.Comonad (Comonad(..))
import Data.Bifunctor
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
import Data.Profunctor
import Data.Profunctor.Rep
import Data.Profunctor.Sieve
import Data.Void
import Prelude
import qualified Control.Category as C (id)
import qualified Control.Monad as M (join)

infixr 5 +

type (+) = Either

rgt :: (a -> b) -> a + b -> b
rgt f = either f id
 
rgt' :: Void + b -> b
rgt' = rgt absurd 

lft :: (b -> a) -> a + b -> a
lft f = either id f

lft' :: a + Void -> a
lft' = lft absurd

swp :: (a1 , a2) -> (a2 , a1)
swp = snd &&& fst

eswp :: (a1 + a2) -> (a2 + a1)
eswp = Right ||| Left

fork :: a -> (a , a)
fork = M.join (,)

join :: (a + a) -> a
join = M.join either id

eval :: (a , a -> b) -> b
eval = uncurry $ flip id

apply :: (b -> a , b) -> a
apply = uncurry id

coeval :: b -> (b -> a) + a -> a
coeval b = either ($ b) id

branch :: (a -> Bool) -> b -> c -> a -> b + c
branch f y z x = if f x then Right z else Left y

branch' :: (a -> Bool) -> a -> a + a
branch' f x = branch f x x x

assocl :: (a , (b , c)) -> ((a , b) , c)
assocl (a, (b, c)) = ((a, b), c)

assocr :: ((a , b) , c) -> (a , (b , c))
assocr ((a, b), c) = (a, (b, c))

eassocl :: (a + (b + c)) -> ((a + b) + c)
eassocl (Left a)          = Left (Left a)
eassocl (Right (Left b))  = Left (Right b)
eassocl (Right (Right c)) = Right c

eassocr :: ((a + b) + c) -> (a + (b + c))
eassocr (Left (Left a))  = Left a
eassocr (Left (Right b)) = Right (Left b)
eassocr (Right c)        = Right (Right c)

fstrong :: Functor f => f a -> b -> f (a , b)
fstrong f b = fmap (,b) f

fchoice :: Traversable f => f (a + b) -> (f a) + b
fchoice = eswp . traverse eswp

forget1 :: ((c , a) -> (c , b)) -> a -> b
forget1 f a = b where (c, b) = f (c, a)

forget2 :: ((a , c) -> (b , c)) -> a -> b
forget2 f a = b where (b, c) = f (a, c)

forgetl :: ((c + a) -> (c + b)) -> a -> b
forgetl f = go . Right where go = either (go . Left) id . f

forgetr :: ((a + c) -> (b + c)) -> a -> b
forgetr f = go . Left where go = either id (go . Right) . f

unarr :: Comonad w => Sieve p w => p a b -> a -> b 
unarr = (extract .) . sieve

peval :: Strong p => p a (a -> b) -> p a b
peval = rmap eval . pull

constl :: Profunctor p => b -> p b c -> p a c
constl = lmap . const

constr :: Profunctor p => c -> p a b -> p a c
constr = rmap . const

shiftl :: Profunctor p => p (a + b) c -> p b (c + d)
shiftl = dimap Right Left

shiftr :: Profunctor p => p b (c , d) -> p (a , b) c
shiftr = dimap snd fst

coercer :: Profunctor p => Contravariant (p a) => p a b -> p a c
coercer = rmap absurd . contramap absurd

coercer' :: Representable p => Contravariant (Rep p) => p a b -> p a c
coercer' = lift (phantom .)

coercel :: Profunctor p => Bifunctor p => p a b -> p c b
coercel = first absurd . lmap absurd

coercel' :: Corepresentable p => Contravariant (Corep p) => p a b -> p c b
coercel' = lower (. phantom)

strong :: Strong p => ((a , b) -> c) -> p a b -> p a c
strong f = dimap fork f . second'

costrong :: Costrong p => ((a , b) -> c) -> p c a -> p b a
costrong f = unsecond . dimap f fork

choice :: Choice p => (c -> (a + b)) -> p b a -> p c a
choice f = dimap f join . right'

cochoice :: Cochoice p => (c -> (a + b)) -> p a c -> p a b
cochoice f = unright . dimap join f

pull :: Strong p => p a b -> p a (a , b)
pull = lmap fork . second'

pull' :: Strong p => p b c -> p (a , b) b
pull' = shiftr . pull

lift :: Representable p => ((a -> Rep p b) -> s -> Rep p t) -> p a b -> p s t
lift f = tabulate . f . sieve

lower :: Corepresentable p => ((Corep p a -> b) -> Corep p s -> t) -> p a b -> p s t
lower f = cotabulate . f . cosieve

star :: Applicative f => Star f a a
star = Star pure

toStar :: Sieve p f => p d c -> Star f d c
toStar = Star . sieve

fromStar :: Representable p => Star (Rep p) a b -> p a b
fromStar = tabulate . runStar

costar :: Foldable f => Monoid b => (a -> b) -> Costar f a b
costar f = Costar (foldMap f)

uncostar :: Applicative f => Costar f a b -> a -> b
uncostar f = runCostar f . pure

toCostar :: Cosieve p f => p a b -> Costar f a b
toCostar = Costar . cosieve

fromCostar :: Corepresentable p => Costar (Corep p) a b -> p a b
fromCostar = cotabulate . runCostar

pushr :: Closed p => (forall x. Applicative (p x)) => p (a , b) c -> p a b -> p a c
pushr = papply . curry' 

pushl :: Closed p => (forall x. Applicative (p x)) => p a c -> p b c -> p a (b -> c)
pushl f g = curry' $ pdivided f g

ppure :: Profunctor p => (forall x. Applicative (p x)) => b -> p a b
ppure b = dimap (const ()) (const b) $ pure ()

pabsurd :: Profunctor p => (forall x. Divisible (p x)) => p Void a
pabsurd = rmap absurd $ conquer

infixr 3 @@@

-- | Profunctorial version of '***' from 'Control.Arrow'.
--
-- @
-- p <*> x ≡ dimap fork eval (p @@@ x)
-- @
--
(@@@) :: Profunctor p => (forall x. Applicative (p x)) => p a1 b1 -> p a2 b2 -> p (a1 , a2) (b1 , b2)
f @@@ g = pappend f g

pappend :: Profunctor p => (forall x. Applicative (p x)) => p a1 b1 -> p a2 b2 -> p (a1 , a2) (b1 , b2)
pappend f g = dimap fst (,) f <*> lmap snd g

-- | Profunctor equivalent of 'Data.Functor.Divisible.divide'.
--
pdivide :: Profunctor p => (forall x. Applicative (p x)) => (a -> (a1 , a2)) -> p a1 b -> p a2 b -> p a b
pdivide f x y = dimap f fst $ pappend x y

-- | Profunctor equivalent of 'Data.Functor.Divisible.divided'.
--
pdivided :: Profunctor p => (forall x. Applicative (p x)) => p a1 b -> p a2 b -> p (a1 , a2) b
pdivided = pdivide id

-- | Profunctor equivalent of '<*>'.
--
papply :: Profunctor p => (forall x. Applicative (p x)) => p a (b -> c) -> p a b -> p a c
papply f x = dimap fork apply (f @@@ x)

-- | Profunctor equivalent of 'liftA2'.
--
pliftA2 :: Profunctor p => (forall x. Applicative (p x)) => ((b1 , b2) -> b) -> p a b1 -> p a b2 -> p a b
pliftA2 f x y = dimap fork f $ pappend x y
