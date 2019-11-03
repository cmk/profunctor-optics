module Data.Profunctor.Misc where

import Control.Arrow ((|||),(&&&))
import Control.Category
import Control.Comonad (Comonad(..))
import Control.Monad (join)
import Data.Bifunctor
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
import Data.Profunctor
import Data.Profunctor.Rep
import Data.Profunctor.Sieve
import Data.Void
import Prelude hiding ((.), id)

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

dup :: a -> (a , a)
dup = join (,)

dedup :: (a + a) -> a
dedup = join either id

swp :: (a1 , a2) -> (a2 , a1)
swp = snd &&& fst

swp' :: (a1 + a2) -> (a2 + a1)
swp' = Right ||| Left

assocl :: (a , (b , c)) -> ((a , b) , c)
assocl (a, (b, c)) = ((a, b), c)

assocr :: ((a , b) , c) -> (a , (b , c))
assocr ((a, b), c) = (a, (b, c))

assocl' :: (a + (b + c)) -> ((a + b) + c)
assocl' (Left a)          = Left (Left a)
assocl' (Right (Left b))  = Left (Right b)
assocl' (Right (Right c)) = Right c

assocr' :: ((a + b) + c) -> (a + (b + c))
assocr' (Left (Left a))  = Left a
assocr' (Left (Right b)) = Right (Left b)
assocr' (Right c)        = Right (Right c)

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

fstrong :: Functor f => f a -> b -> f (a , b)
fstrong f b = fmap (,b) f

fchoice :: Traversable f => f (a + b) -> (f a) + b
fchoice = swp' . traverse swp'

pfirst :: Strong p => p a b -> p (a , c) (b , c)
pfirst = first'

psecond :: Strong p => p a b -> p (c , a) (c , b)
psecond = second'

pleft :: Choice p => p a b -> p (a + c) (b + c)
pleft = left'

pright :: Choice p => p a b -> p (c + a) (c + b)
pright = right'

pcurry :: Closed p => p (a , b) c -> p a (b -> c)
pcurry = curry'

puncurry :: Strong p => p a (b -> c) -> p (a , b) c
puncurry = uncurry'

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

coercer :: Profunctor p => Contravariant (p a) => p a c -> p a d
coercer = rmap absurd . contramap absurd

coercer' :: Representable p => Contravariant (Rep p) => p a b -> p a c
coercer' = lift (phantom .)

coercel :: Profunctor p => Bifunctor p => p a c -> p b c
coercel = first absurd . lmap absurd

coercel' :: Corepresentable p => Contravariant (Corep p) => p a b -> p c b
coercel' = lower (. phantom)

strong :: Strong p => ((a , b) -> c) -> p a b -> p a c
strong f = dimap dup f . psecond

costrong :: Costrong p => ((a , b) -> c) -> p c a -> p b a
costrong f = unsecond . dimap f dup

choice :: Choice p => (c -> (a + b)) -> p b a -> p c a
choice f = dimap f dedup . pright

cochoice :: Cochoice p => (c -> (a + b)) -> p a c -> p a b
cochoice f = unright . dimap dedup f

pull :: Strong p => p a b -> p a (a , b)
pull = lmap dup . psecond

parr :: Category p => Profunctor p => (a -> b) -> p a b
parr f = dimap id f id

punarr :: Comonad w => Sieve p w => p a b -> a -> b 
punarr = (extract .) . sieve

returnP :: Category p => Profunctor p => p a a
returnP = parr id

ex1 :: Category p => Profunctor p => p (a , b) b
ex1 = parr snd

ex2 :: Category p => Profunctor p => p (a , b) a
ex2 = parr fst

inl :: Category p => Profunctor p => p a (a + b)
inl = parr Left

inr :: Category p => Profunctor p => p b (a + b)
inr = parr Right

braid :: Category p => Profunctor p => p (a , b) (b , a)
braid = parr swp

braid' :: Category p => Profunctor p => p (a + b) (b + a)
braid' = parr swp'

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

infixr 3 @@@

-- | TODO: Document
--
-- @p <*> x ≡ dimap dup eval (p @@@ x)@
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
papply f x = dimap dup apply (f @@@ x)

-- | Profunctor equivalent of 'liftA2'.
--
pliftA2 :: Profunctor p => (forall x. Applicative (p x)) => ((b1 , b2) -> b) -> p a b1 -> p a b2 -> p a b
pliftA2 f x y = dimap dup f $ pappend x y

ppure :: Profunctor p => (forall x. Applicative (p x)) => b -> p a b
ppure b = dimap (const ()) (const b) $ pure ()

pabsurd :: Profunctor p =>  (forall x. Divisible (p x)) => p Void a
pabsurd = rmap absurd $ conquer
