module Data.Semiring.Cayley where

import Data.Profunctor
import Data.Profunctor.Closed 

import Data.Semiring

import Control.Applicative
import Control.Monad




type Grate s t a b = forall p. Closed p => p a b -> p s t

grate :: (((s -> a) -> b) -> t) -> Grate s t a b
grate f pab = dimap (flip ($)) f (closed pab)

(•) :: (Monoid a, Semiring a) => End a -> End a -> End a
(End f) • (End g) = End $ \y -> f one >< g one <> y

repr :: (Monoid a, Semiring a) => End a -> End (End a)
repr f = End $ \g -> f • g

-- | repr . abst = id 
abst :: (Monoid a, Semiring a) => End (End a) -> End a
abst (End f) = f $ End (one <>)

-- This is a Grate'.
abst' :: (Monoid a, Semiring a) => ((a -> a) -> t) -> t
abst' f = f (one <>)

abstracted :: (Monoid s, Semiring s) => Grate s t s t
abstracted = grate abst' 

-- type Cayley = Compose End End
-- Cayley a ~ End (End a)
-- Cayley a ~ Over' a a
-- https://www.reddit.com/r/haskell/comments/3v6zs6/folds_are_are_closed_corepresentable_profunctors/
newtype Cayley a = Cayley { runCayley :: (a -> a) -> a -> a } -- deriving Generic

instance Semigroup (Cayley a) where
  (Cayley f) <> (Cayley g) = Cayley $ \h -> f h . g h -- liftA2 (.)

instance Monoid (Cayley a) where
  mempty = Cayley $ const id

instance Semiring (Cayley a) where
  (Cayley f) >< (Cayley g) = Cayley $ f . g


repr1 :: (Monoid a, Semiring a) => a -> Cayley a
repr1 x = Cayley $ \ h y -> x >< h zero <> y

abst1 :: (Monoid a, Semiring a) => Cayley a -> a
abst1 (Cayley f) = f (one <>) zero 


{-
λ> import Orphans
λ> foo = repr1 False
λ> bar = repr1 True
λ> abst1 $ (foo <> bar) >< (foo >< bar)
False
λ> (False <> True) >< (False >< True)
False


λ> foo x = \ h y -> x >< h one <> y
λ> :t foo

abst :: (Monoid a, Semiring a) => End (a -> a) -> a -> a
abst (End f) = f (one <>)

-}

-- TODO is there a type upstream for this?
-- Exponential of the Cartesian product.
newtype Exp f g x = Exp { runExp :: forall y. (x -> y) -> (f y -> g y) }

instance Functor (Exp f g) where fmap f m = Exp (\k -> runExp m (k . f ))


uncurry' :: (Functor f, Functor g, Functor h) => (forall x . f x -> Exp g h x ) -> (forall x . (f x , g x ) -> h x )
uncurry' f = \fgx -> runExp (f (fst fgx )) id (snd fgx )

curry' :: (Functor f, Functor g, Functor h) => (forall x . (f x , g x ) -> h x ) -> (forall x . f x -> Exp g h x )
curry' f = \fx -> Exp (\t -> \gy -> f (fmap t fx , gy))


--newtype CayleyT f x = CayleyT { runCayleyT :: Ran (Exp f f) (Exp f f) x } deriving Functor

-- A right Kan extension over Exp.
newtype CayleyT f a = CayleyT { runCayleyT :: forall x. (a -> Exp f f x) -> Exp f f x }

instance Functor (CayleyT f) where

  fmap f c = CayleyT $ \g -> runCayleyT c (g . f)
  {-# INLINE fmap #-}


instance Applicative (CayleyT f) where

  pure x = CayleyT ($ x)

  CayleyT f <*> CayleyT c = CayleyT $ \ g -> f $ \ a -> c (g . a)


instance Alternative (CayleyT f) where

  empty = CayleyT $ \k -> Exp (\c x -> x )

  (CayleyT a) <|> (CayleyT b) = CayleyT $ \sk -> Exp (\f fk -> runExp (a sk) f (runExp (b sk) f fk))


instance Monad (CayleyT f) where

  return = pure

  CayleyT c >>= f = CayleyT $ \g -> c (\a -> runCayleyT (f a) g)

{-

instance MonadPlus (CayleyT f) where

  mzero = empty

  mplus = (<|>)

repn2 :: Monad m => m a -> CayleyT m a
repn2 x = CayleyT (Ran (\g -> Exp (\h m -> (x >>= \a -> runExp (g a) h m))))

--TODO see if we can make this work
--repn2' :: Applicative f => f a -> CayleyT f a
--repn2' x = CayleyT (Ran (\g -> Exp (\h m -> (x <**> \a -> runExp (g a) h m))))

abst2 :: MonadPlus m => CayleyT m a -> m a
abst2 (CayleyT (Ran f)) = runExp (f (\x -> Exp (\h m -> return (h x ) `mplus` m))) id mzero

abst2' :: Alternative f => CayleyT f a -> f a
abst2' (CayleyT (Ran f)) = runExp (f (\x -> Exp (\h m -> pure (h x ) <|> m))) id empty

anyof :: Alternative f => [a] -> f a
anyof [ ] = empty
anyof (x : xs) = anyof xs <|> pure x

-- much faster to do this way. we run it first on CayleyT [ ], and then we flatten back the result to lists
anyof' :: [a] -> [a]
anyof' xs = abst2' (anyof xs)


-}
-- | The sum of a collection of actions, generalizing 'concat'.
--
-- asum [Just "Hello", Nothing, Just "World"]
-- Just "Hello"
--asum :: (Foldable t, Alternative f) => t (f a) -> f a
--asum = foldr (<|>) empty


{-
-- Represents the closure of Day convolution
newtype ED f g x = ED { runED :: forall y. f y -> g (x, y) }

instance Functor g => Functor (ED f g) where

  fmap f (ED g) = ED $ \y -> fmap (\(a, b) -> (f a, b)) (g y)



newtype CayleyT f x = CayleyT { runCayleyT :: ED (Exp f f) (Exp f f) x }

instance Functor f => Functor (CayleyT f) where

  fmap f (CayleyT z) = CayleyT (ED (\fx -> fmap (\(x , y) -> (f x, y)) (runED z fx)))


instance Functor f => Applicative (CayleyT f ) where

  pure v = CayleyT (ED (\f -> fmap (\y -> (v, y)) f ))

  (CayleyT (ED h)) <*> (CayleyT (ED v)) = fmap (uncurry ($)) (CayleyT (ED (\f -> fmap (\(b, (a, y)) -> ((a, b), y)) (v (h f )))))


instance Functor f => Alternative (CayleyT f ) where
  empty = CayleyT (ED (const (Exp (\h x -> x ))))

  CayleyT f <|> CayleyT g = CayleyT (ED (\h -> Exp (\j i -> runExp (runED f h) j (runExp (runED g h) j i))))


rep :: Alternative f => f a -> CayleyT f a
rep x = CayleyT (ED (\g -> Exp (\f fx -> runExp g (flip (curry f)) empty <*> x <|> fx )))

abs :: Alternative f => CayleyT f a -> f a
abs (CayleyT (ED f )) = runExp (f (Exp (\g i -> pure (g ()) <|> i))) fst empty

-}


{-
foo = Nothing
bar = Just ("there"++)
baz = Just " !"

foo <|> bar <*> baz

abs $ rep foo <|> rep bar <*> rep baz
-}

