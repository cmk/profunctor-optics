{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
module Data.Profunctor.Fold (
    Fold(..)
  , module Data.Profunctor.Fold
  , module F
  ) where

import Control.Category
import Control.Applicative
import Control.Arrow
import Control.Monad (join)

import Control.Comonad
import Data.Distributive
import Data.Foldable
import Data.Functor.Rep as Functor
import Data.Monoid
import Data.Profunctor.Closed
import Data.Profunctor
import Data.Profunctor.Sieve
import Data.Profunctor.Rep as Profunctor
import Prelude hiding ((.), id, fold, foldl)
import Control.Foldl (Fold(..), FoldM(..), EndoM(..), foldM)
import qualified Data.Strict as S
import qualified Control.Foldl as F hiding (foldOverM, handlesM, HandlerM, foldOver, handles, Handler)
import qualified Data.Profunctor.Optic as O
import Control.Exception.Optic
import System.IO.Unsafe
import Data.IORef
{-
λ> readf myf
"there"
λ> modifyf myf (++" you")
"thereyou"
λ> readIORef io
("hi","there you")
-}

io = unsafePerformIO $ newIORef ("hi","there")

myf :: FoldM IO [Char] [Char]
myf = FoldM (\(x,_) y -> writeIORef io (x,y) >> readIORef io) (readIORef io) (\(x,y) -> pure y)

foldingMl :: Applicative m => O.Lens s s a b -> s -> FoldM m b a
foldingMl o x = O.withLens o $ \sa sbt -> FoldM (\s b -> pure (sbt s b)) (pure x) (pure . sa)

foldingl :: O.Lens s s a b -> s -> Fold b a
foldingl o x = O.withLens o $ \sa sbt -> Fold sbt x sa

withFold :: Fold a b -> (forall x. (x -> a -> x) -> x -> (x -> b) -> r) -> r
withFold (Fold h z k) f = f h z k

--withFoldM f $ \xamx mx mxb -> 
{-
unfold = choose . getCompose . createA1 @Unfoldable (Compose . return . unfold . foldr (<|>) empty . getCompose) . Compose . return
choose :: Alternative f => [f a] -> f a
choose = chooseMap id
-- | Choose one of the values from the list and apply the given function.
chooseMap :: Alternative f => (a -> f b) -> [a] -> f b
chooseMap f = foldr ((<|>) . f) empty
-- | Given a number 'n', return a number between '0' and 'n - 1'.
chooseInt :: Alternative f => Int -> f Int
chooseInt n = chooseMap pure [0 .. n - 1]
-}

--unfoldr :: Unfoldable t => (b -> Maybe (a, b)) -> b -> Maybe (t a)
--Maybe (b, x) -> x
--x -> Maybe (b, x)
--Pastro Env a b, Tambara Env a b
--Lens s t a b -> p s t -> Pastro p a b
--((y, z) -> b) -> p x y -> (a -> (x, z)) -> Pastro p a b
--FoldM (s -> b -> m t) (m s) (s -> m a)
--UnfoldM (s -> b -> m t) (m s) (s -> Either t a)

--moore :: Distributive f => Optic L.Fold (f a) (f b) a b
--moore = corepresented $ \fab fs -> fmap fab $ distribute fs

--mooreOf :: Distributive f => L.Fold a b -> L.Fold (f a) (f b)
--mooreOf = lower cotraverse

-- | Upgrade a more traditional monadic fold to accept the `FoldM` type
withFoldM_ :: Monad m => FoldM m a b -> (forall x . (x -> a -> m x) -> m x -> m x) -> m b
withFoldM_ (FoldM h z k) f = f h z >>= k

withFoldM :: FoldM m a b -> (forall x. (x -> a -> m x) -> m x -> (x -> m b) -> r) -> r
withFoldM (FoldM h z k) f = f h z k

readf :: Monad m => FoldM m a b -> m b
readf x = foldM x []

writef :: Monad m => FoldM m a b -> a -> m b
writef x y = withFoldM_ x $ \h z -> z >>= flip h y

modifyf :: Monad m => FoldM m a b -> (b -> a) -> m b
modifyf x f = withFoldM x $ \h z k -> z >>= (\x -> (fmap f . k) x >>= h x) >>= k

data Myopic p s t = forall a b. Myopic (O.Optic p s t a b) (p a b)

lowerMyopic :: Myopic p s t -> p s t
lowerMyopic (Myopic o p) = o p

instance Profunctor p => Profunctor (Myopic p) where
  dimap f g (Myopic o p) = Myopic (dimap f g . o) p
--previewf

{-
{-| A handler for the upstream input of a `Fold`

    Any lens, traversal, or prism will type-check as a `Handler`
-}
type Handler s a = forall r. O.AFold (Endo (Endo r)) s a

type HandlerM m s a = forall r. O.AFold (Endo (EndoM m r)) s a 

foldMlOf' :: Monad m => O.AFold (Endo (EndoM m r)) s a -> (r -> a -> m r) -> r -> s -> m r
foldMlOf' o f c s = O.foldrOf o f' mempty s `appEndoM` c
  where f' x (EndoM k) = EndoM $ \z -> (f $! z) x >>= k

handles :: Handler s a -> Fold a b -> Fold s b
handles o (Fold h z k) = Fold (O.foldlOf' o h) z k

handlesM :: Monad m => HandlerM m s a -> FoldM m a b -> FoldM m s b
handlesM o (FoldM h z k) = FoldM (foldMlOf' o h) z k
-}


moore :: (s -> (b, a -> s)) -> s -> Fold a b
moore f s = Fold (snd . f) s (fst . f)
{-# INLINE moore #-}

run :: Foldable t => t a -> Fold a b -> b
run t (Fold h z k) = k $! foldl h z t
{-# INLINE run #-}

prefix :: Foldable t => t a -> Fold a b -> Fold a b
prefix s = flip F.fold s . duplicate
{-# INLINE prefix #-}

--leaky
postfix :: Foldable t => Fold a b -> t a -> Fold a b
postfix t s = extend (flip F.fold s) t
{-# INLINE postfix #-}

run1 :: a -> Fold a b -> b
run1 t (Fold h z k) = k $! h z t
{-# INLINE run1 #-}

prefix1 :: a -> Fold a b -> Fold a b
prefix1 x = run1 x . duplicate
{-# INLINE prefix1 #-}

postfix1 :: Fold a b -> a -> Fold a b
postfix1 t a = extend (run1 a) t
{-# INLINE postfix1 #-}

intersperse :: a -> Fold a b -> Fold a b
intersperse a (Fold h z k) = Fold h' S.Nothing (S.maybe (k z) k) where
  h' S.Nothing b  = S.Just (h z b)
  h' (S.Just x) b = S.Just (h (h x a) b)
{-# INLINE intersperse #-}

instance Distributive (Fold a) where
  --distribute x = Fold (\fm a -> fmap (prefix1 a) fm) x (fmap extract)
  distribute = distributeRep
  {-# INLINE distribute #-}

instance Functor.Representable (Fold a) where
  type Rep (Fold a) = [a]
  index = cosieve
  tabulate = cotabulate

instance Costrong Fold where
  unfirst = unfirstCorep
  unsecond = unsecondCorep

instance Closed Fold where
  closed (Fold h z k) = Fold (liftA2 h) (pure z) (\f x -> k (f x))

-- | >>> cosieve (Fold (+) 0 id) [1,2,3]
-- 6
instance Cosieve Fold [] where
  cosieve (Fold h0 z0 k0) as0 = go k0 h0 z0 as0 where
    go k _ z [] = k z
    go k h z (a:as) = go k h (h z a) as
  {-# INLINE cosieve #-}

instance Corepresentable Fold where
  type Corep Fold = []
  cotabulate f = Fold (flip (:)) [] (f . reverse)
  {-# INLINE cotabulate #-}
