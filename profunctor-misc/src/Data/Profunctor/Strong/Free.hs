module Data.Profunctor.Strong.Free where

import Data.Bifunctor
import Data.Profunctor
import Data.Profunctor.Misc
import Data.Profunctor.Monad
import Data.Profunctor.Strong

newtype FreeStrong p s t = FreeStrong (p s (s -> t))

instance Profunctor p => Profunctor (FreeStrong p) where
  dimap l r (FreeStrong p) = FreeStrong (dimap l (dimap l r) p)

instance Profunctor p => Strong (FreeStrong p) where
  first' (FreeStrong p) = FreeStrong (dimap fst first p)

instance ProfunctorFunctor FreeStrong where
  promap eta (FreeStrong p) = FreeStrong (eta p)

instance ProfunctorMonad FreeStrong where
  proreturn p = FreeStrong (rmap const p)
  
  projoin (FreeStrong p) = peval p

-- | 'counitFS' preserves strength.
--
-- See <https://r6research.livejournal.com/27858.html>.
--
counitFS :: Strong p => FreeStrong p :-> p
counitFS (FreeStrong p) = dimap fork apply (first' p)

toPastro :: FreeStrong p a b -> Pastro p a b
toPastro (FreeStrong p) = Pastro apply p fork

fromPastro :: Profunctor p => Pastro p a b -> FreeStrong p a b
fromPastro (Pastro l m r) = FreeStrong (dimap (fst . r) (\y a -> l (y, (snd (r a)))) m)
