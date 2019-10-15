{-# LANGUAGE UndecidableInstances, UndecidableSuperClasses, TypeOperators , GADTs, DataKinds, KindSignatures, TypeFamilies #-}

{-# LANGUAGE ExistentialQuantification #-}

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE QuantifiedConstraints #-}
-- {-# LANGUAGE IncoherentInstances #-}
-- {-# LANGUAGE OverlappingInstances #-}


module Data.Profunctor.Optic.Type (
    module Data.Profunctor.Optic.Type
  , module VL
  , module Export
) where

import Data.Semigroup (First, Last)
import Data.Profunctor.Optic.Prelude

import qualified Data.Profunctor.Optic.Type.VL as VL
import           Control.Applicative
import           Control.Monad
import           Control.Monad.Fix
import           Data.Bifoldable
import Data.Bifunctor as Export (Bifunctor (..))
import           Data.Bitraversable
import           Data.Coerce
import           Data.Data
import           Data.Distributive
import Data.Functor.Classes
import Data.Functor.Apply (Apply(..))

import Linear.V2
import Pipes
import qualified Pipes.Prelude as Pipes

import Data.Functor.Base (NonEmptyF(..))

import Data.Traversable

type Optic p s t a b = p a b -> p s t

type Optic' p s a = Optic p s s a a

type Equality s t a b = forall p. Optic p s t a b 

type Equality' s a = Equality s s a a

type Iso s t a b = forall p. Profunctor p => Optic p s t a b

type Iso' s a = Iso s s a a

type IsoVL s t a b = forall f g. Functor f => Functor g => IsoLike f g s t a b

type IsoVL' s a = IsoVL s s a a 

type IsoLike f g s t a b = Optic (Bistar f g) s t a b

type Over p s t a b = Representable p => Optic p s t a b

type Over' p s a = Representable p => Optic p s s a a

type LensLike f s t a b = Optic (Star f) s t a b

type LensLike' f s a = LensLike f s s a a

type Under p s t a b = Corepresentable p => Optic p s t a b

type Under' p s a = Under p s s a a

type GrateLike g s t a b = Optic (Costar g) s t a b

type GrateLike' g s a = GrateLike g s s a a

-- * 

type Grate s t a b = forall p. Closed p => Optic p s t a b

type Grate' s a = Grate s s a a

--type Lens s t a b = forall p. Tambara (,) p => Optic p s t a b
type Lens s t a b = forall p. Strong p => Optic p s t a b

type Lens' s a = Lens s s a a

type Colens s t a b = forall p. Costrong p => Optic p s t a b

type Colens' s a = Colens s s a a

--type Lens s t a b = forall p. Tambara (+) p => Optic p s t a b
type Prism s t a b = forall p. Choice p => Optic p s t a b

type Prism' s a = Prism s s a a

type Coprism s t a b = forall p. Cochoice p => Optic p s t a b

type Coprism' s a = Coprism s s a a

-- A 'Affine' extracts at most one result, with no monoidal interactions.
type Affine s t a b = forall p. Strong p => Choice p => Optic p s t a b

type Affine' s a = Affine s s a a

--type Coaffine s t a b = forall p. Costrong p => Cochoice p => Optic p s t a b

--type Coaffine' s a = Coaffine s s a a

-- *


--type Traversal s t a b = forall p. Tambara (Church _ _) p => Optic p s t a b
type Traversal s t a b = forall p. Applicative (Rep p) => Over p s t a b

type Traversal' s a = Traversal s s a a

--type CotraversalVL s t a b = forall f g. (Applicative f, Functor g) => AdapterLike f g s t a b
type Cotraversal s t a b = forall p. Distributive (Corep p) => Under p s t a b

-- A 'Traversal1' extracts at least one result.
--type Traversal1 s t a b = forall p. Apply (Rep p) => Over p s t a b

--type Traversal1' s a = Traversal1 s s a a


--type Fold s a = forall p. (forall x. Contravariant (p x), Biapplicative p) => Optic' p s a
--type Fold s a = forall p. RPhantom p => Strong p => Optic' p s a
type Fold s a = forall p. Applicative (Rep p) => Contravariant (Rep p) => Over' p s a

type FoldLike r s a = LensLike' (Const r) s a

-- A 'Fold0' extracts at most one result.
type Fold0 s a = forall p. Choice p => Contravariant (Rep p) => Over' p s a

type Fold1 s a = forall p. Apply (Rep p) => Contravariant (Rep p) => Over' p s a

type Unfold t b = forall p. Distributive (Corep p) => Contravariant (Corep p) => Under' p t b

type UnfoldLike r t b = GrateLike' (Const r) t b

-- A 'Unfold0' extracts at least one result. should be able to do this w/ a GrateLike / Cotraversal
--type Unfold0 t b = forall p. Strong p => Contravariant (Corep p) => Under' p t b

type PrimGetter s t a b = forall p. Contravariant (Rep p) => Over p s t a b

type PrimGetter' s a = PrimGetter s s a a

type PrimReview s t a b = forall p. Contravariant (Corep p) => Under p s t a b

type PrimReview' t b = PrimReview t t b b

-- A 'Getter' extracts exactly one result.
--type Getter s a = forall p . Strong p => Representable p => Contravariant (Rep p) => p a b -> p s t
--type Getter s a = forall p. Strong p => Contravariant (Rep p) => Over' p s a
type Getter s a = forall p. Contravariant (Rep p) => Over' p s a

--type Review t b = forall p. Choice p => Contravariant (Corep p) => Under' p t b

type Review t b = forall p. Contravariant (Corep p) => Under' p t b



-- * Setter
type Setter s t a b = forall p. Distributive (Rep p) => Over p s t a b
--type SetterVL s t a b = forall f. F.Representable f => LensLike f s t a b

type Setter' s a = Setter s s a a

type Resetter s t a b = forall p. Applicative (Corep p) => Under p s t a b
--type ResetterVL s t a b = forall f. Representable f => Applicative f => GrateLike f s t a b

type Resetter' s a = Resetter s s a a

type ASetter s t a b = LensLike Identity s t a b

type AResetter s t a b = GrateLike Identity s t a b

overLike :: ((a -> b) -> s -> t) -> ASetter s t a b
overLike sec = between Star runStar $ \f -> Identity . sec (runIdentity . f)

-- | TODO: Document
--
underLike :: ((a -> b) -> s -> t) -> AResetter s t a b
underLike sec = between Costar runCostar $ \f -> sec (f . Identity) . runIdentity

-- | TODO: Document
--
cloneOver :: LensLike (Rep p) s t a b -> Over p s t a b
cloneOver = between fromStar star 

-- | TODO: Document
--
cloneUnder :: GrateLike (Corep p) s t a b -> Under p s t a b
cloneUnder = between fromCostar costar 

closed' :: Under p (c -> a) (c -> b) a b
closed' = lower cotraverse

-- ^ @
-- under :: Resetter s t a b -> (a -> b) -> s -> t
-- @
--
-- Demote a resetter to a semantic editor combinator.
--
-- @
-- under :: Prism s t a b -> Traversal s t a b
-- under :: Grid s t a b -> Traversal s t a b
-- under :: Adapter s t a b -> Lens s t a b
-- @
--
-- Covert an 'AdapterLike' optic into a 'LensLike' optic.
--
-- Note: this function is unrelated to the lens package's @under@ function.
--under :: AResetter s t a b -> (a -> b) -> s -> t
--under l f = l (f . runIdentity) . Identity


--https://r6research.livejournal.com/27858.html

type p :~> q = forall x y. p x y -> q x y

--FreeStrong (IsoRep a b) s t = IsoRep a b s (s -> t) = (s -> a, b -> s -> t)
--FreeChoice (IsoRep a b) s t ≅ (s -> (Either a t), b -> t).

newtype FreeStrong p s t = FreeStrong (p s (s -> t))

instance Profunctor p => Profunctor (FreeStrong p) where
  dimap l r (FreeStrong p) = FreeStrong (dimap l (dimap l r) p)

instance Profunctor p => Strong (FreeStrong p) where
  first' (FreeStrong p) = FreeStrong (dimap fst first p)

mapFreeStrong :: (Profunctor p, Profunctor q) => (p :~> q) -> (FreeStrong p :~> FreeStrong q)
mapFreeStrong eta (FreeStrong p) = FreeStrong (eta p)

lowerFS :: Strong p => FreeStrong p a b -> p a b
lowerFS (FreeStrong p) = papply p

unitFS :: Profunctor p => p :~> FreeStrong p
unitFS p = FreeStrong (rmap const p)

-- | 'counit' preserves strength.
-- <https://r6research.livejournal.com/27858.html>
counitFS :: Strong p => FreeStrong p :~> p
counitFS (FreeStrong p) = dimap dup eval (first' p)

toFreeStrong :: Profunctor p => Pastro p a b -> FreeStrong p a b
toFreeStrong (Pastro l m r) = FreeStrong (dimap (fst . r) (\y a -> l (y, (snd (r a)))) m)

toPastro :: FreeStrong p a b -> Pastro p a b
toPastro (FreeStrong p) = Pastro eval p dup

upsert :: Optic (Costar Maybe) s t a b -> (Maybe a -> b) -> Maybe s -> t
upsert p = runCostar . p . Costar

upsert' :: Optic (Costar Maybe) s t a b -> b -> Maybe s -> t
upsert' p b = runCostar . p $ Costar (const b)

achroma
    :: Strong p
    => TambaraL NonEmptyF p
    => (s -> a)             -- ^ view
    -> (Maybe s -> b -> t)  -- ^ mset
    -> Optic p s t a b
achroma sa msbt = dimap (\s -> (Just s, sa s)) (uncurry msbt) . dimap swp swp . embedl

data Cat = Cat
    { _catName  :: String
    , _catOwner :: Maybe String
    , _catLifes :: Maybe Int
    }
  deriving Show

catName :: Strong p => TambaraL NonEmptyF p => Optic p Cat Cat String String
catName = achroma _catName $ \ms n ->
    maybe (Cat n Nothing Nothing) (\s -> s {_catName = n }) ms

{-
catName' :: Strong p => TambaraL NonEmptyF p => Optic p Cat Cat String String
catName' = achroma _catName $ \ms n ->
    maybe (Cat n def def) (\s -> s {_catName = n }) ms
-}

catLifes  :: Strong p => Optic p Cat Cat (Maybe Int) (Maybe Int)
catLifes
    = dimap (\(Cat n o l) -> ((n, o), l)) (\((n, o), l) -> Cat n o l)
    . second'

--felix :: Cat
--felix = review catName "Felix"  & catLifes ?~ 7

type SLens s t a b = forall p. Tambara (,) p => Product (,) p => Optic p s t a b

--type CLens s t a b = forall p. Category p => Strong p => Optic p s t a b

--v2 :: Semigroupal p => Optic p (V2 a) (V2 b) a b
v2 :: SLens (V2 a) (V2 b) a b
v2 p = dimap (\(V2 x y) -> (x, y)) (\(x, y) -> V2 x y) (p *** p)

firstNSecond' :: SLens (a, a, c) (b, b, c) a b
firstNSecond' p = dimap group group' (embedl (p *** p)) where
  group  (x, y, z) = ((x, y), z)
  group' ((x, y), z) = (x, y, z)


data FunList a b t = Done t | More a (FunList a b (b -> t)) -- deriving Functor

instance Functor (FunList a b) where
  fmap f (Done t) = Done (f t)
  fmap f (More x l) = More x (fmap (f .) l)

instance Applicative (FunList a b) where
  pure = Done
  Done f <*> fa = fmap f fa
  More x l <*> l' = More x (fmap flip l <*> l')
  --More s r <*> fa = More s (flip <$> r <*> fa)

instance (a ~ b) => Comonad (FunList a b) where
  extract (Done a) = a
  extract (More s r) = extract r s
  extend f (Done a) = Done (f (Done a))
  extend f (More s r) = More s (extend (\r' s' -> f (More s' r')) r)

single :: a -> FunList a b b
single x = More x (Done id)

fuse :: FunList b b t -> t
fuse (Done t) = t
fuse (More x l) = fuse l x

newtype RotateFunList b t a = Rotate { unrotate :: FunList a b t }

out :: FunList a b t -> t + (a, FunList a b (b -> t))
out (Done t) = Left t
out (More x l) = Right (x, l)

inn :: t + (a, FunList a b (b -> t)) -> FunList a b t
inn (Left t) = Done t
inn (Right (x, l)) = More x l

traversing :: Choice p => Product (,) p => Product (+) p => p a b -> p (FunList a c t) (FunList b c t)
traversing k = dimap out inn (embedr (k *** (traversing k)))

instance (Choice p, Product (,) p, Product (+) p) => TambaraR (RotateFunList r) p where
  embedr = dimap unrotate Rotate . traversing

{-
instance (Product (,) p, Product (+) p) => Tambara (RotateFunList r) p where
  embdr p = dimap (out . unrotate) (Rotate . inn) (embdr (p *** (embdr p)))




profunctor arrow wrapper / pipe arrow wrapper / pipe profunctor wrapper
Semigroupal cat?

run :: Monad m => Producer s m r -> Consumer t m r -> Pipe s t m r -> m r
run x y z = runEffect $ x >-> z >-> y

runRead :: Monad m => Producer s m s -> (s -> a) -> m a
runRead p f = run (f <$> p) await $ Pipes.map f

runReadWrite :: Monad m => Producer s m s -> Consumer t m () -> (s -> t) -> m ()
runReadWrite p q f = run (void p) q $ Pipes.map f 

runWriteOnly :: Monad m => Consumer t m () -> (b -> t) -> m ()
runWriteOnly q f = run (pure ()) q $ Pipes.map f

data IOP m t s = IOP (t -> m ()) (m s)

writeout fp x y = Environment x (IOP (writeFile fp) (readFile fp)) y
  :: FilePath
     -> ((z -> String) -> b)
     -> (a -> z -> String)
     -> Environment (IOP IO) a b

foo :: F.Fold a b1 -> Environment p a b2
foo = F.purely $ \xax x xb -> Environment ($x) undefined (flip xax)

foo :: Optic (->) s t a b -> ((s -> y) -> a) -> p t y -> Environment p b a
foo o x y = Environment x y (flip (set o))

foo :: Optic (Re (->) x s1) s2 t x s1 -> ((s1 -> y) -> b) -> p x y -> Environment p s2 b
foo o x y = Environment x y (flip (set $ re o))

\o x y -> Environment x y (flip (set o))











contents' :: TraversalP s t a b -> s -> [a]
contents' tr = getConstant . runUpStar (tr (UpStar (\a -> Constant [a])))

Finally, the unsafe concrete firstNSecond example:

firstNSecond :: Traversal (a, a, c) (b, b, c) a b
firstNSecond = Traversal c f where
  c (a1, a2, _)  = [a1, a2]
  f (bs, (_, _, x)) = (head bs, (head . tail) bs, x)
could be adapted to a profunctor traversal as follows:

firstNSecond' :: TraversalP (a, a, c) (b, b, c) a b
firstNSecond' pab = dimap group group' (first' (pab `par` pab)) where
  group  (x, y, z) = ((x, y), z)
  group' ((x, y), z) = (x, y, z)


Found hole: _ :: (Corep p (c, a) -> (c, b)) -> Corep p a -> b

(f (c,a) -> (c,b)) -> f a

foo :: ((c, b) -> (c, a)) -> b -> a
foo g fa = g' fa where g' (a, fa) = g (a, fa)

grt :: Grate a t a t
grt = inverted id id

λ> over _1 (+1) (1,2)
(2,2)
λ> grt = grate id id
λ> over grt (+1) 1

toLensLike :: AdapterLike f Identity s t a b -> LensLike f s t a b
toLensLike o h = lower' o h runIdentity Identity -- l f = l (f . runIdentity) . Identity 

--fromLensLike :: AdapterLike f Identity s t a b -> LensLike f s t a b
--fromLensLike o h = lower o h Identity runIdentity 

toLensLike' o h = lower' o h getConst Const 

toGrateLike :: AdapterLike Identity g s t a b -> GrateLike g s t a b
toGrateLike o h = colower o h runIdentity Identity

toGrateLike' o h = colower o h getConst Const


lift :: LensLike f s t a b -> AdapterLike f Identity s t a b
lift l f = l (f . Identity) . runIdentity
-}



---------------------------------------------------------------------
-- 'Re'
---------------------------------------------------------------------


--The 'Re' type, and its instances witness the symmetry of 'Profunctor' 

newtype Re p s t a b = Re { runRe :: p b a -> p t s }

instance Profunctor p => Profunctor (Re p s t) where
    dimap f g (Re p) = Re (p . dimap g f)

instance Cochoice p => Choice (Re p s t) where
    right' (Re p) = Re (p . unright)

instance Costrong p => Strong (Re p s t) where
    first' (Re p) = Re (p . unfirst)

instance Choice p => Cochoice (Re p s t) where
    unright (Re p) = Re (p . right')

instance Strong p => Costrong (Re p s t) where
    unfirst (Re p) = Re (p . first')
