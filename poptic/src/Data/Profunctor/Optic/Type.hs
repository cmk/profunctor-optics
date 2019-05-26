{-# LANGUAGE UndecidableSuperClasses, TypeOperators , GADTs, DataKinds, KindSignatures, TypeFamilies #-}

{-# LANGUAGE TupleSections, FlexibleInstances, UndecidableInstances #-}

module Data.Profunctor.Optic.Type (
    module Data.Profunctor.Optic.Type
  , module Data.Profunctor.Optic.Type.Class
) where

import Data.Profunctor.Optic.Type.Class 
import Data.Profunctor.Optic.Prelude

--type Optical c s t a b = forall p. c p => Optic p s t a b

--type Optical' c s a = Optical c s s a a

type Optic p s t a b = p a b -> p s t

type Optic' p s a = Optic p s s a a

-- | A witness that @(a ~ s, b ~ t)@.
type Equality s t a b = forall p. Optic p s t a b 

--type Equality s t a b = Optical Equalizing s t a b

type Equality' s a = Equality s s a a

type Iso s t a b = forall p. Profunctor p => Optic p s t a b --Optical Profunctor s t a b

type Iso' s a = Iso s s a a

type AnIso s t a b = Optic (IsoRep a b) s t a b

type AnIso' s a = AnIso s s a a

type Lens s t a b = forall p. Strong p => Optic p s t a b  --Optical Strong s t a b

type Lens' s a = Lens s s a a

type ALens s t a b = Optic (LensRep a b) s t a b

type ALens' s a = ALens s s a a

type Prism s t a b = forall p. Choice p => Optic p s t a b  --Optical Choice s t a b

type Prism' s a = Prism s s a a

type APrism s t a b = Optic (PrismRep a b) s t a b

--type APrism s t a b = Optic (Star (Either a)) s t a b

type APrism' s a = APrism s s a a

type Affine s t a b = forall p. AffineTraversing p => Optic p s t a b --Optical AffineTraversing s t a b

type Affine' s a = Affine s s a a

type AnAffine s t a b = Optic (AffineRep a b) s t a b

type AnAffine' s a = Affine s s a a

type Traversal s t a b = forall p. Traversing p => Optic p s t a b  --Optical Traversing s t a b

type Traversal' s a = Traversal s s a a

type Traversal1 s t a b = forall p. Traversing1 p => Optic p s t a b  --Optical Traversing s t a b

type Traversal1' s a = Traversal1 s s a a

type Fold s a = forall p. Folding p => Optic' p s a  --Optical' Folding s a

type Fold1 s a = forall p. Folding1 p => Optic' p s a 

type AffineFold s a = forall p. AffineFolding p => Optic' p s a  --Optical' AffineFolding s a

type Setter s t a b = forall p. Mapping p => Optic p s t a b  --Optical Mapping s t a b

type Setter' s a = Setter s s a a

type ASetter s t a b = Optic (->) s t a b 

type PrimGetter s a = forall p. OutPhantom p => Optic' p s a -- Optical' OutPhantom s a
--type APrimGetter s a = Optic' Tagged s a

--type Getting r s a = Optic' (Star (Const r)) s a

-- type GetterRep r s a = Optic' (Star (Const r)) s a
-- type AGetter s a = forall r. GetterRep r s a

type Getter s a = forall p. Getting p => Optic' p s a  --Optical' Getting s a

type AGetter r s a = Optic' (Star (Const r)) s a


type PrimReview t b = forall p. InPhantom p => Optic' p t b --Optical InPhantom s t a b
-- type APrimReview t b = Optic' Tagged t b

--type Reviewing r t b = Optic' (Costar (Const r)) t b
--class (InPhantom p, Choice p) => Reviewing p

type Review t b = forall p. Reviewing p => Optic' p t b --Optical' Reviewing t b
-- type Review t b = forall r. Reviewing r t b
-- type AReview t b = Optic' Tagged t b
type AReview t b = forall r. Optic' (Costar (Const r)) t b

type Closure s t a b = forall p. Closed p => Optic p s t a b  --Optical Closed s t a b

type Closure' s a = Closure s s a a

type AClosure s t a b = Optic (ClosureRep a b) s t a b


---------------------------------------------------------------------
-- 
---------------------------------------------------------------------

newtype Paired p c d a b = Paired { runPaired :: p (c,a) (d,b) }

fromTambara :: Profunctor p => Tambara p a b -> Paired p d d a b
fromTambara = Paired . dimap swap swap . runTambara

instance Profunctor p => Profunctor (Paired p c d) where
  dimap f g (Paired pab) = Paired $ dimap (fmap f) (fmap g) pab

instance Strong p => Strong (Paired p c d) where
  second' (Paired pab) = Paired . dimap shuffle shuffle . second' $ pab
   where
    shuffle (x,(y,z)) = (y,(x,z))

instance OutPhantom p => OutPhantom (Paired p c d) where
  ocoerce (Paired pab) = Paired $ ocoerce pab

-- ^ @
-- paired :: Iso s t a b -> Iso s' t' a' b' -> Iso (s, s') (t, t') (a, a') (b, b')
-- paired :: Lens s t a b -> Lens s' t' a' b' -> Lens (s, s') (t, t') (a, a') (b, b')
-- @
paired 
  :: Profunctor p 
  => Optic (Paired p s' t') s t a b 
  -> Optic (Paired p a b) s' t' a' b' 
  -> Optic p (s, s') (t, t') (a, a') (b, b')
paired lab lcd = 
  dimap swap swap . runPaired . lab . Paired . 
  dimap swap swap . runPaired . lcd . Paired

pairing :: Profunctor p => (s -> a) -> (b -> t) -> Optic p (c, s) (d, t) (c, a) (d, b)
pairing f g = between runPaired Paired (dimap f g)

---------------------------------------------------------------------
-- 
---------------------------------------------------------------------

newtype Split p c d a b = Split { runSplit :: p (Either c a) (Either d b) }

fromTambaraSum :: Profunctor p => TambaraSum p a b -> Split p d d a b
fromTambaraSum = Split . dimap swap swap . runTambaraSum

instance Profunctor p => Profunctor (Split p c d) where
  dimap f g (Split pab) = Split $ dimap (fmap f) (fmap g) pab

instance Choice p => Choice (Split p c d) where
  right' (Split pab) = Split . dimap shuffle shuffle . right' $ pab
   where
    shuffle = Right . Left ||| (Left ||| Right . Right)

instance InPhantom p => InPhantom (Split p c d) where
  icoerce (Split pab) = Split $ icoerce pab

-- ^ @
-- split :: Iso s t a b -> Iso s' t' a' b' -> Iso (Either s s') (Either t t') (Either a a') (Either b b')
-- split :: Prism s t a b -> Prism s' t' a' b' -> Lens (Either s s') (Either t t') (Either a a') (Either b b')
-- split :: Getter s t a b -> Getter s' t' a' b' -> Review (Either s s') (Either t t') (Either a a') (Either b b')
-- @
split 
  :: Profunctor p 
  => Optic (Split p s' t') s t a b 
  -> Optic (Split p a b) s' t' a' b' 
  -> Optic p (Either s s') (Either t t') (Either a a') (Either b b')
split lab lcd = 
  dimap swap swap . runSplit . lab . Split . 
  dimap swap swap . runSplit . lcd . Split

splitting :: Profunctor p => (s -> a) -> (b -> t) -> Optic p (Either c s) (Either d t) (Either c a) (Either d b)
splitting f g = between runSplit Split (dimap f g)

---------------------------------------------------------------------
-- 
---------------------------------------------------------------------


--The 'Re' type, and its instances witness the symmetry of 'Profunctor' 
-- and the relation between 'InPhantom' and 'OutPhantom'.

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

instance (Costrong p, InPhantom p) => OutPhantom (Re p s t) where 
    ocoerce (Re p) = Re (p . icoerce)

instance (Cochoice p, OutPhantom p) => InPhantom (Re p s t) where 
    icoerce (Re p) = Re (p . ocoerce)

---------------------------------------------------------------------
-- 
---------------------------------------------------------------------

-- | The 'IsoRep' profunctor precisely characterizes an 'Iso'.
data IsoRep a b s t = IsoRep (s -> a) (b -> t)

instance Functor (IsoRep a b s) where
  fmap f (IsoRep sa bt) = IsoRep sa (f . bt)
  {-# INLINE fmap #-}

instance Profunctor (IsoRep a b) where
  dimap f g (IsoRep sa bt) = IsoRep (sa . f) (g . bt)
  {-# INLINE dimap #-}
  lmap f (IsoRep sa bt) = IsoRep (sa . f) bt
  {-# INLINE lmap #-}
  rmap f (IsoRep sa bt) = IsoRep sa (f . bt)
  {-# INLINE rmap #-}

---------------------------------------------------------------------
-- 
---------------------------------------------------------------------


-- | The 'PrismRep' profunctor precisely characterizes a 'Prism'.
data PrismRep a b s t = PrismRep (b -> t) (s -> Either t a)

instance Functor (PrismRep a b s) where

  fmap f (PrismRep bt seta) = PrismRep (f . bt) (either (Left . f) Right . seta)
  {-# INLINE fmap #-}

instance Profunctor (PrismRep a b) where

  dimap f g (PrismRep bt seta) = PrismRep (g . bt) $
    either (Left . g) Right . seta . f
  {-# INLINE dimap #-}

  lmap f (PrismRep bt seta) = PrismRep bt (seta . f)
  {-# INLINE lmap #-}

  rmap f (PrismRep bt seta) = PrismRep (f . bt) (either (Left . f) Right . seta)
  {-# INLINE rmap #-}

instance Choice (PrismRep a b) where

  left' (PrismRep bt seta) = PrismRep (Left . bt) $ 
    either (either (Left . Left) Right . seta) (Left . Right)
  {-# INLINE left' #-}

  right' (PrismRep bt seta) = PrismRep (Right . bt) $ 
    either (Left . Left) (either (Left . Right) Right . seta)
  {-# INLINE right' #-}



---------------------------------------------------------------------
-- 
---------------------------------------------------------------------


-- | The `LensRep` profunctor precisely characterizes a 'Lens'.
data LensRep a b s t = LensRep (s -> a) (s -> b -> t)

instance Profunctor (LensRep a b) where

  dimap f g (LensRep sa sbt) = LensRep (sa . f) (\s -> g . sbt (f s))

instance Strong (LensRep a b) where

  first' (LensRep sa sbt) =
    LensRep (\(a, _) -> sa a) (\(s, c) b -> ((sbt s b), c))

  second' (LensRep sa sbt) =
    LensRep (\(_, a) -> sa a) (\(c, s) b -> (c, (sbt s b)))

---------------------------------------------------------------------
-- 
---------------------------------------------------------------------

-- | The `LensRep` profunctor precisely characterizes a 'Lens'.
data AffineRep a b s t = AffineRep (s -> Either t a) (s -> b -> t)

idAffineRep :: AffineRep a b a b
idAffineRep = AffineRep Right (\_ -> id)

instance Profunctor (AffineRep u v) where
    dimap f g (AffineRep getter setter) = AffineRep
        (\a -> first g $ getter (f a))
        (\a v -> g (setter (f a) v))

instance Strong (AffineRep u v) where
    first' (AffineRep getter setter) = AffineRep
        (\(a, c) -> first (,c) $ getter a)
        (\(a, c) v -> (setter a v, c))

instance Choice (AffineRep u v) where
    right' (AffineRep getter setter) = AffineRep
        (\eca -> unassoc (second getter eca))
        (\eca v -> second (`setter` v) eca)


---------------------------------------------------------------------
-- 
---------------------------------------------------------------------

-- | The 'ClosureRep' profunctor precisely characterizes 'Closure'.

newtype ClosureRep a b s t = ClosureRep { unClosureRep :: ((s -> a) -> b) -> t }

instance Profunctor (ClosureRep a b) where
  dimap f g (ClosureRep z) = ClosureRep $ \d -> g (z $ \k -> d (k . f))

instance Closed (ClosureRep a b) where
  -- closed :: p a b -> p (x -> a) (x -> b)
  closed (ClosureRep z) = ClosureRep $ \f x -> z $ \k -> f $ \g -> k (g x)

{-
---------------------------------------------------------------------
-- 
---------------------------------------------------------------------

newtype Matched r a b = Matched { runMatched :: a -> Either b r }

instance Profunctor (Matched r) where
    dimap f g (Matched p) = Matched (first g . p . f)

instance Choice (Matched r) where
    right' (Matched p) = Matched (unassocE . fmap p)

instance Strong (Matched r) where
    first' (Matched p) = Matched (\(a,c) -> first (,c) (p a))

instance Costrong (Matched r) where
    unfirst (Matched f) =
       Matched (first fst . f . (, error "Costrong Matched"))

--TODO give this a Traversing instance or else use matching'

---------------------------------------------------------------------
-- 
---------------------------------------------------------------------

newtype Previewed r a b = Previewed { runPreviewed :: a -> Maybe r }

instance Profunctor (Previewed r) where
    dimap f _ (Previewed p) = Previewed (p . f)

instance OutPhantom (Previewed r) where
    ocoerce (Previewed p) = (Previewed p)

instance Choice (Previewed r) where
    right' (Previewed p) = Previewed (either (const Nothing) p)

instance Strong (Previewed r) where
    first' (Previewed p) = Previewed (p . fst)
-}

---------------------------------------------------------------------
-- 
---------------------------------------------------------------------


newtype Pre a b = Pre { runPre :: Maybe a }

instance Phantom (Pre a) where coerce (Pre p) = (Pre p)

instance Functor (Pre a) where
    fmap _ (Pre p) = Pre p

instance Contravariant (Pre a) where
    contramap _ (Pre p) = Pre p

instance Semigroup a => Applicative (Pre a) where
    pure _ = Pre $ Nothing

    (Pre pbc) <*> (Pre pb) = Pre $ pbc <> pb

---------------------------------------------------------------------
-- 
---------------------------------------------------------------------


-- http://hackage.haskell.org/package/lens-4.17/docs/src/Control.Lens.Internal.Context.html#Context

-- | The indexed store can be used to characterize a 'Lens'
-- and is used by 'cloneLens'.
--
-- @'Context' a b t@ is isomorphic to
-- @newtype 'Context' a b t = 'Context' { runContext :: forall f. 'Functor' f => (a -> f b) -> f t }@,
-- and to @exists s. (s, 'Lens' s t a b)@.
--
-- A 'Context' is like a 'Lens' that has already been applied to a some structure.
--data Context a b t = Context (b -> t) a

data Context a b t = Context (b -> t) a 

instance Functor (Context a b) where
    fmap g (Context h a) = Context (g . h) a
    {-# INLINE fmap #-}

instance Profunctor (Context a) where
    dimap f g (Context h a) = Context (g . h . f) a
    {-# INLINE dimap #-}

---------------------------------------------------------------------
-- 
---------------------------------------------------------------------

newtype Indexed p i a b = Indexed { runIndexed :: p (i, a) b }


instance Profunctor p => Profunctor (Indexed p i) where
    dimap f g (Indexed p) = Indexed (dimap (fmap f) g p)
    --dimap f g (Indexed p) = Indexed (dimap (second' f) g p)

instance Strong p => Strong (Indexed p i) where
    first' (Indexed p) = Indexed (lmap unassoc (first' p))



instance Choice p => Choice (Indexed p i) where
    left' (Indexed p) = Indexed $
        lmap (\(i, e) -> first (i,) e) (left' p)


instance Traversing p => Traversing (Indexed p i) where
    wander f (Indexed p) = Indexed $
         wander (\g (i, s) -> f (curry g i) s) p


type IndexedOptic p i s t a b = Indexed p i a b -> p s t
type IndexedOptic' p i s a = IndexedOptic p i s s a a


itraversing 
  :: Traversing p
  => (forall f. Applicative f => (i -> a -> f b) -> s -> f t)
  -> IndexedOptic p i s t a b
itraversing itr (Indexed pab) = wander (\f s -> itr (curry f) s) pab

ifoldMapOf :: IndexedOptic' (Forget r) i s a -> (i -> a -> r) -> s -> r
ifoldMapOf o f = runForget (o (Indexed (Forget (uncurry f))))

icompose 
  :: Profunctor p
  => (i -> j -> k)
  -> (Indexed p i u v -> p s t)
  -> (Indexed (Indexed p i) j a b -> Indexed p i u v)
  -> (Indexed p k a b -> p s t)
icompose ijk stuv uvab ab = icompose' ijk
    (stuv . Indexed)
    (runIndexed . uvab . Indexed . Indexed)
    (runIndexed ab)

icompose' 
  :: Profunctor p
  => (i -> j -> k)
  -> (p (i, u) v -> p s t)
  -> (p (i, (j, a)) b -> p (i, u) v)
  -> (p (k, a) b -> p s t)
icompose' ijk stuv uvab ab = stuv (uvab (lmap f ab))
  where
    f (i, (j, a)) = (ijk i j, a)

itraverseList :: Applicative f => (Int -> a -> f b) -> [a] -> f [b]
itraverseList f = go 0
  where
    go _ []     = pure []
    go i (a:as) = (:) <$> f i a <*> go (i + 1) as

itraversedList :: Traversing p => IndexedOptic p Int [a] [b] a b
itraversedList = itraversing itraverseList

---------------------------------------------------------------------
-- 
---------------------------------------------------------------------


newtype Zipped a b = Zipped { runZipped :: a -> a -> b }

instance Profunctor Zipped where
    dimap f g (Zipped p) = Zipped (\x y -> g (p (f x) (f y)))

instance Closed Zipped where
    closed (Zipped p) = Zipped (\f g x -> p (f x) (g x))

instance Choice Zipped where
    right' (Zipped p) = Zipped (\x y -> p <$> x <*> y)

instance Strong Zipped where
    first' (Zipped p) = Zipped (\(x, c) (y, _) -> (p x y, c))
