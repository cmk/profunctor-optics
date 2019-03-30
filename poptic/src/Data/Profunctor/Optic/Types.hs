{-# LANGUAGE UndecidableSuperClasses, TypeOperators , GADTs, DataKinds, KindSignatures, TypeFamilies #-}

{-# LANGUAGE TupleSections, FlexibleInstances, UndecidableInstances #-}

module Data.Profunctor.Optic.Types (
    module Data.Profunctor.Optic.Types
  , module Data.Profunctor.Optic.Types.Class
) where

import Data.Profunctor.Optic.Types.Class 

type Optical c s t a b = forall p. c p => Optic p s t a b

type Optical' c s a = Optical c s s a a

type Optic p s t a b = p a b -> p s t

type Optic' p s a = Optic p s s a a

type Equality s t a b = Optical Equalizing s t a b

type Equality' s a = Equality s s a a

type Iso s t a b = Optical Profunctor s t a b

type Iso' s a = Iso s s a a

type AnIso s t a b = Optic (IsoP a b) s t a b

type AnIso' s a = AnIso s s a a

type Lens s t a b = Optical Strong s t a b

type Lens' s a = Lens s s a a

type ALens s t a b = Optic (LensP a b) s t a b

type ALens' s a = ALens s s a a

type Prism s t a b = Optical Choice s t a b

type Prism' s a = Prism s s a a

type APrism s t a b = Optic (PrismP a b) s t a b

type APrism' s a = APrism s s a a

type Affine s t a b = Optical AffineTraversing s t a b

type Affine' s a = Affine s s a a

type AnAffine s t a b = Optic (AffineP a b) s t a b

type AnAffine' s a = Affine s s a a

type Traversal s t a b = Optical Traversing s t a b

type Traversal' s a = Traversal s s a a

type Fold s a = Optical' Folding s a

type AffineFold s a = Optical' AffineFolding s a

-- See http://conal.net/blog/posts/semantic-editor-combinators
type Setter' s a = Setter s s a a

type Setter s t a b = Optical Mapping s t a b

type PrimGetter s t a b = Optical Bicontravariant s t a b

type Getter s a = Optical' Getting s a

type AGetter s a = Optic' (Forget a) s a 

type PrimReview s t a b = Optical Bifunctor s t a b

type Review t b = Optical' Reviewing t b

type AReview t b = Optic' Tagged t b

-- | A closure (http://r6research.livejournal.com/28050.html)
type Closure s t a b = Optical Closed s t a b

type Closure' s a = Closure s s a a

type AClosure s t a b = Optic (ClosureP a b) s t a b


---------------------------------------------------------------------
-- 
---------------------------------------------------------------------


--The 'Re' type, and its instances witness the symmetry of 'Profunctor' 
-- and the relation between 'Bifunctor' and 'Bicontravariant'.

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

instance Bifunctor p => Bicontravariant (Re p s t) where 
    cimap f g (Re p) = Re (p . bimap g f)

instance Bicontravariant p => Bifunctor (Re p s t) where 
    bimap f g (Re p) = Re (p . cimap g f)


---------------------------------------------------------------------
-- 
---------------------------------------------------------------------

-- | The 'IsoP' profunctor precisely characterizes an 'Iso'.
data IsoP a b s t = IsoP (s -> a) (b -> t)

instance Functor (IsoP a b s) where
  fmap f (IsoP sa bt) = IsoP sa (f . bt)
  {-# INLINE fmap #-}

instance Profunctor (IsoP a b) where
  dimap f g (IsoP sa bt) = IsoP (sa . f) (g . bt)
  {-# INLINE dimap #-}
  lmap f (IsoP sa bt) = IsoP (sa . f) bt
  {-# INLINE lmap #-}
  rmap f (IsoP sa bt) = IsoP sa (f . bt)
  {-# INLINE rmap #-}

---------------------------------------------------------------------
-- 
---------------------------------------------------------------------


-- | The 'PrismP' profunctor precisely characterizes a 'Prism'.
data PrismP a b s t = PrismP (b -> t) (s -> Either t a)

-- | @type 'PrismP'' a s t = 'PrismP' a a s t@
type PrismP' a = PrismP a a

instance Functor (PrismP a b s) where

  fmap f (PrismP bt seta) = PrismP (f . bt) (either (Left . f) Right . seta)
  {-# INLINE fmap #-}

instance Profunctor (PrismP a b) where

  dimap f g (PrismP bt seta) = PrismP (g . bt) $
    either (Left . g) Right . seta . f
  {-# INLINE dimap #-}

  lmap f (PrismP bt seta) = PrismP bt (seta . f)
  {-# INLINE lmap #-}

  rmap f (PrismP bt seta) = PrismP (f . bt) (either (Left . f) Right . seta)
  {-# INLINE rmap #-}

instance Choice (PrismP a b) where

  left' (PrismP bt seta) = PrismP (Left . bt) $ 
    either (either (Left . Left) Right . seta) (Left . Right)
  {-# INLINE left' #-}

  right' (PrismP bt seta) = PrismP (Right . bt) $ 
    either (Left . Left) (either (Left . Right) Right . seta)
  {-# INLINE right' #-}



---------------------------------------------------------------------
-- 
---------------------------------------------------------------------


-- | The `LensP` profunctor precisely characterizes a 'Lens'.
data LensP a b s t = LensP (s -> a) (s -> b -> t)

instance Profunctor (LensP a b) where

  dimap f g (LensP sa sbt) = LensP (sa . f) (\s -> g . sbt (f s))

instance Strong (LensP a b) where

  first' (LensP sa sbt) =
    LensP (\(a, _) -> sa a) (\(s, c) b -> ((sbt s b), c))

  second' (LensP sa sbt) =
    LensP (\(_, a) -> sa a) (\(c, s) b -> (c, (sbt s b)))

---------------------------------------------------------------------
-- 
---------------------------------------------------------------------

-- | The `LensP` profunctor precisely characterizes a 'Lens'.
data AffineP a b s t = AffineP (s -> Either t a) (s -> b -> t)

sellAffineP :: AffineP a b a b
sellAffineP = AffineP Right (\_ -> id)

instance Profunctor (AffineP u v) where
    dimap f g (AffineP getter setter) = AffineP
        (\a -> first g $ getter (f a))
        (\a v -> g (setter (f a) v))

instance Strong (AffineP u v) where
    first' (AffineP getter setter) = AffineP
        (\(a, c) -> first (,c) $ getter a)
        (\(a, c) v -> (setter a v, c))

instance Choice (AffineP u v) where
    right' (AffineP getter setter) = AffineP
        (\eca -> assoc (second getter eca))
        (\eca v -> second (`setter` v) eca)
      where
        assoc :: Either a (Either b c) -> Either (Either a b) c
        assoc (Left a)          = Left (Left a)
        assoc (Right (Left b))  = Left (Right b)
        assoc (Right (Right c)) = Right c


---------------------------------------------------------------------
-- 
---------------------------------------------------------------------

-- | The 'ClosureP' profunctor precisely characterizes 'Closure'.

newtype ClosureP a b s t = ClosureP { unClosureP :: ((s -> a) -> b) -> t }

instance Profunctor (ClosureP a b) where
  dimap f g (ClosureP z) = ClosureP $ \d -> g (z $ \k -> d (k . f))


instance Closed (ClosureP a b) where
  -- closed :: p a b -> p (x -> a) (x -> b)
  closed (ClosureP z) = ClosureP $ \f x -> z $ \k -> f $ \g -> k (g x)


---------------------------------------------------------------------
-- 
---------------------------------------------------------------------

newtype Matched r a b = Matched { runMatched :: a -> Either b r }

instance Profunctor (Matched r) where
    dimap f g (Matched p) = Matched (first g . p . f)

instance Choice (Matched r) where
    right' (Matched p) = Matched (unassocE . fmap p)

unassocE :: Either a (Either b c) -> Either (Either a b) c
unassocE (Left a)          = Left (Left a)
unassocE (Right (Left b))  = Left (Right b)
unassocE (Right (Right c)) = Right c

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

instance Bicontravariant (Previewed r) where
    cimap f _ (Previewed p) = Previewed (p . f)

instance Choice (Previewed r) where
    right' (Previewed p) = Previewed (either (const Nothing) p)

instance Strong (Previewed r) where
    first' (Previewed p) = Previewed (p . fst)


---------------------------------------------------------------------
-- 
---------------------------------------------------------------------


newtype Indexed p i a b = Indexed { runIndexed :: p (i, a) b }


instance Profunctor p => Profunctor (Indexed p i) where
    dimap f g (Indexed p) = Indexed (dimap (fmap f) g p)
    --dimap f g (Indexed p) = Indexed (dimap (second' f) g p)

instance Strong p => Strong (Indexed p i) where
    first' (Indexed p) = Indexed (lmap unassoc (first' p))

unassoc :: (a,(b,c)) -> ((a,b),c)
unassoc (a,(b,c)) = ((a,b),c)

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



