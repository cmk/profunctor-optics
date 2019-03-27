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

type AnIso s t a b = Optic (Iso_ a b) s t a b

type AnIso' s a = AnIso s s a a

type Lens s t a b = Optical Strong s t a b

type Lens' s a = Lens s s a a

type ALens s t a b = Optic (Lens_ a b) s t a b

type ALens' s a = ALens s s a a

type Prism s t a b = Optical Choice s t a b

type Prism' s a = Prism s s a a

type APrism s t a b = Optic (Prism_ a b) s t a b

type APrism' s a = APrism s s a a

type Affine s t a b = Optical AffineTraversing s t a b

type Affine' s a = Affine s s a a

type AnAffine s t a b = Optic (Affine_ a b) s t a b

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

-- | A grate (http://r6research.livejournal.com/28050.html)
type Grate s t a b = Optical Closed s t a b

type Grate' s a = Grate s s a a

type AGrate s t a b = Optic (Grate_ a b) s t a b

--type AGrate r s t a b = Optic (Environment r) s t a b

newtype Grate_ a b s t = Grate_ (((s -> a) -> b) -> t)

{-
data Environment p a b where
  Environment :: ((s -> a) -> b) -> p x a -> (a -> s -> x) -> Environment p a b
-}

instance Profunctor (Grate_ a b) where
  dimap f g (Grate_ z) = Grate_ $ \d -> g (z $ \k -> d (k . f))

instance Closed (Grate_ a b) where
  closed (Grate_ z) = Grate_ $ \f x -> z $ \k -> f $ \g -> k (g x)

grate :: (((s -> a) -> b) -> t) -> Grate s t a b
grate f pab = dimap (flip ($)) f (closed pab)

grate' :: (s -> a) -> (b -> t) -> Grate s t a b
grate' sa bt = grate $ isoToGrate sa bt

withGrate :: AGrate s t a b -> ((s -> a) -> b) -> t
withGrate g =
 let Grate_ h = (g (Grate_ $ \f -> f id))

  in h

cloneGrate :: AGrate s t a b -> Grate s t a b
cloneGrate g = grate (withGrate g)

cotraversed :: Distributive f => Grate (f a) (f b) a b
cotraversed = grate $ \f -> cotraverse f id

modGrate :: (((s -> a) -> b) -> t) -> (a -> b) -> (s -> t)
modGrate g adj s = g (\get -> adj (get s))

-- Every isomorphism is a grate.
isoToGrate :: (s -> a) -> (b -> t) -> ((s -> a) -> b) -> t
isoToGrate get beget build = beget (build get)





---------------------------------------------------------------------
-- 
---------------------------------------------------------------------


--The Re type, and its instances witness the symmetry of Profunctor and the relation between Bifunctor and Bicontravariant:

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

-- | The 'Iso_' profunctor characterizes an 'Iso'.
data Iso_ a b s t = Iso_ (s -> a) (b -> t)

instance Functor (Iso_ a b s) where
  fmap f (Iso_ sa bt) = Iso_ sa (f . bt)
  {-# INLINE fmap #-}

instance Profunctor (Iso_ a b) where
  dimap f g (Iso_ sa bt) = Iso_ (sa . f) (g . bt)
  {-# INLINE dimap #-}
  lmap f (Iso_ sa bt) = Iso_ (sa . f) bt
  {-# INLINE lmap #-}
  rmap f (Iso_ sa bt) = Iso_ sa (f . bt)
  {-# INLINE rmap #-}

---------------------------------------------------------------------
-- 
---------------------------------------------------------------------


-- | The `Prism_` profunctor characterizes a `Prism`.
data Prism_ a b s t = Prism_ (b -> t) (s -> Either t a)

-- | @type 'Prism_'' a s t = 'Prism_' a a s t@
type Prism_' a = Prism_ a a

instance Functor (Prism_ a b s) where

  fmap f (Prism_ bt seta) = Prism_ (f . bt) (either (Left . f) Right . seta)
  {-# INLINE fmap #-}

instance Profunctor (Prism_ a b) where

  dimap f g (Prism_ bt seta) = Prism_ (g . bt) $
    either (Left . g) Right . seta . f
  {-# INLINE dimap #-}

  lmap f (Prism_ bt seta) = Prism_ bt (seta . f)
  {-# INLINE lmap #-}

  rmap f (Prism_ bt seta) = Prism_ (f . bt) (either (Left . f) Right . seta)
  {-# INLINE rmap #-}


instance Choice (Prism_ a b) where

  left' (Prism_ bt seta) = Prism_ (Left . bt) $ 
    either (either (Left . Left) Right . seta) (Left . Right)
  {-# INLINE left' #-}

  right' (Prism_ bt seta) = Prism_ (Right . bt) $ 
    either (Left . Left) (either (Left . Right) Right . seta)
  {-# INLINE right' #-}



---------------------------------------------------------------------
-- 
---------------------------------------------------------------------


-- | The `Lens_` profunctor characterizes a `Lens`.
data Lens_ a b s t = Lens_ (s -> a) (s -> b -> t)

instance Profunctor (Lens_ a b) where

  dimap f g (Lens_ sa sbt) = Lens_ (sa . f) (\s -> g . sbt (f s))

instance Strong (Lens_ a b) where

  first' (Lens_ sa sbt) =
    Lens_ (\(a, _) -> sa a) (\(s, c) b -> ((sbt s b), c))

  second' (Lens_ sa sbt) =
    Lens_ (\(_, a) -> sa a) (\(c, s) b -> (c, (sbt s b)))

---------------------------------------------------------------------
-- 
---------------------------------------------------------------------

-- | The `Lens_` profunctor characterizes a `Lens`.
data Affine_ a b s t = Affine_ (s -> Either t a) (s -> b -> t)

{-
instance Profunctor (Affine_ a b) where

  dimap f g (Lens_ sa sbt) = Lens_ (sa . f) (\s -> g . sbt (f s))

instance Strong (Affine_ a b) where

  first' (Affine_ sa sbt) =
    Lens_ (\(a, _) -> sa a) (\(s, c) b -> ((sbt s b), c))

  second' (Affine_ sa sbt) =
    Lens_ (\(_, a) -> sa a) (\(c, s) b -> (c, (sbt s b)))
-}


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

newtype Indexed p i s t = Indexed (p (i, s) t)

--instance Profunctor p => Profunctor (Indexed p i) where  dimap f g (Indexed p) = Indexed (dimap (second' f) g p)


instance Profunctor p => Profunctor (Indexed p i) where
    dimap f g (Indexed p) = Indexed (dimap (fmap f) g p)

instance Strong p => Strong (Indexed p i) where
    first' (Indexed p) = Indexed (lmap unassoc (first' p))

unassoc :: (a,(b,c)) -> ((a,b),c)
unassoc (a,(b,c)) = ((a,b),c)

instance Choice p => Choice (Indexed p i) where
    left' (Indexed p) = Indexed $
        lmap (\(i, e) -> first (i,) e) (left' p)

{-
instance Traversing1 p => Traversing1 (Indexed p i) where
    wander1 f (Indexed p) = Indexed $
         wander1 (\g (i, s) -> f (curry g i) s) p
-}
instance Traversing p => Traversing (Indexed p i) where
    wander f (Indexed p) = Indexed $
         wander (\g (i, s) -> f (curry g i) s) p


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

--instance Semigroupal Zipped where mult (Zipped p) (Zipped q) = Zipped (\(a,b) (c,d) -> (p a c, q b d))

--instance Monoidal Zipped where unit = Zipped (\_ _ -> ())



