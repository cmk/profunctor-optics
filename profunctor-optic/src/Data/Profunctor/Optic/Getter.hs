module Data.Profunctor.Optic.Getter where

import Control.Arrow ((&&&))
import Control.Monad.Reader.Class as Reader
import Data.Profunctor.Optic.Types -- (Fold, AGetter, Getter, into, outof, star)
import Data.Profunctor.Optic.Operators

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> import Control.Lens
-- >>> import Data.List.Lens
-- >>> import Debug.SimpleReflect.Expr
-- >>> import Debug.SimpleReflect.Vars as Vars hiding (f,g)
-- >>> let f :: Expr -> Expr; f = Debug.SimpleReflect.Vars.f
-- >>> let g :: Expr -> Expr; g = Debug.SimpleReflect.Vars.g

infixl 8 ^.

-- | View the value pointed to by a 'Getter' or 'Lens' or the
-- result of folding over all the results of a 'Data.Profunctor.Optic.Fold.Fold' or
-- 'Data.Profunctor.Optic.Traversal.Traversal' that points at a monoidal values.
--
-- This is the same operation as 'view' with the arguments flipped.
--
-- The fixity and semantics are such that subsequent field accesses can be
-- performed with ('Prelude..').
--
-- >>> (a,b) ^. _2
-- b
--
-- >>> ("hello","world") ^. _2
-- "world"
--
-- >>> import Data.Complex
-- >>> ((0, 1 :+ 2), 3) ^. _1  . _2 . to magnitude
-- 2.23606797749979
--
-- @
-- ('^.') ::             s -> 'Getter' s a     -> a
-- ('^.') :: 'Data.Monoid.Monoid' m => s -> ''Data.Profunctor.Optic.Fold.Fold' s m       -> m
-- ('^.') ::             s -> 'Data.Profunctor.Optic.Iso.Iso'' s a       -> a
-- ('^.') ::             s -> 'Data.Profunctor.Optic.Lens.Lens'' s a      -> a
-- ('^.') :: 'Data.Monoid.Monoid' m => s -> 'Data.Profunctor.Optic.Traversal.Traversal'' s m -> m
-- @
--
(^.) :: s -> Optic (Forget a) s t a b -> a
(^.) = flip view
{-# INLINE (^.) #-}

-- | Build an (index-preserving) 'Getter' from an arbitrary function.
--
-- @
-- 'to' f '.' 'to' g ≡ 'to' (g '.' f)
-- @
--
-- @
-- a '^.' 'to' f ≡ f a
-- @
--
-- >>> a ^. to f
-- f a
--
-- >>> view ("hello","world") ^. to snd
-- "world"
--
-- >>> 5^.to succ
-- 6
--
-- >>> (0, -5) ^. _2 . to abs
-- 5
--
-- @
-- 'to' :: (s -> a) -> 'IndexPreservingGetter' s a
-- @
--
--to :: (s -> a) -> Getter s a
to :: Bicontravariant p => (s -> a) -> Optic' p s a
to f = cimap f f
--to f p = Forget (runForget p . f)
--to k = dimap k (contramap k)
{-# INLINE to #-}


-- | A variant of 'to' for 'PrimGetter'.
to' :: (s -> a) -> (t -> b) -> PrimGetter s t a b
to' = cimap
{-# INLINE to' #-}


-- | Build an constant-valued (index-preserving) 'Getter' from an arbitrary value.
--
-- @
-- 'like' a '.' 'like' b ≡ 'like' b
-- a '^.' 'like' b ≡ b
-- a '^.' 'like' b ≡ a '^.' 'to' ('const' b)
-- @
--
-- This can be useful as a second case 'failing' a 'Fold'
-- e.g. @foo `failing` 'like' 0@
--
-- @
-- 'like' :: a -> 'IndexPreservingGetter' s a
-- @
--
like :: Bicontravariant p => a -> Optic' p b a
like a = to (const a)



{-
view :: MonadReader s m => AGetter a s a -> m a
view l = Reader.asks (getConst #. l Const)
{-# INLINE view #-}


get :: Optical (SubStar (Constant a)) ta tb a b -> ta -> a
-- ^ @
-- get :: To ta tb a b -> ta -> a
-- get :: Monoid a => Fold ta tb a b -> ta -> a
-- @
get l = gets l id

-}

{-
views :: Fold r s t a b -> (a -> r) -> s -> r
-- ^ @
-- views :: Getter s t a b -> (a -> r) -> s -> r
-- views :: Monoid r => Fold s t a b -> (a -> r) -> s -> r
-- @
views = star Const getConst

--view :: AGetter s t a b -> s -> a
--view :: (s -> r) -> s -> r
--view = views id

-- | View the focus of a `Getter`.
view' :: AGetter s t a b -> s -> a
--view :: (Star (Const a) a b -> Star (Const a) s t) -> s -> a
view' o = views o id --unstar getConst (o $ star Const id)




--to :: (s -> a) -> Star (Const c) a b -> Star (Const c) s t
--to :: (s -> a) -> Fold r s t a b
to :: (s -> a) -> Getter s t a b
to f o = into Star Const (outof runStar getConst o . f)
--to = toOptic Const getConst

cloneGetter :: AGetter s t a b -> Getter s t a b
cloneGetter g = to (view' g)

--withGetter :: LensLike (Const c) s t a b -> (((a -> c) -> s -> c) -> r) -> r
withGetter :: AGetter s t a b -> (Fold c s t a b -> r) -> r
withGetter l f = f . cloneGetter $ l

-- | Combine two getters.
takeBoth :: forall s t a b c d. AGetter s t a b -> AGetter s t c d -> Getter s t (a,c) (b,d)
takeBoth l r = to (view' l &&& view' r)
-}

{-
-- | View the focus of a `Getter`.
view :: AGetter s t a b -> s -> a
view l = runForget (l (Forget id))

-- | Convert a function into a getter.
to :: (s -> a) -> Getter s t a b
to f p = Forget (runForget p . f)
-}


{-
withGetter
  :: Optical (SubStar (Const c1)) s t a b
     -> (((a -> c1) -> s -> c1) -> c2) -> c2

cloneLens :: ALens s t a b -> Lens s t a b
cloneLens l = withLens l $ \x y p -> lens x y p


withLens :: ALens s t a b -> ((s -> a) -> (s -> b -> t) -> r) -> r
withLens l f = case l (Lens_ id $ \_ b -> b) of Lens_ x y -> f x y
-}


