-- | Re-exports from profunctor-optics plus dual optic types and combinators.
--
-- For carrier types ('Span', 'Index', 'Query', 'Layer', 'Transform'),
-- import from "Control.Cirklon.Type.Span", "Control.Cirklon.Type.Index", etc.
module Data.Profunctor.Optic.Import
  ( -- * Re-exports from profunctor-optics
    module Data.Profunctor.Optic.Iso
  , module Data.Profunctor.Optic.Lens
  , module Data.Profunctor.Optic.Prism
  , module Data.Profunctor.Optic.Setter
  , module Data.Profunctor.Optic.View
  , module Data.Profunctor.Optic.Fold
  , module Data.Profunctor.Optic.Traversal
  , module Data.Profunctor.Optic.Combinator
  , module Data.Profunctor.Optic.Carrier
  , module Data.Profunctor.Optic.Types

    -- * Costrong / Cochoice combinators
  , costrong
  , cochoice

    -- * Dual optic types (from profunctor-optics wip/indexed)
  , Relens, Relens', ARelens, ARelens'
  , Reprism, Reprism', AReprism, AReprism'
  , Rxlens, Rxlens'
  , Ixprism, Ixprism'
  , Rxprism, Rxprism'

    -- * Dual optic constructors
  , relens, relensVl, rematching, cloneRelens
  , reprism, reprism', rehandling, cloneReprism

    -- * Dual optic destructors
  , withRelens, withReprism

    -- * Dual optic carriers
  , RelensRep(..), ReprismRep(..)

    -- * Stock dual optics
  , refirst, resecond
  , releft, reright
  , rfirst, rsecond

    -- * Indexed dual constructors
  , rlens, rlensVl
  , jprism, iprism, iprism', jprism'
  , rprism, rprism'

    -- * Helpers
  , assocl, assocr, assocl', assocr'
  , eassocl, eassocr
  , forget1, forget2, forgetl, forgetr
  ) where

import Control.Arrow ((&&&), (|||))
import Data.Bifunctor as B (Bifunctor(..), second)
import Data.Profunctor        (Profunctor(..))
import Data.Profunctor.Strong (Costrong(..))
import Data.Profunctor.Choice (Cochoice(..))

import Data.Profunctor.Optic.Iso hiding ((.),  au, aup)
import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.Prism
import Data.Profunctor.Optic.Setter hiding ((.=), (..=))
import Data.Profunctor.Optic.View
import Data.Profunctor.Optic.Fold
import Data.Profunctor.Optic.Traversal
import Data.Profunctor.Optic.Combinator hiding (reps, (.), (#), (%))
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Types hiding (Traversing, Traversing1, Cotraversing, Cotraversing1)

-- ---------------------------------------------------------------------------
-- Costrong / Cochoice combinators
-- (from profunctor-optics wip/conjoined, Combinator.hs)

-- | Dual of 'strong'. Undo product structure via 'Costrong'.
costrong :: Costrong p => ((a, b) -> c) -> p c a -> p b a
costrong f = unsecond . dimap f (\a -> (a, a))
{-# INLINE costrong #-}

-- | Dual of 'choice'. Undo sum structure via 'Cochoice'.
cochoice :: Cochoice p => (c -> Either a b) -> p a c -> p a b
cochoice f = unright . dimap (either id id) f
{-# INLINE cochoice #-}

-- ---------------------------------------------------------------------------
-- Dual optic types (from profunctor-optics wip/indexed)

-- | Dual of 'Lens'. @re (lens sa sbt) :: Relens b a t s@
type Relens s t a b = forall p. Costrong p => Optic p s t a b
type Relens' s a = Relens s s a a

-- | Dual of 'Prism'. @re (prism sta bt) :: Reprism b a t s@
type Reprism s t a b = forall p. Cochoice p => Optic p s t a b
type Reprism' t b = Reprism t t b b

-- | Indexed relens: coindexed by @r@.
type Rxlens r s t a b = forall p. Costrong p => Ixoptic p r s t a b
type Rxlens' r s a = Rxlens r s s a a

-- | Indexed prism.
type Ixprism i s t a b = forall p. Choice p => Ixoptic p i s t a b
type Ixprism' i s a = Ixprism i s s a a

-- | Indexed reprism: coindexed by @r@.
type Rxprism r s t a b = forall p. Cochoice p => Ixoptic p r s t a b
type Rxprism' r s a = Rxprism r s s a a

-- ---------------------------------------------------------------------------
-- Dual optic constructors

-- | Obtain a 'Relens' from a getter and setter.
--
-- @relens bsa bt ≡ re (lens sa sbt)@ (with roles swapped)
--
-- A 'Relens' is a 'Review': @review (relens f g) ≡ f@
relens :: (b -> s -> a) -> (b -> t) -> Relens s t a b
relens bsa bt = unsecond . dimap (uncurry bsa) (id &&& bt)

-- | Van Laarhoven relens to profunctor relens.
relensVl :: (forall f. Functor f => (t -> f s) -> b -> f a) -> Relens s t a b
relensVl o = unfirst . dimap (uncurry id . swap) ((info &&& vals) . o (flip Index id))
  where swap (a, b) = (b, a)

-- | 'Relens' from its free tensor representation.
rematching :: ((c, s) -> a) -> (b -> (c, t)) -> Relens s t a b
rematching csa bct = unsecond . dimap csa bct

-- | Clone a 'Relens'.
cloneRelens :: ARelens s t a b -> Relens s t a b
cloneRelens o = withRelens o relens

-- | Obtain a 'Reprism' from a getter and matcher.
--
-- @reprism sa bat ≡ re (prism sta bt)@ (with roles swapped)
--
-- A 'Reprism' is a 'View': @view (reprism f g) ≡ f@
reprism :: (s -> a) -> (b -> Either a t) -> Reprism s t a b
reprism sa bat = unright . dimap (id ||| sa) bat

-- | 'Reprism' from a reviewer and 'Maybe' matcher.
reprism' :: (s -> a) -> (a -> Maybe s) -> Reprism' s a
reprism' tb bt = reprism tb $ \b -> maybe (Left b) Right (bt b)

-- | 'Reprism' from its free tensor representation.
rehandling :: (Either c s -> a) -> (b -> Either c t) -> Reprism s t a b
rehandling csa bct = unright . dimap csa bct

-- | Clone a 'Reprism'.
cloneReprism :: AReprism s t a b -> Reprism s t a b
cloneReprism o = withReprism o reprism

-- ---------------------------------------------------------------------------
-- Indexed dual constructors

-- | Indexed 'Relens'.
rlens :: (b -> s -> (r, a)) -> (b -> t) -> Rxlens r s t a b
rlens bsia bt = rlensVl $ \ts b -> bsia b <$> (ts . bt $ b)
{-# INLINE rlens #-}

-- | Van Laarhoven indexed relens.
rlensVl :: (forall f. Functor f => (t -> f s) -> b -> f (r, a)) -> Rxlens r s t a b
rlensVl f = relensVl $ \ts -> f (fmap snd . ts)
{-# INLINE rlensVl #-}

-- | Indexed 'Prism' from an indexed matcher.
jprism :: (i -> s -> Either t a) -> (b -> t) -> Ixprism i s t a b
jprism ista bt = prism (\(i,s) -> fmap (i,) (ista i s)) bt

-- | Indexed 'Prism' from a matcher that returns an indexed result.
iprism :: (s -> Either t (i, a)) -> (b -> t) -> Ixprism i s t a b
iprism stia bt = prism (stia . snd) bt

-- | Indexed 'Prism'' from a 'Maybe' matcher.
iprism' :: (s -> Maybe (i, a)) -> (a -> s) -> Ixprism' i s a
iprism' sia as = iprism (\s -> maybe (Left s) Right (sia s)) as

-- | Indexed 'Prism'' from an indexed 'Maybe' matcher.
jprism' :: (i -> s -> Maybe a) -> (a -> s) -> Ixprism' i s a
jprism' isa as = prism (\(i,s) -> maybe (Left s) (Right . (i,)) (isa i s)) as

-- | Indexed 'Reprism'.
rprism :: Monoid r => (r -> s -> a) -> (b -> Either a t) -> Rxprism r s t a b
rprism rsa bat = reprism (const mempty &&& uncurry rsa) (B.first (mempty,) . bat)

-- | Indexed 'Reprism'' from a 'Maybe' matcher.
rprism' :: Monoid r => (r -> s -> a) -> (a -> Maybe s) -> Rxprism' r s a
rprism' rsa ams = rprism rsa $ \b -> maybe (Left b) Right (ams b)

-- ---------------------------------------------------------------------------
-- Dual optic carriers

-- | Carrier for 'Relens'.
data RelensRep a b s t = RelensRep (b -> s -> a) (b -> t)

type ARelens s t a b = Optic (RelensRep a b) s t a b
type ARelens' s a = ARelens s s a a

instance Profunctor (RelensRep a b) where
  dimap f g (RelensRep bsa bt) = RelensRep (\b s -> bsa b (f s)) (g . bt)

instance Costrong (RelensRep a b) where
  unfirst (RelensRep baca bbc) = RelensRep (curry foo) (forget2 $ bbc . fst)
    where foo = uncurry baca . shuffle . B.second undefined . swap -- TODO: B.second bbc
          shuffle (x,(y,z)) = (y,(x,z))
          swap (a, b) = (b, a)

-- | Carrier for 'Reprism'.
data ReprismRep a b s t = ReprismRep (s -> a) (b -> Either a t)

type AReprism s t a b = Optic (ReprismRep a b) s t a b
type AReprism' s a = AReprism s s a a

instance Functor (ReprismRep a b s) where
  fmap f (ReprismRep sa bat) = ReprismRep sa (B.second f . bat)
  {-# INLINE fmap #-}

instance Profunctor (ReprismRep a b) where
  lmap f (ReprismRep sa bat) = ReprismRep (sa . f) bat
  {-# INLINE lmap #-}
  rmap = fmap
  {-# INLINE rmap #-}

instance Cochoice (ReprismRep a b) where
  unleft (ReprismRep sca batc) = ReprismRep (sca . Left) (forgetr $ either (eassocl . batc) Right)
  {-# INLINE unleft #-}

-- ---------------------------------------------------------------------------
-- Dual optic destructors

-- | Extract the two functions that characterize a 'Relens'.
withRelens :: ARelens s t a b -> ((b -> s -> a) -> (b -> t) -> r) -> r
withRelens l f = case l (RelensRep (flip const) id) of RelensRep x y -> f x y

-- | Extract the two functions that characterize a 'Reprism'.
withReprism :: AReprism s t a b -> ((s -> a) -> (b -> Either a t) -> r) -> r
withReprism o f = case o (ReprismRep id Right) of ReprismRep g h -> f g h

-- ---------------------------------------------------------------------------
-- Stock dual optics

-- | @Relens@ into the first component.
refirst :: Relens a b (a, c) (b, c)
refirst = unfirst

-- | @Relens@ into the second component.
resecond :: Relens a b (c, a) (c, b)
resecond = unsecond

-- | Indexed @Relens@ into the first component.
rfirst :: Rxlens r a b (a, c) (b, c)
rfirst = unfirst . lmap assocr

-- | Indexed @Relens@ into the second component.
rsecond :: Rxlens r a b (c, a) (c, b)
rsecond = unsecond . lmap (\(c, (r, a)) -> (r, (c, a)))

-- | @Reprism@ out of the Left constructor.
releft :: Reprism a b (Either a c) (Either b c)
releft = unleft

-- | @Reprism@ out of the Right constructor.
reright :: Reprism a b (Either c a) (Either c b)
reright = unright

-- ---------------------------------------------------------------------------
-- Structural helpers

assocl :: (a, (b, c)) -> ((a, b), c)
assocl (a, (b, c)) = ((a, b), c)
{-# INLINE assocl #-}

assocr :: ((a, b), c) -> (a, (b, c))
assocr ((a, b), c) = (a, (b, c))
{-# INLINE assocr #-}

assocl' :: (a, Either b c) -> Either (a, b) c
assocl' (a, Left b)  = Left (a, b)
assocl' (_, Right c) = Right c
{-# INLINE assocl' #-}

assocr' :: (Either a b, c) -> Either a (b, c)
assocr' (f, b) = fmap (,b) f
{-# INLINE assocr' #-}

eassocl :: Either a (Either b c) -> Either (Either a b) c
eassocl (Left a)          = Left (Left a)
eassocl (Right (Left b))  = Left (Right b)
eassocl (Right (Right c)) = Right c
{-# INLINE eassocl #-}

eassocr :: Either (Either a b) c -> Either a (Either b c)
eassocr (Left (Left a))  = Left a
eassocr (Left (Right b)) = Right (Left b)
eassocr (Right c)        = Right (Right c)
{-# INLINE eassocr #-}

-- | Forget the first component of a product endomorphism via knot-tying.
forget1 :: ((c, a) -> (c, b)) -> a -> b
forget1 f a = b where (c, b) = f (c, a)
{-# INLINE forget1 #-}

-- | Forget the second component of a product endomorphism via knot-tying.
forget2 :: ((a, c) -> (b, c)) -> a -> b
forget2 f a = b where (b, c) = f (a, c)
{-# INLINE forget2 #-}

-- | Forget the left branch of a sum endomorphism via fixed-point iteration.
forgetl :: (Either c a -> Either c b) -> a -> b
forgetl f = go . Right where go = either (go . Left) id . f
{-# INLINE forgetl #-}

-- | Forget the right branch of a sum endomorphism via fixed-point iteration.
forgetr :: (Either a c -> Either b c) -> a -> b
forgetr f = go . Left where go = either id (go . Right) . f
{-# INLINE forgetr #-}
