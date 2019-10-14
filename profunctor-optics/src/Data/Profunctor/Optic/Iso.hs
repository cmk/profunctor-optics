module Data.Profunctor.Optic.Iso where

import Data.Profunctor.Optic.Prelude
import Data.Maybe (fromMaybe)
import Data.Profunctor.Optic.Type

import Control.Monad (join)

---------------------------------------------------------------------
-- 'Equality' 
---------------------------------------------------------------------

type As a = Equality' a a

---------------------------------------------------------------------
-- 'Re' 
---------------------------------------------------------------------

-- 'simple' is occasionally useful to constraint excessive polymorphism, 
-- e.g turn Optic into simple Optic'.
-- | @foo . (simple :: As Int) . bar@.
simple :: As a
simple = id

-- | Turn a 'Prism' or 'Iso' around to build a 'Getter'.
--
-- If you have an 'Iso', 'from' is a more powerful version of this function
-- that will return an 'Iso' instead of a mere 'Getter'.
--
-- >>> 5 ^.re _Left
-- Left 5
--
-- >>> 6 ^.re (_Left.unto succ)
-- Left 7
--
-- @
-- 'review'  ≡ 'view'  '.' 're'
-- 'reviews' ≡ 'views' '.' 're'
-- 'reuse'   ≡ 'use'   '.' 're'
-- 'reuses'  ≡ 'uses'  '.' 're'
-- @
--
-- @
-- 're' :: 'Prism' s t a b -> 'Getter' b t
-- 're' :: 'Iso' s t a b   -> 'Getter' b t
-- @
--
re :: Optic (Re p a b) s t a b -> Optic p b a t s
re o = (between runRe Re) o id
{-# INLINE re #-}

---------------------------------------------------------------------
-- 'Iso' 
---------------------------------------------------------------------

{- hedgehog predicates

fromTo :: Eq s => IsoRep s s a a -> s -> Bool
fromTo (IsoRep f t) s = (t . f) s == s

toFrom :: Eq a => IsoRep s s a a -> a -> Bool
toFrom (IsoRep f t) a = (f . t) a == a

Since every Iso is both a valid Lens and a valid Prism the laws for those types imply the following laws for an Iso o:

viewP o (reviewP o b) ≡ b
reviewP o (viewP o s) ≡ s

Or even more powerfully using re:

o . re o ≡ id
re o . o ≡ id


λ> from associate ((1, "hi"), True)
(1,("hi",True))
λ> to associate (True, ("hi", 1))
((True,"hi"),1)

-}


-- | Build an 'Iso' from two inverses.
--
-- /Caution/: In order for the generated iso family to be well-defined,
-- you must ensure that the two isomorphism laws hold:
--
-- * @sa . bt === id@
--
-- * @bt . sa === id@
--
iso :: (s -> a) -> (b -> t) -> Iso s t a b
iso = dimap

--isoek :: (forall f p. Applicative f => Profunctor p => (p a (f b) -> p s (f t)) -> Prism s t a b
--isoek l = undefined 

--isovl :: (forall f. Functor f => Functor g => (g a -> f b) -> g s -> f t) -> Prism s t a b
--isovl l = undefined 

-- | Convert from 'AIso' back to any 'Iso'.
cloneIso :: AIso s t a b -> Iso s t a b
cloneIso k = withIso k iso
{-# INLINE cloneIso #-}

---------------------------------------------------------------------
-- 'IsoRep'
---------------------------------------------------------------------

-- | The 'IsoRep' profunctor precisely characterizes an 'Iso'.
data IsoRep a b s t = IsoRep (s -> a) (b -> t)

-- | When you see this as an argument to a function, it expects an 'Iso'.
type AIso s t a b = Optic (IsoRep a b) s t a b

type AIso' s a = AIso s s a a

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

reiso :: AIso s t a b -> (t -> s) -> b -> a
reiso x = withIso x $ \sa bt ts -> sa . ts . bt

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Extract the two functions, one from @s -> a@ and
-- one from @b -> t@ that characterize an 'Iso'.
withIso :: AIso s t a b -> ((s -> a) -> (b -> t) -> r) -> r
withIso x k = case x (IsoRep id id) of IsoRep sa bt -> k sa bt
{-# INLINE withIso #-}

-- | Invert an isomorphism.
--
-- @
-- 'from' ('from' l) ≡ l
-- @
from :: AIso s t a b -> Iso b a t s
from l = withIso l $ \sa bt -> iso bt sa
{-# INLINE from #-}

au :: AIso s t a b -> ((b -> t) -> e -> s) -> e -> a
au l = withIso l $ \sa bt f e -> sa (f bt e)

auf :: Profunctor p => AIso s t a b -> (p r a -> e -> b) -> p r s -> e -> t
auf l = withIso l $ \sa bt f g e -> bt (f (rmap sa g) e)

---------------------------------------------------------------------
-- Common isos
---------------------------------------------------------------------

flipping :: Iso (a -> b -> c) (d -> e -> f) (b -> a -> c) (e -> d -> f)
flipping = iso flip flip

currying :: Iso ((a , b) -> c) ((d , e) -> f) (a -> b -> c) (d -> e -> f)
currying = iso curry uncurry

swapped :: Swap p => Iso (a `p` b) (c `p` d) (b `p` a) (d `p` c)
swapped = iso swap swap

-- | Right association
associated :: Assoc p => Iso ((a `p` b) `p` c) ((d `p` e) `p` f) (a `p` (b `p` c)) (d `p` (e `p` f))
associated = iso assocr assocl

-- | Given a function that is its own inverse, this gives you an 'Iso' using it in both directions.
--
-- @
-- 'involuted' ≡ 'Control.Monad.join' 'iso'
-- @
--
-- >>> "live" ^. involuted reverse
-- "evil"
--
-- >>> "live" & involuted reverse %~ ('d':)
-- "lived"
--
involuted :: (s -> a) -> Iso s a a s
involuted = join iso
{-# INLINE involuted #-}

branched :: (a -> Bool) -> Iso a b (a + a) (b + b)
branched f = iso (branch' f) dedup

-- | If `a1` is obtained from `a` by removing a single value, then
-- | `Maybe a1` is isomorphic to `a`.
non :: Eq a => a -> Iso' (Maybe a) a
non def = iso (fromMaybe def) g
  where g a | a == def  = Nothing
            | otherwise = Just a

-- | @'anon' a p@ generalizes @'non' a@ to take any value and a predicate.
--
-- This function assumes that @p a@ holds @'True'@ and generates an isomorphism between @'Maybe' (a | 'not' (p a))@ and @a@.
--
-- >>> Map.empty & at "hello" . anon Map.empty Map.null . at "world" ?~ "!!!"
-- fromList [("hello",fromList [("world","!!!")])]
--
-- >>> fromList [("hello",fromList [("world","!!!")])] & at "hello" . anon Map.empty Map.null . at "world" .~ Nothing
-- fromList []
anon :: a -> (a -> Bool) -> Iso' (Maybe a) a
anon a p = iso (fromMaybe a) go where
  go b | p b       = Nothing
       | otherwise = Just b
{-# INLINE anon #-}

liftF
  :: Functor f
  => Functor g
  => AIso s t a b
  -> Iso (f s) (g t) (f a) (g b)
liftF l = withIso l $ \sa bt -> iso (fmap sa) (fmap bt)

liftP
  :: Profunctor p
  => Profunctor q
  => AIso s1 t1 a1 b1
  -> AIso s2 t2 a2 b2
  -> Iso (p a1 s2) (q b1 t2) (p s1 a2) (q t1 b2)
liftP f g = 
  withIso f $ \sa1 bt1 -> 
    withIso g $ \sa2 bt2 -> 
      iso (dimap sa1 sa2) (dimap bt1 bt2)

lift2 :: AIso s t a b -> Iso (c , s) (d , t) (c , a) (d , b)
lift2 x = withIso x $ \sa bt -> between runPaired Paired (dimap sa bt)

liftR :: AIso s t a b -> Iso (c + s) (d + t) (c + a) (d + b)
liftR x = withIso x $ \sa bt -> between runSplit Split (dimap sa bt)

---------------------------------------------------------------------
-- 'Paired'
---------------------------------------------------------------------

newtype Paired p c d a b = Paired { runPaired :: p (c,a) (d,b) }

--fromTambara :: Profunctor p => Tambara p a b -> Paired p d d a b
--fromTambara = Paired . swapped . runTambara

instance Profunctor p => Profunctor (Paired p c d) where
  dimap f g (Paired pab) = Paired $ dimap (fmap f) (fmap g) pab

instance Strong p => Strong (Paired p c d) where
  second' (Paired pab) = Paired . dimap shuffle shuffle . second' $ pab
   where
    shuffle (x,(y,z)) = (y,(x,z))

-- ^ @
-- paired :: Iso s t a b -> Iso s' t' a' b' -> Iso (s, s') (t, t') (a, a') (b, b')
-- paired :: Lens s t a b -> Lens s' t' a' b' -> Lens (s, s') (t, t') (a, a') (b, b')
-- @
--
paired 
  :: Profunctor p 
  => Optic (Paired p s2 t2) s1 t1 a1 b1 
  -> Optic (Paired p a1 b1) s2 t2 a2 b2 
  -> Optic p (s1 , s2) (t1 , t2) (a1 , a2) (b1 , b2)
paired x y = 
  swapped . runPaired . x . Paired . swapped . runPaired . y . Paired

---------------------------------------------------------------------
-- 'Split'
---------------------------------------------------------------------

newtype Split p c d a b = Split { runSplit :: p (Either c a) (Either d b) }

--fromTambaraSum :: Profunctor p => TambaraSum p a b -> Split p d d a b
--fromTambaraSum = Split . swapped . runTambaraSum

instance Profunctor p => Profunctor (Split p c d) where
  dimap f g (Split pab) = Split $ dimap (fmap f) (fmap g) pab

instance Choice p => Choice (Split p c d) where
  right' (Split pab) = Split . dimap shuffle shuffle . right' $ pab
   where
    shuffle = Right . Left ||| (Left ||| Right . Right)

-- ^ @
-- split :: Iso s t a b -> Iso s' t' a' b' -> Iso (Either s s') (Either t t') (Either a a') (Either b b')
-- split :: Prism s t a b -> Prism s' t' a' b' -> Lens (Either s s') (Either t t') (Either a a') (Either b b')
-- split :: Getter s t a b -> Getter s' t' a' b' -> Review (Either s s') (Either t t') (Either a a') (Either b b')
-- @
split 
  :: Profunctor p
  => Optic (Split p s2 t2) s1 t1 a1 b1 
  -> Optic (Split p a1 b1) s2 t2 a2 b2 
  -> Optic p (s1 + s2) (t1 + t2) (a1 + a2) (b1 + b2)
split x y = 
  swapped . runSplit . x . Split . swapped . runSplit . y . Split
