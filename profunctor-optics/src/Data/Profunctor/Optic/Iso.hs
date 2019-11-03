module Data.Profunctor.Optic.Iso where

import Data.Foldable
import Data.Profunctor.Optic.Prelude
import Data.Maybe (fromMaybe)
import Data.Profunctor.Optic.Type

import Control.Monad (join)

---------------------------------------------------------------------
-- 'Iso' 
---------------------------------------------------------------------

-- | Build an 'Iso' from two inverses.
--
-- /Caution/: In order for the generated iso family to be well-defined,
-- you must ensure that the two isomorphism laws hold:
--
-- * @sa . bt ≡ id@
--
-- * @bt . sa ≡ id@
--
iso :: (s -> a) -> (b -> t) -> Iso s t a b
iso = dimap

-- | Invert an isomorphism.
--
-- @
-- 'from' ('from' l) ≡ l
-- @
--
from :: AIso s t a b -> Iso b a t s
from l = withIso l $ \sa bt -> iso bt sa
{-# INLINE from #-}

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

instance Sieve (IsoRep a b) (PStore a b) where
  sieve (IsoRep sa bt) s = PStore (sa s) bt

instance Cosieve (IsoRep a b) (PCont a b) where
  cosieve (IsoRep sa bt) (PCont sab) = bt (sab sa)

data PStore a b t = PStore a (b -> t)

values :: PStore a b t -> b -> t
values (PStore _ bt) = bt

info :: PStore a b t -> a
info (PStore a _) = a

instance Functor (PStore a b) where
  fmap f (PStore a bt) = PStore a (f . bt)
  {-# INLINE fmap #-}

instance Profunctor (PStore a) where
  dimap f g (PStore a bt) = PStore a (g . bt . f)
  {-# INLINE dimap #-}

instance a ~ b => Foldable (PStore a b) where
  foldMap f (PStore b bt) = f . bt $ b

newtype PCont a b s = PCont { runPCont :: (s -> a) -> b }

instance Functor (PCont a b) where
  fmap st (PCont sab) = PCont $ \ta -> sab (ta . st)

runPCont' :: PCont a b a -> b
runPCont' (PCont f) = f id

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Extract the two functions, one from @s -> a@ and
-- one from @b -> t@ that characterize an 'Iso'.
withIso :: AIso s t a b -> ((s -> a) -> (b -> t) -> r) -> r
withIso x k = case x (IsoRep id id) of IsoRep sa bt -> k sa bt
{-# INLINE withIso #-}

cycleOf :: AIso s t a b -> (t -> s) -> b -> a
cycleOf x = withIso x $ \sa bt ts -> sa . ts . bt

au :: AIso s t a b -> ((b -> t) -> e -> s) -> e -> a
au l = withIso l $ \sa bt f e -> sa (f bt e)

auf :: Profunctor p => AIso s t a b -> (p r a -> e -> b) -> p r s -> e -> t
auf l = withIso l $ \sa bt f g e -> bt (f (rmap sa g) e)

---------------------------------------------------------------------
-- Common isos
---------------------------------------------------------------------

flipped :: Iso (a -> b -> c) (d -> e -> f) (b -> a -> c) (e -> d -> f)
flipped = iso flip flip

curried :: Iso ((a , b) -> c) ((d , e) -> f) (a -> b -> c) (d -> e -> f)
curried = iso curry uncurry

-- | Given a function that is its own inverse, this gives you an 'Iso' using it in both directions.
--
-- @
-- 'involuted' ≡ 'Control.Monad.join' 'iso'
-- @
--
-- >>> "live" ^. involuted reverse
-- "evil"
--
-- >>> involuted reverse %~ ('d':) $ "live"
-- "lived"
--
involuted :: (s -> a) -> Iso s a a s
involuted = join iso
{-# INLINE involuted #-}

hushed :: Iso (Maybe a) (Maybe b) (() + a) (() + b)
hushed = iso (maybe (Left ()) Right) (const Nothing ||| Just)

duped :: Iso (Bool -> a) (Bool -> b) (a , a) (b , b)
duped = iso to fro
 where
  to f = (f False, f True)
  fro p True = fst p
  fro p False = snd p

coduped :: Iso (Bool , a) (Bool , b) (a + a) (b + b)
coduped = iso f ((,) False ||| (,) True)
 where
  f (False,a) = Left a
  f (True,a) = Right a

-- | Remove a single value from a type.
--
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
--
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

newtype Paired p c d a b = Paired { runPaired :: p (c , a) (d , b) }

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
  dimap swp swp . runPaired . x . Paired . dimap swp swp . runPaired . y . Paired

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
-- split :: View s t a b -> View s' t' a' b' -> Review (Either s s') (Either t t') (Either a a') (Either b b')
-- @
split 
  :: Profunctor p
  => Optic (Split p s2 t2) s1 t1 a1 b1 
  -> Optic (Split p a1 b1) s2 t2 a2 b2 
  -> Optic p (s1 + s2) (t1 + t2) (a1 + a2) (b1 + b2)
split x y = 
  dimap swp' swp' . runSplit . x . Split . dimap swp' swp' . runSplit . y . Split
