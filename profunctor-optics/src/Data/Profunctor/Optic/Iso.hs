module Data.Profunctor.Optic.Iso where

import Data.Profunctor.Optic.Prelude hiding (Product) 
import Data.Bifunctor.Product (Product(..))
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


iso :: (s -> a) -> (b -> t) -> Iso s t a b
iso = dimap


-- | Convert from 'AnIso' back to any 'Iso'.
cloneIso :: AnIso s t a b -> Iso s t a b
cloneIso k = withIso k iso
{-# INLINE cloneIso #-}


-- | Extract the two functions, one from @s -> a@ and
-- one from @b -> t@ that characterize an 'Iso'.
withIso :: AnIso s t a b -> ((s -> a) -> (b -> t) -> r) -> r
withIso ai k = case ai (IsoRep id id) of IsoRep sa bt -> k sa bt
{-# INLINE withIso #-}


-- | Invert an isomorphism.
--
-- @
-- 'from' ('from' l) ≡ l
-- @
from :: AnIso s t a b -> Iso b a t s
from l = withIso l $ \ sa bt -> iso bt sa
{-# INLINE from #-}


-- ^ @
-- from' :: Iso b a t s -> Iso s t a b
-- @
from' :: Optic (Product (Star (Const t)) (Costar (Const s))) b a t s -> Iso s t a b
from' o = iso (review . Const) (getConst . get) 
  where  
    Pair (Star get) (Costar review) = o (Pair (Star Const) (Costar getConst))

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

-- | When you see this as an argument to a function, it expects an 'Iso'.
type AnIso s t a b = Optic (IsoRep a b) s t a b

type AnIso' s a = AnIso s s a a

---------------------------------------------------------------------
-- Common isos
---------------------------------------------------------------------

forget2 :: Iso s t (a, x) (b, x) -> Lens s t a b
forget2 = (. first')

forgetR :: Iso s t (Either a c) (Either b c) -> Prism s t a b
forgetR = (. left')

eitherOne :: Iso (Maybe a) (Maybe b) (Either () a) (Either () b)
eitherOne = iso (maybe (Left ()) Right) (const Nothing ||| Just)

eitherTwo :: Iso (Bool,a) (Bool,b) (Either a a) (Either b b)
eitherTwo = iso f ((,) False ||| (,) True)
 where
  f (False,a) = Left a
  f (True,a) = Right a

indexPair :: Iso (Bool -> a) (Bool -> b) (a,a) (b,b)
indexPair = iso to fro
 where
  to f = (f False, f True)
  fro p True = fst p
  fro p False = snd p


curried :: Iso ((a, b) -> c) ((d, e) -> f) (a -> b -> c) (d -> e -> f)
curried = iso curry uncurry

uncurried :: Iso (a -> b -> c) (d -> e -> f) ((a, b) -> c) ((d, e) -> f)
uncurried = iso uncurry curry

-- | Right association
associated :: Iso ((a, b), c) ((a', b'), c') (a, (b, c)) (a', (b', c'))
associated = iso assoc unassoc

swapped :: Iso (a, b) (c, d) (b, a) (d, c)
swapped = iso swap swap

flipped :: Iso (a -> b -> c) (d -> e -> f) (b -> a -> c) (e -> d -> f)
flipped = iso flip flip

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


fover
  :: Functor f
  => Functor g
  => AnIso s t a b
  -> Iso (f s) (g t) (f a) (g b)
fover l = withIso l $ \sa bt -> iso (fmap sa) (fmap bt)

diover
  :: Profunctor p
  => Profunctor q
  => AnIso s t a b
  -> AnIso ss tt aa bb
  -> Iso (p a ss) (q b tt) (p s aa) (q t bb)
diover f g = 
  withIso f $ \sa bt -> 
    withIso g $ \ssaa bbtt -> 
      iso (dimap sa ssaa) (dimap bt bbtt)

-- | If `a1` is obtained from `a` by removing a single value, then
-- | `Maybe a1` is isomorphic to `a`.
non :: forall a. Eq a => a -> Iso' (Maybe a) a
non def = iso (fromMaybe def) g
  where g a | a == def  = Nothing
            | otherwise = Just a

au :: AnIso s t a b -> ((b -> t) -> e -> s) -> e -> a
au l = withIso l $ \sa bt f e -> sa (f bt e)

auf :: Profunctor p => AnIso s t a b -> (p r a -> e -> b) -> p r s -> e -> t
auf l = withIso l $ \sa bt f g e -> bt (f (rmap sa g) e)

under :: AnIso s t a b -> (t -> s) -> b -> a
under l = withIso l $ \sa bt ts -> sa . ts . bt


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
