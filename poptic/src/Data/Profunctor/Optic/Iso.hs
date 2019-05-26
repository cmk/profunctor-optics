module Data.Profunctor.Optic.Iso where

import Data.Profunctor.Optic.Prelude
import Data.Bifunctor.Product (Product(..))
import Data.Maybe (fromMaybe)
import Data.Profunctor.Optic.Type



{- hedgehog predicates
fromTo :: Eq s => IsoRep s s a a -> s -> Bool
fromTo (IsoRep f t) s = (t . f) s == s

toFrom :: Eq a => IsoRep s s a a -> a -> Bool
toFrom (IsoRep f t) a = (f . t) a == a


associate :: IsoRep ((a, b), c) ((a', b'), c') (a, (b, c)) (a', (b', c'))
associate = IsoRep  f t where
  f ((a, b), c) = (a, (b, c))
  t (a', (b', c')) = ((a', b'), c')

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
-- Common isos
---------------------------------------------------------------------


curried :: Iso ((a, b) -> c) ((d, e) -> f) (a -> b -> c) (d -> e -> f)
curried = iso curry uncurry

uncurried :: Iso (a -> b -> c) (d -> e -> f) ((a, b) -> c) ((d, e) -> f)
uncurried = iso uncurry curry

flipped :: Iso (a -> b -> c) (d -> e -> f) (b -> a -> c) (e -> d -> f)
flipped = iso flip flip

mapping
  :: Functor f
  => Functor g
  => AnIso s t a b
  -> Iso (f s) (g t) (f a) (g b)
mapping l = withIso l $ \sa bt -> iso (fmap sa) (fmap bt)

dimapping
  :: Profunctor p
  => Profunctor q
  => AnIso s t a b
  -> AnIso ss tt aa bb
  -> Iso (p a ss) (q b tt) (p s aa) (q t bb)
dimapping f g = 
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
