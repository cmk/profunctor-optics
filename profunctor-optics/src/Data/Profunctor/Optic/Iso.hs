module Data.Profunctor.Optic.Iso (
    -- * Types
    Equality
  , Equality'
  , As
  , Iso
  , Iso'
  , AIso 
  , AIso'
    -- * Constructors
  , simple
  , iso
  , adapting
  , invert
  , mapping
  , dimapping
  , toYoneda 
  , toCoyoneda
  , cloneIso
    -- * Representatives
  , IsoRep(..)
  , PStore(..)
  , values
  , info 
  , PCont(..)
  , runPCont'
    -- * Primitive operators
  , withIso 
  , cycleOf
  , au 
  , aup 
    -- * Common optics
  , flipped 
  , uncurried
  , swapped 
  , eswapped 
  , associated 
  , eassociated 
  , involuted 
  , added 
  , subtracted 
  , hushed 
  , duped
  , eduped
  , non 
  , anon
    -- * Auxilliary Types
  , Re(..) 
) where

import Data.Foldable
import Data.Group
import Data.Maybe (fromMaybe)
import Data.Profunctor.Choice (TambaraSum(..))
import Data.Profunctor.Strong (Tambara(..))
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Type
import Data.Profunctor.Yoneda (Coyoneda(..), Yoneda(..))
import qualified Control.Monad as M (join)

---------------------------------------------------------------------
-- 'Equality' 
---------------------------------------------------------------------

-- | Constrain excessive polymorphism.
--
-- e.g turn an 'Optic' into an 'Optic'':
--
-- @
-- foo . (simple :: As Int) . bar
-- @
--
simple :: As a
simple = id
{-# INLINE simple #-}

---------------------------------------------------------------------
-- 'Iso' 
---------------------------------------------------------------------

-- | Obtain an 'Iso' from two inverses.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input functions satisfy the following
-- properties:
--
-- * @sa . bt ≡ id@
--
-- * @bt . sa ≡ id@
--
-- More generally, a profunctor optic must be monoidal as a natural 
-- transformation:
-- 
-- * @o id ≡ id@
--
-- * @o ('Data.Profunctor.Composition.Procompose' p q) ≡ 'Data.Profunctor.Composition.Procompose' (o p) (o q)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
iso :: (s -> a) -> (b -> t) -> Iso s t a b
iso = dimap
{-# INLINE iso #-}

-- | Transform a Van Laarhoven 'Iso' into a profunctor 'Iso'.
--
adapting :: (forall f g. Functor f => Functor g => (g a -> f b) -> g s -> f t) -> Iso s t a b
adapting abst = iso f g
  where f = getConst . (abst (Const . runIdentity)) . Identity
        g = runIdentity . (abst (Identity . getConst)) . Const
{-# INLINE adapting #-}

-- | Invert an isomorphism.
--
-- For any valid 'Iso' /o/ we have:
-- @
-- 'invert' ('invert' o) ≡ o
-- @
--
invert :: AIso s t a b -> Iso b a t s
invert o = withIso o $ \sa bt -> iso bt sa
{-# INLINE invert #-}

-- | TODO: Document
--
mapping
  :: Functor f
  => Functor g
  => AIso s t a b
  -> Iso (f s) (g t) (f a) (g b)
mapping l = withIso l $ \sa bt -> iso (fmap sa) (fmap bt)
{-# INLINE mapping #-}

-- | TODO: Document
--
dimapping
  :: Profunctor p
  => Profunctor q
  => AIso s1 t1 a1 b1
  -> AIso s2 t2 a2 b2
  -> Iso (p a1 s2) (q b1 t2) (p s1 a2) (q t1 b2)
dimapping f g = 
  withIso f $ \sa1 bt1 -> 
    withIso g $ \sa2 bt2 -> 
      iso (dimap sa1 sa2) (dimap bt1 bt2)
{-# INLINE dimapping #-}

-- | Lift an 'Iso' into a 'Yoneda'.
--
toYoneda :: Profunctor p => Iso s t a b -> p a b -> Yoneda p s t
toYoneda o p = withIso o $ \sa bt -> Yoneda $ \f g -> dimap (sa . f) (g . bt) p 
{-# INLINE toYoneda #-}

-- | Lift an 'Iso' into a 'Coyoneda'.
--
toCoyoneda :: Iso s t a b -> p a b -> Coyoneda p s t
toCoyoneda o p = withIso o $ \sa bt -> Coyoneda sa bt p
{-# INLINE toCoyoneda #-}

-- | Convert from 'AIso' back to any 'Iso'.
--
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
{-# INLINE values #-}

info :: PStore a b t -> a
info (PStore a _) = a
{-# INLINE info #-}

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

instance a ~ b => Apply (PCont a b) where
  (PCont stab) <.> (PCont sab) = PCont $ \ta -> stab $ \st -> sab (ta . st) 

runPCont' :: PCont a b a -> b
runPCont' (PCont f) = f id
{-# INLINE runPCont' #-}

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Extract the two functions that characterize an 'Iso'.
--
withIso :: AIso s t a b -> ((s -> a) -> (b -> t) -> r) -> r
withIso x k = case x (IsoRep id id) of IsoRep sa bt -> k sa bt
{-# INLINE withIso #-}

-- | TODO: Document
--
cycleOf :: AIso s t a b -> (t -> s) -> b -> a
cycleOf x = withIso x $ \sa bt ts -> sa . ts . bt
{-# INLINE cycleOf #-}

-- | TODO: Document
--
au :: AIso s t a b -> ((b -> t) -> e -> s) -> e -> a
au l = withIso l $ \sa bt f e -> sa (f bt e)
{-# INLINE au #-}

-- | TODO: Document
--
aup :: Profunctor p => AIso s t a b -> (p r a -> e -> b) -> p r s -> e -> t
aup l = withIso l $ \sa bt f g e -> bt (f (rmap sa g) e)
{-# INLINE aup #-}

---------------------------------------------------------------------
-- Common isos
---------------------------------------------------------------------

-- | TODO: Document
--
flipped :: Iso (a -> b -> c) (d -> e -> f) (b -> a -> c) (e -> d -> f)
flipped = iso flip flip
{-# INLINE flipped #-}

-- | TODO: Document
--
uncurried :: Iso ((a , b) -> c) ((d , e) -> f) (a -> b -> c) (d -> e -> f)
uncurried = iso curry uncurry
{-# INLINE uncurried #-}

-- | TODO: Document
--
swapped :: Iso (a , b) (c , d) (b , a) (d , c)
swapped = iso swp swp
{-# INLINE swapped #-}

-- | TODO: Document
--
eswapped :: Iso (a + b) (c + d) (b + a) (d + c)
eswapped = iso eswp eswp
{-# INLINE eswapped #-}

-- | 'Iso' defined by left-association of nested tuples.
--
associated :: Iso (a , (b , c)) (d , (e , f)) ((a , b) , c) ((d , e) , f)
associated = iso assocl assocr
{-# INLINE associated #-}

-- | 'Iso' defined by left-association of nested tuples.
--
eassociated :: Iso (a + (b + c)) (d + (e + f)) ((a + b) + c) ((d + e) + f)
eassociated = iso eassocl eassocr
{-# INLINE eassociated #-}

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
involuted = M.join iso
{-# INLINE involuted #-}

-- | The group isomorphism defined by an element's action.
--
-- >>> [1..3] ^.. traversed . added 1000
-- [1001,1002,1003]
--
added :: Group a => a -> Iso' a a
added n = iso (<> n) (<< n)
{-# INLINE added #-}

-- | The group isomorphism defined by an element's inverse action.
--
-- @
-- 'subtracted' n = 're' ('added' n)
-- @
--
subtracted :: Group a => a -> Iso' a a
subtracted n = iso (<< n) (<> n)
{-# INLINE subtracted #-}

-- | TODO: Document
--
hushed :: Iso (Maybe a) (Maybe b) (() + a) (() + b)
hushed = iso (maybe (Left ()) Right) (const Nothing ||| Just)
{-# INLINE hushed #-}

-- | TODO: Document
--
duped :: Iso (Bool -> a) (Bool -> b) (a , a) (b , b)
duped = iso to fro
 where
  to f = (f False, f True)
  fro p True = fst p
  fro p False = snd p
{-# INLINE duped #-}

-- | TODO: Document
--
eduped :: Iso (Bool , a) (Bool , b) (a + a) (b + b)
eduped = iso f ((,) False ||| (,) True)
 where
  f (False,a) = Left a
  f (True,a) = Right a
{-# INLINE eduped #-}

-- | Remove a single value from a type.
--
non :: Eq a => a -> Iso' (Maybe a) a
non def = iso (fromMaybe def) g
  where g a | a == def  = Nothing
            | otherwise = Just a
{-# INLINE non #-}

-- | @'anon' a p@ generalizes @'non' a@ to take any value and a predicate.
--
-- This function assumes that @p a@ holds @'True'@ and generates an isomorphism between @'Maybe' (a | 'not' (p a))@ and @a@.
--
-- >>> Map.empty & at "hello" . anon Map.empty Map.null . at "world" ?~ "!!!"
-- invertList [("hello",invertList [("world","!!!")])]
--
-- >>> invertList [("hello",invertList [("world","!!!")])] & at "hello" . anon Map.empty Map.null . at "world" .~ Nothing
-- invertList []
--
anon :: a -> (a -> Bool) -> Iso' (Maybe a) a
anon a p = iso (fromMaybe a) go where
  go b | p b       = Nothing
       | otherwise = Just b
{-# INLINE anon #-}
