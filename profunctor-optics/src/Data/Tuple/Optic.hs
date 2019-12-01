{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE RankNTypes             #-}
module Data.Tuple.Optic (
    -- * Fold & Ixfold
    type Field
  , _1
  , _2
  , _3
  , _4
  , _5
  , _6
  , _7
  , _8
  , _9
  , _10
  , co1
  , pmapped
  , curried
  , swapped
) where

import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.Setter
import Data.Profunctor.Optic.Type hiding (Rep)
import Data.Profunctor.Optic.View hiding (to, from)
import Generics.SOP
import GHC.Exts
import GHC.TypeLits

{-
type Foo a = forall b. (b, a)

type family Ten (c :: (* -> * -> *) -> Constraint) :: * -> *
type instance Ten Choice = forall b. (b + a)
type instance Ten Strong = Foo 
data Module c p a b where
  Module :: c p => (Ten c z y -> b) -> p x y -> (a -> Ten c z x) -> Module c p a b
matching :: (s -> (c , a)) -> ((c , b) -> t) -> Lens s t a b

  _1 = lensVl $ \k ~(a,b) -> (\a' -> (a',b)) <$> k a
  {-# INLINE _1 #-}

-- | Right Tambara module parametrized by a tensor.
class Profunctor p => TambaraR (o :: * -> * -> *) p where
  embedr :: p a b -> p (c `o` a) (c `o` b)
-}

--class Field1 s t a b | s -> a, t -> b, s b -> t, t a -> s where
{-
type family Ten (s :: k) :: * -> * -> *
type instance Ten (,) = (,)
type instance Ten (,,) = (,)

class Field1 s t a b where
  embed :: s -> Ten s c a
  project :: Ten t c b -> t
class Field1 (o :: * -> * -> *) s t a b where
  embed :: s -> (c `o` a)
  project :: (c `o` b) -> t

instance Field1 (a,b) (a',b) a a' where
  embed ~(a,b) = (b,a)
  project = swap

-}

 
---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

type Field (n :: Nat) s t a b = (App (a -> b) s (n-1) t, Sel s (n-1) a)

-- >>> ("first",'a',3,4.2) ^. _1
-- "first"
-- >>> ("first",'a') ^. _1
-- "first"
--
_1 :: forall s t a b . Field 1 s t a b => Lens s t a b
_1 = lens sel1 $ \s b -> app1 @((->) a b) (const b) s

_2 :: forall s t a b . Field 2 s t a b => Lens s t a b
_2 = lens sel2 $ \s b -> app2 @((->) a b) (const b) s

_3 :: forall s t a b . Field 3 s t a b => Lens s t a b
_3 = lens sel3 $ \s b -> app3 @((->) a b) (const b) s

_4 :: forall s t a b . Field 4 s t a b => Lens s t a b
_4 = lens sel4 $ \s b -> app4 @((->) a b) (const b) s

_5 :: forall s t a b . Field 5 s t a b => Lens s t a b
_5 = lens sel5 $ \s b -> app5 @((->) a b) (const b) s

_6 :: forall s t a b . Field 6 s t a b => Lens s t a b
_6 = lens sel6 $ \s b -> app6 @((->) a b) (const b) s

_7 :: forall s t a b . Field 7 s t a b => Lens s t a b
_7 = lens sel7 $ \s b -> app7 @((->) a b) (const b) s

_8 :: forall s t a b . Field 8 s t a b => Lens s t a b
_8 = lens sel8 $ \s b -> app8 @((->) a b) (const b) s

_9 :: forall s t a b . Field 9 s t a b => Lens s t a b
_9 = lens sel9 $ \s b -> app9 @((->) a b) (const b) s

_10 :: forall s t a b . Field 10 s t a b => Lens s t a b
_10 = lens sel10 $ \s b -> app10 @((->) a b) (const b) s

-- | Apply a polymorphic function to each element in an n-ary tuple.
--
-- All elements in the tuple must be of the same type.
--
-- >>> over pmapped (+1) (1,2,3,4)
-- (2,3,4,5)
--
pmapped :: Mono (Poly a b) s t => Setter s t a b
pmapped = setter pmap 

--co1 = colensVl $ \f ~(a,b) -> (,b) <$> f a

co1 :: forall s t a b . Field 1 s t a b => Colens b a t s
co1 = colensVl $ \f s -> (\b -> app1 @((->) a b) (const b) s) <$> (f . sel1) s

---------------------------------------------------------------------
-- Apply
---------------------------------------------------------------------

-- | Applies a function to the first element of an n-ary tuple
--
-- >>> app1 (+1) (5,6,7)
-- (6,6,7)
app1 :: App f s 0 t => f -> s -> t
app1 f ~s = app f s (Proxy :: Proxy 0)

app2 :: App f s 1 t => f -> s -> t
app2 f s = app f s (Proxy :: Proxy 1)

app3 :: App f s 2 t => f -> s -> t
app3 f s = app f s (Proxy :: Proxy 2)

app4 :: App f s 3 t => f -> s -> t
app4 f s = app f s (Proxy :: Proxy 3)

app5 :: App f s 4 t => f -> s -> t
app5 f s = app f s (Proxy :: Proxy 4)

app6 :: App f s 5 t => f -> s -> t
app6 f s = app f s (Proxy :: Proxy 5)

app7 :: App f s 6 t => f -> s -> t
app7 f s = app f s (Proxy :: Proxy 6)

app8 :: App f s 7 t => f -> s -> t
app8 f s = app f s (Proxy :: Proxy 7)

app9 :: App f s 8 t => f -> s -> t
app9 f s = app f s (Proxy :: Proxy 8)

app10 :: App f s 9 t => f -> s -> t
app10 f s = app f s (Proxy :: Proxy 9)

class App f s (n :: Nat) t | f s n -> t where
  -- | Applies a function to the element at index @n@ in an n-ary tuple.
  --
  -- >>> app not (Proxy 2) (False,True,False)
  -- (False,True,True)
  --
  -- `app` also works for polymorphic functions
  --
  -- >>> app show (5,'c',False) (Proxy :: Proxy 2)
  -- (5,'c',"False")
  app :: f -> s -> Proxy n -> t

instance (GenericNP s rep_s, GenericNP t rep_t, GApp f rep_s (Lit n) rep_t) => App f s n t where
  app f s Proxy = to_np $ gapp f (from_np s) (Proxy :: Proxy (Lit n))

class GApp f s (n :: Nat') t | f s n -> t where
  gapp :: f -> s -> Proxy n -> t

instance {-# OVERLAPPING #-} (a ~ a', b ~ b') => GApp (a -> b) (NP I (a' ': xs)) Z' (NP I (b' ': xs)) where
  gapp f (I a :* xs) _ = I (f a) :* xs

instance {-# OVERLAPPING #-} GApp f (NP I xs) n (NP I xs') => GApp f (NP I (c ': xs)) (S' n) (NP I (c ': xs')) where
  gapp f (c :* xs) _ = c :* gapp f xs (Proxy :: Proxy n)

---------------------------------------------------------------------
-- Select
---------------------------------------------------------------------

-- | Selects the first element in an n-ary tuple
--
-- >>> sel1 (0,'d','c')
-- 0
sel1 :: Sel s 0 t => s -> t
sel1 ~s = sel s (Proxy :: Proxy 0)

sel2 :: Sel s 1 t => s -> t
sel2 s = sel s (Proxy :: Proxy 1)

sel3 :: Sel s 2 t => s -> t
sel3 s = sel s (Proxy :: Proxy 2)

sel4 :: Sel s 3 t => s -> t
sel4 s = sel s (Proxy :: Proxy 3)

sel5 :: Sel s 4 t => s -> t
sel5 s = sel s (Proxy :: Proxy 4)

sel6 :: Sel s 5 t => s -> t
sel6 s = sel s (Proxy :: Proxy 5)

sel7 :: Sel s 6 t => s -> t
sel7 s = sel s (Proxy :: Proxy 6)

sel8 :: Sel s 7 t => s -> t
sel8 s = sel s (Proxy :: Proxy 7)

sel9 :: Sel s 8 t => s -> t
sel9 s = sel s (Proxy :: Proxy 8)

sel10 :: Sel s 9 t => s -> t
sel10 s = sel s (Proxy :: Proxy 9)

--class Sel (n :: Nat) s a | n s -> a where

class Sel s (n :: Nat) t | s n -> t where
  -- | Takes an n-ary tuple and a `Proxy` carrying a `Nat`, returns the element with the index specified by the @Nat@
  --
  -- >>> sel (1,'d',False,'c') (Proxy :: Proxy 2)
  -- False
  sel :: s -> Proxy n -> t

instance (GenericNP s rep_s, GSel (RepNP s) (Lit n) t) => Sel s n t where
  sel s Proxy = gsel (from_np s) (Proxy :: Proxy (Lit n))

class GSel s (n :: Nat') t | s n -> t where
  gsel :: s -> Proxy n -> t

instance GSel (NP I (t ': xs)) Z' t where
  gsel np _ = unI $ hd np

instance GSel (NP I xs) n t => GSel (NP I (a ': xs)) (S' n) t where
  gsel np _ = gsel (tl np) (Proxy :: Proxy n)

---------------------------------------------------------------------
-- Mono
---------------------------------------------------------------------

class Mono f s t | f s -> t where
  -- | Maps a monomorphic function over each element in an n-ary tuple that matches the type of the argument of the function
  --
  -- >>> mmap not (True,'c',False)
  -- (False,'c',True)
  --
  -- Sometimes it is necessary to specify the result type.
  --
  -- >>> mmap (+1) (5,6,7,False) :: (Integer,Integer,Integer,Bool)
  -- (6,7,8,False)
  --
  -- Using `pmap` this is not necessary. However, to use `mapPolyT` the tuple may only contains elements of a single type.
  mmap :: f -> s -> t

instance (GenericNP s rep_s, GenericNP t rep_t, Applicable f rep_s ~ app, GMono f app rep_s rep_t) => Mono f s t where
  mmap f s = to_np $ gmmap f (Proxy :: Proxy app) (from_np s)

class GMono f (app :: [Bool]) s t | f app s -> t where
  gmmap :: f -> Proxy app -> s -> t

instance GMono f '[] (NP I '[]) (NP I '[]) where
  gmmap _ _ = id

instance GMono (a -> b) apps (NP I xs) (NP I xs') => GMono (a -> b) ('True ': apps) (NP I (a ': xs)) (NP I (b ': xs')) where
  gmmap f _ (I a :* xs) = I (f a) :* gmmap f (Proxy :: Proxy apps) xs

instance (a ~ a', b ~ b', GMono (Poly a b) apps (NP I xs) (NP I xs')) => GMono (Poly a b) ('True ': apps) (NP I (a' ': xs)) (NP I (b' ': xs')) where
  gmmap p@(Poly f) _ (I a :* xs) = I (f a) :* gmmap p (Proxy :: Proxy apps) xs

instance GMono f apps (NP I xs) (NP I xs') => GMono f ('False ': apps) (NP I (c ': xs)) (NP I (c ': xs')) where
  gmmap f _ (c :* xs) = c :* gmmap f (Proxy :: Proxy apps) xs

data Poly a b where
  Poly :: (a -> b) -> Poly a b

polyT :: (a -> b) -> Poly a b
polyT = Poly

-- | Applies a polymorphic function to each element in an n-ary tuple. Requires all elements in the tuple to be of the same type.
--
-- >>> pmap (+1) (5,6,7,8)
-- (6,7,8,9)
--
-- >>> pmap (+1) (5 :: Int,6,7,False)
-- No instance for (Num Bool) arising from the literal `5'
pmap :: Mono (Poly a b) s t => (a -> b) -> s -> t
pmap f s = mmap (polyT f) s

---------------------------------------------------------------------
-- Type utils
---------------------------------------------------------------------

type family Applicable f s where
  Applicable f (NP I '[]) = '[]
  Applicable (a -> b)     (NP I (a ': xs)) = 'True  ': Applicable (a -> b)     (NP I xs)
  Applicable (Poly a b)   (NP I (d ': xs)) = 'True  ': Applicable (Poly a b) (NP I xs)
  Applicable (a -> b)     (NP I (c ': xs)) = 'False ': Applicable (a -> b)     (NP I xs)

type family ApplicableN f s n where
  ApplicableN (a -> b)     (NP I (a ': xs)) Z'     = '[ 'True ]
  ApplicableN (Poly a b)   (NP I (d ': xs)) Z'     = '[ 'True ]
  ApplicableN f            (NP I (a ': xs)) (S' n) = 'False ': ApplicableN f (NP I xs) n

type family Tuple s where
  Tuple (NP I '[]) = ()
  Tuple (NP I '[a]) = a
  Tuple (NP I '[a, b]) = (a,b)
  Tuple (NP I '[a, b, c]) = (a,b,c)
  Tuple (NP I '[a, b, c, d]) = (a,b,c,d)
  Tuple (NP I '[a, b, c, d, e]) = (a,b,c,d,e)
  Tuple (NP I '[a, b, c, d, e, f]) = (a,b,c,d,e,f)
  Tuple (NP I '[a, b, c, d, e, f, g]) = (a,b,c,d,e,f,g)
  Tuple (NP I '[a, b, c, d, e, f, g, h]) = (a,b,c,d,e,f,g,h)
  Tuple (NP I '[a, b, c, d, e, f, g, h, i]) = (a,b,c,d,e,f,g,h,i)
  Tuple (NP I '[a, b, c, d, e, f, g, h, i, j]) = (a,b,c,d,e,f,g,h,i,j)
  Tuple (NP I '[a, b, c, d, e, f, g, h, i, j, k]) = (a,b,c,d,e,f,g,h,i,j,k)

data Nat' = Z' | S' Nat'

type family Lit (n :: Nat) :: Nat' where
  Lit 0 = Z'
  Lit n = S' (Lit (n - 1))

class RepNP s ~ rep => GenericNP s rep | s -> rep, rep -> s where
  type RepNP s :: *
  from_np :: RepNP s ~ rep => s -> rep
  to_np :: RepNP s ~ rep => rep -> s

instance (Generic s, Rep s ~ SOP I '[xs], RepNP s ~ rep, Tuple rep ~ s) => GenericNP s rep where
  type RepNP s = ToNP (Rep s)
  from_np s = gtoNP $ from s
  to_np p = to $ gfromNP p

type family ToNP s where
  ToNP (SOP I '[xs]) = NP I xs

gtoNP :: (SOP I '[xs]) -> NP I xs
gtoNP (SOP (Z np)) = np

gfromNP :: NP I xs -> SOP I '[xs]
gfromNP np = SOP $ Z np

