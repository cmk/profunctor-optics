{-# LANGUAGE TemplateHaskell, CPP #-}

module Data.Profunctor.Reference.PIORef where

import Data.IORef
import Data.Monoid
import Data.Profunctor.Optic
import Data.Profunctor.Reference.Types
import Data.Profunctor.Reference.Global

import Data.Tuple (swap)
import Control.Category ((>>>),(<<<))


import Control.Monad.Trans.Reader
--import Control.Concurrent.STM
import Control.Concurrent.MVar (MVar)
-- $setup
-- >>> :set -XTypeApplications
-- >>> :set -XScopedTypeVariables
-- >>> :set -XOverloadedStrings
-- >>> import Data.IORef
-- >>> import Data.Monoid (Sum(..))
-- >>> import Data.Profunctor.Optic



-- | 'PRef's are profunctors.
--
-- 'dimap' example:
--
-- >>> s = ("hi",2) :: (String, Int)
-- >>> t = ("there!",2) :: (String, Int)
-- >>> rs <- newRef @IO @IORef s
-- >>> rt <- newRef @IO @IORef t
-- >>> o :: PIORef Profunctor (String, Int) (String, Int) = PIORef id rt rs
-- >>> readPIORef (dimap id fst o)
-- "hi"
--
-- >>> tosnd a = ("bye", a)
-- >>> o' :: PIORef Profunctor Int String = dimap tosnd fst o
-- >>> modifyPIORef o' length >> readRef rt
-- ("bye",2)
-- >>> readRef rs
-- ("hi",2)



{-

:set -XTypeApplications
:set -XScopedTypeVariables
:set -XOverloadedStrings
import Data.IORef
s = ("hi!",2) :: (String, Int)
--t = ("there!",2) :: (String, Int)
t = (4,2)  :: (Int, Int)
rs <- newRef @IO @IORef s
rt <- newRef @IO @IORef t
o :: PIORef Strong Int String = PRef _1 rt rs
--o :: PIORef Profunctor (String, Int) (String, Int) = PIORef id rt rs
o' = dimap id length o
readPIORef o'

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

-}


declareIORef "t" [t| (Int, Int) |] [e| (4, 2) |]
declareIORef "x" [t| (String, Int) |] [e| ("hi!", 2) |]
declareIORef "y" [t| (Int, String) |] [e| (4, "there") |]

declareMVar "xm" [t| (String, Int) |] [e| ("hi!", 2) |]

swapped :: Iso (a, b) (b', a') (b, a) (a', b')
swapped = iso swap swap

--declareTMVar "ytm" [t| (Int, String) |] [e| (4, "there") |]
--type Server' b' b m r = forall x' x. Proxy x' x b' b m r
--type Pipe a b = Proxy () a () b

--fooPfm :: c Tagged => Pf IO c b a -> IO ()
--fooPfm (PIORef o _ rt) = runContT rt print -- $ (f . review o) 

{-
out <- makeOutputStream $ maybe (return ()) (writeIORef y)
> inp <- makeInputStream $ return (Just x)
> st = PRef swapped inp out

st :: PRef Profunctor OutputStream InputStream (String, Int) (Int, String)
st = PRef swapped inp out

foup :: IO (OutputStream (Int, String))
foup = makeOutputStream $ maybe (return ()) (writeIORef y)


ok = PRef swapped (Star ReaderT) (Star ReaderT)

-}


foof :: Monad m => PRef Profunctor m m (String, Int) (Int, String) 
foof = PRef swapped (return ("hi!", 2)) (return (4, "there"))

i :: PRef Profunctor IORef IORef (String, Int) (Int, String) 
i = PRef swapped x y

-- like i, but with a [] in covariant pos
h :: PRef Profunctor IORef [] (String, Int) (Int, String) 
h = PRef swapped [("hi!", 2)] y

j :: PRef Profunctor IORef IORef (Int, String) (String, Int) 
j = PRef swapped y x

-- like j, but with an MVar in contravariant pos
k :: PRef Profunctor MVar IORef (Int, String) (String, Int) 
k = PRef swapped y xm


ji :: PRef Profunctor IORef IORef (Int, String) (Int, String)
ji = j >>> i

-- category instance requires that rs / rt be fixed
ki :: PRef Profunctor MVar IORef (Int, String) (Int, String)
ki = k `compose_pxy` i

kh :: PRef Profunctor MVar [] (Int, String) (Int, String) 
kh = k `compose_pxy` h

ij :: PRef Profunctor IORef IORef (String, Int) (String, Int)
ij = i >>> j

--Optic p (Int, String) (String, Int) (String, Int) (Int, String)


-- like
--p (String, Int) (Int, String) (Int, String) (String, Int)






jik :: PRef Profunctor IORef IORef (Int, String) (String, Int)
jik = ji `compose_pxy` k


kij :: PRef Profunctor MVar IORef (Int, String) (String, Int)
kij = k `compose_pxy` ij

foo :: PRef Profunctor y s (String, Int) a  -> PRef Profunctor MVar s (Int, String) a
foo = (k `compose_pxy`)

len :: [a] -> Int
len = length 

j' :: PRef Profunctor IORef IORef ([a], String) (String, Int)
j' = lmap (bimap len id) j

i' :: PRef Profunctor IORef IORef (String, Int) (String, String)
i' = rmap (bimap show id) i

i'j' :: PRef Profunctor IORef IORef (String, Int) (String, Int)
i'j' = i' >>> j'

j'i' :: PRef Profunctor IORef IORef ([a], String) (String, String)
j'i' = j' >>> i'


{-
o_xt :: PIORef Strong Int String 
o_xt = PRef _1 x t

o_ty :: PIORef Strong String Int 
o_ty = PRef _2 t y

-- o_xy = o_xt >>> o_ty

-}


---------------------------------------------------------------------
--  Creating 'PIORef's
---------------------------------------------------------------------

-- | Create a new 'PIORef' with purely local state.
--
-- The optic argument is exposed for completeness, but in most cases
-- should be set to 'id'.
newLocalPIORef 
  :: Optical c s t a b 
  -> s 
  -> t
  -> IO (PIORef c b a)
newLocalPIORef o s t = (PRef o) <$> newIORef s <*> newIORef t


-- | A variant of 'newLocalPIORef' that uses the same ref for both read
--
-- and write operations. Note that this is distinct from a 'PIORef''.
newLocalPIORef'
  :: Optical c s s a a 
  -> s 
  -> IO (PIORef c a a)
newLocalPIORef' o s = newLocalPIORef o s s 


---------------------------------------------------------------------
--  Reading 'PIORef's
---------------------------------------------------------------------

-- | Read a value from a 'PIORef'.
--
--
readPIORef 
  :: c (Forget a)
  => PIORef c b a 
  -> IO a
readPIORef (PRef o s _) = view o <$> readIORef s

-- | Read a value from a 'PIORef' with profunctorial choice.
previewPIORef 
  :: c (Previewed a)
  => PIORef c b a 
  -> IO (Maybe a)
previewPIORef (PRef o s _) = preview o <$> readIORef s 


-- | A variant of 'previewPIORef' that updates the write ref on failure.
--
-- If the read and write refs are the same then this function reduces
-- to 'previewPIORef' with the overhead of an extra io operation.
matchPIORef
  :: c (Matched a)
  => PIORef c b a 
  -> IO (Maybe a)
matchPIORef (PRef o rs rt) =
  do s <- readIORef rs
     case match o s of
       Left t -> 
         writeIORef rt t >> return Nothing
       Right a ->
         return $ Just a


foldMapOfPIORef
  :: c (Forget r)
  => PIORef c b a 
  -> (a -> r)
  -> IO r
foldMapOfPIORef (PRef o rs _) f = foldMapOf o f <$> readIORef rs 


-- sumPIORef?
sumOfPIORef :: c (Forget (Sum a)) => PIORef c b a -> IO a
sumOfPIORef r = getSum <$> foldMapOfPIORef r Sum



---------------------------------------------------------------------
--  Modifying 'PIORef's
---------------------------------------------------------------------

-- | Write operation that only opens the write ref.
--
-- Use this with 'Choice'-constrained optics.  Use 'modifyPIORef' with
-- a constant argument to modify lens-like optics.
writePIORef :: c Tagged => PIORef c b a -> b -> IO ()
writePIORef (PRef o _ rt) b = writeIORef rt . review o $ b


-- | Modify a 'PIORef'.
--
-- Note that this operation is lazy. Depending on use unevaluated 
-- expression thunks can pile up in memory resulting in a space leak. 
-- To update strictly use 'modifyPIORef''.
--
-- Lens example:
--
-- >>> s = ("hi!",2) :: (String, Int)
-- >>> t = (4,2)  :: (Int, Int)
-- >>> rs <- newRef @IO @IORef s
-- >>> rt <- newRef @IO @IORef t
-- >>> o :: PIORef Strong Int String = PRef _1 rt rs
-- >>> o' :: PIORef Strong String String = PRef _1 rs rs
--
-- >>> modifyPIORef o' tail >> readIORef rs 
-- ("i!",2)
-- >>> readIORef rt 
-- (4,2)
-- >>> modifyPIORef o length >> readIORef rs
-- ("i!",2)
-- >>> readIORef rt 
-- (2,2)
--
--
-- Prism example:
--
-- >>> s = Just "hi!" :: Maybe String
-- >>> t = Nothing  :: Maybe Int
-- >>> rs <- newRef @IO @IORef s
-- >>> rt <- newRef @IO @IORef t
-- >>> o :: PIORef Choice Int String = PRef _Just rt rs
-- >>> o' :: PIORef Choice String String = PRef _Just rs rs
-- >>> modifyPIORef o' tail >> readIORef rs
-- Just "i!"
-- >>> readIORef rt 
-- Nothing
-- >>> modifyPIORef o length >> readIORef rs
-- Just "i!"
-- >>> readIORef rt 
-- Just 2
--
--
-- Traversal example:
--
-- >>> s = ["hi", "there"] :: [String]
-- >>> t = fmap Sum [1..10] :: [Sum Int]
-- >>> rs <- newRef @IO @IORef s
-- >>> rt <- newRef @IO @IORef t
-- >>> o :: PIORef Traversing (Sum Int) String = PRef traversed rt rs
-- >>> o' :: PIORef Traversing String String = PRef traversed rs rs
-- >>> modifyPIORef o (Sum . length) >> readIORef rs
-- ["hi","there"]
-- >>> readIORef rt 
-- [Sum {getSum = 2},Sum {getSum = 5}]
-- >>> modifyPIORef o' ("oh" ++) >> readIORef rs
-- ["ohhi","ohthere"]
--
modifyPIORef 
  :: c (->)
  => PIORef c b a 
  -> (a -> b) 
  -> IO ()
modifyPIORef (PRef o rs rt) f = readIORef rs >>= writeIORef rt . over o f

-- | Strict variant of 'modifyPIORef'. This forces both the value stored
--
-- as well as the value returned. This function is atomic when r is a 
-- TVar or TMVar.
modifyPIORef' :: c (->) => PIORef c b a -> (a -> b) -> IO ()
modifyPIORef' (PRef o rs rt) f =
  do s <- readIORef rs
     let t = over o f s
     t `seq` writeIORef rt t

-- TODO more like foldState
atomicModifyPIORef'
  :: c (Star ((,) a))
  => PIORef c b a 
  -> (a -> (a, b))
  -> IO ()
atomicModifyPIORef' (PRef o rs rt) f = 
  do s <- readIORef rs
     let t = pstate o f s
     t `seq` writeIORef rt t






{-


atomicModifyIORef' :: IORef a -> (a -> (a, b)) -> IO b
statePIORef :: Optic (Star ((,) a)) s t a b -> (a -> (a, b)) -> s -> t

over :: Optic (->) s t a b -> (a -> b) -> s -> t
over = id

review :: Optic Tagged s t a b -> b -> t
review = through Tagged unTagged

-- | 'view o == foldMapOf o id'
view :: Optic (Forget a) s t a b -> s -> a
view o = (through Forget runForget) o id

match :: Optic (Matched a) s t a b -> s -> Either t a
match o = (through Matched runMatched) o Right

preview :: Optic (Previewed a) s t a b -> s -> Maybe a
preview o = (through Previewed runPreviewed) o Just

foldMapOf :: Optic (Forget r) s t a b -> (a -> r) -> s -> r
foldMapOf = through Forget runForget

zipWithOf :: Optic Zipped s t a b -> (a -> a -> b) -> s -> s -> t
zipWithOf = through Zipped runZipped 


zipWithPIORef' :: c Zipped => PIORef c b a -> (a -> a -> b) -> IO ()
zipWithPIORef' (PIORef o rs rt) f =
  do s <- readIORef rs
     let t = zipWithOf o f s s 
     t `seq` writeIORef rt t

-- | 'traverseOf' can be used to convert 'Strong' optics to their
-- van Laarhoven equivalents.
traverseOf :: Optic (Star f) s t a b -> (a -> f b) -> s -> f t
traverseOf = through Star runStar

cotraverseOf :: Optic (Costar f) s t a b -> (f a -> b) -> (f s -> t)
cotraverseOf = through Costar runCostar
-}




{-



-- Affine PIORef
--
aff :: Affine (Either c a, d) (Either c b, d) a b
aff = first' . right'

s = (Just "hi!", 2) :: (Maybe String, Int)
t = (Nothing, 2) :: (Maybe Int, Int)

rs <- newRef @IORef @IO s
rt <- newRef @IORef @IO t

o :: PIORef IORef AffineLike Int String = PIORef (_1 . _Just) rs rt
o' :: PIORef IORef AffineLike String String = PIORef (_1 . _Just) rs rs


modifyPIORef o' tail >> readRef rs >>= print >> readRef rt >>= print
-- (Just "i!",2)
-- (Nothing,2)

modifyPIORef o length >> readRef rs >>= print >> readRef rt >>= print
--(Just "i!",2)
--(Just 2,2)


-- Affine PIORef 2
--

s = (Nothing, 2) :: (Maybe String, Int)
t = (Just 4, 2) :: (Maybe Int, Int)

rs <- newRef @IORef @IO s
rt <- newRef @IORef @IO t

o :: PIORef IORef AffineLike Int String = PIORef (_1 . _Just) rs rt
o' :: PIORef IORef AffineLike String String = PIORef (_1 . _Just) rs rs


modifyPIORef o' tail >> readRef rs >>= print >> readRef rt >>= print
-- (Nothing,2)
-- (Just 4,2)

modifyPIORef o length >> readRef rs >>= print >> readRef rt >>= print
-- (Nothing,2)
-- (Nothing,2)


-}



