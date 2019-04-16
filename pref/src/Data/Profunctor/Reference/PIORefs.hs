{-# LANGUAGE TemplateHaskell, CPP #-}

{-# LANGUAGE  FlexibleContexts, ScopedTypeVariables           #-}

module Data.Profunctor.Reference.PIORefs where

import Data.IORef
import Data.Monoid
import Data.Profunctor.Optic hiding (has)
import Data.Profunctor.Reference.PRefs
import Data.Profunctor.Reference.Global
import Data.Profunctor.Reference.Types
import Data.Validation (Validation(..))
import Data.Tuple (swap)
import Control.Category ((>>>),(<<<))

import Data.Void
import Control.Monad.Trans.Reader


--import Control.Concurrent.STM
--
import Control.Monad.Reader
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible

import Control.Applicative
-- $setup
-- >>> :set -XTypeApplications
-- >>> :set -XScopedTypeVariables
-- >>> :set -XOverloadedStrings
-- >>> import Data.IORef
-- >>> import Data.Monoid (Sum(..))
-- >>> import Data.Profunctor.Optic



-- | 'PRefs are profunctors.
--
-- 'dimap' example:
--
-- >>> s = ("hi",2) :: (String, Int)
-- >>> t = ("there!",2) :: (String, Int)
-- >>> rs <- newRef @IO @IORef s
-- >>> rt <- newRef @IO @IORef t
-- >>> o :: PIORefs Profunctor (String, Int) (String, Int) = PIORefs id rt rs
-- >>> readPIORefs (dimap id fst o)
-- "hi"
--
-- >>> tosnd a = ("bye", a)
-- >>> o' :: PIORefs Profunctor Int String = dimap tosnd fst o
-- >>> modifyPIORefs o' length >> readRef rt
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
o :: PIORefs Strong Int String = PRefs _1 rt rs
--o :: PIORefs Profunctor (String, Int) (String, Int) = PIORefs id rt rs
o' = dimap id length o
readPIORefs o'

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

data Config = Config { cnum :: Int, cstr :: String }
--make lenses

--type (a <– b) = Op a b
out :: Op a Void
out = Op absurd 

--foo :: PRefs c (Op a) ((->) (String, Int)) Int String
foo :: PRefs Profunctor (Op a) ((->) (String, Int)) Void String
foo = PRefs (dimap fst absurd) id out 

foo' :: Decidable f => PRefs Profunctor f ((->) (String, Int)) b String
foo' = PRefs (dimap fst id) id conquer

-- null :: PRefs Profunctor g f Void ()
--withfoo :: Applicative f => PRefs Profunctor SettableStateVar f b Void
--withfoo = PRefs () pure printout

-- you can essentially write to a contravariant functor (>$) :: b -> f b -> f a
--  contramap . const
--  runReader hasfoo ("hi", 3)
-- "hi"
hasfoo :: MonadReader (String, Int) m => m String
hasfoo = has foo

nada :: (Functor f, Contravariant f) => f a -> f b
nada x = () <$ x $< ()


hasfoobar
  :: PRefs Profunctor rt ry b Void
  -> PRefs Profunctor rt ((->) (String, Int)) b String
hasfoobar = (foo >.>)

-- <$< foo


inp :: GettableStateVar (String, Int)
inp = makeGettableStateVar $ readIORef x

debug :: Show a => SettableStateVar a
debug = SettableStateVar print

printout :: SettableStateVar (String, Int)
printout = debug


trefs :: PRefs Strong SettableStateVar GettableStateVar String String
trefs = PRefs _1 inp printout

{-
> get trefs
"hi!"
> trefs $= "hello!"
("hello!",2)
> get trefs
"hi!"
> trefs $~ (++ " ahoy!")
("hi! ahoy!",2)
-}

--declareTMVar "ytm" [t| (Int, String) |] [e| (4, "there") |]
--type Server' b' b m r = forall x' x. Proxy x' x b' b m r
--type Pipe a b = Proxy () a () b

--fooPfm :: c Tagged => Pf IO c b a -> IO ()
--fooPfm (PIORefs o _ rt) = runContT rt print -- $ (f . review o) 

{-
out <- makeOutputStream $ maybe (return ()) (writeIORef y)
> inp <- makeInputStream $ return (Just x)
> st = PRefs swapped inp out

st :: PRefs Profunctor OutputStream InputStream (String, Int) (Int, String)
st = PRefs swapped inp out

foup :: IO (OutputStream (Int, String))
foup = makeOutputStream $ maybe (return ()) (writeIORef y)


ok = PRefs swapped (Star ReaderT) (Star ReaderT)

-}

{-
foof :: Monad m => PRefs Profunctor m m (String, Int) (Int, String) 
foof = PRefs swapped (return ("hi!", 2)) (return (4, "there"))

i :: PRefs Profunctor IORef IORef (String, Int) (Int, String) 
i = PRefs swapped x y

-- like i, but with a [] in covariant pos
h :: PRefs Profunctor IORef [] (String, Int) (Int, String) 
h = PRefs swapped [("hi!", 2)] y

j :: PRefs Profunctor IORef IORef (Int, String) (String, Int) 
j = PRefs swapped y x

-- like j, but with an MVar in contravariant pos
k :: PRefs Profunctor MVar IORef (Int, String) (String, Int) 
k = PRefs swapped y xm


ji :: PRefs Profunctor IORef IORef (Int, String) (Int, String)
ji = j >>> i
-}
{-
-- category instance requires that rs / rt be fixed
ki :: PRefs Profunctor MVar IORef (Int, String) (Int, String)
ki = k `compose_pxy` i

kh :: PRefs Profunctor MVar [] (Int, String) (Int, String) 
kh = k `compose_pxy` h

ij :: PRefs Profunctor IORef IORef (String, Int) (String, Int)
ij = i >>> j

--Optic p (Int, String) (String, Int) (String, Int) (Int, String)


-- like
--p (String, Int) (Int, String) (Int, String) (String, Int)






jik :: PRefs Profunctor IORef IORef (Int, String) (String, Int)
jik = ji `compose_pxy` k


kij :: PRefs Profunctor MVar IORef (Int, String) (String, Int)
kij = k `compose_pxy` ij

foo :: PRefs Profunctor y s (String, Int) a  -> PRefs Profunctor MVar s (Int, String) a
foo = (k `compose_pxy`)
-}

{-
len :: [a] -> Int
len = length 

j' :: PRefs Profunctor IORef IORef ([a], String) (String, Int)
j' = lmap (bimap len id) j

i' :: PRefs Profunctor IORef IORef (String, Int) (String, String)
i' = rmap (bimap show id) i

i'j' :: PRefs Profunctor IORef IORef (String, Int) (String, Int)
i'j' = i' >>> j'

j'i' :: PRefs Profunctor IORef IORef ([a], String) (String, String)
j'i' = j' >>> i'
-}

{-
o_xt :: PIORefs Strong Int String 
o_xt = PRefs _1 x t

o_ty :: PIORefs Strong String Int 
o_ty = PRefs _2 t y

-- o_xy = o_xt >>> o_ty

-}


type PIORefs c b a = PRefs c IORef IORef b a

---------------------------------------------------------------------
--  Creating 'PIORefs's
---------------------------------------------------------------------

-- | Create a new 'PIORefs' with purely local state.
--
-- The optic argument is exposed for completeness, but in most cases
-- should be set to 'id'.
newLocalPIORefs 
  :: Optical c s t a b 
  -> s 
  -> t
  -> IO (PIORefs c b a)
newLocalPIORefs o s t = (PRefs o) <$> newIORef s <*> newIORef t


-- | A variant of 'newLocalPIORefs' that uses the same ref for both read
--
-- and write operations. Note that this is distinct from a 'PIORefs''.
newLocalPIORefs'
  :: Optical c s s a a 
  -> s 
  -> IO (PIORefs c a a)
newLocalPIORefs' o s = newLocalPIORefs o s s 


---------------------------------------------------------------------
--  Reading 'PIORefs's
---------------------------------------------------------------------


-- | Read a value from a 'PIORefs'.
--
--
readPIORefs 
  :: c (Star (Const a)) 
  => PIORefs c b a 
  -> IO a
readPIORefs (PRefs o rs _) = view o <$> readIORef rs


-- | Read a value from a 'PIORefs' with profunctorial choice.
previewPIORefs 
  :: c (Star (Const (First a)))
  => PIORefs c b a 
  -> IO (Maybe a)
previewPIORefs (PRefs o rs _) = preview o <$> readIORef rs 



-- | A variant of 'previewPIORefs' that updates the write ref on failure.
--
-- If the read and write refs are the same then this function reduces
-- to 'previewPIORefs' with the overhead of an extra io operation.
matchPIORefs
  :: c (Star (Either a))
  => PIORefs c b a 
  -> IO (Maybe a)
matchPIORefs (PRefs o rs rt) =
  do s <- readIORef rs
     case match o s of
       Left t -> 
         writeIORef rt t >> return Nothing
       Right a ->
         return $ Just a


-- | A variant of 'matchPIORefs' that uses the `Validation` applicative.
--
-- If the read and write refs are the same then this function reduces
-- to 'previewPIORefs' with the overhead of an extra io operation.
validatePIORefs
  :: c (Star (Validation a))
  => PIORefs c b a 
  -> IO (Maybe a)
validatePIORefs (PRefs o rs rt) =
  do s <- readIORef rs
     case validateOf o s of
       Failure t -> 
         writeIORef rt t >> return Nothing
       Success a ->
         return $ Just a



foldMapOfPIORefs
  :: c (Star (Const r))
  => PIORefs c b a 
  -> (a -> r)
  -> IO r
foldMapOfPIORefs (PRefs o rs _) f = foldMapOf o f <$> readIORef rs 


-- sumPIORefs?
sumOfPIORefs :: c (Star (Const (Sum a))) => PIORefs c b a -> IO a
sumOfPIORefs r = getSum <$> foldMapOfPIORefs r Sum



---------------------------------------------------------------------
--  Modifying 'PIORefs's
---------------------------------------------------------------------

-- | Write operation that only opens the write ref.
--
-- Use this with 'Choice'-constrained optics.  Use 'modifyPIORefs' with
-- a constant argument to modify lens-like optics.
writePIORefs :: c (Costar (Const b)) => PIORefs c b a -> b -> IO ()
writePIORefs (PRefs o _ rt) b = writeIORef rt . review o $ b


-- | Modify a 'PIORefs'.
--
-- Note that this operation is lazy. Depending on use unevaluated 
-- expression thunks can pile up in memory resulting in a space leak. 
-- To update strictly use 'modifyPIORefs''.
--
-- Lens example:
--
-- >>> s = ("hi!",2) :: (String, Int)
-- >>> t = (4,2)  :: (Int, Int)
-- >>> rs <- newRef @IO @IORef s
-- >>> rt <- newRef @IO @IORef t
-- >>> o :: PIORefs Strong Int String = PRefs _1 rt rs
-- >>> o' :: PIORefs Strong String String = PRefs _1 rs rs
--
-- >>> modifyPIORefs o' tail >> readIORef rs 
-- ("i!",2)
-- >>> readIORef rt 
-- (4,2)
-- >>> modifyPIORefs o length >> readIORef rs
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
-- >>> o :: PIORefs Choice Int String = PRefs _Just rt rs
-- >>> o' :: PIORefs Choice String String = PRefs _Just rs rs
-- >>> modifyPIORefs o' tail >> readIORef rs
-- Just "i!"
-- >>> readIORef rt 
-- Nothing
-- >>> modifyPIORefs o length >> readIORef rs
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
-- >>> o :: PIORefs Traversing (Sum Int) String = PRefs traversed rt rs
-- >>> o' :: PIORefs Traversing String String = PRefs traversed rs rs
-- >>> modifyPIORefs o (Sum . length) >> readIORef rs
-- ["hi","there"]
-- >>> readIORef rt 
-- [Sum {getSum = 2},Sum {getSum = 5}]
-- >>> modifyPIORefs o' ("oh" ++) >> readIORef rs
-- ["ohhi","ohthere"]
--
modifyPIORefs 
  :: c (->)
  => PIORefs c b a 
  -> (a -> b) 
  -> IO ()
modifyPIORefs (PRefs o rs rt) f = readIORef rs >>= writeIORef rt . over o f



-- | Strict variant of 'modifyPIORefs'. This forces both the value stored
--
-- as well as the value returned. This function is atomic when r is a 
-- TVar or TMVar.
modifyPIORefs' :: c (->) => PIORefs c b a -> (a -> b) -> IO ()
modifyPIORefs' (PRefs o rs rt) f =
  do s <- readIORef rs
     let t = over o f s
     t `seq` writeIORef rt t


-- TODO more like foldState
atomicModifyPIORefs'
  :: c (Star ((,) a))
  => PIORefs c b a 
  -> (a -> (a, b))
  -> IO ()
atomicModifyPIORefs' (PRefs o rs rt) f = 
  do s <- readIORef rs
     let t = pstate o f s
     t `seq` writeIORef rt t









{-



-- Affine PIORefs
--
aff :: Affine (Either c a, d) (Either c b, d) a b
aff = first' . right'

s = (Just "hi!", 2) :: (Maybe String, Int)
t = (Nothing, 2) :: (Maybe Int, Int)

rs <- newRef @IORef @IO s
rt <- newRef @IORef @IO t

o :: PIORefs IORef AffineLike Int String = PIORefs (_1 . _Just) rs rt
o' :: PIORefs IORef AffineLike String String = PIORefs (_1 . _Just) rs rs


modifyPIORefs o' tail >> readRef rs >>= print >> readRef rt >>= print
-- (Just "i!",2)
-- (Nothing,2)

modifyPIORefs o length >> readRef rs >>= print >> readRef rt >>= print
--(Just "i!",2)
--(Just 2,2)


-- Affine PIORefs 2
--

s = (Nothing, 2) :: (Maybe String, Int)
t = (Just 4, 2) :: (Maybe Int, Int)

rs <- newRef @IORef @IO s
rt <- newRef @IORef @IO t

o :: PIORefs IORef AffineLike Int String = PIORefs (_1 . _Just) rs rt
o' :: PIORefs IORef AffineLike String String = PIORefs (_1 . _Just) rs rs


modifyPIORefs o' tail >> readRef rs >>= print >> readRef rt >>= print
-- (Nothing,2)
-- (Just 4,2)

modifyPIORefs o length >> readRef rs >>= print >> readRef rt >>= print
-- (Nothing,2)
-- (Nothing,2)


-}



