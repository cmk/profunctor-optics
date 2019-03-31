{-# LANGUAGE TemplateHaskell, CPP #-}

module Data.Profunctor.Reference.PRef where

import Data.IORef
import Data.Monoid
import Data.Profunctor.Optic
import Data.Profunctor.Reference.Types
import Data.Profunctor.Reference.Global


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
-- >>> o :: PRef Profunctor (String, Int) (String, Int) = PRef id rt rs
-- >>> readPRef (dimap id fst o)
-- "hi"
--
-- >>> tosnd a = ("bye", a)
-- >>> o' :: PRef Profunctor Int String = dimap tosnd fst o
-- >>> modifyP o' length >> readRef rt
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
o :: PRef Strong Int String = PRef _1 rt rs
--o :: PRef Profunctor (String, Int) (String, Int) = PRef id rt rs
o' = dimap id length o
readP o'

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

declareIORef "rs" [t| (String, Int) |] [e| ("hi!", 2) |]
declareIORef "rt" [t| (Int, Int) |] [e| (4, 2) |]

i :: PRef Profunctor (String, Int) (String, Int) 
i = Pxy id rs rs

o :: PRef Strong Int String 
o = Pxy _1 rs rt

type PRef = Pxy IORef IORef

---------------------------------------------------------------------
--  Creating 'PRef's
---------------------------------------------------------------------

-- | Create a new 'PRef' with purely local state.
--
-- The optic argument is exposed for completeness, but in most cases
-- should be set to 'id'.
newLocalPRef 
  :: Optical c s t a b 
  -> s 
  -> t
  -> IO (PRef c b a)
newLocalPRef o s t = (Pxy o) <$> newIORef s <*> newIORef t


-- | A variant of 'newLocalPRef' that uses the same ref for both read
--
-- and write operations. Note that this is distinct from a 'PRef''.
newLocalPRef'
  :: Optical c s s a a 
  -> s 
  -> IO (PRef c a a)
newLocalPRef' o s = newLocalPRef o s s 


---------------------------------------------------------------------
--  Reading 'PRef's
---------------------------------------------------------------------

-- | Read a value from a 'PRef'.
--
--
readPRef 
  :: c (Forget a)
  => PRef c b a 
  -> IO a
readPRef (Pxy o s _) = view o <$> readIORef s


-- | Read a value from a 'PRef' with profunctorial choice.
previewPRef 
  :: c (Previewed a)
  => PRef c b a 
  -> IO (Maybe a)
previewPRef (Pxy o s _) = preview o <$> readIORef s 


-- | A variant of 'previewPRef' that updates the write ref on failure.
--
-- If the read and write refs are the same then this function reduces
-- to 'previewPRef' with the overhead of an extra io operation.
matchPRef
  :: c (Matched a)
  => PRef c b a 
  -> IO (Maybe a)
matchPRef (Pxy o rs rt) =
  do s <- readIORef rs
     case match o s of
       Left t -> 
         writeIORef rt t >> return Nothing
       Right a ->
         return $ Just a


foldMapOfPRef
  :: c (Forget r)
  => PRef c b a 
  -> (a -> r)
  -> IO r
foldMapOfPRef (Pxy o rs _) f = foldMapOf o f <$> readIORef rs 


-- sumPRef?
sumOfPRef :: c (Forget (Sum a)) => PRef c b a -> IO a
sumOfPRef r = getSum <$> foldMapOfPRef r Sum



---------------------------------------------------------------------
--  Modifying 'PRef's
---------------------------------------------------------------------

-- | Write operation that only opens the write ref.
--
-- Use this with 'Choice'-constrained optics.  Use 'modifyPRef' with
-- a constant argument to modify lens-like optics.
writePRef :: c Tagged => PRef c b a -> b -> IO ()
writePRef (Pxy o _ rt) b = writeIORef rt . review o $ b


-- | Modify a 'PRef'.
--
-- Note that this operation is lazy. Depending on use unevaluated 
-- expression thunks can pile up in memory resulting in a space leak. 
-- To update strictly use 'modifyPRef''.
--
-- Lens example:
--
-- >>> s = ("hi!",2) :: (String, Int)
-- >>> t = (4,2)  :: (Int, Int)
-- >>> rs <- newRef @IO @IORef s
-- >>> rt <- newRef @IO @IORef t
-- >>> o :: PRef Strong Int String = PRef _1 rt rs
-- >>> o' :: PRef Strong String String = PRef _1 rs rs
--
-- >>> modifyP o' tail >> readIORef rs 
-- ("i!",2)
-- >>> readIORef rt 
-- (4,2)
-- >>> modifyP o length >> readIORef rs
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
-- >>> o :: PRef Choice Int String = PRef _Just rt rs
-- >>> o' :: PRef Choice String String = PRef _Just rs rs
-- >>> modifyP o' tail >> readIORef rs
-- Just "i!"
-- >>> readIORef rt 
-- Nothing
-- >>> modifyP o length >> readIORef rs
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
-- >>> o :: PRef Traversing (Sum Int) String = PRef traversed rt rs
-- >>> o' :: PRef Traversing String String = PRef traversed rs rs
-- >>> modifyP o (Sum . length) >> readIORef rs
-- ["hi","there"]
-- >>> readIORef rt 
-- [Sum {getSum = 2},Sum {getSum = 5}]
-- >>> modifyP o' ("oh" ++) >> readIORef rs
-- ["ohhi","ohthere"]
--
modifyPRef 
  :: c (->)
  => PRef c b a 
  -> (a -> b) 
  -> IO ()
modifyPRef (Pxy o rs rt) f = readIORef rs >>= writeIORef rt . over o f


-- | Strict variant of 'modifyPRef'. This forces both the value stored
--
-- as well as the value returned. This function is atomic when r is a 
-- TVar or TMVar.
modifyPRef' :: c (->) => PRef c b a -> (a -> b) -> IO ()
modifyPRef' (Pxy o rs rt) f =
  do s <- readIORef rs
     let t = over o f s
     t `seq` writeIORef rt t









{-
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


zipWithPRef' :: c Zipped => PRef c b a -> (a -> a -> b) -> IO ()
zipWithPRef' (Pxy o rs rt) f =
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
