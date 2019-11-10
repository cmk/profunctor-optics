{-# LANGUAGE GADTs #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ExistentialQuantification #-}
module Data.Profunctor.Arrow where

import Control.Arrow (Arrow, Kleisli(..))
import Control.Category hiding ((.), id)
import Control.Comonad (Comonad, Cokleisli(..))
import Control.Monad hiding (join)
import Data.Profunctor
import Data.Profunctor.Misc

import qualified Control.Arrow as A
import qualified Control.Category as C
import Data.Profunctor.Composition
import Data.Profunctor.Choice
import Data.Profunctor.Closed
import Data.Profunctor.Strong
import Data.Profunctor.Traversing
import Data.Profunctor.Mapping
import Data.Profunctor.Monad
import Data.Profunctor.Yoneda
import Data.Profunctor.Trans

import Prelude

import Data.Kind
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Monoid (Any(..))
import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S

{-
--data PArrow p a b = forall x y. PArrow { runPArrow :: p (b , x) y -> p (a , x) y }
data Exp p q a b = forall d . Exp ( p b d -> q a d)
instance (Profunctor g,Profunctor h) => Profunctor (Exp g h) where
  dimap m1 m2 (Exp gh) = Exp (dimap m1 id . gh . dimap m2 id)

instance (Profunctor p, Profunctor q) => Profunctor (Rift p q) where
  dimap ca bd f = Rift (lmap ca . runRift f . lmap bd)

phi ::(Procompose f g :-> h) -> (f :-> Rift g h)
--phi :: (Procompose p q d c -> b x1 x2) -> p x2 c -> Rift q b x1 d
phi m f = Rift (\g -> m (Procompose f g))
--Procompose :: p x c -> q d x -> Procompose p q d c
-}

--data PArrow p a b where PArrow :: (p (b , x) y -> p (a , x) y) -> PArrow p a b
newtype PArrow p a b = PArrow { runPArrow :: forall x y. p (b , x) y -> p (a , x) y }

instance Profunctor p => Profunctor (PArrow p) where
  dimap f g (PArrow pp) = PArrow $ \p -> dimap (lift f) id (pp (dimap (lift g) id p))
    where lift f (a, b) = (f a, b)

instance Profunctor p => Category (PArrow p) where
  id = PArrow id

  PArrow pp . PArrow qq = PArrow $ \r -> qq (pp r)

instance Profunctor p => Strong (PArrow p) where
  first' (PArrow pp) = PArrow $ lmap assocr . pp . lmap assocl

-- repn . abst = id
-- abst . repn = id
repn :: Arrow a => a b c -> PArrow a b c
repn x = PArrow (\z -> A.first x >>> z)

abst :: Arrow a => PArrow a b c -> a b c
abst (PArrow aa) = A.arr (\x -> (x,())) >>> aa (A.arr fst)



{-
A free prearrow is one that gives us an instance of Category and Profunctor for any type with minimal effort from that type. 
A truly free prearrow would provide (.) and dimap. But we can actually separate those two and do them one at a time. 
If we separate (.) and dimap, we can start with the data source, give it a Profunctor instance on Free, and then give it a Category instance that preserves the Profunctor instance. 
This will be valuable because it means we can change the Profunctor instance and the data source in isolation from each other and from the Category instance.
-}

-- | Free monoid in the category of profunctors.
--
-- See <https://arxiv.org/abs/1406.4823> section 6.2.
-- 
--
data Prearrow p a b where
  Parr :: (a -> b) -> Prearrow p a b
  Comp :: p x b -> Prearrow p a x -> Prearrow p a b

instance Profunctor p => Profunctor (Prearrow p) where
  dimap l r (Parr f) = Parr (dimap l r f)
  dimap l r (Comp f g) = Comp (rmap r f) (lmap l g)

instance Profunctor p => Category (Prearrow p) where
  id = Parr id
  Parr g . f = rmap g f
  Comp h g . f = Comp h (g <<< f)

instance Strong p => Strong (Prearrow p) where
  first' (Parr f) = Parr (first' f)
  first' (Comp f g) = Comp (first' f) (first' g)

instance Choice p => Choice (Prearrow p) where
  left' (Parr f) = Parr (left' f)
  left' (Comp f g) = Comp (left' f) (left' g)

instance Closed p => Closed (Prearrow p) where
  closed (Parr f) = Parr (closed f)
  closed (Comp f g) = Comp (closed f) (closed g)

runPrearrow :: Category q => Profunctor q => p :-> q -> Prearrow p a b -> q a b
runPrearrow _ (Parr g) = arr g
runPrearrow f (Comp g h) = f g <<< runPrearrow f h

liftProfunctorTrans :: ProfunctorTrans p => q a b -> Prearrow (p q) a b
liftProfunctorTrans q = Comp (plift q) (Parr id)

type ArrTrans p q a b = ProfunctorTrans p => Prearrow (p q) a b

--foo :: ProfunctorTrans t => t p a b -> p :-> q -> q a b
foo :: Profunctor q => Free m p a b -> p :-> q -> q a b
foo (Free l p r) pq = dimap l r (_ (pq p))

type ArrChoice p = Prearrow (FreeChoice p)

runArrChoice :: Category q => Choice q => p :-> q -> ArrChoice p a b -> q a b
runArrChoice pq = runPrearrow (`withFreeChoice` pq)

runArrChoiceM :: Monad m => (forall x y. p x y -> x -> m y) -> ArrChoice p a b -> (a -> m b)
runArrChoiceM f = runKleisli . runArrChoice (Kleisli . f)

liftArrChoice :: p a b -> ArrChoice p a b
liftArrChoice p = Comp (choice_lift p) (Parr id)

withFreeChoice :: Choice q => FreeChoice p a b -> p :-> q -> q a b
withFreeChoice (Free l p r) pq = dimap l r (right' (pq p))

withFreeStrong :: Strong q => FreeStrong p a b -> p :-> q -> q a b
withFreeStrong (Free l p r) pq = dimap l r (second' (pq p))

withFreeClosed :: Closed q => FreeClosed p a b -> p :-> q -> q a b
withFreeClosed (Free l p r) pq = dimap l r (closed (pq p))

withFreeAffine :: Choice q => Strong q => FreeAffine p a b -> p :-> q -> q a b
withFreeAffine (Free l p r) pq = dimap l r (affine (pq p))

--TODO: unify w optics package somehow
withFreeTraversal :: Traversing q => FreeTraversal p a b -> p :-> q -> q a b
withFreeTraversal (Free l p r) pq = dimap l r (traverse' (pq p))

withFreeSetter :: Mapping q => FreeSetter p a b -> p :-> q -> q a b
withFreeSetter (Free l p r) pq = dimap l r (map' (pq p))

--foo :: Choice q => ProfunctorTrans p => p :-> q -> FreeChoice p a b -> q a b
--foo pq (Free l p r) = dimap l r (right' (pq p))

{-


traversal_comp :: Traversable f => FreeTraversal p a b -> FreeTraversal p (f a) (f b)


-- A submonoid is unital if we can have some identity optic.  It is
-- functorial and multiplicative if we can create a bigger optic from
-- a small one.
class Tensorial mon where
  idOptic   :: ExOptic mon a b a b
  multOptic :: (mon f) => ExOptic mon a b s t -> ExOptic mon a b (f s) (f t)

runAp :: Applicative g => (forall x. f x -> g x) -> Ap f a -> g a Source#

class Monad m => MonadFree f m | m -> f where
  -- | Add a layer.
  --
  -- @
  -- wrap (fmap f x) ≡ wrap (fmap return x) >>= f
  -- @
  wrap :: f (m a) -> m a
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 704
  default wrap :: (m ~ t n, MonadTrans t, MonadFree f n, Functor f) => f (m a) -> m a
  wrap = join . lift . wrap . fmap return


Given a natural transformation from f to g, this gives a canonical monoidal natural transformation from Ap f to g.

runAp t == retractApp . hoistApp t
runAp_ :: Monoid m => (forall a. f a -> m) -> Ap f b -> m


retract :: Monad f => Free f a -> f a
retract (Parr a) = return a
retract (Free as) = as >>= retract

-- | Tear down a 'Free' 'Monad' using iteration.
iter :: Functor f => (f a -> a) -> Free f a -> a
iter _ (Parr a) = a
iter phi (Free m) = phi (iter phi <$> m)

-- | Like 'iter' for applicative values.
iterA :: (Applicative p, Functor f) => (f (p a) -> p a) -> Free f a -> p a
iterA _   (Parr x) = pure x
iterA phi (Free f) = phi (iterA phi <$> f)

-- | Like 'iter' for monadic values.
iterM :: (Monad m, Functor f) => (f (m a) -> m a) -> Free f a -> m a
iterM _   (Parr x) = return x
iterM phi (Free f) = phi (iterM phi <$> f)

-- | Lift a natural transformation from @f@ to @g@ into a natural transformation from @'Free' f@ to @'Free' g@.
hoistFree :: Functor g => (forall a. f a -> g a) -> Free f b -> Free g b
hoistFree _ (Parr a)  = Parr a
hoistFree f (Free as) = Free (hoistFree f <$> f as)

-- | The very definition of a free monad is that given a natural transformation you get a monad homomorphism.
foldFree :: Monad m => (forall x . f x -> m x) -> Free f a -> m a
foldFree _ (Parr a)  = return a
foldFree f (Free as) = f as >>= foldFree f

retractAp :: Applicative f => Ap f a -> f a
liftAp :: f a -> Ap f a
hoistAp :: (forall a. f a -> g a) -> Ap f b -> Ap g b

runTambara
  :: m q
  => (forall x y . p x y -> q x y)
  -> Free m p a b
  -> q a b
runTambara f (Pastro r g l) = dimap l r (first' (f g))

runTambara \f (Free r p l) -> dimap l r (affine_comp (f p))


runFreeCoyoneda
  :: (Category q, Profunctor q)
  => (forall x y. p x y -> q x y)
  -> Prearrow (Coyoneda p) a b
  -> q a b
runFreeCoyoneda f = runPrearrow (runCoyoneda f)

runPastroArr
  :: (Category q, Strong q)
  => (forall x y . p x y -> q x y)
  -> PastroArr p a b
  -> q a b
runPastroArr f = runPrearrow (runPastro f)

runCoyoneda
  :: Profunctor q
  => (forall x y. p x y -> q x y)
  -> Coyoneda p a b
  -> q a b
runCoyoneda f (Coyoneda l r g) = dimap l r (f g)

runPastro
  :: Strong q
  => (forall x y . p x y -> q x y)
  -> Pastro p a b
  -> q a b
runPastro f (Pastro r g l) = dimap l r (first' (f g))

runArrM :: Monad m => (forall x y. p x y -> x -> m y) -> CoyoArr p a b -> (a -> m b)
runArrM f = runKleisli . runFreeCoyoneda (Kleisli . f)

runArrM' :: Monad m => (forall x y. p x y -> x -> m y) -> PastroArr p a b -> (a -> m b)
runArrM' f = runKleisli . runPastroArr (Kleisli . f)

runArrW :: Comonad w => (forall x y. p x y -> w x -> y) -> CoyoArr p a b -> (w a -> b)
runArrW f = runCokleisli . runFreeCoyoneda (Cokleisli . f)

--runEnv :: MonadPlus m => (forall x y. p x y -> Env m x y) -> CoyoArr p a b -> Env m a b
--runEnv = runFreeCoyoneda 
-}


{-
type CoyoArr p = Prearrow (Coyoneda p)
type PastroArr p = Prearrow (Pastro p)

type TravArr p = Prearrow (FreeTraversing p)

liftArr :: p a b -> CoyoArr p a b
liftArr p = Comp (Coyoneda id id p) (Parr id)

--TODO use toPastro for this?
--liftPastro :: p a b -> PastroArr p a b
--liftPastro f = Comp (Pastro fst f _) (Parr id)

liftPastro :: p a b -> PastroArr p a b
liftPastro p = Comp (Pastro fst p fork) (Parr id)

liftTrav :: p a b -> TravArr p a b
liftTrav p = Comp (FreeTraversing runIdentity p Identity) (Parr id)

liftEnv :: p a b -> Prearrow (Environment p) a b
liftEnv p = Comp (Environment ($ ()) p const) (Parr id)

runTrav
  :: (Category q, Profunctor q)
  => (forall f x y . Traversable f => p x y -> q (f x) (f y))
  -> TravArr p a b
  -> q a b
runTrav _ (Parr g) = rmap g id
runTrav f (Comp (FreeTraversing unpack g pack) h) =
  dimap pack unpack (f g) . runTrav f h

runPro'
  :: Strong q
  => (forall x y . p x y -> q x y)
  -> Pastro p a b
  -> q a b
runPro' f (Pastro r g l) = dimap l r (first' (f g))

runArr'
  :: (Category q, Strong q)
  => (forall x y . p x y -> q x y)
  -> PastroArr p a b
  -> q a b
runArr' f = runPrearrow (runPro' f)
-}


{-
type Idx = Int
type Username = String
-- | Data source
data DataSource a b where
  GetUsernames :: DataSource (Set Idx) (Map Idx Username)
  GetFriends :: DataSource Idx (Set Idx)
  --DataSourceError :: DataSource String b



--getUsernames :: CoyoArr DataSource (Set Idx) (Map Idx Username)
getUsernames = liftArr GetUsernames

--getFriends :: CoyoArr DataSource Idx (Set Idx)
getFriends = liftArr GetFriends

getUsernamesP :: PastroArr DataSource (Set Idx) (Map Idx Username)
getUsernamesP = liftPastro GetUsernames

getFriendsP :: PastroArr DataSource Idx (Set Idx)
getFriendsP = liftPastro GetFriends

--getFriendsUsernames :: CoyoArr DataSource Idx [Username]
getFriendsUsernames = arr M.elems . getUsernames . getFriends

resourcesNeeded :: CoyoArr DataSource a b -> (Bool, Bool)
resourcesNeeded f =
  let toAny :: DataSource x y -> Append (Any, Any) x y
      toAny GetUsernames = Append (Any True, Any False) -- Need manager
      toAny GetFriends = Append (Any False, Any True) -- Need postgres
      Append (Any managerNeeded, Any postgresNeeded) = runFreeCoyoneda toAny f
  in (managerNeeded, postgresNeeded)

runDataSource :: CoyoArr DataSource a b -> a -> IO b
runDataSource f a = do
  let (managerNeeded, postgresNeeded) = resourcesNeeded f
  print (managerNeeded, postgresNeeded)
{-
  manager <- if managerNeeded
    then Just <$> newManager defaultManagerSettings
    else return Nothing
  conn <- if postgresNeeded
    then Just <$> connectPostgreSQL ""
    else return Nothing
-}

  let toIO :: DataSource x y -> x -> IO y
      toIO GetUsernames users = do
        --print users
        return $ M.fromSet (const "Joe") users
        --let manager' = fromJust manager
      toIO GetFriends user = do
        --let conn' = fromJust conn
        return $ S.singleton user

  runArrM toIO f a

{-
λ> runDataSource getFriendsUsernames 8
(True,True)
["Joe"]
-}

runDataSource' :: PastroArr DataSource a b -> a -> IO b
runDataSource' f a = do
  let toIO :: DataSource x y -> x -> IO y
      toIO GetUsernames users = do
        --print users
        return $ M.fromSet (const "Joe") users
        --let manager' = fromJust manager
      toIO GetFriends user = do
        --let conn' = fromJust conn
        return $ S.singleton user

  runArrM' toIO f a

friendsAndUsername :: PastroArr DataSource Idx (Maybe Username, Set Idx)
friendsAndUsername =
  pull (liftPastro GetFriends)
    >>> first' (pull $ lmap S.singleton $ liftPastro GetUsernames)
    >>> arr (\((user, usernames), ids) -> (M.lookup user usernames, ids))

--λ> runDataSource' friendsAndUsername' 8
--(Just "Joe",fromList [8])
friendsAndUsername' :: PastroArr DataSource Idx (Maybe Username, Set Idx)
friendsAndUsername' = proc user -> do
  friends <- liftPastro GetFriends -< user
  usernames <- liftPastro GetUsernames -< S.singleton user
  arr id -< (M.lookup user usernames, friends)

{-
data DataSourc a b where
  DataSourceError :: DataSourc String b
  GetUserName :: DataSourc (Set Idx) (Map Idx Username)
  GetFriend :: DataSourc Idx (Set Idx)

friendsAndUsername'' :: CoyoArr DataSourc Idx (Set Idx, Username)
friendsAndUsername'' = proc user -> do
  friends <- liftArr GetFriend -< user
  usernames <- liftArr GetUserName -< S.singleton user
  case M.lookup user usernames of
    Nothing -> liftArr DataSourceError -< "no username for " ++ show user
    Just name -> returnA -< (friends, name)
-}






-}


-- Analog of 'Const' for pliftows
newtype Append r a b = Append { getAppend :: r }

instance Profunctor (Append r) where
  dimap _ _ (Append x) = Append x

instance Monoid r => Category (Append r) where
  id = Append mempty
  Append x . Append y = Append (x <> y)

-- @
-- (a '>>>' b) '>>>' c = a '>>>' (b '>>>' c)
-- 'arr' f '>>>' a = 'dimap' f id a
-- a '>>>' arr f = 'dimap' id f a
-- 'arr' (g . f) = 'arr' f '>>>' 'arr' g
-- @
--
arr :: Category p => Profunctor p => (a -> b) -> p a b
arr f = dimap id f C.id

preturn :: Category p => Profunctor p => p a a
preturn = arr id

ex1 :: Category p => Profunctor p => p (a , b) b
ex1 = arr snd

ex2 :: Category p => Profunctor p => p (a , b) a
ex2 = arr fst

inl :: Category p => Profunctor p => p a (a + b)
inl = arr Left

inr :: Category p => Profunctor p => p b (a + b)
inr = arr Right

braid :: Category p => Profunctor p => p (a , b) (b , a)
braid = arr swp

braide :: Category p => Profunctor p => p (a + b) (b + a)
braide = arr eswp

loop :: Costrong p => p (a, d) (b, d) -> p a b
loop = unfirst

left :: Choice p => p a b -> p (a + c) (b + c)
left = left'

right :: Choice p => p a b -> p (c + a) (c + b)
right = right'

-- @
-- first ('arr' f) = 'arr' (f '***' id)
-- first (a '>>>' b) = first a '>>>' first b
-- @
--
first :: Strong p => p a b -> p (a , c) (b , c)
first = first'

second :: Strong p => p a b -> p (c , a) (c , b)
second = second'

returnA :: Category p => Profunctor p => p a a
returnA = C.id

infixr 3 ***

(***) :: Category p => Strong p => p a1 b1 -> p a2 b2 -> p (a1 , a2) (b1 , b2)
x *** y = first x >>> arr swp >>> first y >>> arr swp

infixr 2 +++

(+++) :: Category p => Choice p => p a1 b1 -> p a2 b2 -> p (a1 + a2) (b1 + b2)
x +++ y = left x >>> arr eswp >>> left y >>> arr eswp

infixr 3 &&&

(&&&) :: Category p => Strong p => p a b1 -> p a b2 -> p a (b1 , b2)
x &&& y = dimap fork id $ x *** y 

infixr 2 |||

(|||) :: Category p => Choice p => p a1 b -> p a2 b -> p (a1 + a2) b
x ||| y = pchoose id x y

infixr 0 $$$

($$$) :: Category p => Strong p => p a (b -> c) -> p a b -> p a c
($$$) f x = dimap fork apply (f *** x)

pselect :: Category p => Choice p => ((b1 + b2) -> b) -> p a b1 -> p a b2 -> p a b
pselect f x y = dimap Left f $ x +++ y

pchoose :: Category p => Choice p => (a -> (a1 + a2)) -> p a1 b -> p a2 b -> p a b
pchoose f x y = dimap f join $ x +++ y
