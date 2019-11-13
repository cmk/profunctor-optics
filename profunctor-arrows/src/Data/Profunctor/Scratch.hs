{-# LANGUAGE GADTs #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ExistentialQuantification #-}
module Data.Profunctor.Scratch where

import Control.Exception
import Control.Arrow (Arrow, Kleisli(..))
import Control.Category hiding ((.), id)
import Control.Comonad (Comonad, Cokleisli(..))
import Control.Monad hiding (join)
import Data.Profunctor
import Data.Profunctor.Arrow
import Data.Profunctor.Arrow.Free
import Data.Profunctor.Extra
import Data.Profunctor.Trans.Adapter
import Data.Profunctor.Trans.Affine
import Data.Profunctor.Trans.Choice
import Data.Profunctor.Trans.Strong
import Data.Profunctor.Trans.Traversal
import Data.Profunctor.Trans.Internal

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

import System.IO.Error
import Prelude

import Data.Maybe (fromJust)
import Data.Kind
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Monoid (Any(..))
import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S

-- example based on a post by Will Fancher https://elvishjerricco.github.io/2017/03/10/profunctors-arrows-and-static-analysis.html
type Id = Int
type Username = String

--symbolic profunctor representing a data source
data DataSourceA a b where
  GetUsernamesA :: DataSourceA (Set Id) (Map Id Username)
  GetFriendsA :: DataSourceA Id (Set Id)

getUsernamesA :: FreeAdapter DataSourceA (Set Id) (Map Id Username)
getUsernamesA = liftAdapter GetUsernamesA

getFriendsA :: FreeAdapter DataSourceA Id (Set Id)
getFriendsA = liftAdapter GetFriendsA

friendsAndUsernames :: FreeAdapter DataSourceA Id [Username]
friendsAndUsernames = arr M.elems <<< getUsernamesA <<< getFriendsA

--we can statically analyze the entire expression
resourcesNeeded :: FreeAdapter DataSourceA a b -> (Bool, Bool)
resourcesNeeded f =
  let toAny :: DataSourceA x y -> Append (Any, Any) x y
      toAny GetUsernamesA = Append (Any True, Any False) -- Need manager
      toAny GetFriendsA = Append (Any False, Any True) -- Need postgres
      Append (Any managerNeeded, Any postgresNeeded) = foldAdapter toAny f
  in (managerNeeded, postgresNeeded)

runDataSourceA :: FreeAdapter DataSourceA a b -> a -> IO b
runDataSourceA f a = do
  let (managerNeeded, postgresNeeded) = resourcesNeeded f
  print (managerNeeded, postgresNeeded)
{- todo: use file instead
  manager <- if managerNeeded
    then Just <$> newManager defaultManagerSettings
    else return Nothing
  conn <- if postgresNeeded
    then Just <$> connectPostgreSQL ""
    else return Nothing
-}

  let toIO :: DataSourceA x y -> x -> IO y
      toIO GetUsernamesA users = do
        --print users
        return $ M.fromSet (const "Joe") users
        --let manager' = fromJust manager
      toIO GetFriendsA user = do
        --let conn' = fromJust conn
        return $ S.singleton user

  runAdapterM toIO f a

{-
λ> runDataSourceA friendsAndUsernames 8
(True,True)
["Joe"]
-}

--now add Strength
getUsernamesA' :: FreeStrong DataSourceA (Set Id) (Map Id Username)
getUsernamesA' = liftStrong GetUsernamesA

getFriendsA' :: FreeStrong DataSourceA Id (Set Id)
getFriendsA' = liftStrong GetFriendsA

friendsAndUsernames2 :: FreeStrong DataSourceA Id (Maybe Username, Set Id)
friendsAndUsernames2 =
  pull getFriendsA'
    >>> first' (pull $ lmap S.singleton $ getUsernamesA')
    >>> arr (\((user, usernames), ids) -> (M.lookup user usernames, ids))

--same expr written w/ arrow syntax
friendsAndUsernames2Syn :: FreeStrong DataSourceA Id (Maybe Username, Set Id)
friendsAndUsernames2Syn = proc user -> do
  friends <- getFriendsA' -< user
  usernames <- getUsernamesA' -< S.singleton user
  arr id -< (M.lookup user usernames, friends)


runDataSourceA' :: FreeStrong DataSourceA a b -> a -> IO b
runDataSourceA' f a = do
  let toIO :: DataSourceA x y -> x -> IO y
      toIO GetUsernamesA users = do
        --print users
        return $ M.fromSet (const "Joe") users
        --let manager' = fromJust manager
      toIO GetFriendsA user = do
        --let conn' = fromJust conn
        return $ S.singleton user

  runStrongM toIO f a

--λ> runDataSourceA' friendsAndUsernames2 8
--(Just "Joe",fromList [8])


-- now add Choice
data DataSourceB a b where
  DataSourceErrorB :: DataSourceB String b
  GetUsernamesB :: DataSourceB (Set Id) (Map Id Username)
  GetFriendsB :: DataSourceB Id (Set Id)

--arrow-based DSL for expressions
friendsAndUsernames3 :: FreeAffine DataSourceB Id (Set Id, Username)
friendsAndUsernames3 = proc user -> do
  friends <- liftAffine GetFriendsB -< user
  usernames <- liftAffine GetUsernamesB -< S.singleton user
  case M.lookup user usernames of
    Nothing -> liftAffine DataSourceErrorB -< "no username for " ++ show user
    Just name -> returnA -< (friends, name)

runDataSourceB :: FreeAffine DataSourceB a b -> a -> IO b
runDataSourceB f = do
  let toIO :: DataSourceB x y -> x -> IO y
      toIO GetUsernamesB user = do
        --print users
        return $ M.empty --M.fromSet (const "Joe") user
        --let manager' = fromJust manager
      toIO GetFriendsB user = do
        --let conn' = fromJust conn
        return $ S.singleton user
      toIO DataSourceErrorB msg = do
        --let conn' = fromJust conn
        ioError . userError $ msg
  runAffineM toIO f

{-
λ> runDataSourceB friendsAndUsernames3 8
*** Exception: user error (no username for 8)
-}


-- now add Traversable
data DataSourceC a b where
  --DataSourceErrorC :: DataSourceC String b
  GetUsernamesC :: DataSourceC Id Username
  GetFriendsC :: DataSourceC Id (Set Id)

getUsernamesC :: FreeTraversal DataSourceC Id Username
getUsernamesC = liftTraversal GetUsernamesC

getFriendsC :: FreeTraversal DataSourceC Id (Set Id)
getFriendsC = liftTraversal GetFriendsC

--arrow-based DSL for expressions
friendsAndUsernames4 :: FreeTraversal DataSourceC Id (Map Id Username)
friendsAndUsernames4 = proc user -> do
  friends <- getFriendsC -< user
  traverse' getUsernamesC -< M.fromSet id friends
{-
  usernames <- traverse' getUsernamesC -< M.fromSet id friends
  case M.lookup user usernames of
    Nothing -> liftAffine DataSourceErrorC -< "no usernamesB for " ++ show user
    Just namesB -> returnA -< (friends, name)
-}

runDataSourceC :: FreeTraversal DataSourceC a b -> a -> IO b
runDataSourceC f = do
  let toIO :: Traversable f => DataSourceC x y -> f x -> IO (f y)
      --toIO DataSourceError4 msg = do
      --  ioError . userError $ msg
      toIO GetUsernamesC users = do
        let userIds = foldr S.insert S.empty users
            usernames = M.fromList [(1,"Chris"),(2,"Xine")]
        -- Call some API to get usernames
        --usernames <- ...
        return $ fromJust $ traverse (`M.lookup` usernames) users
      toIO GetFriendsC users = traverse (pure . S.singleton) $ users
  runTraversalM toIO f 

{-
λ> runDataSourceC friendsAndUsernames4 1
fromList [(1,"Chris")]
-}
