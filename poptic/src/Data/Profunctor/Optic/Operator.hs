module Data.Profunctor.Optic.Operator (
    module Data.Profunctor.Optic.Operator
) where

import Data.Profunctor.Types hiding (Forget(..))
import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Type
import Data.Either.Validation

import Control.Monad.Reader as Reader
import Control.Monad.State as State

import Control.Monad
--import Control.Monad.Reader.Class as Reader

import Data.List.NonEmpty (NonEmpty(..), nonEmpty)
--import Data.NonEmpty
import Data.Valid
import Data.Semiring
import Orphans

data ValidationError
    = InvalidRecord String
    -- ^ An 'InvalidRecord' indicates that a 'Validator' has failed.
    | MissingField String
    -- ^ A 'MissingField' indicates that a required field has not been set.
    deriving (Eq, Ord, Show)


type ValidationErrors = NonEmpty ValidationError
type ValidationErrors' = [ValidationError]

msg = "empty list"

validateNel :: String -> [a] -> Validation ValidationErrors (NonEmpty a)
validateNel s = note (pure . InvalidRecord $ s) . nonEmpty

nel :: Validating ValidationErrors s t [a] (NonEmpty a) -> s -> Validation ValidationErrors t
nel = validate $ validateNel msg

validateNel' :: String -> [a] -> Validation ValidationErrors' (NonEmpty a)
validateNel' s = note (pure . InvalidRecord $ s) . nonEmpty

nel' :: Validating ValidationErrors' s t [a] (NonEmpty a) -> s -> Validation ValidationErrors' t
nel' = validate $ validateNel' msg

{-
advantages of profunctor optics
- better semantic fit 
  - conceptually simpler

- build your own profunctors (& lots of things are profunctors)
  - more precise semantics (since you control the typeclass instances)

- other stuff like grates and free profunctors

disadvantages
- need to have a profunctor to do anything
- performance???



--TODO bad example use a different non-empty structure to accumulate errors
λ> nel traverse1' ([2] :| [[],[],[1]])
Failure (InvalidRecord "empty list" :| [InvalidRecord "empty list"])

λ> nel _2 (7,[])
Failure (InvalidRecord "empty list" :| [])

λ> nel _R $ Left [1]
Success (Left [1])
λ> nel _L $ Left [1]
Success (Left (1 :| []))
λ> nel _R $ Right []
Failure (InvalidRecord "empty list" :| [])


λ> nel _R $ Left [1]
Success (Left [1])
λ> nel _L $ Left [1]
Success (Left (1 :| []))

λ> nel' _R $ Right []
Failure [InvalidRecord "empty list"]
λ> nel' _L $ Left [1]
Success (Left (1 :| []))
λ> nel' _R $ Left [1]
Success (Left [1])
λ> nel' _R $ Left []
Success (Left [])

-- Problem #1: we aren't failing correctly. we never even tested the list b/c the prism failed to match

-- change choice instance to use alternative
λ> nel' _R $ Right []
Failure [InvalidRecord "empty list"]
λ> nel' _R $ Left [1]
Failure []
λ> nel _R $ Left [1]
error: Could not deduce (Monoid (NonEmpty ValidationError))
-- this is good! now both nel and nel' fail when the prism misses, and the nonempty version doesn't typecheck b/c it can't show anything on a miss

λ> nel' _Just $ Nothing
Failure []
λ> nel' _Just $ Just []
Failure [InvalidRecord "empty list"]
λ> nel' _Just $ Just [1,2]
Success (Just (1 :| [2]))

nel' _Just $ Nothing
nel' _Just $ Just [1,2]
λ> nel' (traverse' . _Just) $ [Nothing, Nothing, Just [1,2]]
Failure []
-- Problem #1: now we're failing too fast. the whole point of a Valid is to try and validate everything and return all the errors. can we extend this to include the optic?

-- change instance again to use semiring semantics

-}


validate
  :: (a -> Validation r b)
     -> Validating r s t a b
     -> s
     -> Validation r t
--validate f o = swap . h where Validated h = o (Validated $ swap . f)
validate f o = h where Validated h = o (Validated $ f)

{-

validate
  :: (a -> Validation r b)
     -> Validating r s t a b
     -> s
     -> Validation r t
validate f o = h where Star h = o (Star f)

validate :: (a -> Validation t b) -> Validating t s t a b -> s -> Validation t a
validate f o = swap . h where Star h = o (Star $ f)

validate :: Validating e s t a b -> s -> Validation e a
validate o = h where Validated h = o (Validated Success)

validate
  :: (a -> Validation r b)
     -> Validating r s t a b
     -> s
     -> Validation r t
validate f o = swap . h where Validated h = o (Validated $ swap . f)

-}








--preview :: Previewing s a -> s -> Maybe a
--preview o = h where Previewed h = o (Previewed Just)


--match o = swap . h where Star h = o (Star Left)
--match = between (dstar swap) (ustar id Left)

-- | A more restrictive variant of 'match'.
--match' :: Optic (Matched a) s t a b -> s -> Either t a
--match' o = (between Matched runMatched) o Right




--foldMapOf = between (dstar getConst) (ustar Const)

--foldMapping :: ((a -> r) -> s -> r) -> AFold r s a
--foldMapping = between (ustar Const) (dstar getConst) 

unfoldMapOf :: ACofold r t b -> (r -> b) -> r -> t
unfoldMapOf = between (coDstar Const) (coUstar getConst) 

--getConst . h where Star h = o . forget $ f

--foldMapMOf = (betweenM unforget forget)


--foo :: Alternative f => Optic (Forget (Alt f a)) s t a b -> s -> f a
--foo o = runAlt . foldMapOf o (Alt . pure)





