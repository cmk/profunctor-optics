module Data.Profunctor.Optic.Operator (
    module Data.Profunctor.Optic.Operator
  , swap
) where

import Data.Profunctor.Types
import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Type
import Data.Either.Validation

import Control.Monad.Reader as Reader
import Control.Monad.State as State

import Control.Monad
--import Control.Monad.Reader.Class as Reader

import Data.List.NonEmpty (NonEmpty(..), nonEmpty)

data ValidationError
    = InvalidRecord String
    -- ^ An 'InvalidRecord' indicates that a 'Validator' has failed.
    | MissingField String
    -- ^ A 'MissingField' indicates that a required field has not been set.
    deriving (Eq, Ord, Show)


type ValidationErrors = NonEmpty ValidationError
type ValidationErrors' = [ValidationError]

validateNel :: String -> [a] -> Validation ValidationErrors (NonEmpty a)
validateNel s = note (pure . InvalidRecord $ s) . nonEmpty

msg = "empty list"

nel :: Validating ValidationErrors s t [a] (NonEmpty a) -> s -> Validation ValidationErrors t
nel = validate $ validateNel msg

{-


validateNel' :: String -> [a] -> Validation ValidationErrors' (NonEmpty a)
validateNel' s = note (pure . InvalidRecord $ s) . nonEmpty

nel' :: Validating ValidationErrors' s t [a] (NonEmpty a) -> s -> Validation ValidationErrors' t
nel' = validate $ validateNel' msg



λ> nel _2 (7,[])
Failure (MissingField "empty list" :| [])
λ> nel both ([],[])
Failure (MissingField "empty list" :| [MissingField "empty list"])


λ> nel _R $ Left [1]
Success (Left [1])
λ> nel _L $ Left [1]
Success (Left (1 :| []))

λ> nel _R $ Left [1]
Success (Left [1])
λ> nel _L $ Left [1]
Success (Left (1 :| []))
λ> nel' _L $ Left [1]
Success (Left (1 :| []))
λ> nel' _R $ Left [1]
Success (Left [1])
λ> nel' _R $ Left []
Success (Left [])
λ> nel' _R $ Right []
Failure [MissingField "empty list"]

-- problem is we are moving the Either into the errors
nel _L :: Either [a] c -> Validation ValidationErrors (Either (NonEmpty a) c)
nel _1 :: ([a], c) -> Validation ValidationErrors (NonEmpty a, c)

validated $ validateNel msg

validate _Success $ validateNel msg [1]
Success (1 :| [])

validate  $ validateNel msg []

λ> nel _2 (7,[])
Failure (MissingField "empty list" :| [])

λ> nel _2 ([],[])
Failure (MissingField "empty list" :| [])

λ> nel both ([],[])
Failure (MissingField "empty list" :| [MissingField "empty list"])

nel both ([1,2],[3])
Success (1 :| [2],3 :| [])
-}


validate
  :: (a -> Validation r b)
     -> Validating r s t a b
     -> s
     -> Validation r t
validate f o = swap . h where Validated h = o (Validated $ swap . f)

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





re :: Optic (Re p a b) s t a b -> Optic p b a t s
re o = (between runRe Re) o id


preview :: Previewing s a -> s -> Maybe a
--previewOf' o = runPre . getConst . h where Star h = o (Star $ Const . Pre . Just)
preview o = h where Previewed h = o (Previewed Just)

-- ^ @
-- match :: Traversal s t a b -> s -> Either t a
-- @
--match :: Matching a s t a b -> s -> Either t a
--match o = h where Matched h = o (Matched Right)

match :: Matching a s t a b -> s -> Either t a
match o = swap . h where Star h = o (Star Left)


-- | Test whether the optic matches or not.
isMatched :: Matching a s t a b -> s -> Bool
isMatched o = either (const False) (const True) . match o

-- | Test whether the optic matches or not.
isntMatched :: Matching a s t a b -> s -> Bool
isntMatched o = not . isMatched o

--match o = swap . h where Star h = o (Star Left)
--match = between (dstar swap) (ustar id Left)

-- | A more restrictive variant of 'match'.
--match' :: Optic (Matched a) s t a b -> s -> Either t a
--match' o = (between Matched runMatched) o Right

previewOf :: AFolding r s a -> (a -> r) -> s -> Maybe r
previewOf = between (dstar runPre) (ustar $ Pre . Just)

foldMapOf :: Folding r s a -> (a -> r) -> s -> r
foldMapOf = between (dstar getConst) (ustar Const)

foldMapping :: ((a -> r) -> s -> r) -> Folding r s a
foldMapping = between (ustar Const) (dstar getConst) 

unfoldMapOf :: Unfolding r t b -> (r -> b) -> r -> t
unfoldMapOf = between (coDstar Const) (coUstar getConst) 

--getConst . h where Star h = o . forget $ f

--foldMapMOf = (betweenM unforget forget)

--foldMapOf' :: Optic (Forget r) s t a b -> (a -> r) -> s -> r
--foldMapOf' = between runForget Forget






{-
The laws for a 'Traversal' follow from the laws for 'Traversable' as stated in "The Essence of the Iterator Pattern".

Identity:

traverseOf t (Identity . f) ≡  Identity (fmap f)

Composition:

Compose . fmap (traverseOf t f) . traverseOf t g == traverseOf t (Compose . fmap f . g)

One consequence of this requirement is that a 'Traversal' needs to leave the same number of elements as a
candidate for subsequent 'Traversal' that it started with. 

-}
-- ^ @
-- traverseOf :: Functor f => Lens s t a b -> (a -> f b) -> s -> f t
-- traverseOf :: Applicative f => Traversal s t a b -> (a -> f b) -> s -> f t
-- traverseOf $ _1 . _R :: Applicative f => (a -> f b) -> (Either c a, d) -> f (Either c b, d)
-- traverseOf == between runStar Star 
-- @

traverseOf :: Optic (Star f) s t a b -> (a -> f b) -> s -> f t
traverseOf o f = tf where Star tf = o (Star f)

-- cotraverseOf == between runCostar Costar 
cotraverseOf :: Optic (Costar f) s t a b -> (f a -> b) -> (f s -> t)
cotraverseOf o f = tf where Costar tf = o (Costar f)

-- special case where f = (a,a)
zipWithOf :: Optic Zipped s t a b -> (a -> a -> b) -> s -> s -> t
zipWithOf = between runZipped Zipped



