-- | See <https://en.wikipedia.org/wiki/Binary_relation#Properties>.
-- 
-- Note that these properties do not exhaust all of the possibilities.
--
-- For example, the relation \( y = x^2 \) is neither irreflexive, 
-- nor coreflexive, nor reflexive, since it contains the pairs
-- \( (0, 0) \) and \( (2, 4) \), but not \( (2, 2) \).
--
--  The latter two facts also rule out quasi-reflexivity.
module Test.Property.Relation.Reflexive where

import Test.Property.Util


-- | \( \forall a: (a \# a) \)
--
-- For example, ≥ is a reflexive relation but > is not.
--
reflexive :: (r -> r -> Bool) -> (r ->  Bool)
reflexive (#) a = a # a 


-- | \( \forall a: \neg (a \# a) \)
--
-- For example, > is an irreflexive relation, but ≥ is not.
--
irreflexive :: (r -> r -> Bool) -> (r ->  Bool)
irreflexive (#) a = not $ a # a


-- | \( \forall a, b: ((a \# b) \wedge (b \# a)) \Rightarrow (a \equiv b) \)
--
-- For example, the relation over the integers in which each odd number is 
-- related to itself is a coreflexive relation. The equality relation is the 
-- only example of a relation that is both reflexive and coreflexive, and any 
-- coreflexive relation is a subset of the equality relation.
--
coreflexive :: Eq r => (r -> r -> Bool) -> (r -> r -> Bool)
coreflexive = coreflexive_on (==)


-- | \( \forall a, b: ((a \# b) \wedge (b \# a)) \Rightarrow (a \doteq b) \)
--
coreflexive_on :: (r -> r -> Bool) -> (r -> r -> Bool) -> (r -> r -> Bool)
coreflexive_on (~~) (#) a b = (a # b) && (b # a) ==> (a ~~ b)


-- | \( \forall a, b: (a \# b) \Rightarrow ((a \# a) \wedge (b \# b)) \)
--
quasireflexive :: (r -> r -> Bool) -> (r -> r -> Bool)
quasireflexive (#) a b = (a # b) ==> (a # a) && (b # b)
