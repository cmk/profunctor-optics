-- | See <https://en.wikipedia.org/wiki/Connex_relation>.
module Test.Property.Relation.Connex where

import Test.Property.Util

-- | \( \forall a, b: ((a \# b) \vee (b \# a)) \)
--
-- For example, ≥ is a connex relation, while 'divides evenly' is not.
-- 
-- A connex relation cannot be symmetric, except for the universal relation.
--
connex :: (r -> r -> Bool) -> r -> r -> Bool
connex (#) a b = (a # b) || (b # a)


-- | \( \forall a, b: \neg (a \equiv b) \Rightarrow ((a \# b) \vee (b \# a)) \)
--
-- A binary relation is semiconnex if it relates all pairs of _distinct_ elements in some way.
--
-- A relation is connex if and only if it is semiconnex and reflexive.
--
semiconnex :: Eq r => (r -> r -> Bool) -> r -> r -> Bool
semiconnex = semiconnex_on (==)


-- | \( \forall a, b: \neg (a \doteq b) \Rightarrow ((a \# b) \vee (b \# a)) \)
--
semiconnex_on :: (r -> r -> Bool) -> (r -> r -> Bool) -> r -> r -> Bool
semiconnex_on (~~) (#) a b = not (a ~~ b) ==> connex (#) a b


-- | \( \forall a, b, c: ((a \# b) \vee (a \equiv b) \vee (b \# a)) \wedge \neg ((a \# b) \wedge (a \equiv b) \wedge (b \# a)) \)
--
-- Note that @ trichotomous (>) @ should hold for any 'Ord' instance.
--
trichotomous :: Eq r => (r -> r -> Bool) -> r -> r -> Bool
trichotomous = trichotomous_on (==)


-- | \( \forall a, b, c: ((a \# b) \vee (a \doteq b) \vee (b \# a)) \wedge \neg ((a \# b) \wedge (a \doteq b) \wedge (b \# a)) \)
--
-- In other words, exactly one of \(a \# b\), \(a \doteq b\), or \(b \# a\) holds.
-- 	
-- For example, > is a trichotomous relation, while ≥ is not.
--
trichotomous_on :: (r -> r -> Bool) -> (r -> r -> Bool) -> r -> r -> Bool
trichotomous_on (~~) (#) a b = xor3 (a # b) (a ~~ b) (b # a)
