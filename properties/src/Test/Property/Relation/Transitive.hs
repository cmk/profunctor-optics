module Test.Property.Relation.Transitive where

import Test.Property.Util


-- | \( \forall a, b, c: ((a \# b) \wedge (b \# c)) \Rightarrow (a \# c) \)
--
-- For example, "is ancestor of" is a transitive relation, while "is parent of" is not.
--
transitive :: (r -> r -> Bool) -> r -> r -> r -> Bool
transitive (#) a b c = (a # b) && (b # c) ==> a # c


-- | \( \forall a, b, c: ((a \# b) \wedge (a \# c)) \Rightarrow (b \# c) \)
--
-- For example, /=/ is an right Euclidean relation because if /x = y/ and /x = z/ then /y = z/.
--
euclidean :: (r -> r -> Bool) -> r -> r -> r -> Bool
euclidean (#) a b c = (a # b) && (a # c) ==> b # c


-- |  \( \forall a, b, c: ((b \# a) \wedge (c \# a)) \Rightarrow (b \# c) \)
--
-- For example, /=/ is a left Euclidean relation because if /x = y/ and /x = z/ then /y = z/.
--
euclidean' :: (r -> r -> Bool) -> r -> r -> r -> Bool
euclidean' (#) a b c = (b # a) && (c # a) ==> b # c
