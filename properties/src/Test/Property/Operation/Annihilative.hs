module Test.Property.Operation.Annihilative where

import Test.Property.Util


-- | \( \forall a: (u \# a) \equiv u \)
--
-- Right annihilativity of an element /u/ with respect to an operator /#/.
--
-- For example, @False@ is a right annihilative element of @||@.
--
annihilative :: Eq r => (r -> r -> r) -> r -> (r -> Bool)
annihilative = annihilative_on (==)

-- | \( \forall a: (a \# u) \equiv u \)
--
-- Left annihilativity of an element /u/ with respect to an operator /#/.
--
-- For example, @Nothing@ is a right annihilative element of @*>@.
--
annihilative' :: Eq r => (r -> r -> r) -> r -> (r -> Bool)
annihilative' = annihilative_on' (==)

annihilative_on :: (r -> r -> Bool) -> (r -> r -> r) -> r -> (r -> Bool)
annihilative_on (~~) (#) u a = (u # a) ~~ u

annihilative_on' :: (r -> r -> Bool) -> (r -> r -> r) -> r -> (r -> Bool)
annihilative_on' (~~) (#) u a = (a # u) ~~ u
