module Test.Property.Operation.Commutative where

-- | \( \forall a, b: a \# b \equiv b \# a \)
--
commutative :: Eq r => (r -> r -> r) -> r -> r -> Bool
commutative = commutative_on (==)

-- | \( \forall a, b: a \# b \doteq b \# a \)
--
commutative_on :: (r -> r -> Bool) -> (r -> r -> r) -> r -> r -> Bool
commutative_on (~~) (#) a b = (a # b) ~~ (b # a)

