module Test.Property.Operation.Distributive where

import Test.Property.Util


-- | \( \forall a, b, c: (a \# b) \% c \equiv (a \% c) \# (b \% c) \)
--
distributive :: Eq r => (r -> r -> r) -> (r -> r -> r) -> (r -> r -> r -> Bool)
distributive = distributive_on (==)

-- | \( \forall a, b, c: c \% (a \# b) \equiv (c \% a) \# (c \% b) \)
--
distributive' :: Eq r => (r -> r -> r) -> (r -> r -> r) -> (r -> r -> r -> Bool)
distributive' = distributive_on' (==)

distributive_on :: (r -> r -> Bool) -> (r -> r -> r) -> (r -> r -> r) -> (r -> r -> r -> Bool)
distributive_on (~~) (#) (%) a b c = ((a # b) % c) ~~ ((a % c) # (b % c))

distributive_on' :: (r -> r -> Bool) -> (r -> r -> r) -> (r -> r -> r) -> (r -> r -> r -> Bool)
distributive_on' (~~) (#) (%) a b c = (c % (a # b)) ~~ ((c % a) # (c % b))
