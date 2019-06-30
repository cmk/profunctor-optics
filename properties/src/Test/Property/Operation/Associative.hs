module Test.Property.Operation.Associative where

import Test.Property.Util


-- | \( \forall a, b, c: (a \# b) \# c \equiv a \# (b \# c) \)
--
associative :: Eq r => (r -> r -> r) -> (r -> r -> r -> Bool)
associative = associative_on (==)


-- | \( \forall a, b, c: (a \# b) \# c \doteq a \# (b \# c) \)
--
associative_on :: (r -> r -> Bool) -> (r -> r -> r) -> (r -> r -> r -> Bool)
associative_on (~~) (#) a b c = ((a # b) # c) ~~ (a # (b # c)) 
