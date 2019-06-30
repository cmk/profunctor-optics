module Test.Property.Function.Invertible where

import Test.Property.Util

-- | \( \forall a: f (g a) \equiv a \)
--
invertible :: Eq r => (r -> r) -> (r -> r) -> (r -> Bool)
invertible = invertible_on (==)

-- | \( \forall a: f (g a) \doteq a \)
--
invertible_on :: (r -> r -> Bool) -> (r -> r) -> (r -> r) -> (r -> Bool)
invertible_on (~~) f g a = g (f a) ~~ a
