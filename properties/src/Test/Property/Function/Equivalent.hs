module Test.Property.Function.Equivalent where

import Test.Property.Util


-- | \( \forall a: f a \# b \Leftrightarrow a \# g b \)
--
-- For example, a Galois connection is defined by @adjoint_on (<=)@.
--
adjoint_on :: (r -> r -> Bool) -> (r -> r) -> (r -> r) -> (r -> r -> Bool)
adjoint_on (#) f g a b = f a # b <==> a # g b


-- | \( \forall a: f a \equiv g a \)
--
equivalent :: Eq r => (r -> r) -> (r -> r) -> (r -> Bool)
equivalent = equivalent_on (==)


-- | \( \forall a: f a \doteq g a \)
--
equivalent_on :: (r -> r -> Bool) -> (r -> r) -> (r -> r) -> (r -> Bool)
equivalent_on (~~) f g a = f a ~~ g a
