module Test.Property.Function.Injective where

import Test.Property.Util

-- | \( \forall a: f a \equiv f b \Rightarrow a \equiv b \)
--
injective :: Eq r => (r -> r) -> r -> r -> Bool
injective = injective_on (==)


-- | \( \forall a: f a \doteq f b \Rightarrow a \doteq b \)
--
injective_on :: (r -> r -> Bool) -> (r -> r) -> r -> r -> Bool
injective_on (~~) f a b = (f a ~~ f b) ==> (a ~~ b)
