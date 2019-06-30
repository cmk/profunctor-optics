module Test.Property.Function.Idempotent where

import Data.List (unfoldr)
import Numeric.Natural (Natural(..))
import Test.Property.Util

idempotent :: Eq r => (r -> r) -> r -> Bool
idempotent f = projective f f

projective :: Eq r => (r -> r) -> (r -> r) -> r -> Bool
projective f g r = g (f r) == f r

idempotent_k :: Eq r => Natural -> (r -> r) -> r -> Bool
idempotent_k k f r = k >= 1 ==> foldr (.) id fs r == f r
  where fs = (`unfoldr` k) $ \m -> if m==1 then Nothing else Just (f,m-1)
