module Test.Property.Function.Monotone where

import Test.Property.Util

monotone :: Ord r => (r -> r) -> r -> r -> Bool
monotone = monotone_on (<=)

monotone_on :: (r -> r -> Bool) -> (r -> r) -> r -> r -> Bool
monotone_on (<~) f a b = a <~ b ==> f a <~ f b

antitone :: Ord r => (r -> r) -> r -> r -> Bool
antitone = antitone_on (<=)

antitone_on :: (r -> r -> Bool) -> (r -> r) -> r -> r -> Bool
antitone_on (<~) f a b = a <~ b ==> f b <~ f a
