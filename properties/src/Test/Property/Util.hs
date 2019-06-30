module Test.Property.Util where


xor :: Bool -> Bool -> Bool
xor a b = (a || b) && not (a && b)

xor3 :: Bool -> Bool -> Bool -> Bool
xor3 a b c = (a `xor` (b `xor` c)) && not (a && b && c)

infixr 0 ==>

(==>) :: Bool -> Bool -> Bool
(==>) a b = not a || b

iff :: Bool -> Bool -> Bool
iff a b = a ==> b && b ==> a

infixr 1 <==>

(<==>) :: Bool -> Bool -> Bool
(<==>) = iff
