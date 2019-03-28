
module Data.Profunctor.Optic.Operators where

import Data.Profunctor.Optic.Types



re :: Optic (Re p a b) s t a b -> Optic p b a t s
re o = (through Re runRe) o id

over :: Optic (->) s t a b -> (a -> b) -> s -> t
over = id

review :: Optic Tagged s t a b -> b -> t
review = through Tagged unTagged

-- | 'view o == foldMapOf o id'
view :: Optic (Forget a) s t a b -> s -> a
view o = (through Forget runForget) o id

match :: Optic (Matched a) s t a b -> s -> Either t a
match o = (through Matched runMatched) o Right

preview :: Optic (Previewed a) s t a b -> s -> Maybe a
preview o = (through Previewed runPreviewed) o Just

foldMapOf :: Optic (Forget r) s t a b -> (a -> r) -> s -> r
foldMapOf = through Forget runForget

zipWithOf :: Optic Zipped s t a b -> (a -> a -> b) -> s -> s -> t
zipWithOf = through Zipped runZipped 

-- | 'traverseOf' can be used to convert 'Strong' optics to their
-- van Laarhoven equivalents.
traverseOf :: Optic (Star f) s t a b -> (a -> f b) -> s -> f t
traverseOf = through Star runStar

cotraverseOf :: Optic (Costar f) s t a b -> (f a -> b) -> (f s -> t)
cotraverseOf = through Costar runCostar

-- | Box up a profunctor, map it through an optic, then unbox.
through :: (t1 -> t2) -> (t3 -> t4) -> (t2 -> t3) -> t1 -> t4
through up down optic a = down (optic $ up a)

switch :: Either b a -> Either a b
switch (Left e) = Right e
switch (Right e) = Left e
