{-# LANGUAGE UndecidableSuperClasses, TypeOperators , GADTs, DataKinds, KindSignatures, TypeFamilies #-}

{-# LANGUAGE TupleSections #-}

module Data.Profunctor.Optic.Operators where

import Data.Profunctor.Optic.Types



through :: (t1 -> t2) -> (t3 -> t4) -> (t2 -> t3) -> t1 -> t4
through up down o f = down (o $ up f)


switch :: Either b a -> Either a b
switch (Left e) = Right e
switch (Right e) = Left e


re :: Optic (Re p a b) s t a b -> Optic p b a t s
re o = (through Re runRe) o id

over :: Optic (->) s t a b -> (a -> b) -> s -> t
over = id

reover :: Optic (Re (->) a b) s t a b -> (t -> s) -> (b -> a)
reover = over . re

set :: Optic (->) s t a b -> s -> b -> t
set o s b = over o (const b) s

reset :: Optic (Re (->) a b) s t a b -> b -> s -> a
reset = set . re

view :: Optic (Forget a) s t a b -> s -> a
view o = (through Forget runForget) o id

review :: Optic Tagged s t a b -> b -> t
review = through Tagged unTagged

preview :: Optic (Previewed a) s t a b -> s -> Maybe a
preview o = (through Previewed runPreviewed) o Just

matching :: Optic (Matched a) s t a b -> s -> Either t a
matching o = (through Matched runMatched) o Right

foldMapOf :: Optic (Forget r) s t a b -> (a -> r) -> s -> r
foldMapOf = through Forget runForget

traverseOf :: Optic (Star f) s t a b -> (a -> f b) -> s -> f t
traverseOf = through Star runStar

zipFWithOf :: Optic (Costar f) s t a b -> (f a -> b) -> (f s -> t)
zipFWithOf = through Costar runCostar

zipWithOf :: Optic Zipped s t a b -> (a -> a -> b) -> s -> s -> t
zipWithOf = through Zipped runZipped 





into :: ((a -> b) -> c) -> (r -> b) -> (a -> r) -> c
into up f = up . (f .)


outof :: (c -> a -> b) -> (b -> r) -> c -> a -> r
outof down g = (g .) . down


star
  :: (c -> f b)
  -> (f t -> d)
  -> Optic (Star f) s t a b 
  -> (a -> c)
  -> s
  -> d
star up down o f = outof runStar down (o . into Star up $ f)


costar
  :: (c -> b)
  -> (t -> d)
  -> Optic (Costar f) s t a b 
  -> (f a -> c)
  -> f s
  -> d
costar up down o f = outof runCostar down (o . into Costar up $ f)


mirrored :: Optic (Star (Either a)) s t a b -> s -> Either a t
mirrored o =
 let k = through (into Star Left) runStar
  in k o id

matching' :: Optic (Star (Either a)) s t a b -> s -> Either t a
matching' o = switch . mirrored o


cool :: Functor f => (b -> r) -> (r -> t) -> (s -> a) -> Optic (Costar f) s t a b
cool br rt sa o = into Costar rt (outof runCostar br o . fmap sa)


neat
  :: Optic (Star Maybe) s t a b
  -> (a -> b) -> s -> Maybe t
neat o ab = (star Just . fmap) id o ab 

word
  :: Monoid a -- Default a
  => Optic (Costar Maybe) s t a b 
  -> (a -> b) -> Maybe s -> t
word o ab = costar ab id o (maybe mempty id)


{-
costar Just
  :: (t -> d)
     -> Optic (Costar f) s t a1 (Maybe a2) -> (f a1 -> a2) -> f s -> d

outof runCostar Just :: Costar f d a -> f d -> Maybe a
outof runCostar Just
-}

--star' up down o f = outof runStar up (o . into Star down $ f)

baz
  :: Optic (Costar f) s t a b -> (f a -> b) -> f s -> Maybe t
baz = costar id Just

--bippy :: Optic (Costar f) s t a b -> (f a -> b) -> f s -> Maybe r
--bippy costar id (const Nothing)


{-


mirrored :: Optic (Star (Either a)) s t a b -> s -> Either a t

previewed :: (Star Maybe c1 c1 -> Star Maybe d c2) -> d -> Maybe c2
previewed o =
 let k = through (into Star Just) runStar
  in k o id
-}



-- | Apply a function to the foci of a `Setter`.
--over :: Setter s t a b -> (a -> b) -> s -> t
--over = undefined -- star Identity runIdentity 

-- | Set the foci of a `Setter` to a constant value.
--set :: Setter s t a b -> b -> s -> t
--set l b = over l (const b)



{-
--change to a vl lens
withStar :: Optic (Star f) s t a b
         -> (a -> f b) -> s -> f t
withStar o f = runStar (o (Star f))

λ> :t set (rePrism right')
set (rePrism right') :: s -> Either c t -> t

rePrism :: Prism s t a b -> Lens b a t s
rePrism f o = f (reviewP o) (reset o)

newtype Star f a b = Star {runStar :: a -> f b}
newtype Costar f a b = Costar {runCostar :: f a -> b}


newtype Forget r a b = Forget { runForget :: a -> r }
Note: Forget r is isomorphic to Star (Const r).


over :: Setter s t a b -> (a -> b) -> s -> t
over = star Identity runIdentity 

coover :: Optic (Costar Identity) s t a b -> (a -> b) -> s -> t
coover o f = costar f id o runIdentity . Identity

star Just Just
  :: Optic (Star Maybe) s t a b -> (a -> b) -> s -> Maybe (Maybe t)

preview :: Optic (Star Maybe) s t a b -> (a -> b) -> s -> Maybe t
preview = through (star Just) runStar


matching :: Optic (Star (Either e)) s t a b -> (a -> b) -> s -> Either e t
matching = through (star Right) runStar

matching :: Optic (Star (Either a)) s t a b -> s -> Either a t
matching = through (star Left) runStar $ id


matching :: Optic (Star (Either a)) s t a b -> (a -> a) -> s -> Either a t
matching = through (into Star Left) runStar



matching' :: ((a -> Either e b) -> s -> t) -> Optic (Star (Either e)) s t a b
matching' = through runStar (star Right)

-}


