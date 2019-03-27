module Data.Profunctor.Optic.Fold where

import Data.Monoid
--import Data.Monoid (All(..), Any(..), First(..), Product(..), Sum(..))
import Data.Profunctor.Optic.Getter
import Data.Profunctor.Optic.Types -- (Fold, star)
import Data.Profunctor.Optic.Operators

import Data.Functor.Const (Const(..))



---------------------------------------------------------------------
-- Affine Fold
---------------------------------------------------------------------

afolding :: (s -> Maybe a) -> AffineFold s a
afolding f = cimap (\s -> maybe (Left s) Right (f s)) Left . right'

--We can freely convert between AffineFold s a and Getter s (Maybe a):

--getterToAF, getterToAF' :: Getter s t (Maybe a) b -> AffineFold s s a a

getterToAF :: Getter s (Maybe a) -> AffineFold s a
getterToAF o = afolding (view o) --  = o . _Just

--afToGetter :: AffineFold s a -> Getter s (Maybe a)
--afToGetter o = to (preview o)


{-
gets :: Optical (SubStar (Constant r)) ta tb a b -> (a -> r) -> ta -> r
-- ^ @
-- gets :: To ta tb a b -> (a -> r) -> ta -> r
-- gets :: Monoid r => Fold ta tb a b -> (a -> r) -> ta -> r
-- @
gets l f = getConstant . h
 where
  Kleisli h = l (Kleisli (Constant . f))

get :: Optical (SubStar (Constant a)) ta tb a b -> ta -> a
-- ^ @
-- get :: To ta tb a b -> ta -> a
-- get :: Monoid a => Fold ta tb a b -> ta -> a
-- @
get l = gets l id

beget :: Optical (SuperStar (Constant b)) ta tb a b -> b -> tb
-- ^ @
-- beget :: Fro ta tb a b -> b -> tb
-- @
beget l = h . Constant
 where
  SuperStar h = l (SuperStar getConstant)

set :: ((a -> b) -> c) -> b -> c
-- ^ @
-- set :: SEC ta tb a b -> b -> ta -> tb
-- @
set l = l . const

modifyF :: Optical (SubStar f) ta tb a b -> (a -> f b) -> ta -> f tb
-- ^ @
-- modifyF :: Functor f => Lens ta tb a b -> (a -> f b) -> ta -> f tb
-- modifyF :: Applicative f => Traversal ta tb a b -> (a -> f b) -> ta -> f tb
-- @
modifyF l f = tf
 where
  Kleisli tf = l (Kleisli f)

match :: Optical (SubStar (Either a)) ta tb a b -> ta -> Either tb a
-- ^ @
-- match :: Traversal ta tb a b -> ta -> Either tb a
-- @
match l = switch . h
 where
  Kleisli h = l (Kleisli Left)

toListOf :: Applicative f => Optical (SubStar (Constant (f a))) ta tb a b -> ta -> f a
-- ^ @
-- toListOf :: Fold ta tb a b -> ta -> [a]
-- toListOf :: (Applicative f, Monoid (f a)) => Fold ta tb a b -> ta -> f a
-- toListOf :: Applicative f => To ta tb a b -> ta -> f a
-- @
toListOf l = gets l pure

firstOf :: Optical (SubStar (Constant (First a))) ta tb a b -> ta -> Maybe a
-- ^ @
-- firstOf :: Fold ta tb a b -> ta -> Maybe a
-- @
firstOf l = getFirst . gets l (First . pure)

sumOf :: Optical (SubStar (Constant (Sum a))) ta tb a b -> ta -> a
sumOf l = getSum . gets l Sum

productOf :: Optical (SubStar (Constant (Product a))) ta tb a b -> ta -> a
productOf l = getProduct . gets l Product

allOf :: Optical (SubStar (Constant All)) ta tb a b -> (a -> Bool) -> ta -> Bool
allOf l p = getAll . gets l (All . p)

anyOf :: Optical (SubStar (Constant Any)) ta tb a b -> (a -> Bool) -> ta -> Bool
anyOf l p = getAny . gets l (Any . p)

lengthOf :: Num r => Optical (SubStar (Constant (Sum r))) ta tb a b -> ta -> r
lengthOf l = getSum . gets l (const (Sum 1))

nullOf :: Optical (SubStar (Constant All)) ta tb a b -> ta -> Bool
nullOf l = allOf l (const False)

infixl 8 ^., ^.., ^?
infixr 4 .~

x^.l = get l x
x^..l = toListOf l x
x^?l = firstOf l x
l.~x = set l x

to :: (ta -> a) -> To ta tb a b
to f = ocoerce . imap f

fro :: (b -> tb) -> Fro ta tb a b
fro f = icoerce . omap f

foldMapOf :: Fold r s t a b -> (a -> r) -> s -> r
foldMapOf o f = getConst . runStar (o . star Const $ f)



-}


{-
-- | Folds all foci of a `Fold` to one. Similar to 'view'.
foldOf :: Fold a s t a b -> s -> a
foldOf p = foldMapOf p id


infixl 8 ^?

(^?) :: s -> Fold (First a) s t a b -> Maybe a
s ^? p = preview' p s

-- | Previews the first value of a fold, if there is any.
preview' :: Fold (First a) s t a b -> s -> Maybe a
preview' p = getFirst . foldMapOf p (First . Just)


-- | Right fold over a 'Fold'.
foldrOf :: Fold (Endo r) s t a b -> (a -> r -> r) -> r -> s -> r
foldrOf p f r = flip appEndo r . foldMapOf p (Endo . f)

-- | Left fold over a 'Fold'.
foldlOf :: Fold (Dual (Endo r)) s t a b -> (r -> a -> r) -> r -> s -> r
foldlOf p f r = flip appEndo r . getDual . foldMapOf p (Dual . Endo . flip f)

allOf :: Fold All s t a b -> (a -> Bool) -> s -> Bool
allOf p f = getAll . foldMapOf p (All . f)

anyOf :: Fold Any s t a b -> (a -> Bool) -> s -> Bool
anyOf p f = getAny . foldMapOf p (Any . f)

-- | Whether a `Fold` contains a given element.
elemOf :: Eq a => Fold Any s t a b -> a -> s -> Bool
elemOf p a = anyOf p (== a)

-- | Whether a `Fold` not contains a given element.
notElemOf :: Eq a => Fold All s t a b -> a -> s -> Bool
notElemOf p a = allOf p (/= a)

-- | The sum of all foci of a `Fold`.
sumOf :: Fold (Sum a) s t a b -> s -> a
sumOf p = getSum . foldMapOf p Sum

-- | The product of all foci of a `Fold`.
productOf :: Fold (Product a) s t a b -> s -> a
productOf p = getProduct . foldMapOf p Product

-- | The number of foci of a `Fold`.
lengthOf :: Fold (Sum Int) s t a b -> s -> Int
lengthOf p = getSum . foldMapOf p (const $ Sum 1)

-- | The first focus of a `Fold`, if there is any. Synonym for `preview`.
firstOf :: Fold (First a) s t a b -> s -> Maybe a
firstOf p = getFirst . foldMapOf p (First . Just)

-- | The last focus of a `Fold`, if there is any.
lastOf :: Fold (Last a) s t a b -> s -> Maybe a
lastOf p = getLast . foldMapOf p (Last . Just)

-- | Collects the foci of a `Fold` into a list.
toListOf :: Fold (Endo [a]) s t a b -> s -> [a]
toListOf p = foldrOf p (:) []

infixl 8 ^..

(^..) :: s -> Fold (Endo [a]) s t a b -> [a]
s ^.. p = toListOf p s

-- | Traverse the foci of a `Fold`, discarding the results.
traverseOf_
  :: Applicative f
  => Fold (Endo (f ())) s t a b
  -> (a -> f r)
  -> s
  -> f ()
traverseOf_ p f = foldrOf p (\a f' -> (() <$) (f a) *> f') $ pure ()


-- | Sequence the foci of a `Fold`, discarding the results.
sequenceOf_ 
  :: Applicative f 
  => Fold (Endo (f ())) s t (f a) b 
  -> s 
  -> f ()
sequenceOf_ p = traverseOf_ p id


-- | Find the first focus of a `Fold` that satisfies a predicate, if there is any.
findOf :: Fold (Endo (Maybe a)) s t a b -> (a -> Bool) -> s -> Maybe a
findOf p f = foldrOf p (\a -> maybe (if f a then Just a else Nothing) Just) Nothing


-- | Determines whether a `Fold` has at least one focus.
has :: Fold Any s t a b -> s -> Bool
has p = getAny . foldMapOf p (const (Any True))


-- | Determines whether a `Fold` does not have a focus.
hasnt :: Fold All s t a b -> s -> Bool
hasnt p = getAll . foldMapOf p (const (All False))

-}


{-
-- | Replicates the elements of a fold.
replicated :: forall a b t r. Monoid r => Int -> Fold r a b a t
replicated i (Forget a) = Forget (go i a)
  where go 0 _ = mempty
        go n x = x <> go (n - 1) x


-- | Folds over a `Foldable` container.
folded :: forall g a b t r. Monoid r => Foldable g => Fold r (g a) b a t
folded (Forget a) = Forget (foldMap a)
-}


{-



-- | The maximum of all foci of a `Fold`, if there is any.
maximumOf :: forall s t a b. Ord a => Fold (Endo (->) (Maybe a)) s t a b -> s -> Maybe a
maximumOf p = foldrOf p (\a -> Just . maybe a (max a)) Nothing where
  max a b = if a > b then a else b

-- | The minimum of all foci of a `Fold`, if there is any.
minimumOf :: forall s t a b. Ord a => Fold (Endo (->) (Maybe a)) s t a b -> s -> Maybe a
minimumOf p = foldrOf p (\a -> Just . maybe a (min a)) Nothing where
  min a b = if a < b then a else b

-- | Find the first focus of a `Fold` that satisfies a predicate, if there is any.
findOf :: Fold (Endo (Maybe a)) s t a b -> (a -> Boolean) -> s -> Maybe a
findOf p f = foldrOf p (\a -> maybe (if f a then Just a else Nothing) Just) Nothing


-- | Filters on a predicate.
(a -> Bool) -> p (Either a a) (Either b b) -> p (Either a a) (Either b b)

--filtered :: Choice p => (a -> Bool) -> Optic' p a a
filtered f =
  right' .
    dimap
      (\x -> if f x then Right x else Left x)
      (either id id)



-- | Builds a `Fold` using an unfold.
unfolded
  :: forall r s t a b
   . Monoid r
  => (s -> Maybe (Tuple a s))
  -> Fold r s t a b
unfolded f p = Forget go
  where
  go = maybe mempty (\(Tuple a sn) -> unwrap p a <> go sn) . f

-- | Fold map over an `IndexedFold`.
ifoldMapOf
  :: forall r i s t a b
   . IndexedFold r i s t a b
  -> (i -> a -> r)
  -> s
  -> r
ifoldMapOf p f = unwrap $ p $ Indexed $ Forget (uncurry f)

-- | Right fold over an `IndexedFold`.
ifoldrOf
  :: forall i s t a b r
   . IndexedFold (Endo (->) r) i s t a b
  -> (i -> a -> r -> r)
  -> r
  -> s
  -> r
ifoldrOf p f r = flip unwrap r . ifoldMapOf p (\i -> Endo . f i)

-- | Left fold over an `IndexedFold`.
ifoldlOf
  :: forall i s t a b r
   . IndexedFold (Dual (Endo (->) r)) i s t a b
  -> (i -> r -> a -> r)
  -> r
  -> s
  -> r
ifoldlOf p f r =
  flip unwrap r
    . unwrap
    . ifoldMapOf p (\i -> Dual . Endo . flip (f i))

-- | Whether all foci of an `IndexedFold` satisfy a predicate.
iallOf
  :: forall i s t a b r
   . HeytingAlgebra r
   => IndexedFold (Conj r) i s t a b
   -> (i -> a -> r)
   -> s
   -> r
iallOf p f = unwrap . ifoldMapOf p (\i -> Conj . f i)

-- | Whether any focus of an `IndexedFold` satisfies a predicate.
ianyOf
  :: forall i s t a b r
   . HeytingAlgebra r
  => IndexedFold (Disj r) i s t a b
  -> (i -> a -> r)
  -> s
  -> r
ianyOf p f = unwrap . ifoldMapOf p (\i -> Disj . f i)

-- | Find the first focus of an `IndexedFold` that satisfies a predicate, if
-- | there is any.
ifindOf
  :: forall i s t a b
   . IndexedFold (Endo (->) (Maybe a)) i s t a b
  -> (i -> a -> Boolean)
  -> s
  -> Maybe a
ifindOf p f =
  ifoldrOf
    p
    (\i a -> maybe (if f i a then Just a else Nothing) Just)
    Nothing

-- | Collects the foci of an `IndexedFold` into a list.
itoListOf
  :: forall i s t a b
   . IndexedFold (Endo (->) (List (Tuple i a))) i s t a b
  -> s
  -> List (Tuple i a)
itoListOf p = ifoldrOf p (\i x xs -> Tuple i x : xs) Nil

-- | Traverse the foci of an `IndexedFold`, discarding the results.
itraverseOf_
  :: forall i f s t a b r. (Applicative f)
  => IndexedFold (Endo (->) (f Unit)) i s t a b
  -> (i -> a -> f r)
  -> s
  -> f Unit
itraverseOf_ p f = ifoldrOf p (\i a fu -> void (f i a) *> fu) (pure unit)

-- | Flipped version of `itraverseOf_`.
iforOf_
  :: forall i f s t a b r. (Applicative f)
  => IndexedFold (Endo (->) (f Unit)) i s t a b
  -> s
  -> (i -> a -> f r)
  -> f Unit
iforOf_ = flip . itraverseOf_

-}
