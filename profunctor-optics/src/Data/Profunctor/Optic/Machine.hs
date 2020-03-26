{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Machine (
    -- * Moore
    Moore
  , moore
  , mooreVl
  , listing
  , packing
  , chunking
  , foldingr
  , foldingr'
  , foldingl
  , foldingl'
  , foldingrM
  , foldinglM
  , traversing_
  , mappingM_
  , foldMapping
    -- * Mealy 
  , Mealy
  , mealy
  , mealyVl
  , listing1
  , packing1
  , foldingl1
  , foldingr1
  , foldingrM1
  , foldinglM1
  , traversing1_
  , foldMapping1
    -- * Optics
  , head1
  , last1
  , projected
  , minimized
  , maximized
  , minimizedBy
  , maximizedBy
  , minimizedDef 
  , maximizedDef
  , minimizedByDef
  , maximizedByDef
  , foundDef
    -- * Sequential optics
  , packed
  , packed'
  , taken
  , taken'
  , padded
  , padded'
  , takenWhile
  , takenWhile'
  , droppedWhile
  , droppedWhile'
  , filteredBy
  , filteredBy'
  , filteredBy1
  , broken
  , spanned
  , partitioned
  , partitioned'
  , groupedAllOn
  , splitWhen
  , splitFirst
 -- , intercalated
    -- * Operators
  , buildl
  , buildsl
  , obuildl
  , obuildsl
  , buildl1
  , buildsl1
  , obuildl1
  , obuildsl1
  , listl
  , listl1
  , mconcatl
  , sconcatl
  , mconcatsl
  , sconcatsl
) where

import Data.List.NonEmpty (NonEmpty (..))
import Data.Monoid
import Data.MonoTraversable (MonoFoldable(..), Element)
import Data.NonNull (NonNull)
import Data.Semigroup
import Data.Sequences (IsSequence, LazySequence, Index)
import Data.Profunctor.Optic.Carrier hiding (Index)
import Data.Profunctor.Optic.Combinator
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Types
import Data.Semigroup.Foldable as F1
import qualified Control.Foldl as L
import qualified Data.Foldable as F
import qualified Data.Profunctor.Rep.Foldl as L
import qualified Data.Profunctor.Rep.Foldl1 as L1
import qualified Data.NonNull as NN
import qualified Data.Sequences as MS
import qualified Data.List.NonEmpty as NE
import qualified Data.MonoTraversable as MT

--import qualified Control.Foldl.ByteString as LB

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XFlexibleContexts
-- >>> :set -XTypeApplications
-- >>> :set -XTypeFamilies
-- >>> :set -XTupleSections
-- >>> :set -XRankNTypes
-- >>> import Data.Char
-- >>> import Data.Monoid
-- >>> import Data.Semigroup
-- >>> import Data.List.NonEmpty (NonEmpty(..))
-- >>> import Data.Function ((&))
-- >>> import Data.Foldable
-- >>> import Data.Ord
-- >>> import Data.List ((!!))
-- >>> import qualified Control.Foldl as L
-- >>> import qualified Data.ByteString as B
-- >>> import qualified Data.ByteString.Lazy as BL
-- >>> import qualified Data.ByteString.Char8 as C
-- >>> import qualified Data.ByteString.Lazy.Char8 as CL
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- 'Moore'
---------------------------------------------------------------------

-- | Obtain a 'Moore' directly.
--
moore :: (s -> a) -> (forall f. Foldable f => f s -> b -> t) -> Moore s t a b
moore sa sbt p = cotabulate $ \s -> sbt s (cosieve p . fmap sa $ s)
{-# INLINE moore #-}

-- | Transform a Van Laarhoven 'Moore' into a profunctor 'Moore'.
--
mooreVl :: (forall f. Foldable f => (f a -> b) -> f s -> t) -> Moore s t a b
mooreVl = corepresent
{-# INLINE mooreVl #-}

-- | A < http://events.cs.bham.ac.uk/syco/strings3-syco5/slides/roman.pdf list lens >.
--
listing :: (s -> a) -> ([s] -> b -> t) -> Moore s t a b
listing sa sbt = moore sa $ sbt . F.toList
{-# INLINE listing #-}

-- | TODO: Document
--
packing :: IsSequence s => (Element s -> a) -> (s -> b -> t) -> Moore (Element s) t a b
packing sa sbt = moore sa $ sbt . MS.pack . F.toList
{-# INLINEABLE packing #-}

-- | TODO: Document
--
chunking :: LazySequence l s => (s -> a) -> (l -> b -> t) -> Moore s t a b
chunking sa sbt = moore sa $ sbt . MS.fromChunks . F.toList
{-# INLINEABLE chunking #-}

-- | TODO: Document
--
foldingr :: (s -> a) -> (s -> r -> r) -> r -> (r -> b -> t) -> Moore s t a b
foldingr sa h z rbt = moore sa $ rbt . F.foldr h z
{-# INLINE foldingr #-}

-- | TODO: Document
--
foldingr' :: (s -> a) -> (s -> r -> r) -> r -> (r -> b -> t) -> Moore s t a b
foldingr' sa h z rbt = moore sa $ rbt . F.foldr' h z
{-# INLINE foldingr' #-}

-- | TODO: Document
--
foldingl :: (s -> a) -> (r -> s -> r) -> r -> (r -> b -> t) -> Moore s t a b
foldingl sa h z rbt = moore sa $ rbt . F.foldl h z
{-# INLINE foldingl #-}

-- | TODO: Document
--
foldingl' :: (s -> a) -> (r -> s -> r) -> r -> (r -> b -> t) -> Moore s t a b
foldingl' sa h z rbt = moore sa $ rbt . F.foldl' h z
{-# INLINE foldingl' #-}

-- | TODO: Document
--
foldingrM :: Monad m => (s -> a) -> (s -> r -> m r) -> r -> (m r -> b -> t) -> Moore s t a b
foldingrM sa h z rbt = moore sa $ rbt . F.foldrM h z
{-# INLINE foldingrM #-}

-- | TODO: Document
--
foldinglM :: Monad m => (s -> a) -> (r -> s -> m r) -> r -> (m r -> b -> t) -> Moore s t a b
foldinglM sa h z rbt = moore sa $ rbt . F.foldlM h z
{-# INLINE foldinglM #-}

-- | TODO: Document
--
traversing_ :: Applicative f => (s -> a) -> (s -> f r) -> (f () -> b -> t) -> Moore s t a b
traversing_ sa h sbt = moore sa $ sbt . F.traverse_ h
{-# INLINE traversing_ #-}

-- | TODO: Document
--
mappingM_ :: Monad m => (s -> a) -> (s -> m r) -> (m () -> b -> t) -> Moore s t a b
mappingM_ sa h sbt = moore sa $ sbt . F.mapM_ h
{-# INLINE mappingM_ #-}

-- | TODO: Document
--
foldMapping :: Monoid r => (s -> a) -> (s -> r) -> (r -> b -> t) -> Moore s t a b
foldMapping sa sr rbt = moore sa $ rbt . F.foldMap sr
{-# INLINE foldMapping #-}

---------------------------------------------------------------------
-- 'Mealy'
---------------------------------------------------------------------

-- | Obtain a 'Mealy' directly.
--
mealy :: (s -> a) -> (forall f. Foldable1 f => f s -> b -> t) -> Mealy s t a b
mealy sa sbt p = cotabulate $ \s -> sbt s (cosieve p . fmap sa $ s)
{-# INLINE mealy #-}

-- | Transform a Van Laarhoven 'Mealy' into a profunctor 'Mealy'.
--
mealyVl :: (forall f. Foldable1 f => (f a -> b) -> f s -> t) -> Mealy s t a b
mealyVl = corepresent
{-# INLINE mealyVl #-}

-- | A non-empty list lens.
--
listing1 :: (s -> a) -> (NonEmpty s -> b -> t) -> Mealy s t a b
listing1 sa sbt = mealy sa $ sbt . F1.toNonEmpty
{-# INLINE listing1 #-}

-- | TODO: Document
--
packing1 :: IsSequence s => (Element s -> a) -> (NonNull s -> b -> t) -> Mealy (Element s) t a b
packing1 sa sbt = mealy sa $ sbt . NN.fromNonEmpty . F1.toNonEmpty
{-# INLINEABLE packing1 #-}

-- | TODO: Document
--
foldingr1 :: (s -> a) -> (s -> s -> s) -> (s -> b -> t) -> Mealy s t a b
foldingr1 sa h sbt = mealy sa $ sbt . F.foldr1 h
{-# INLINE foldingr1 #-}

-- | TODO: Document
--
foldingl1 :: (s -> a) -> (s -> s -> s) -> (s -> b -> t) -> Mealy s t a b
foldingl1 sa h sbt = mealy sa $ sbt . F.foldl1 h
{-# INLINE foldingl1 #-}

-- | TODO: Document
--
foldingrM1 :: Monad m => (s -> a) -> (s -> s -> m s) -> (m s -> b -> t) -> Mealy s t a b
foldingrM1 sa h sbt = mealy sa $ sbt . F1.foldrM1 h
{-# INLINE foldingrM1 #-}

-- | TODO: Document
--
foldinglM1 :: Monad m => (s -> a) -> (s -> s -> m s) -> (m s -> b -> t) -> Mealy s t a b
foldinglM1 sa h sbt = mealy sa $ sbt . F1.foldlM1 h
{-# INLINE foldinglM1 #-}

-- | TODO: Document
--
traversing1_ :: Apply f => (s -> a) -> (s -> f r) -> (f () -> b -> t) -> Mealy s t a b
traversing1_ sa h sbt = mealy sa $ sbt . F1.traverse1_ h
{-# INLINE traversing1_ #-}

-- | TODO: Document
--
foldMapping1 :: Semigroup r => (s -> a) -> (s -> r) -> (r -> b -> t) -> Mealy s t a b
foldMapping1 sa sr rbt = mealy sa $ rbt . F1.foldMap1 sr
{-# INLINE foldMapping1 #-}

---------------------------------------------------------------------
-- Optics
---------------------------------------------------------------------

-- | Retain the first out-of-focus part of a lens.
--
-- >>> sconcatsl (head1 second) Sum getSum $ ("foo",1) :| [("bar",2),("baz",3)]
-- ("foo",6)
-- >>> listl1 (head1 second . last1 first) $ ("key1",(0,"apples")) :| [("key2",(4,"oranges")),("key3",(1,"beets"))]
-- ("key1",(0 :| [4,1],"beets"))
--
head1 :: Lens s t a b -> Mealy s t a b
head1 o = withLens o $ \sa sbt -> listing1 sa $ sbt . NE.head

-- | Retain the last out-of-focus part of a lens.
--
-- >>> sconcatsl (last1 second) Sum getSum $ ("one",1) :| [("two",2),("three",3)]
-- ("three",6)
-- 
last1 :: Lens s t a b -> Mealy s t a b
last1 o = withLens o $ \sa sbt -> listing1 sa $ sbt . NE.last

-- | Project away a structure.
--
-- >>> listl1 (projected snd . maximized second) $ ("key1",(0,"apples")) :| [("key2",(4,"oranges")),("key3",(1,"beets"))]
-- (4,"apples" :| ["oranges","beets"])
--
projected :: (s -> a) -> Moore s b a b
projected sa = moore sa (flip const)
{-# INLINE projected #-}

-- | Minimize over a lens.
--
minimized :: Ord s => Lens s t a b -> Mealy s t a b
minimized o = withLens o $ \sa sbt -> mealy sa $ \fs b -> sbt (F.minimum fs) b
{-# INLINE minimized #-}

-- | Maximize over a lens.
--
-- >>> listl1 (maximized second) $ (0,"zero") :| [(1,"one"),(2,"two")]
-- (2,"zero" :| ["one","two"])
-- >>> buildsl1 (maximized second) (++) id id $ (0,"zero") :| [(1,"one"),(2,"two")] 
-- (2,"zeroonetwo")
-- >>> listl1 (maximized second . minimized first) $ ("key1",(0,"apples")) :| [("key2",(4,"oranges")),("key3",(1,"beets"))]
-- ("key3",(0 :| [4,1],"apples"))
--
maximized :: Ord s => Lens s t a b -> Mealy s t a b
maximized o = withLens o $ \sa sbt -> mealy sa $ \fs b -> sbt (F.maximum fs) b
{-# INLINE maximized #-}

-- | Minimize over a 'Lens' using a comparator.
--
minimizedBy :: (s -> s -> Ordering) -> Lens s t a b -> Mealy s t a b
minimizedBy cmp o = withLens o $ \sa sbt -> mealy sa $ \fs b -> sbt (F.minimumBy cmp fs) b 
{-# INLINE minimizedBy #-}

-- | Maximize over a 'Lens' using a comparator.
--
maximizedBy :: (s -> s -> Ordering) -> Lens s t a b -> Mealy s t a b
maximizedBy cmp o = withLens o $ \sa sbt -> mealy sa $ \fs b -> sbt (F.maximumBy cmp fs) b 
{-# INLINE maximizedBy #-}

-- | Minimize over a 'Lens' using a default.
--
minimizedDef :: Ord s => s -> Lens s t a b -> Moore s t a b
minimizedDef s o = withLens o $ \sa sbt -> moore sa $ \fs b -> flip sbt b $ maybe s id $ minimumMay fs
{-# INLINE minimizedDef #-}

-- | Maximize over a 'Lens' using a default.
--
-- >>> [(1,"one"),(2,"two")] & maximizedDef (0,[]) second //~ head
-- (2,"one")
-- >>> [(1,"one"),(2,"two")] & swapped . maximizedDef ([],0) first //~ head
-- (2,"one")
-- >>> listl (maximizedDef (0,[]) second) [(1,"one"),(2,"two")]
-- (2,["one","two"])
-- >>> listl (maximizedDef (0,[]) second . cotraversed1) [(1,"one"),(2,"two")]
-- (2,["ot","nw","eo"])
-- >>> buildl (maximizedDef (0,[]) second . cotraversed1) L.revList [(1,"one"),(2,"two")]
-- (2,["to","wn","oe"])
--
maximizedDef :: Ord s => s -> Lens s t a b -> Moore s t a b
maximizedDef s o = withLens o $ \sa sbt -> moore sa $ \fs b -> flip sbt b $ maybe s id $ maximumMay fs
{-# INLINE maximizedDef #-}

-- | Minimize over a 'Lens' using a comparator and a default.
--
minimizedByDef :: (s -> s -> Ordering) -> s -> Lens s t a b -> Moore s t a b
minimizedByDef cmp s o = withLens o $ \sa sbt -> moore sa $ \fs b -> flip sbt b $ maybe s id $ minimumByMay cmp fs
{-# INLINE minimizedByDef #-}

-- | Maximize over a 'Lens' using a comparator and a default.
--
maximizedByDef :: (s -> s -> Ordering) -> s -> Lens s t a b -> Moore s t a b
maximizedByDef cmp s o = withLens o $ \sa sbt -> moore sa $ \fs b -> flip sbt b $ maybe s id $ maximumByMay cmp fs 
{-# INLINE maximizedByDef #-}

-- | Search over the a 'Lens' using a predicate and a default.
--
-- >>> mconcatl (foundDef (const . even . fst) (0,mempty) second) $ (fmap . fmap) Sum [(1,1),(3,2),(4,3),(6,4)]
-- (4,Sum {getSum = 10})
-- >>> ("key1",(0,"apples")) :| [("key2",(4,"oranges")),("key3",(1,"beets"))] & (minimized second . foundDef (\s b -> snd s == b) (0,mempty) second) /~ "oranges"
-- ("key1",(4,"oranges"))
--
foundDef :: (s -> b -> Bool) -> s -> Lens s t a b -> Moore s t a b 
foundDef p s o = withLens o $ \sa sbt -> moore sa $ \fs b -> flip sbt b $ maybe s id $ F.find (flip p b) fs
{-# INLINE foundDef #-}

---------------------------------------------------------------------
-- Sequential optics
---------------------------------------------------------------------

packed :: IsSequence s => Lens s t a b -> Moore (Element s) t a b
packed o = withLens o $ \sa sbt -> packing (sa . MT.opoint) sbt

-- | TODO: Document
--
packed' :: LazySequence l s => Lens l t a b -> Moore s t a b
packed' o = withLens o $ \la lbt -> chunking (la . MS.fromStrict) lbt
{-# INLINE packed' #-}

-- | TODO: Document
--
-- >>> "foobar" & taken id /~ 3 :: String
-- "foo"
-- >>> listl (taken $ const 3) "foobar" :: String
-- "foo"
--
taken :: IsSequence s => (b -> Index s) -> Moore (Element s) s (Element s) b
taken f = packing id $ \s b -> MS.take (f b) s

-- | TODO: Document
--
-- >>> CL.unpack $ listl (taken' $ const 9) $ fmap C.pack ["foo","bar","baz","bip"]
-- "foobarbaz"
-- >>> CL.unpack $ fmap C.pack ["foo","bar","baz","bip"] & taken' fromIntegral /~ 9
-- "foobarbaz"
-- >>> CL.unpack $ fmap C.pack ["foo","bar","baz","bip"] & taken' fromIntegral //~ (3 *) . head 
-- "foobarbaz"
-- >>> fmap CL.unpack $ (fmap.fmap) C.pack [(0,"zero"),(1,"one"),(2,"two")] & maximizedDef (0,mempty) second . taken' fromIntegral //~ maximum
-- (2,"zero")
--
taken' :: LazySequence l s => (b -> Index l) -> Moore s l (Index s) b
taken' f = chunking MS.lengthIndex $ \s b -> MS.take (f b) s
{-# INLINE taken' #-}

-- | TODO: Document
--
padded :: IsSequence s => Element s -> Moore s [s] (Index s) (Index s)
padded w = listing MS.lengthIndex $ \s b -> fmap (\x -> MS.take b (x <> MS.replicate b w)) s
{-# INLINE padded #-}

-- | TODO: Document
--
-- >>> ["foo","barbaz","bippy"] & padded ' ' /~ 4
-- ["foo ","barb","bipp"]
-- >>> ["foo","barbaz","bippy"] & padded ' ' //~ maximum
-- ["foo   ","barbaz","bippy "]
--
padded' :: LazySequence l s => Element s -> Moore s l (Index s) (Index s)
padded' w = moore MS.lengthIndex $ \bs n -> MS.fromChunks $
  fmap (\s -> MS.take n $ s <> MS.replicate n w) $ F.toList bs
{-# INLINE padded' #-}

-- | TODO: Document
--
-- >>> listl (takenWhile id $ const . isAlpha) "foo2bar" :: String
-- "foo"
-- >>> [(1,"one"),(0,"zero"),(2,"two")] & minimizedDef (0,[]) second . takenWhile id (/=) /~ "two" :: (Int,[String])
-- (0,["one","zero"])
-- >>> [(1,"one"),(0,"zero"),(2,"two")] & maximizedDef (0,[]) second . takenWhile id (/=) //~ maximum :: (Int,[String])
-- (2,["one"])
--
takenWhile :: IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> Moore (Element s) s a b
takenWhile sa sbt = packing sa $ \s b -> MS.takeWhile (flip sbt b) s
{-# INLINE takenWhile #-}

-- | TODO: Document
--
-- >>> CL.unpack $ listl (takenWhile' id $ const . isAlpha . chr . fromIntegral) $ fmap C.pack ["foo","bar","2baz"]
-- "foobar"
--
takenWhile' :: LazySequence l s => (s -> a) -> (Element l -> b -> Bool) -> Moore s l a b
takenWhile' sa sbt = chunking sa $ \s b -> MS.takeWhile (flip sbt b) s
{-# INLINE takenWhile' #-}

-- | TODO: Document
--
droppedWhile :: IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> Moore (Element s) s a b
droppedWhile sa sbt = packing sa $ \s b -> MS.dropWhile (flip sbt b) s
{-# INLINE droppedWhile #-}

-- | TODO: Document
--
droppedWhile' :: LazySequence l s => (s -> a) -> (Element l -> b -> Bool) -> Moore s l a b
droppedWhile' sa sbt = chunking sa $ \s b -> MS.dropWhile (flip sbt b) s
{-# INLINE droppedWhile' #-}

-- | Filter a sequence of elements using a Moore machine. 
--
-- >>> "foobar" & filteredBy id (==) /~ 'b' :: String
-- "b"
-- >>> "foobar" & filteredBy id (\c i -> ord c /= i) /~ 111 :: String
-- "fbar"
-- >>> "fizbuz" & filteredBy ord (\c i -> ord c /= i) //~ maximum :: String
-- "fibu"
-- >>> ["bob","oob","baz"] & filteredBy head (==) //~ reverse :: [String]
-- ["bob"]
-- >>> ["bob","bob","baz"] & filteredBy head (==) //~ reverse :: [String]
-- []
--
-- Take all strings @s@ that pass the following test:
--
-- * @s@ must not include a /z/
--
-- * @s@ must be equal to the concatenation of the first characters in each string in the remaining list
--
-- >>> ["z","obb","bob","baz"] & (filteredBy head (==) . filteredBy id (/=)) /~ 'z' :: [String]
-- ["obb"]
--
filteredBy :: IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> Moore (Element s) s a b
filteredBy sa sbt = packing sa $ \s b -> MS.filter (flip sbt b) s
{-# INLINE filteredBy #-}

-- | Filter a chunked sequence of elements using a Moore machine. 
--
-- >>> CL.unpack $ fmap C.pack ["foo","bar"] & filteredBy' (ord . C.head) (/=) /~ 111 
-- "fbar"
-- >>> CL.unpack $ fmap C.pack ["f","i","z","b","u","z"] & filteredBy' (ord . C.head) (\e b -> fromIntegral e /= b) //~ maximum
-- "fibu"
-- >>> CL.unpack $ fmap C.pack ["fizbuz"] & filteredBy' (ord . C.head) (\e b -> fromIntegral e /= b) //~ maximum 
-- "izbuz"
--
filteredBy' :: LazySequence l s => (s -> a) -> (Element l -> b -> Bool) -> Moore s l a b
filteredBy' sa sbt = chunking sa $ \s b -> MS.filter (flip sbt b) s
{-# INLINE filteredBy' #-}

-- | TODO: Document
--
filteredBy1 :: IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> Mealy (Element s) s a b
filteredBy1 sa sbt = packing1 sa $ \s b -> NN.nfilter (flip sbt b) s
{-# INLINE filteredBy1 #-}

-- | TODO: Document
--
broken :: IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> Moore (Element s) (s, s) a b
broken sa sbt = packing sa $ \s b -> MS.break (flip sbt b) s
{-# INLINE broken #-}

-- | TODO: Document
--
spanned :: IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> Moore (Element s) (s, s) a b
spanned sa sbt = packing sa $ \s b -> MS.span (flip sbt b) s
{-# INLINE spanned #-}

-- | TODO: Document
--
-- >>> listl (partitioned id $ const . odd) [1..10] :: ([Int],[Int])
-- ([1,3,5,7,9],[2,4,6,8,10])
-- >>> [1..10] & partitioned id (>=) //~ (!! 5) :: ([Int],[Int])
-- ([6,7,8,9,10],[1,2,3,4,5])
-- >>> [1..10] & partitioned id (<) /~ 6 :: ([Int],[Int])
-- ([1,2,3,4,5],[6,7,8,9,10])
-- >>> [1..10] & partitioned id (==) /~ 6 :: (B.ByteString, B.ByteString)
-- ("\ACK","\SOH\STX\ETX\EOT\ENQ\a\b\t\n")
--
partitioned :: IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> Moore (Element s) (s, s) a b
partitioned sa sbt = packing sa $ \s b -> MS.partition (flip sbt b) s
{-# INLINE partitioned #-}

-- | TODO: Document
--
partitioned' :: LazySequence l s => (s -> a) -> (Element l -> b -> Bool) -> Moore s (l, l) a b
partitioned' sa sbt = chunking sa $ \s b -> MS.partition (flip sbt b) s
{-# INLINE partitioned' #-}

-- | TODO: Document
--
-- >>> "Mississippi" & groupedAllOn id (==) /~ 'i' :: [String]
-- ["Msssspp","iiii"]
-- >>> listl (minimizedDef (' ',0) first . groupedAllOn id (const . (== 'i'))) [('H',1),('a',2),('w',3),('a',4),('i',5),('i',6)] :: ([String],Int)
-- (["Hawa","ii"],1)
--
groupedAllOn :: IsSequence s => Eq r => (Element s -> a) -> (Element s -> b -> r) -> Moore (Element s) [s] a b
groupedAllOn sa sbt = packing sa $ \s b -> MS.groupAllOn (flip sbt b) s
{-# INLINE groupedAllOn #-}

-- | TODO: Document
--
splitWhen :: IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> Moore (Element s) [s] a b 
splitWhen sa sbt = packing sa $ \s b -> MS.splitWhen (flip sbt b) s 
{-# INLINE splitWhen #-}

-- | TODO: Document
--
splitFirst :: IsSequence s => (Element s -> a) -> ((Element s, s) -> b -> t) -> Mealy (Element s) t a b 
splitFirst sa sbt = packing1 sa $ sbt . NN.splitFirst
{-# INLINE splitFirst #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | TODO: Document
--
buildl :: Foldable f => AFoldl s t a b -> L.Fold a b -> f s -> t
buildl o f s = flip L.foldl s . o $ f
{-# INLINE buildl #-}

-- | TODO: Document
--
-- >>> buildsl unpacked (++) [] id ["foo","bar","baz"]
-- "foobarbaz"
-- 
-- A version of the /build/ function from < http://hackage.haskell.org/package/base-4.12.0.0/docs/src/GHC.Base.html#build base >.
--
-- See also < https://www.microsoft.com/en-us/research/wp-content/uploads/2016/07/deforestation-short-cut.pdf A Short Cut to Deforestation.>
--
buildsl :: Foldable f => AFoldl s t a b -> (x -> a -> x) -> x -> (x -> b) -> f s -> t
buildsl o h z k = buildl o $ L.Fold h z k
{-# INLINE buildsl #-}

-- | TODO: Document
--
obuildl :: MonoFoldable s => AFoldl (Element s) t a b -> L.Fold a b -> s -> t 
obuildl o f = (`L.withFoldl` MT.ofoldlUnwrap) . o $ f
{-# INLINE obuildl #-}

-- | TODO: Document
--
obuildsl :: MonoFoldable s => AFoldl (Element s) t a b -> (x -> a -> x) -> x -> (x -> b) -> s -> t 
obuildsl o h z k = obuildl o $ L.Fold h z k
{-# INLINE obuildsl #-}

-- | TODO: Document
--
buildl1 :: Foldable1 f => AFoldl1 s t a b -> L1.Foldl1 a b -> f s -> t
buildl1 o f s = flip L1.foldl1 s . o $ f
{-# INLINE buildl1 #-}

-- | TODO: Document
--
buildsl1 :: Foldable1 f => AFoldl1 s t a b -> (x -> a -> x) -> (a -> x) -> (x -> b) -> f s -> t
buildsl1 o h z k = buildl1 o $ L1.Foldl1 h z k
{-# INLINE buildsl1 #-}

-- | TODO: Document
--
obuildl1 :: IsSequence s => AFoldl1 (Element s) t a b -> L1.Foldl1 a b -> NonNull s -> t 
obuildl1 o f = (`L1.withFoldl1` ofoldl1Unwrap) . o $ f
{-# INLINE obuildl1 #-}

-- | TODO: Document
--
obuildsl1 :: IsSequence s => AFoldl1 (Element s) t a b -> (x -> a -> x) -> (a -> x) -> (x -> b) -> NonNull s -> t 
obuildsl1 o h z k = obuildl1 o $ L1.Foldl1 h z k
{-# INLINE obuildsl1 #-}

-- | TODO: Document
--
-- @
-- 'listl' o = 'buildl' o 'Control.Foldl.list'
-- 'listl' id = 'Control.Foldl.fold' 'Control.Foldl.list' = 'Data.Foldable.toList'
-- @
--
-- >>> listl closed [("foo: "++) . show, ("bar: "++) . show] 42
-- ["foo: 42","bar: 42"]
--
listl :: Foldable f => AFoldl s t a [a] -> f s -> t
listl o = buildl o L.list
{-# INLINE listl #-}

-- | TODO: Document
--
listl1 :: Foldable1 f => AFoldl1 s t a (NonEmpty a) -> f s -> t
listl1 o s = flip L1.foldl1 s . o $ L1.list1
{-# INLINE listl1 #-}

-- | TODO: Document
--
-- >>> mconcatl cotraversed1 [["foo","bar"],["baz","bip"]]
-- ["foobaz","barbip"]
--
mconcatl :: Foldable f => Monoid m => AFoldl s t m m -> f s -> t
mconcatl o s = flip L.foldl s . o $ L.mconcat
{-# INLINE mconcatl #-}

-- | TODO: Document
--
sconcatl :: Foldable1 f => Semigroup m => AFoldl1 s t m m -> f s -> t
sconcatl o s = flip L1.foldl1 s . o $ L1.sconcat
{-# INLINE sconcatl #-}

-- | TODO: Document
--
-- >>> mconcatsl cotraversed1 Sum getSum [[1,2,3],[4,5,6,7]]
-- [5,7,9]
--
mconcatsl :: Foldable f => Monoid m => AFoldl s t a b -> (a -> m) -> (m -> b) -> f s -> t
mconcatsl o f g s = flip L.foldl s . o $ L.foldMap f g
{-# INLINE mconcatsl #-}

-- | TODO: Document
--
sconcatsl :: Foldable1 f => Semigroup m => AFoldl1 s t a b -> (a -> m) -> (m -> b) -> f s -> t
sconcatsl o f g s = flip L1.foldl1 s . o $ L1.foldMap1 f g
{-# INLINE sconcatsl #-}

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

ofoldl1Unwrap :: IsSequence s => (x -> Element s -> x) -> (Element s -> x) -> (x -> b) -> NonNull s -> b 
ofoldl1Unwrap h z k nnull = k (ofoldl' h (z initial) s) where (initial,s) = NN.splitFirst nnull

liftMay :: (a -> Bool) -> (a -> b) -> a -> Maybe b
liftMay prd f a = if prd a then Nothing else Just $ f a

minimumMay, maximumMay :: Foldable f => Ord a => f a -> Maybe a
minimumMay = liftMay F.null F.minimum
maximumMay = liftMay F.null F.maximum

minimumByMay, maximumByMay :: Foldable f => (a -> a -> Ordering) -> f a -> Maybe a
minimumByMay = liftMay F.null . F.minimumBy
maximumByMay = liftMay F.null . F.maximumBy
