{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.List (
    -- * List
    List
  , list
  , listing
  , packing
  , chunking
  , foldingr
  , foldingr'
  , foldingl
  , foldingl'
  , foldMapping
    -- * List1 
  , List1
  , list1
  , listing1
  , packing1
  , foldingl1
  , foldingr1
  , foldMapping1
    -- * Lens optics
  , head1
  , last1
  , projected
  , minimized
  , maximized
  , minimizedDef 
  , maximizedDef
  , minimizedBy
  , maximizedBy
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
  , listl
  , listsl
  , listl1
  , listsl1
  , buildl
  , buildsl
  , obuildl
  , buildlM
  , buildslM
  , buildl1
  , buildsl1
  , obuildl1
  , premaplM
  , premapslM
  , postscanl
  , postscansl
    -- * IO
  , haltl
  , haltsl
  , haltl_
  , haltsl_
  , skipl
  , skipsl
  , skipl_
  , skipsl_
) where


import Control.Exception (Exception (..))
import Control.Monad.IO.Unlift
import Data.List.NonEmpty (NonEmpty (..))
import Data.Maybe (listToMaybe)
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
import qualified Control.Exception as Ex
import qualified Data.Foldable as F
import qualified Data.Profunctor.Rep.Foldl as L
import qualified Data.Profunctor.Rep.Foldl1 as L1
import qualified Data.NonNull as NN
import qualified Data.Sequences as MS
import qualified Data.List.NonEmpty as NE
import qualified Data.MonoTraversable as MT


import Data.Profunctor.Optic.Prism
import Data.Profunctor.Optic.Fold
import Data.Maybe
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
-- >>> import qualified Data.ByteString as B
-- >>> import qualified Data.ByteString.Lazy as BL
-- >>> import qualified Data.ByteString.Char8 as C
-- >>> import qualified Data.ByteString.Lazy.Char8 as CL
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- 'List'
---------------------------------------------------------------------

-- | Obtain a 'List' lens directly.
--
-- See < https://arxiv.org/pdf/2001.07488.pdf > section 3.1.4 or the slides < http://events.cs.bham.ac.uk/syco/strings3-syco5/slides/roman.pdf here >.
-- 
-- @since 0.0.3
list :: (s -> a) -> (forall f. Foldable' f => f s -> b -> t) -> List s t a b
list sa sbt p = cotabulate $ \s -> sbt s (cosieve p . fmap sa $ s)
{-# INLINE list #-}

-- | 
--
-- @since 0.0.3
listing :: (s -> a) -> ([s] -> b -> t) -> List s t a b
listing sa sbt = list sa $ sbt . F.toList
{-# INLINE listing #-}

-- | TODO: Document
--
-- @since 0.0.3
packing :: IsSequence s => (Element s -> a) -> (s -> b -> t) -> List (Element s) t a b
packing sa sbt = list sa $ sbt . MS.pack . F.toList
{-# INLINEABLE packing #-}

-- | TODO: Document
--
-- @since 0.0.3
chunking :: LazySequence l s => (s -> a) -> (l -> b -> t) -> List s t a b
chunking sa sbt = list sa $ sbt . MS.fromChunks . F.toList
{-# INLINEABLE chunking #-}

-- | TODO: Document
--
-- @since 0.0.3
foldingr :: (s -> a) -> (s -> r -> r) -> r -> (r -> b -> t) -> List s t a b
foldingr sa h z rbt = list sa $ rbt . F.foldr h z
{-# INLINE foldingr #-}

-- | TODO: Document
--
-- @since 0.0.3
foldingr' :: (s -> a) -> (s -> r -> r) -> r -> (r -> b -> t) -> List s t a b
foldingr' sa h z rbt = list sa $ rbt . F.foldr' h z
{-# INLINE foldingr' #-}

-- | TODO: Document
--
-- @since 0.0.3
foldingl :: (s -> a) -> (r -> s -> r) -> r -> (r -> b -> t) -> List s t a b
foldingl sa h z rbt = list sa $ rbt . F.foldl h z
{-# INLINE foldingl #-}

-- | TODO: Document
--
-- @since 0.0.3
foldingl' :: (s -> a) -> (r -> s -> r) -> r -> (r -> b -> t) -> List s t a b
foldingl' sa h z rbt = list sa $ rbt . F.foldl' h z
{-# INLINE foldingl' #-}

-- | TODO: Document
--
-- @since 0.0.3
foldMapping :: Monoid r => (s -> a) -> (s -> r) -> (r -> b -> t) -> List s t a b
foldMapping sa sr rbt = list sa $ rbt . F.foldMap sr
{-# INLINE foldMapping #-}

---------------------------------------------------------------------
-- 'List1'
---------------------------------------------------------------------

-- | Obtain a 'List1' directly.
--
-- @since 0.0.3
list1 :: (s -> a) -> (forall f. Foldable1' f => f s -> b -> t) -> List1 s t a b
list1 sa sbt p = cotabulate $ \s -> sbt s (cosieve p . fmap sa $ s)
{-# INLINE list1 #-}

-- | A non-empty list lens.
--
-- @since 0.0.3
listing1 :: (s -> a) -> (NonEmpty s -> b -> t) -> List1 s t a b
listing1 sa sbt = list1 sa $ sbt . F1.toNonEmpty
{-# INLINE listing1 #-}

-- | TODO: Document
--
-- @since 0.0.3
packing1 :: IsSequence s => (Element s -> a) -> (NonNull s -> b -> t) -> List1 (Element s) t a b
packing1 sa sbt = list1 sa $ sbt . NN.fromNonEmpty . F1.toNonEmpty
{-# INLINE packing1 #-}

-- | TODO: Document
--
-- @since 0.0.3
foldingr1 :: (s -> a) -> (s -> s -> s) -> (s -> b -> t) -> List1 s t a b
foldingr1 sa h sbt = list1 sa $ sbt . F.foldr1 h
{-# INLINE foldingr1 #-}

-- | TODO: Document
--
-- @since 0.0.3
foldingl1 :: (s -> a) -> (s -> s -> s) -> (s -> b -> t) -> List1 s t a b
foldingl1 sa h sbt = list1 sa $ sbt . F.foldl1 h
{-# INLINE foldingl1 #-}

-- | TODO: Document
--
-- @since 0.0.3
foldMapping1 :: Semigroup r => (s -> a) -> (s -> r) -> (r -> b -> t) -> List1 s t a b
foldMapping1 sa sr rbt = list1 sa $ rbt . F1.foldMap1 sr
{-# INLINE foldMapping1 #-}

---------------------------------------------------------------------
-- Optics
---------------------------------------------------------------------

-- | Retain the first out-of-focus part of a lens.
--
-- >>> sconcats (head1 second) Sum getSum $ ("foo",1) :| [("bar",2),("baz",3)]
-- ("foo",6)
-- >>> listl1 (head1 second . last1 first) $ ("key1",(0,"apples")) :| [("key2",(4,"oranges")),("key3",(1,"beets"))]
-- ("key1",(0 :| [4,1],"beets"))
--
-- @since 0.0.3
head1 :: Lens s t a b -> List1 s t a b
head1 o = withLens o $ \sa sbt -> listing1 sa $ sbt . NE.head
{-# INLINE head1 #-}

-- | Retain the last out-of-focus part of a lens.
--
-- >>> sconcats (last1 second) Sum getSum $ ("one",1) :| [("two",2),("three",3)]
-- ("three",6)
-- 
-- @since 0.0.3
last1 :: Lens s t a b -> List1 s t a b
last1 o = withLens o $ \sa sbt -> listing1 sa $ sbt . NE.last
{-# INLINE last1 #-}

-- | Project away a structure.
--
-- >>> listl1 (projected snd . maximized second) $ ("key1",(0,"apples")) :| [("key2",(4,"oranges")),("key3",(1,"beets"))]
-- (4,"apples" :| ["oranges","beets"])
--
-- @since 0.0.3
projected :: (s -> a) -> List s b a b
projected sa = list sa (flip const)
{-# INLINE projected #-}

-- | Minimize over a lens.
--
-- @since 0.0.3
minimized :: Ord s => Lens s t a b -> List1 s t a b
minimized o = withLens o $ \sa sbt -> list1 sa $ \fs b -> sbt (F.minimum fs) b
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
-- @since 0.0.3
maximized :: Ord s => Lens s t a b -> List1 s t a b
maximized o = withLens o $ \sa sbt -> list1 sa $ \fs b -> sbt (F.maximum fs) b
{-# INLINE maximized #-}

-- | Minimize over a 'Lens' using a default.
--
-- @since 0.0.3
minimizedDef :: Ord s => s -> Lens s t a b -> List s t a b
minimizedDef s o = withLens o $ \sa sbt -> list sa $ \fs b -> flip sbt b $ maybe s id $ minimumMay fs
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
-- >>> buildsl (maximizedDef (0,[]) second . cotraversed1) (\x a -> a:x) [] id [(1,"one"),(2,"two")]
-- (2,["to","wn","oe"])
--
-- @since 0.0.3
maximizedDef :: Ord s => s -> Lens s t a b -> List s t a b
maximizedDef s o = withLens o $ \sa sbt -> list sa $ \fs b -> flip sbt b $ maybe s id $ maximumMay fs
{-# INLINE maximizedDef #-}

-- | Minimize over a 'Lens' using a comparator.
--
-- @since 0.0.3
minimizedBy :: (s -> s -> Ordering) -> Lens s t a b -> List1 s t a b
minimizedBy cmp o = withLens o $ \sa sbt -> list1 sa $ \fs b -> sbt (F.minimumBy cmp fs) b 
{-# INLINE minimizedBy #-}

-- | Maximize over a 'Lens' using a comparator.
--
-- @since 0.0.3
maximizedBy :: (s -> s -> Ordering) -> Lens s t a b -> List1 s t a b
maximizedBy cmp o = withLens o $ \sa sbt -> list1 sa $ \fs b -> sbt (F.maximumBy cmp fs) b 
{-# INLINE maximizedBy #-}

-- | Minimize over a 'Lens' using a comparator and a default.
--
-- @since 0.0.3
minimizedByDef :: (s -> s -> Ordering) -> s -> Lens s t a b -> List s t a b
minimizedByDef cmp s o = withLens o $ \sa sbt -> list sa $ \fs b -> flip sbt b $ maybe s id $ minimumByMay cmp fs
{-# INLINE minimizedByDef #-}

-- | Maximize over a 'Lens' using a comparator and a default.
--
-- @since 0.0.3
maximizedByDef :: (s -> s -> Ordering) -> s -> Lens s t a b -> List s t a b
maximizedByDef cmp s o = withLens o $ \sa sbt -> list sa $ \fs b -> flip sbt b $ maybe s id $ maximumByMay cmp fs 
{-# INLINE maximizedByDef #-}

-- | Search over the a 'Lens' using a predicate and a default.
--
-- >>> mconcats (foundDef (const . even . fst) (0,0) second) Sum getSum $ [(1,1),(3,2),(4,3),(6,4)] :: (Int, Int)
-- (4,10)
-- >>> ("key1",(0,"apples")) :| [("key2",(4,"oranges")),("key3",(1,"beets"))] & (minimized second . foundDef (\s b -> snd s == b) (0,mempty) second) /~ "oranges"
-- ("key1",(4,"oranges"))
--
-- @since 0.0.3
foundDef :: (s -> b -> Bool) -> s -> Lens s t a b -> List s t a b 
foundDef p s o = withLens o $ \sa sbt -> list sa $ \fs b -> flip sbt b $ maybe s id $ F.find (flip p b) fs
{-# INLINE foundDef #-}

---------------------------------------------------------------------
-- Sequential optics
---------------------------------------------------------------------

-- | TODO: Document
--
-- @since 0.0.3
packed :: IsSequence s => Lens s t a b -> List (Element s) t a b
packed o = withLens o $ \sa sbt -> packing (sa . MT.opoint) sbt

-- | TODO: Document
--
-- @since 0.0.3
packed' :: LazySequence l s => Lens l t a b -> List s t a b
packed' o = withLens o $ \la lbt -> chunking (la . MS.fromStrict) lbt
{-# INLINE packed' #-}

-- | TODO: Document
--
-- >>> "foobar" & taken id /~ 3 :: String
-- "foo"
-- >>> listl (taken $ const 3) "foobar" :: String
-- "foo"
--
-- @since 0.0.3
taken :: IsSequence s => (b -> Index s) -> List (Element s) s (Element s) b
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
-- @since 0.0.3
taken' :: LazySequence l s => (b -> Index l) -> List s l (Index s) b
taken' f = chunking MS.lengthIndex $ \s b -> MS.take (f b) s
{-# INLINE taken' #-}

-- | TODO: Document
--
-- @since 0.0.3
padded :: IsSequence s => Element s -> List s [s] (Index s) (Index s)
padded w = listing MS.lengthIndex $ \s b -> fmap (\x -> MS.take b (x <> MS.replicate b w)) s
{-# INLINE padded #-}

-- | TODO: Document
--
-- >>> ["foo","barbaz","bippy"] & padded ' ' /~ 4
-- ["foo ","barb","bipp"]
-- >>> ["foo","barbaz","bippy"] & padded ' ' //~ maximum
-- ["foo   ","barbaz","bippy "]
--
-- @since 0.0.3
padded' :: LazySequence l s => Element s -> List s l (Index s) (Index s)
padded' w = list MS.lengthIndex $ \bs n -> MS.fromChunks $
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
-- @since 0.0.3
takenWhile :: IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> List (Element s) s a b
takenWhile sa sbt = packing sa $ \s b -> MS.takeWhile (flip sbt b) s
{-# INLINE takenWhile #-}

-- | TODO: Document
--
-- >>> CL.unpack $ listl (takenWhile' id $ const . isAlpha . chr . fromIntegral) $ fmap C.pack ["foo","bar","2baz"]
-- "foobar"
--
-- @since 0.0.3
takenWhile' :: LazySequence l s => (s -> a) -> (Element l -> b -> Bool) -> List s l a b
takenWhile' sa sbt = chunking sa $ \s b -> MS.takeWhile (flip sbt b) s
{-# INLINE takenWhile' #-}

-- | TODO: Document
--
-- @since 0.0.3
droppedWhile :: IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> List (Element s) s a b
droppedWhile sa sbt = packing sa $ \s b -> MS.dropWhile (flip sbt b) s
{-# INLINE droppedWhile #-}

-- | TODO: Document
--
-- @since 0.0.3
droppedWhile' :: LazySequence l s => (s -> a) -> (Element l -> b -> Bool) -> List s l a b
droppedWhile' sa sbt = chunking sa $ \s b -> MS.dropWhile (flip sbt b) s
{-# INLINE droppedWhile' #-}

-- | Filter a sequence of elements using a List machine. 
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
-- @since 0.0.3
filteredBy :: IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> List (Element s) s a b
filteredBy sa sbt = packing sa $ \s b -> MS.filter (flip sbt b) s
{-# INLINE filteredBy #-}

-- | Filter a chunked sequence of elements using a List machine. 
--
-- >>> CL.unpack $ fmap C.pack ["foo","bar"] & filteredBy' (ord . C.head) (/=) /~ 111 
-- "fbar"
-- >>> CL.unpack $ fmap C.pack ["f","i","z","b","u","z"] & filteredBy' (ord . C.head) (\e b -> fromIntegral e /= b) //~ maximum
-- "fibu"
-- >>> CL.unpack $ fmap C.pack ["fizbuz"] & filteredBy' (ord . C.head) (\e b -> fromIntegral e /= b) //~ maximum 
-- "izbuz"
--
-- @since 0.0.3
filteredBy' :: LazySequence l s => (s -> a) -> (Element l -> b -> Bool) -> List s l a b
filteredBy' sa sbt = chunking sa $ \s b -> MS.filter (flip sbt b) s
{-# INLINE filteredBy' #-}

-- | TODO: Document
--
-- @since 0.0.3
filteredBy1 :: IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> List1 (Element s) s a b
filteredBy1 sa sbt = packing1 sa $ \s b -> NN.nfilter (flip sbt b) s
{-# INLINE filteredBy1 #-}

-- | TODO: Document
--
-- @since 0.0.3
broken :: IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> List (Element s) (s, s) a b
broken sa sbt = packing sa $ \s b -> MS.break (flip sbt b) s
{-# INLINE broken #-}

-- | TODO: Document
--
-- @since 0.0.3
spanned :: IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> List (Element s) (s, s) a b
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
-- @since 0.0.3
partitioned :: IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> List (Element s) (s, s) a b
partitioned sa sbt = packing sa $ \s b -> MS.partition (flip sbt b) s
{-# INLINE partitioned #-}

-- | TODO: Document
--
-- @since 0.0.3
partitioned' :: LazySequence l s => (s -> a) -> (Element l -> b -> Bool) -> List s (l, l) a b
partitioned' sa sbt = chunking sa $ \s b -> MS.partition (flip sbt b) s
{-# INLINE partitioned' #-}

-- | TODO: Document
--
-- >>> "Mississippi" & groupedAllOn id (==) /~ 'i' :: [String]
-- ["Msssspp","iiii"]
-- >>> listl (minimizedDef (' ',0) first . groupedAllOn id (const . (== 'i'))) [('H',1),('a',2),('w',3),('a',4),('i',5),('i',6)] :: ([String],Int)
-- (["Hawa","ii"],1)
--
-- @since 0.0.3
groupedAllOn :: IsSequence s => Eq r => (Element s -> a) -> (Element s -> b -> r) -> List (Element s) [s] a b
groupedAllOn sa sbt = packing sa $ \s b -> MS.groupAllOn (flip sbt b) s
{-# INLINE groupedAllOn #-}

-- | TODO: Document
--
-- @since 0.0.3
splitWhen :: IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> List (Element s) [s] a b 
splitWhen sa sbt = packing sa $ \s b -> MS.splitWhen (flip sbt b) s 
{-# INLINE splitWhen #-}

-- | TODO: Document
--
-- @since 0.0.3
splitFirst :: IsSequence s => (Element s -> a) -> ((Element s, s) -> b -> t) -> List1 (Element s) t a b 
splitFirst sa sbt = packing1 sa $ sbt . NN.splitFirst
{-# INLINE splitFirst #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | TODO: Document
--
-- @since 0.0.3
listl :: Foldable f => AFoldl s t a [a] -> f s -> t
listl o = listsl o . L.foldable
{-# INLINE listl #-}

-- | TODO: Document
--
-- @
-- 'listsl' o = 'buildl' o 'Control.Foldl.list'
-- 'listsl' id = 'Control.Foldl.fold' 'Control.Foldl.list' = 'Data.Foldable.toList'
-- @
--
-- >>> listsl closed [("foo: "++) . show, ("bar: "++) . show] 42
-- ["foo: 42","bar: 42"]
--
-- @since 0.0.3
listsl :: AFoldl s t a [a] -> L.Unfoldl s -> t
listsl o = L.withFoldl L.list $ buildsl o
{-# INLINE listsl #-}

-- | TODO: Document
--
-- @since 0.0.3
listl1 :: Foldable1 f => AFoldl1 s t a (NonEmpty a) -> f s -> t
listl1 o s = flip L1.foldl1 s . o $ L1.list1
{-# INLINE listl1 #-}

-- | TODO: Document
--
-- @since 0.0.3
listsl1 :: AFoldl1 s t a (NonEmpty a) -> L1.Unfoldl1 s -> t
listsl1 o = L1.withFoldl1 L1.list1 $ buildsl1 o
{-# INLINE listsl1 #-}

-- | TODO: Document
--
-- @since 0.0.3
buildl :: Foldable f => AFoldl s t a b -> (x -> a -> x) -> x -> (x -> b) -> f s -> t 
buildl o h z k = buildsl o h z k . L.foldable
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
-- Usable in conjunction with /purely/ from the /foldl/ package.
--
-- @since 0.0.3
buildsl :: AFoldl s t a b -> (x -> a -> x) -> x -> (x -> b) -> L.Unfoldl s -> t
buildsl o h z k u = flip L.build u . o $ L.Foldl h z k
{-# INLINE buildsl #-}

-- | TODO: Document
--
-- @
-- 'obuildl' o h z k = 'buildsl' o h z k . 'Data.Profunctor.Rep.Foldl.ofoldable'
-- @
--
-- Usable in conjunction with /purely/ from the /foldl/ package.
--
-- @since 0.0.3
obuildl :: MonoFoldable s => AFoldl (Element s) t a b -> (x -> a -> x) -> x -> (x -> b) -> s -> t 
obuildl o h z k = (`L.withFoldl` MT.ofoldlUnwrap) . o $ L.Foldl h z k
{-# INLINE obuildl #-}

-- | TODO: Document
--
-- @since 0.0.3
buildlM :: Foldable f => Monad m => AFoldl s t a b -> (x -> a -> x) -> x -> (x -> b) -> f s -> m t
buildlM o h z k = buildslM o h z k . L.foldableM
{-# INLINE buildlM #-}

-- | TODO: Document
--
-- @since 0.0.3
buildslM :: Monad m => AFoldl s t a b -> (x -> a -> x) -> x -> (x -> b) -> L.UnfoldlM m s -> m t
buildslM o h z k u = flip L.buildM u . L.generalize . o $ L.Foldl h z k
{-# INLINE buildslM #-}

-- | TODO: Document
--
-- @since 0.0.3
buildl1 :: Foldable1 f => AFoldl1 s t a b -> (x -> a -> x) -> (a -> x) -> (x -> b) -> f s -> t
buildl1 o h z k = buildsl1 o h z k . L1.foldable1
{-# INLINE buildl1 #-}

-- | TODO: Document
--
-- @since 0.0.3
buildsl1 :: AFoldl1 s t a b -> (x -> a -> x) -> (a -> x) -> (x -> b) -> L1.Unfoldl1 s -> t
buildsl1 o h z k u = flip L1.build1 u . o $ L1.Foldl1 h z k
{-# INLINE buildsl1 #-}

-- | TODO: Document
--
-- @
-- 'obuildl1' o h z k = 'buildsl1' o h z k . 'Data.Profunctor.Rep.Foldl1.nonNull'
-- @
--
-- @since 0.0.3
obuildl1 :: IsSequence s => AFoldl1 (Element s) t a b -> (x -> a -> x) -> (a -> x) -> (x -> b) -> NonNull s -> t 
obuildl1 o h z k = (`L1.withFoldl1` ofoldl1Unwrap) . o $ L1.Foldl1 h z k
{-# INLINE obuildl1 #-}

-- | TODO: Document
--
-- @since 0.0.3
--buildslM1 :: Monad m => AFoldl1 s t a b -> (x -> a -> m x) -> (a -> m x) -> (x -> m b) -> L.UnfoldlM m s -> m t
--buildslM1 o h z k u = flip L1.buildM1 u . L1.generalize1 . o $ L1.Foldl1 h z k
--{-# INLINE buildslM1 #-}

-- | TODO: Document
--
-- @since 0.0.3
premaplM :: Foldable f => Monad m => AFoldl s t a b -> L.Foldl a b -> (r -> m s) -> f r -> m t
premaplM o f g s = flip L.foldlM s . L.premapM g . L.generalize . o $ f
{-# INLINE premaplM #-}

-- | TODO: Document
--
-- @since 0.0.3
premapslM :: Foldable f => Monad m => AFoldl s t a b -> (x -> a -> x) -> x -> (x -> b) -> (r -> m s) -> f r -> m t
premapslM o h z k = premaplM o $ L.Foldl h z k 
{-# INLINE premapslM #-}

-- | TODO: Document
--
-- @since 0.0.3
postscanl :: Traversable f => AFoldl s t a b -> L.Foldl a b -> f s -> f t
postscanl o f s = flip L.postscan s . o $ f
{-# INLINE postscanl #-}

-- | TODO: Document
--
-- Usable in conjunction with /purely/ from the /foldl/ package.
--
-- >>> postscansl cotraversed1 (+) 0 id [[1,2],[3,4],[5,6]] 
-- [[1,2],[4,6],[9,12]]
-- >>> postscansl cotraversed1 (<>) mempty id [["foo","bar"],["baz","bip"],["bip","bop"]]
-- [["foo","bar"],["foobaz","barbip"],["foobazbip","barbipbop"]]
--
-- @since 0.0.3
postscansl :: Traversable f => AFoldl s t a b -> (x -> a -> x) -> x -> (x -> b) -> f s -> f t
postscansl o h z k = postscanl o $ L.Foldl h z k
{-# INLINE postscansl #-}

---------------------------------------------------------------------
-- IO
---------------------------------------------------------------------

-- | TODO: Document
--
-- >>> import qualified Control.Exception as Ex
-- >>> f x = if x < 10 then return x else Ex.throw Ex.Overflow
-- >>> exfold = premapM f (generalize list)
-- >>> xs = [1, 2, 500, 4] :: [Integer]
-- >>> foldlM (halt @Ex.ArithException exfold) xs
-- (Just arithmetic overflow,[1,2])
--
-- @since 0.0.3
haltl :: Exception e => Foldable f => MonadUnliftIO m => AFoldl s t a b -> L.Foldl a b -> (r -> m s) -> f r -> m (Maybe e, t)
haltl o f g s = flip L.foldlM s . L.halt . L.premapM g . L.generalize . o $ f
{-# INLINE haltl #-}

-- | TODO: Document
--
-- @since 0.0.3
haltsl :: Exception e => Foldable f => MonadUnliftIO m => AFoldl s t a b -> (x -> a -> x) -> x -> (x -> b) -> (r -> m s) -> f r -> m (Maybe e, t)
haltsl o h z k = haltl o $ L.Foldl h z k
{-# INLINE haltsl #-}

-- | TODO: Document
--
-- @since 0.0.3
haltl_ :: Foldable f => MonadUnliftIO m => AFoldl s t a b -> L.Foldl a b -> (r -> m s) -> f r -> m t
haltl_ o f g s = flip L.foldlM s . L.halt_ . L.premapM g . L.generalize . o $ f
{-# INLINE haltl_ #-}

-- | TODO: Document
--
-- @since 0.0.3
haltsl_ :: Foldable f => MonadUnliftIO m => AFoldl s t a b -> (x -> a -> x) -> x -> (x -> b) -> (r -> m s) -> f r -> m t
haltsl_ o h z k = haltl_ o $ L.Foldl h z k
{-# INLINE haltsl_ #-}

-- | TODO: Document
--
-- @since 0.0.3
skipl :: Exception e => Foldable f => MonadUnliftIO m => AFoldl s t a b -> L.Foldl a b -> (r -> m s) -> f r -> m ([e], t)
skipl o f g s = flip L.foldlM s . L.skip . L.premapM g . L.generalize . o $ f
{-# INLINE skipl #-}

-- | TODO: Document
--
-- @since 0.0.3
skipsl :: Exception e => Foldable f => MonadUnliftIO m => AFoldl s t a b -> (x -> a -> x) -> x -> (x -> b) -> (r -> m s) -> f r -> m ([e], t)
skipsl o h z k = skipl o $ L.Foldl h z k
{-# INLINE skipsl #-}

-- | TODO: Document
--
-- @since 0.0.3
skipl_ :: Foldable f => MonadUnliftIO m => AFoldl s t a b -> L.Foldl a b -> (r -> m s) -> f r -> m t
skipl_ o f g s = flip L.foldlM s . L.skip_ . L.premapM g . L.generalize . o $ f
{-# INLINE skipl_ #-}

-- | TODO: Document
--
-- @since 0.0.3
skipsl_ :: Foldable f => MonadUnliftIO m => AFoldl s t a b -> (x -> a -> x) -> x -> (x -> b) -> (r -> m s) -> f r -> m t
skipsl_ o h z k = skipl_ o $ L.Foldl h z k
{-# INLINE skipsl_ #-}

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
