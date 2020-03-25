{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Scan where
{- (
    -- * Coscan
    Coscan
  , rescans
  , lifting
  , lifting
  , reversing
  , building

  , packing
  , chunking
  , foldingr
  , foldingr'
  , foldingl
  , foldingl'

  , mconcating
    -- * Coscan1 
  , Coscan1
  , rescans1
  , lifting1
  , packing1
  , foldingl1
  , foldingr1
  , mconcating1
    -- * Lens optics
  , head1
  , last1
  , selected
  , minimized
  , maximized
  , minimizedDef 
  , maximizedDef
  , minimizedBy
  , maximizedBy
  , minimizedByDef
  , maximizedByDef
  , found
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
  , filteredOn
  , filteredOn'
  , filteredOn1
  , broken
  , spanned
  , partitioned
  , partitioned'
  , groupedAllOn
  , splitWhen
  , splitFirst
 -- , intercalated
    -- * Operators
  , builds
  , buildsl
  , builds1
  , buildsl1
  , buildl
  , lifts
  , obuildl
  , buildlM
  , liftsM
  , buildl1
  , lifts1
  , obuildl1
  , premaplM
  , premapslM
  , opremaplM
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
-}

import Control.Exception (Exception (..), SomeException (..), SomeAsyncException (..))
import Control.Foldl (Fold(..))
import Control.Monad.IO.Unlift
import Control.Monad.State.Strict
import Data.Foldable (Foldable)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Int
import Data.Char
import Data.Maybe (listToMaybe)
import Data.Monoid
import Data.Profunctor.Optic.Carrier hiding (Index)
import Data.Profunctor.Optic.Combinator
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Traversal
import Data.Profunctor.Optic.Type
import Data.Profunctor.Rep.Fold -- (L, Fold(..), FoldM(..), Free(..), FreeM(..))
import Data.Profunctor.Rep.Fold1 hiding (scan1) -- (Scan(..), Fold1(..), Free1(..), FreeM1(..))
import Data.Semigroup
import Data.Semigroup.Foldable as F1
import Data.Word
import qualified Control.Exception as Ex
import qualified Control.Foldl as FL
import qualified Control.Scanl as SL
import qualified Control.Foldl.ByteString as FLB
import qualified Control.Monad as M
import qualified Data.Foldable as F
import qualified Data.List.NonEmpty as NE
import qualified Data.Profunctor.Rep.Fold as L
import qualified Data.Profunctor.Rep.Fold1 as L1
import qualified Data.ByteString       as BS
import qualified Data.ByteString.Builder as B
import qualified Data.ByteString.Char8 as CS
import qualified Data.ByteString.Lazy       as BL
import qualified Data.ByteString.Lazy.Char8 as CL

import qualified Data.Bifunctor as B
import Data.Profunctor.Optic.Iso as I
import Data.Profunctor.Optic.Prism
import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.View
import Data.Function (on)
import qualified Prelude as P


--F.foldr ((.|.)) (zeroBits) 
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
-- >>> import Data.Coscan.NonEmpty (NonEmpty(..))
-- >>> import Data.Function ((&))
-- >>> import Data.Foldable
-- >>> import Data.Ord
-- >>> import Data.Coscan ((!!))
-- >>> import Data.ByteString.Internal (w2c, c2w)
-- >>> import qualified Data.ByteString as B
-- >>> import qualified Data.ByteString.Lazy as BL
-- >>> import qualified Data.ByteString.Char8 as C
-- >>> import qualified Data.ByteString.Lazy.Char8 as CL
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- 'Coscan'
---------------------------------------------------------------------

-- | Obtain a 'Coscan' directly.
--
-- See < https://arxiv.org/pdf/2001.07488.pdf > section 3.1.4 or the slides < http://events.cs.bham.ac.uk/syco/strings3-syco5/slides/roman.pdf here >.
-- 
-- @since 0.0.3
rescan :: (s -> a) -> (forall f. Traversable f => f s -> b -> t) -> Coscan s t a b
rescan sa ret p = cotabulate $ \fs -> ret fs (cosieve p . fmap sa $ fs)
{-# INLINE rescan #-}

-- | Obtain a non-empty 'Coscan' from a non-empty left lift.
--
-- @since 0.0.3
relisting :: (s -> a) -> ([s] -> b -> t) -> Coscan s t a b
relisting sa ret = rescan sa $ ret . F.toList

-- | Obtain a 'Coscan' from a right fold.
--
-- @since 0.0.3
relifting :: (s -> a) -> (Free s -> b -> t) -> Coscan s t a b
relifting sa ret = rescan sa $ ret . L.liftr
{-# INLINE relifting #-}

-- | Obtain a reversed 'Coscan' from a (strict) left fold.
--
-- @since 0.0.3
reversing :: (s -> a) -> (Free s -> b -> t) -> Coscan s t a b
reversing sa ret = rescan sa $ ret . L.liftl
{-# INLINE reversing #-}

---------------------------------------------------------------------
-- 'Coscan1'
---------------------------------------------------------------------

-- | Obtain a 'Coscan1' directly.
--
-- Any 'Coscan' may be composed with a 'Coscan1' to obtain another 'Coscan1'.
--
-- @since 0.0.3
rescan1 :: (s -> a) -> (forall f. Traversable1 f => f s -> b -> t) -> Coscan1 s t a b
rescan1 sa ret p = cotabulate $ \s -> ret s (cosieve p . fmap sa $ s)
{-# INLINE rescan1 #-}

-- | Obtain a non-empty 'Coscan' from a non-empty left lift.
--
-- @since 0.0.3
relifting1 :: (s -> a) -> (Free1 s -> b -> t) -> Coscan1 s t a b
relifting1 sa ret = rescan1 sa $ ret . L1.liftr

-- | Obtain a reversed non-empty 'Coscan' from a non-empty left lift.
--
-- @since 0.0.3
reversing1 :: (s -> a) -> (Free1 s -> b -> t) -> Coscan1 s t a b
reversing1 sa ret = rescan1 sa $ ret . L1.liftl

---------------------------------------------------------------------
-- Optics
---------------------------------------------------------------------

-- | The identity for 'Coscan' optics.
--
coscanned :: Coscan a b a b
coscanned = selected id

-- | TODO: Document
--
reliftedA :: Applicative f => Coscan (f a) (f b) a b
reliftedA p = cotabulate $ fmap (cosieve p) . sequenceA
{-# INLINE reliftedA #-}

-- | TODO: Document
--
reliftedF :: Apply f => Coscan1 (f a) (f b) a b
reliftedF p = cotabulate $ fmap (cosieve p) . sequence1
{-# INLINE reliftedF #-}

-- | Variant of 'reliftedA' specialized to zip-lists.
--
-- Useful because lists are not 'Control.Coapplicative.Coapplicative'.
--
rezipped :: Coscan [a] [b] a b
rezipped = zipListed . reliftedA
{-# INLINE rezipped #-}

-- Prepend an accumulated value to the tape head.
-- >>> review (consed $ L.headDef 0) 3
-- [3]
-- >>> run (consed CL.head) B.char8 ["foo","bar","baz"]
-- ["fbb","foo","bar","baz"]
consed :: (Free s -> s) -> Coscan' (Free s) s 
consed f = relifting f $ \fs s -> s `L.cons` F.fold fs

-- Append an accumulated value to the tape tail.
--
-- >>> builds (snoced CL.head) B.char8 ["foo","bar","baz"]
-- ["foo","bar","baz","fbb"]
snoced :: (Free s -> s) -> Coscan' (Free s) s 
snoced f = relifting f $ \fs s -> F.fold fs `L.snoc` s

-- >>> L.liftl [1..4] & appended //~ L.reverse
-- [4,3,2,1,1,2,3,4]
appended :: Coscan a (Free a) a (Free a)
appended = relifting id $ L.append

-- | Select a substruct to operate on.
--
-- Akin to a /SELECT/ statement in a SQL dialect, this will project 
-- away the remainder of the struct:
--
-- >>> P.zip [1..] "foobar" & selected snd . ne /~ 'o'
-- "fbar"
-- >>> ("key1",(0,"apples")) :| [("key2",(4,"oranges")),("key3",(1,"beets"))] & rescans1 (selected snd . maximized second) //~ cosieve FL.rescan
-- (4,"apples" :| ["oranges","beets"])
--
-- @since 0.0.3
selected :: (s -> a) -> Coscan s b a b
selected sa = rescan sa (flip const)
{-# INLINE selected #-}

-- | Filter a sequence of elements using a 'Coscan'. 
--
-- >>> "foobar" & filtered id (==) /~ 'b'
-- "b"
-- >>> L.chars "foobar" & filtered id (/=) /~ 'o'
-- "fbar"
-- >>> L.chars "fizbuz" & filtered id (/=) //~ F.maximum
-- "fibu"
--
-- Filter on strings equal to the reverse of the first characters in each string:
--
-- >>> l = fmap L.chars $ liftl ["boo","oob","ozo"]
-- >>> l & filtered (L.headDef '_') (==) //~ L.reverse
-- ["oob"]
--
-- A example composing rescans. Take the head strings of all lists that pass the following test:
--
-- * each string element must not include a /z/
--
-- * the first string element must be a concatenation of the first characters in each string in the remaining rescan
--
-- The resulting filter should therefore be sensitive to ordering:
--
-- >>> [l,L.reverse l] <&> filtered (L.headDef '_') (==) . ne /~ 'z'
-- [["boo"],["oob"]]
--
-- @since 0.0.3
filtered :: (s -> a) -> (s -> b -> Bool) -> Coscan s (Free s) a b
filtered sa ret = relifting sa $ \s b -> L.filter (flip ret b) s
{-# INLINE filtered #-}

-- | TODO: Document
--
-- @since 0.0.3
mconcated :: Monoid r => (s -> a) -> (s -> r) -> (r -> b -> t) -> Coscan s t a b
mconcated sa sr rbt = rescan sa $ rbt . F.foldMap sr
{-# INLINE mconcated #-}

-- | TODO: Document
--
-- @since 0.0.3
sconcated :: Semigroup r => (s -> a) -> (s -> r) -> (r -> b -> t) -> Coscan1 s t a b
sconcated sa sr rbt = rescan1 sa $ rbt . F1.foldMap1 sr
{-# INLINE sconcated #-}

-- | TODO: Document
--
-- >>> ["foo","barbaz","bippy"] & padded ' ' /~ 4
-- "foo barbbipp"
-- >>> ["foo","barbaz","bippy"] & padded ' ' //~ F.maximum
-- "foo   barbazbippy "
--
-- @since 0.0.3
padded :: a -> Coscan' (Free a) Int
padded a = rescan F.length $ \as n -> F.foldl' (flip (<>)) mempty $ fmap (pad n a) as
  where pad i x u = L.take i $ u `L.append` L.replicate i x

-- | TODO: Document
--
-- >>> L.liftr "foobar" & taken id id /~ 3
-- "foo"
-- >>> L.liftr "foobar" & taken id ((\i -> i - 113) . fromIntegral . c2w) //~ L.headDef '_' -- 'r' is ascii code pt 114
-- "f"
--
-- @since 0.0.3
taken :: (s -> a) -> (b -> Int) -> Coscan s (Free s) a b 
taken sa f = relifting sa $ \s b -> L.take (f b) s

-- | TODO: Document
--
-- >>> rescan (takenWhile id $ const . isAlpha . w2c) "foo2bar"
-- "foo"
-- >>> P.zip [0..] "foobar" & maximizedDef (0,' ') second . takenWhile ord B.char8 (/=) /~ c2w 'b' 
-- (5,"foo")
--
-- @since 0.0.3
takenWhile :: (s -> a) -> (s -> b -> Bool) -> Coscan s (Free s) a b
takenWhile sa ret = relifting sa $ \s b -> L.takeWhile (flip ret b) s
{-# INLINE takenWhile #-}

-- | TODO: Document
--
-- >>> "foobar" & partitioned id (/=) /~ 'o'
-- ("fbar","oo")
-- >>> L.liftl [0..9] & partitioned id (\a b -> abs (a - b) < 1.0) //~ cosieve FL.mean
-- ([4.0,5.0],[0.0,1.0,2.0,3.0,6.0,7.0,8.0,9.0])
--
-- @since 0.0.3
partitioned :: (s -> a) -> (s -> b -> Bool) -> Coscan s (Free s, Free s) a b
partitioned sa ret = relifting sa $ \s b -> L.partition (flip ret b) s
{-# INLINE partitioned #-}

---------------------------------------------------------------------
-- Lens-derived optics
---------------------------------------------------------------------

-- | Retain the first out-of-focus part of a lens.
--
-- >>> sconcats (head1 second) Sum getSum $ ("foo",1) :| [("bar",2),("baz",3)]
-- ("foo",6)
-- >>> rescan1 (head1 second . last1 first) $ ("key1",(0,"apples")) :| [("key2",(4,"oranges")),("key3",(1,"beets"))]
-- ("key1",(0 :| [4,1],"beets"))
--
-- @since 0.0.3
head1 :: Lens s t a b -> Coscan1 s t a b
head1 o = withLens o $ \sa ret -> relifting1 sa $ ret . L1.head
{-# INLINE head1 #-}

-- | Retain the last out-of-focus part of a lens.
--
-- >>> sconcats (last1 second) Sum getSum $ ("one",1) :| [("two",2),("three",3)]
-- ("three",6)
-- 
-- @since 0.0.3
last1 :: Lens s t a b -> Coscan1 s t a b
last1 o = withLens o $ \sa ret -> relifting1 sa $ ret . L1.last
{-# INLINE last1 #-}

-- | Search over the a 'Lens' using a predicate and a default.
--
-- Sum over the second field, search through the first:
-- >>> foldMaps (foundDef (0,0) (even . fst) second) Sum getSum $ [(1,1),(3,2),(4,3),(6,4)]
-- (4,10)
--
-- @since 0.0.3
foundDef :: s -> (s -> Bool) -> Lens s t a b -> Coscan s t a b 
foundDef s pred o = withLens o $ \sa ret -> rescan sa $ \fs b -> flip ret b $ maybe s id $ F.find pred fs
{-# INLINE foundDef #-}

-- | Minimize over a lens.
--
-- @since 0.0.3
minimized :: Ord s => Lens s t a b -> Coscan1 s t a b
minimized = minimizedBy compare
{-# INLINE minimized #-}

-- | Maximize over a lens.
--
-- >>> rescans1 (maximized second) $ (0,"zero") :| [(1,"one"),(2,"two")]
-- (2,"zero" :| ["one","two"])
-- >>> sconcats (maximized second) id id $ (0,"zero") :| [(1,"one"),(2,"two")] 
-- (2,"zeroonetwo")
-- >>> rescans1 (maximized second . minimized first) $ ("key1",(0,"apples")) :| [("key2",(4,"oranges")),("key3",(1,"beets"))]
-- ("key3",(0 :| [4,1],"apples"))
--
-- @since 0.0.3
maximized :: Ord s => Lens s t a b -> Coscan1 s t a b
maximized = maximizedBy compare
{-# INLINE maximized #-}

-- | Minimize over a 'Lens' using a default.
--
-- >>> runsFold (maximizedDef ('_',0) second) FL.mean $ P.zip "foobarbazbip" (P.enumFromThenTo 0 0.1 1)
-- ('z',0.49999999999999994)
--
-- @since 0.0.3
minimizedDef :: Ord s => s -> Lens s t a b -> Coscan s t a b
minimizedDef = minimizedByDef compare
{-# INLINE minimizedDef #-}

-- | Maximize over a 'Lens' using a default.
--
-- >>> [(1,"one"),(2,"two")] & maximizedDef (0,[]) second //~ head
-- (2,"one")
-- >>> [(1,"one"),(2,"two")] & swapped . maximizedDef ([],0) first //~ head
-- (2,"one")
-- >>> rescans (maximizedDef (0,[]) second) [(1,"one"),(2,"two")]
-- (2,["one","two"])
-- >>> rescans (maximizedDef (0,[]) second . cotraversed1) [(1,"one"),(2,"two")]
-- (2,["ot","nw","eo"])
-- >>> lifts (maximizedDef (0,[]) second . cotraversed1) (\x a -> a:x) [] id [(1,"one"),(2,"two")]
-- (2,["to","wn","oe"])
--
-- @since 0.0.3
maximizedDef :: Ord s => s -> Lens s t a b -> Coscan s t a b
maximizedDef = maximizedByDef compare
{-# INLINE maximizedDef #-}

-- | Minimize over a 'Lens' using a comparator.
--
-- @since 0.0.3
minimizedBy :: (s -> s -> Ordering) -> Lens s t a b -> Coscan1 s t a b
minimizedBy cmp o = withLens o $ \sa ret -> rescan1 sa $ \fs b -> ret (F.minimumBy cmp fs) b 
{-# INLINE minimizedBy #-}

-- | Maximize over a 'Lens' using a comparator.
--
-- @since 0.0.3
maximizedBy :: (s -> s -> Ordering) -> Lens s t a b -> Coscan1 s t a b
maximizedBy cmp o = withLens o $ \sa ret -> rescan1 sa $ \fs b -> ret (F.maximumBy cmp fs) b 
{-# INLINE maximizedBy #-}

-- | Minimize over a 'Lens' using a comparator and a default.
--
-- @since 0.0.3
minimizedByDef :: (s -> s -> Ordering) -> s -> Lens s t a b -> Coscan s t a b
minimizedByDef cmp s o = withLens o $ \sa ret -> rescan sa $ \fs b -> flip ret b $ maybe s id $ minByMay cmp fs
{-# INLINE minimizedByDef #-}

-- | Maximize over a 'Lens' using a comparator and a default.
--
-- @since 0.0.3
maximizedByDef :: (s -> s -> Ordering) -> s -> Lens s t a b -> Coscan s t a b
maximizedByDef cmp s o = withLens o $ \sa ret -> rescan sa $ \fs b -> flip ret b $ maybe s id $ maxByMay cmp fs 
{-# INLINE maximizedByDef #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- \o h z k -> refoldsr o h z k . L.liftr :: Foldable f => ACoscan s t a b -> (a -> r -> r) -> r -> (r -> b) -> f s -> t
refoldsr :: ACoscan s t a b -> (a -> r -> r) -> r -> (r -> b) -> Free s -> t
refoldsr o h z k = costars o $ \f -> k $ L.retractr f h z

refoldsl :: ACoscan s t a b -> (r -> a -> r) -> r -> (r -> b) -> Free s -> t
refoldsl o h z k = costars o $ \f -> k $ L.retractl' f h z

refoldsl1 :: ACoscan1 s t a b -> (r -> a -> r) -> (a -> r) -> (r -> b) -> Free1 s -> t
refoldsl1 o h z k = costars o $ \f -> k $ L1.retractl f h z

{-
λ> prescans cotraversed (<>) mempty id [Just "foo", Nothing, Just "bar", Just "baz", Nothing]
[Just "foo",Just "foo",Just "foobar",Just "foobarbaz",Just "foobarbaz"]

λ> prescans cotraversed (<>) mempty id [["foo","bar"],["baz","bip"],["bip","bop"]]
[["foo","bar"],["foobaz","barbip"],["foobazbip","barbipbop"]]

λ> prescans coleft (<>) mempty id [["foo","bar"],["baz","bip"],["bip","bop"]]
-}
prescans :: Traversable f => ACoscan s t a b -> (a -> r -> r) -> r -> (r -> b) -> f s -> f t
prescans o h z k fs = evalState (traverse f fs) mempty
  where 
   f s = state $ \x -> (refoldsr o h z k $ L.snoc x s, L.snoc x s)

-- | TODO: Document
--
-- >>> scans cotraversed1 (L1.foldMap1 Sum getSum) [[1,2],[3,4],[5,6]] 
-- [[1,2],[4,6],[9,12]]
-- >>> scans cotraversed1 L1.sconcat [["foo","bar"],["baz","bip"],["bip","bop"]]
-- [["foo","bar"],["foobaz","barbip"],["foobazbip","barbipbop"]]
--
-- @since 0.0.3

{-# INLINE prescansl1 #-}
{-

λ> prescansl1 left (<>) id id $ [Left "foo", Left "bar", Right 3, Left "baz"]
[Left "foo",Left "barfoo",Left "barfoo",Left "bazbarfoo"]

λ> prescansl1 left (<>) id id $ [Right 0, Left "foo", Right 1, Left "baz", Right 3]
[Right 0,Right 0,Right 1,Right 1,Right 3]

λ> prescansl1 right (\r a -> r <> Sum a) Sum getSum $ [Right 0, Left "foo", Right 1, Left "baz", Right 3]
[Right 0,Right 0,Right 1,Right 1,Right 4]

-}
prescansl1 :: Traversable f => ACoscan1 s t a b -> (r -> a -> r) -> (a -> r) -> (r -> b) -> f s -> f t
prescansl1 o h z k fs = evalState (traverse f fs) mempty
  where
    f s = state $ \x -> (refoldsl1 o h z k $ L1.snoc1 x s, L.snoc x s)

{-# INLINE rescansl1 #-}
rescansl1 :: Traversable f => ACoscan1 s t a b -> (r -> a -> r) -> (a -> r) -> (r -> b) -> s -> f s -> f t
rescansl1 o h z k x fs = evalState (traverse f fs) (pure x)
  where
   f s = state $ \x -> (refoldsl1 o h z k $ L1.snoc1 x s, L.snoc x s)

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

liftMay :: (a -> Bool) -> (a -> b) -> a -> Maybe b
liftMay prd f a = if prd a then Nothing else Just $ f a

minMay, maxMay :: F.Foldable f => Ord a => f a -> Maybe a
minMay = liftMay F.null F.minimum
maxMay = liftMay F.null F.maximum

minByMay, maxByMay :: F.Foldable f => (a -> a -> Ordering) -> f a -> Maybe a
minByMay = liftMay F.null . F.minimumBy
maxByMay = liftMay F.null . F.maximumBy
