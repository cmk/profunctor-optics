{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Scan where
{- (
    -- * Rescan
    Rescan
  , rescans
  , unfolding
  , unfolding
  , reversing
  , building

  , packing
  , chunking
  , foldingr
  , foldingr'
  , foldingl
  , foldingl'

  , mconcating
    -- * Rescan1 
  , Rescan1
  , rescans1
  , unfolding1
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
  , unfolds
  , obuildl
  , buildlM
  , unfoldsM
  , buildl1
  , unfolds1
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
import Data.Profunctor.Rep.Fold -- (L, Fold(..), FoldM(..), Unfold(..), UnfoldM(..))
import Data.Profunctor.Rep.Fold1 hiding (scan1) -- (Scan(..), Fold1(..), Unfold1(..), UnfoldM1(..))
import Data.Semigroup
import Data.Semigroup.Foldable as F1
import Data.Word
import qualified Control.Exception as Ex
import qualified Control.Foldl as FL
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
-- >>> import Data.Rescan.NonEmpty (NonEmpty(..))
-- >>> import Data.Function ((&))
-- >>> import Data.Foldable
-- >>> import Data.Ord
-- >>> import Data.Rescan ((!!))
-- >>> import Data.ByteString.Internal (w2c, c2w)
-- >>> import qualified Data.ByteString as B
-- >>> import qualified Data.ByteString.Lazy as BL
-- >>> import qualified Data.ByteString.Char8 as C
-- >>> import qualified Data.ByteString.Lazy.Char8 as CL
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- 'Rescan'
---------------------------------------------------------------------

-- | Obtain a rescan lens directly.
--
-- See < https://arxiv.org/pdf/2001.07488.pdf > section 3.1.4 or the slides < http://events.cs.bham.ac.uk/syco/strings3-syco5/slides/roman.pdf here >.
-- 
-- @since 0.0.3
rescan :: (s -> a) -> (forall f. Traversable f => f s -> b -> t) -> Rescan s t a b
rescan sa ret p = cotabulate $ \fs -> ret fs (cosieve p . fmap sa $ fs)
{-# INLINE rescan #-}

relisting :: (s -> a) -> ([s] -> b -> t) -> Rescan s t a b
relisting sa ret = rescan sa $ ret . F.toList

-- an http://oleg.fi/gists/posts/2018-03-28-achromatic-lens.html
relisting0 :: (s -> a) -> (Maybe s -> b -> t) -> Rescan s t a b
relisting0 sa sbt = relisting sa $ sbt . listToMaybe

-- | Obtain a 'Rescan' from an unfold.
--
-- @since 0.0.3
unfolding :: (s -> a) -> (Unfold s -> b -> t) -> Rescan s t a b
unfolding sa ret = rescan sa $ ret . L.unfoldr
{-# INLINE unfolding #-}

-- | Obtain a reversed 'Rescan' from a (strict) left unfold.
--
-- @since 0.0.3
reversing :: (s -> a) -> (Unfold s -> b -> t) -> Rescan s t a b
reversing sa ret = rescan sa $ ret . L.unfoldl
{-# INLINE reversing #-}

{- TODO
GlassRep type and instances
explore Cochoice for Cotraversal0, looks probably correct given below
merge Resetter and Rescan

cMatch::s->Either(c t) a

--affine
build::b->t
access::s->Either t (a , b->t)

--apochromatic
view::s->a
maybeUpdate::s->Maybe(b->t)
create::b->t

foldLens :: (forall f. Traversable f => f s -> s) -> Lens s t a b -> Rescan s t a b
foldLens f o = withLens o $ \sa sbt -> unfolding sa $ sbt . f

foldLens1 :: Lens s t a b -> Rescan1 s t a b
foldLens1 o = withLens o $ \sa sbt -> unfolding1 sa $ sbt . copure

--rescan sa ret p = cotabulate $ \fs -> ret fs (cosieve p . fmap sa $ fs)
-- (a1 -> a2 + a3) -> (a3 -> a2) -> p2 a2 c -> p1 a1 c
foldPrism :: (forall f. Traversable f => f t -> t) -> Prism s t a b -> Rescan s t a b
foldPrism f o = withPrism o $ \seta bt p -> cotabulate $ \fs -> either f (bt . cosieve p) . coapply $ fmap seta fs

foldPrism1 :: Prism s t a b -> Rescan1 s t a b
foldPrism1 o = withPrism o $ \seta bt p -> cotabulate $ \fs -> either copure (bt . cosieve p) . coapply $ fmap seta fs
-}








unleft' (Costar f) = Costar (go . fmap Left) where go = either id (go . pure . Right) . f 

--instance Traversable f => Cochoice (Star f) where
--unright' :: Traversable f => Optic (Star f) 

--unright' (Star f) = Star (fmap Right . go) where go = either (copure . Left . go) id . f
--either Left Right . coapply . f
--(go . Left) 
--unright (Star f) = 

glassing :: (((s -> a) -> b) -> s -> t) -> Cotraversal1 s t a b
glassing o = cotraversalVl1 $ \f s -> (o $ \h -> f (h <$> s)) (copure s)

unright' :: Coapplicative f => Star f (Either a b) (Either a c) -> Star f b c
unright' (Star f) = Star (go . Right) where go = either (go . Left) id . B.first copure . coapply . f

rightCorep :: Cotraversal1 (c + a) (c + b) a b
rightCorep = cotraversalVl1 $ \f -> B.second f . B.first copure . coapply -- distributeEither 

leftCorep :: Cotraversal1 (a + c) (b + c) a b
leftCorep = cotraversalVl1 $ \f -> B.first f . B.second copure . coapply -- distributeEither 

cojust :: Cotraversal (Maybe a) (Maybe b) a b
cojust = cotraversalVl $ \f -> fmap f . distributeMaybe

corescan :: Cotraversal [a] [b] a b
corescan = cotraversalVl $ \f -> fmap f . distributeRescan

distributeEither :: Coapplicative f => f (a + b) -> a + (f b)
distributeEither = B.first copure . coapply

distributeMaybe :: Coapply f => f (Maybe a) -> Maybe (f a) 
distributeMaybe = either l r . coapply . fmap proj where
    l = const Nothing
    r = Just
    proj = maybe (Left ()) Right

-- >>> distribute1 ["hi","jk"]
-- ["hj","ik"]
distributeRescan :: Coapply f => f [a] -> [f a]
distributeRescan = either l r . coapply . fmap proj where
    l = const []
    r f = (fst $ select f) : (distribute1 . snd $ select f)
    proj [] = Left ()
    proj (x:xs) = Right (x, xs)

---------------------------------------------------------------------
-- 'Rescan1'
---------------------------------------------------------------------

-- | Obtain a 'Rescan1' directly.
--
-- Any 'Rescan' may be composed with a 'Rescan1' to obtain another 'Rescan1'.
--
-- @since 0.0.3
rescan1 :: (s -> a) -> (forall f. Traversable1 f => f s -> b -> t) -> Rescan1 s t a b
rescan1 sa ret p = cotabulate $ \s -> ret s (cosieve p . fmap sa $ s)
{-# INLINE rescan1 #-}
{-
relisting1 :: (s -> a) -> (NonEmpty s -> b -> t) -> Rescan1 s t a b
relisting1 sa ret = rescan1 sa $ ret . F1.toNonEmpty

-- | Obtain a non-empty rescan lens from a non-empty left unfold.
--
-- @since 0.0.3
unfolding1 :: (s -> a) -> (Unfold1 s -> b -> t) -> Rescan1 s t a b
unfolding1 sa ret = rescan1 sa $ ret . L1.unfoldl1

-- | Obtain a reversed non-empty rescan lens from a non-empty left unfold.
--
-- @since 0.0.3
reversing1 :: (s -> a) -> (Unfold1 s -> b -> t) -> Rescan1 s t a b
reversing1 sa ret = rescan1 sa $ ret . L1.unfoldr1
-}
---------------------------------------------------------------------
-- Optics
---------------------------------------------------------------------

pointed :: Rescan (Maybe c, a) (Maybe c, b) a b
pointed = relisting0 snd $ \_ b -> (Nothing, b)

-- >>> L.unfoldl [1..4] & appended //~ L.reverse
-- [1,2,3,4,4,3,2,1]
appended :: Rescan a (Unfold a) a (Unfold a)
appended = unfolding id $ L.append

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
--selected :: (s -> a) -> Rescan s t a t
selected sa = rescan sa (flip const)
{-# INLINE selected #-}

-- | Filter a sequence of elements using a rescan lens. 
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
-- >>> l = fmap L.chars $ unfoldl ["boo","oob","ozo"]
-- >>> l & filtered (L.headDef '_') (==) //~ L.reverse
-- ["oob"]
--
-- A demonstration of composing rescan lenses. Take the head strings of all rescans that pass the following test:
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
filtered :: (s -> a) -> (s -> b -> Bool) -> Rescan s (Unfold s) a b
filtered sa ret = unfolding sa $ \s b -> L.filter (flip ret b) s
{-# INLINE filtered #-}

-- >>> "foo123" & filtered_ isDigit //~ cosieve FL.scan
-- "123"
filtered_ :: (a -> Bool) -> Rescan a (Unfold a) a b
filtered_ f = filtered id $ \s _ -> f s

-- | Filter a sequence of elements using a rescan lens. 
--
-- >>> "foobar" & eq /~ 'b'
-- "b"
-- >>> P.zip [1..] "foobar" & selected snd . ne /~ 'o'
-- "fbar"
-- >>> costars ne F.maximum "fizbuz"
-- "fibu"
--
eq, ne :: Eq a => Rescan a (Unfold a) a a
eq = filtered id (==)
ne = filtered id (/=)

-- | Filter a sequence of elements using a rescan lens. 
--
lt, le, ge, gt :: Ord a => Rescan a (Unfold a) a a
lt = filtered id (<)
le = filtered id (<=)
ge = filtered id (>)
gt = filtered id (>)

-- | TODO: Document
--
-- @since 0.0.3
mconcated :: Monoid r => (s -> a) -> (s -> r) -> (r -> b -> t) -> Rescan s t a b
mconcated sa sr rbt = rescan sa $ rbt . F.foldMap sr
{-# INLINE mconcated #-}

-- | TODO: Document
--
-- @since 0.0.3
sconcated :: Semigroup r => (s -> a) -> (s -> r) -> (r -> b -> t) -> Rescan1 s t a b
sconcated sa sr rbt = rescan1 sa $ rbt . F1.foldMap1 sr
{-# INLINE sconcated #-}

-- Prepend an accumulated value to the tape head.
-- >>> review (consed $ L.headDef 0) 3
-- [3]
-- >>> run (consed CL.head) B.char8 ["foo","bar","baz"]
-- ["fbb","foo","bar","baz"]
consed :: (Unfold s -> s) -> Rescan' (Unfold s) s 
consed f = unfolding f $ \fs s -> s `L.cons` F.fold fs

-- Append an accumulated value to the tape tail.
--
-- >>> builds (snoced CL.head) B.char8 ["foo","bar","baz"]
-- ["foo","bar","baz","fbb"]
snoced :: (Unfold s -> s) -> Rescan' (Unfold s) s 
snoced f = unfolding f $ \fs s -> F.fold fs `L.snoc` s

-- | TODO: Document
--
-- >>> ["foo","barbaz","bippy"] & padded ' ' /~ 4
-- "foo barbbipp"
-- >>> ["foo","barbaz","bippy"] & padded ' ' //~ P.maximum
-- "foo   barbazbippy "
--
-- @since 0.0.3
--paddedr :: a -> Rescan' (Unfold a) Int
--paddedr a = rescan F.length $ \as n ->
--  F.fold $ fmap (\s -> (L.reverse . L.take n . L.reverse) $ s `L.appendr` L.replicate n a) as

padded :: a -> Rescan' (Unfold a) Int
padded a = rescan F.length $ \as n -> F.foldl' (flip (<>)) mempty $ fmap (pad n a) as
  where pad i x u = L.take i $ u `L.append` L.replicate i x

-- | TODO: Document
--
-- >>> L.unfoldr "foobar" & taken id id /~ 3
-- "foo"
-- >>> L.unfoldr "foobar" & taken id ((\i -> i - 113) . fromIntegral . c2w) //~ L.headDef '_' -- 'r' is ascii code pt 114
-- "f"
--
-- @since 0.0.3
taken :: (s -> a) -> (b -> Int) -> Rescan s (Unfold s) a b 
taken sa f = unfolding sa $ \s b -> L.take (f b) s

-- >>> L.unfoldr "foobar" & takenl id ((\i -> i - 113) . fromIntegral . c2w) //~ L.headDef '_' 
-- "r"
takenl :: (s -> a) -> (b -> Int) -> Rescan s (Unfold s) a b 
takenl sa f = reversing sa $ \s b -> L.take (f b) s



-- | TODO: Document
--
-- >>> rescan (takenWhile id $ const . isAlpha . w2c) "foo2bar"
-- "foo"
-- >>> P.zip [0..] "foobar" & maximizedDef (0,' ') second . takenWhile ord B.char8 (/=) /~ c2w 'b' 
-- (5,"foo")
--
-- @since 0.0.3
takenWhile :: (s -> a) -> (s -> b -> Bool) -> Rescan s (Unfold s) a b
takenWhile sa ret = unfolding sa $ \s b -> L.takeWhile (flip ret b) s
{-# INLINE takenWhile #-}

-- | TODO: Document
--
-- >>> "foobar" & partitioned id (/=) /~ 'o'
-- ("fbar","oo")
-- >>> L.unfoldl [0..9] & partitioned id (\a b -> abs (a - b) < 1.0) //~ cosieve FL.mean
-- ([4.0,5.0],[0.0,1.0,2.0,3.0,6.0,7.0,8.0,9.0])
--
-- @since 0.0.3
partitioned :: (s -> a) -> (s -> b -> Bool) -> Rescan s (Unfold s, Unfold s) a b
partitioned sa ret = unfolding sa $ \s b -> L.partition (flip ret b) s
{-# INLINE partitioned #-}

---------------------------------------------------------------------
-- Lens-derived optics
---------------------------------------------------------------------
{-
-- | Retain the first out-of-focus part of a lens.
--
-- >>> sconcats (head1 second) Sum getSum $ ("foo",1) :| [("bar",2),("baz",3)]
-- ("foo",6)
-- >>> rescan1 (head1 second . last1 first) $ ("key1",(0,"apples")) :| [("key2",(4,"oranges")),("key3",(1,"beets"))]
-- ("key1",(0 :| [4,1],"beets"))
--
-- @since 0.0.3
head1 :: Lens s t a b -> Rescan1 s t a b
head1 o = withLens o $ \sa ret -> unfolding1 sa $ ret . L1.head
--head1 o = withLens o $ \sa ret -> rescan1 sa $ ret . P.head . F.toList --TODO a/b
{-# INLINE head1 #-}

-- | Retain the last out-of-focus part of a lens.
--
-- >>> sconcats (last1 second) Sum getSum $ ("one",1) :| [("two",2),("three",3)]
-- ("three",6)
-- 
-- @since 0.0.3
last1 :: Lens s t a b -> Rescan1 s t a b
last1 o = withLens o $ \sa ret -> unfolding1 sa $ ret . L1.last
{-# INLINE last1 #-}

-- | Search over the a 'Lens' using a predicate and a default.
--
-- Sum over the second field, search through the first:
-- >>> foldMaps (foundDef (0,0) (even . fst) second) Sum getSum $ [(1,1),(3,2),(4,3),(6,4)]
-- (4,10)
--
-- @since 0.0.3
foundDef :: s -> (s -> Bool) -> Lens s t a b -> Rescan s t a b 
foundDef s pred o = withLens o $ \sa ret -> rescan sa $ \fs b -> flip ret b $ maybe s id $ F.find pred fs
{-# INLINE foundDef #-}

-- | Minimize over a lens.
--
-- @since 0.0.3
minimized :: Ord s => Lens s t a b -> Rescan1 s t a b
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
maximized :: Ord s => Lens s t a b -> Rescan1 s t a b
maximized = maximizedBy compare
{-# INLINE maximized #-}

-- | Minimize over a 'Lens' using a default.
--
-- >>> runsFold (maximizedDef ('_',0) second) FL.mean $ P.zip "foobarbazbip" (P.enumFromThenTo 0 0.1 1)
-- ('z',0.49999999999999994)
--
-- @since 0.0.3
minimizedDef :: Ord s => s -> Lens s t a b -> Rescan s t a b
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
-- >>> unfolds (maximizedDef (0,[]) second . cotraversed1) (\x a -> a:x) [] id [(1,"one"),(2,"two")]
-- (2,["to","wn","oe"])
--
-- @since 0.0.3
maximizedDef :: Ord s => s -> Lens s t a b -> Rescan s t a b
maximizedDef = maximizedByDef compare
{-# INLINE maximizedDef #-}

-- | Minimize over a 'Lens' using a comparator.
--
-- @since 0.0.3
minimizedBy :: (s -> s -> Ordering) -> Lens s t a b -> Rescan1 s t a b
minimizedBy cmp o = withLens o $ \sa ret -> rescan1 sa $ \fs b -> ret (F.minimumBy cmp fs) b 
{-# INLINE minimizedBy #-}

-- | Maximize over a 'Lens' using a comparator.
--
-- @since 0.0.3
maximizedBy :: (s -> s -> Ordering) -> Lens s t a b -> Rescan1 s t a b
maximizedBy cmp o = withLens o $ \sa ret -> rescan1 sa $ \fs b -> ret (F.maximumBy cmp fs) b 
{-# INLINE maximizedBy #-}

-- | Minimize over a 'Lens' using a comparator and a default.
--
-- @since 0.0.3
minimizedByDef :: (s -> s -> Ordering) -> s -> Lens s t a b -> Rescan s t a b
minimizedByDef cmp s o = withLens o $ \sa ret -> rescan sa $ \fs b -> flip ret b $ maybe s id $ minByMay cmp fs
{-# INLINE minimizedByDef #-}

-- | Maximize over a 'Lens' using a comparator and a default.
--
-- @since 0.0.3
maximizedByDef :: (s -> s -> Ordering) -> s -> Lens s t a b -> Rescan s t a b
maximizedByDef cmp s o = withLens o $ \sa ret -> rescan sa $ \fs b -> flip ret b $ maybe s id $ maxByMay cmp fs 
{-# INLINE maximizedByDef #-}
-}

---------------------------------------------------------------------
-- ByteString optics
---------------------------------------------------------------------
-- | TODO: Document
--
-- @since 0.0.3
encoded :: (s -> a) -> (s -> B.Builder) -> (BL.ByteString -> b -> t) -> Rescan s t a b
encoded sa sb ret = mconcated sa sb $ ret . B.toLazyByteString
{-# INLINE encoded #-}


-- λ> build (filtered (view strict) (==)) $ fmap CL.pack ["bar","bar","bar"]

-- TODO move to bytestring optics
build :: Foldable f => ARescan s t BS.ByteString BL.ByteString -> f s -> t
build o = runsFold o $ FLB.lazy

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------


mconcats o = runsFold o $ FL.mconcat
foldMaps o f g = runsFold o $ FL.foldMap f g

rescans :: ARescan s t a b -> FL.Fold a b -> [s] -> [t]
rescans o f s = flip FL.scan s . o $ f

-- > unfolds :: ARescan s t a b -> (Unfold a -> b) -> Unfold s -> t
unfolds :: ARescan s t a b -> (Unfold a -> b) -> Unfold s -> t
unfolds o = cosieve . o . cotabulate

{-
-- | TODO: Document
--
-- >>> scans cotraversed1 (L1.foldMap1 Sum getSum) [[1,2],[3,4],[5,6]] 
-- [[1,2],[4,6],[9,12]]
-- >>> scans cotraversed1 L1.sconcat [["foo","bar"],["baz","bip"],["bip","bop"]]
-- [["foo","bar"],["foobaz","barbip"],["foobazbip","barbipbop"]]
--
-- @since 0.0.3
scans :: Traversable f => ARescan1 s t a b -> L1.Fold1 a b -> f s -> f t
scans o f = L1.scan . o $ f
{-# INLINE scans #-}

-- | TODO: Document
--
-- >>> postscans ge FL.mconcat $ ["a","b","c"] 
-- [[],["b"],["b","c"]]
-- >>> postscans cotraversed1 FL.sum [[1,2],[3,4],[5,6]] 
-- [[1,2],[4,6],[9,12]]
--
-- @since 0.0.3
postscans :: Traversable f => ARescan s t a b -> FL.Fold a b -> f s -> f t
postscans o f = FL.postscan . o $ f
{-# INLINE postscans #-}


-- | TODO: Document
--
-- > runsFold1 o f1 s = L1.purely_ (L1.runfold1 s) . o $ f1
--
-- @since 0.0.3
runsFold1 :: Foldable1 f => ARescan1 s t a b -> L1.Fold1 a b -> f s -> t
runsFold1 o f1 s = flip L1.fold1 s . o $ f1
{-# INLINE runsFold1 #-}
-}


-- | TODO: Document
--
-- > runsFold o f s = Control.Foldl.purely_ (Data.Unfold.runfold s) . o $ f
--
-- >>> runsFold (re . chars) (++) [] id ["foo","bar","baz"]
-- "foobarbaz"
-- 
-- @ 'runsFold' :: 'ARescan' s t a b -> 'L' x a b -> 'L.Unfold' s -> t @
--
-- @since 0.0.3
runsFold :: Foldable f => ARescan s t a b -> FL.Fold a b -> f s -> t
runsFold o f s = flip FL.fold s . o $ f
{-# INLINE runsFold #-}

-- | TODO: Document
--
-- @since 0.0.3
runsFoldM :: Monad m => ARescan s t a b -> FL.Fold a b -> UnfoldM m s -> m t
runsFoldM o f (UnfoldM u) = FL.impurely_ (u . flip) . FL.generalize . o $ f
{-# INLINE runsFoldM #-}

-- | TODO: Document
--
-- @since 0.0.3
premapsM :: Monad m => ARescan s t a b -> FL.Fold a b -> UnfoldM m r -> (r -> m s) -> m t
premapsM o f (UnfoldM u) r = FL.impurely_ (u . flip) . FL.premapM r . FL.generalize . o $ f
{-# INLINE premapsM #-}

---------------------------------------------------------------------
-- IO
---------------------------------------------------------------------

-- | TODO: Document
--
-- >>> import qualified Control.Exception as Ex
-- >>> f x = if x < 10 then return x else Ex.throw Ex.Overflow
-- >>> exfold = lmapM f (generalize rescans)
-- >>> xs = [1, 2, 500, 4] :: [Integer]
-- >>> foldlM (halt @Ex.ArithException exfold) xs
-- (Just arithmetic overflow,[1,2])
--
-- @since 0.0.3
halts :: Exception e => MonadUnliftIO m => ARescan s t a b -> FL.Fold a b -> UnfoldM m r -> (r -> m s) -> m (Maybe e, t)
halts o f (UnfoldM u) r = FL.impurely_ (u . flip) . halt . FL.premapM r . FL.generalize . o $ f
{-# INLINE halts #-}

-- | TODO: Document
--
-- @since 0.0.3
halts_ :: MonadUnliftIO m => ARescan s t a b -> FL.Fold a b -> UnfoldM m r -> (r -> m s) -> m t
halts_ o f (UnfoldM u) r = FL.impurely_ (u . flip) . halt_ . FL.premapM r . FL.generalize . o $ f
{-# INLINE halts_ #-}

-- | TODO: Document
--
-- @since 0.0.3
skips :: Exception e => MonadUnliftIO m => ARescan s t a b -> FL.Fold a b -> UnfoldM m r -> (r -> m s) -> m ([e], t)
skips o f (UnfoldM u) r = FL.impurely_ (u . flip) . skip . FL.premapM r . FL.generalize . o $ f
{-# INLINE skips #-}

-- | TODO: Document
--
-- @since 0.0.3
skips_ :: MonadUnliftIO m => ARescan s t a b -> FL.Fold a b -> UnfoldM m r -> (r -> m s) -> m t
skips_ o f (UnfoldM u) r = FL.impurely_ (u . flip) . skip_ . FL.premapM r . FL.generalize . o $ f
{-# INLINE skips_ #-}

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
