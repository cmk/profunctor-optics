{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.List where
{- (
    -- * List
    List
  , list
  , unfolding
  , unfoldingl
  , unfoldingr
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
  , unfolding1
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
  , runsl
  , obuildl
  , buildlM
  , runslM
  , buildl1
  , runsl1
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
import Control.Monad.IO.Unlift
import Data.List.NonEmpty (NonEmpty (..))
import Data.Foldable (Foldable)
import Data.Maybe (listToMaybe)
import Data.Monoid
import Data.NonNull (NonNull)
import Data.Semigroup
import Data.Profunctor.Optic.Carrier hiding (Index)
import Data.Profunctor.Optic.Combinator
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Type
import Data.Semigroup.Foldable as F1
import qualified Control.Exception as Ex
import qualified Data.Foldable as F

import Data.Profunctor.Rep.Fold -- (L, Fold(..), FoldM(..), Unfold(..), UnfoldM(..))
import Data.Profunctor.Rep.Fold1  hiding (list1) -- (Scan(..), Fold1(..), Unfold1(..), UnfoldM1(..))
import qualified Data.Profunctor.Rep.Fold as L
import qualified Data.Profunctor.Rep.Fold1 as L1
import Data.Word
import qualified Data.List.NonEmpty as NE

import qualified Data.ByteString      as BS
import qualified Data.ByteString.Lazy as BL

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

import Data.Profunctor.Optic.Traversal
import Control.Monad.State.Strict

--import Control.Scanl (Scan(..))
import Control.Foldl (Fold(..))

--import qualified Control.Scanl as L1
import qualified Control.Foldl as FL



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
unfolding :: (s -> a) -> (Unfold s -> b -> t) -> List s t a b
unfolding sa sbt = list sa $ sbt . L.forwards
{-# INLINE unfolding #-}

reversing :: (s -> a) -> (Unfold s -> b -> t) -> List s t a b
reversing sa sbt = list sa $ sbt . L.backwards
{-# INLINE reversing #-}

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
unfolding1 :: (s -> a) -> (Unfold1 s -> b -> t) -> List1 s t a b
unfolding1 sa sbt = list1 sa $ sbt . L1.forwards
--cotabulate $ \s -> sbt (FL.foldable s) (cosieve p . fmap sa $ s)

--scanning :: Traversal1 s t a b -> Fold1 a b -> Fold1 s t
--scanning o = L1.purely_ $ \f -> Fold1 (state . fmap swap . flip (mapAccumsL o f))

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
head1 o = withLens o $ \sa sbt -> unfolding1 sa $ sbt . L1.head
{-# INLINE head1 #-}

-- | Retain the last out-of-focus part of a lens.
--
-- >>> sconcats (last1 second) Sum getSum $ ("one",1) :| [("two",2),("three",3)]
-- ("three",6)
-- 
-- @since 0.0.3
last1 :: Lens s t a b -> List1 s t a b
last1 o = withLens o $ \sa sbt -> unfolding1 sa $ sbt . L1.last
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
-- >>> runsl1 (maximized second) (++) id id $ (0,"zero") :| [(1,"one"),(2,"two")] 
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
minimizedDef s o = withLens o $ \sa sbt -> list sa $ \fs b -> flip sbt b $ maybe s id $ minMay fs
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
-- >>> runsl (maximizedDef (0,[]) second . cotraversed1) (\x a -> a:x) [] id [(1,"one"),(2,"two")]
-- (2,["to","wn","oe"])
--
-- @since 0.0.3
maximizedDef :: Ord s => s -> Lens s t a b -> List s t a b
maximizedDef s o = withLens o $ \sa sbt -> list sa $ \fs b -> flip sbt b $ maybe s id $ maxMay fs
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
minimizedByDef cmp s o = withLens o $ \sa sbt -> list sa $ \fs b -> flip sbt b $ maybe s id $ minByMay cmp fs
{-# INLINE minimizedByDef #-}

-- | Maximize over a 'Lens' using a comparator and a default.
--
-- @since 0.0.3
maximizedByDef :: (s -> s -> Ordering) -> s -> Lens s t a b -> List s t a b
maximizedByDef cmp s o = withLens o $ \sa sbt -> list sa $ \fs b -> flip sbt b $ maybe s id $ maxByMay cmp fs 
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
-- Operators
---------------------------------------------------------------------

-- | TODO: Document
--
-- >>> runs unpacked (++) [] id ["foo","bar","baz"]
-- "foobarbaz"
-- 
-- Usable in conjunction with /purely/ from the /foldl/ package.
--
-- @ 'runs' :: 'AList' s t a b -> 'L' x a b -> 'L.Unfold' s -> t @
--
-- @since 0.0.3
runs :: Foldable f => AList s t a b -> FL.Fold a b -> f s -> t
runs o f s = flip FL.fold s . o $ f
{-# INLINE runs #-}

runs1 :: Foldable1 f => AList1 s t a b -> L1.Fold1 a b -> f s -> t
runs1 o f1 s = flip L1.fold1 s . o $ f1
{-# INLINE runs1 #-}

-- | TODO: Document
--
-- @since 0.0.3
runsM :: Monad m => AList s t a b -> FL.Fold a b -> UnfoldM m s -> m t
runsM o f (UnfoldM u) = FL.impurely_ u . FL.generalize . o $ f
{-# INLINE runsM #-}

-- | TODO: Document
--
-- @since 0.0.3
--runsM1 :: Monad m => AList1 s t a b -> L1.Fold1 a b -> UnfoldM1 m s -> m t
--runsM1 o f u = flip L1.foldsM1 u . o $ f
--{-# INLINE runsM1 #-}

-- | TODO: Document
--
-- @
-- 'lists' o = 'build' o 'Control.Fold.list'
-- 'lists' id = 'Data.Foldable.toList'
-- @
--
-- >>> lists cotraversed1 $ L.forwards ["foo","bar"] :: [String]
-- ["fb","oa","or"]
-- >>> lists (minimizedDef (0,0) first) $ (,) <$> L.forwards [1,2] <*> L.bytes "abc"
-- ([1,1,1,2,2,2],97)
-- >>> lists (minimizedDef (0,0) second) $ (,) <$> L.forwards [1,2] <*> L.bytes "abc"
-- (1,[97,98,99,97,98,99])
--
-- @since 0.0.3
lists :: Foldable f => AList s t a [a] -> f s -> t
lists o = runs o FL.list
{-# INLINE lists #-}

-- | TODO: Document
--
-- @since 0.0.3
lists1 :: Foldable1 f => AList1 s t a (NonEmpty a) -> f s -> t
lists1 o = runs1 o L1.list1
{-# INLINE lists1 #-}

-- | TODO: Document
--
-- @since 0.0.3
listsM :: Monad m => AList s t a [a] -> UnfoldM m s -> m t
listsM o = runsM o FL.list
{-# INLINE listsM #-}

-- | TODO: Document
--
-- @since 0.0.3
premapsM :: Monad m => AList s t a b -> FL.Fold a b -> UnfoldM m r -> (r -> m s) -> m t
premapsM o f (UnfoldM u) r = FL.impurely_ u . FL.premapM r . FL.generalize . o $ f
{-# INLINE premapsM #-}

-- | TODO: Document
--
-- Usable in conjunction with /purely/ from the /foldl/ package.
--
-- >>> postscans cotraversed1 FL.sum [[1,2],[3,4],[5,6]] 
-- [[1,2],[4,6],[9,12]]
-- >>> postscans cotraversed1 FL.mconcat [["foo","bar"],["baz","bip"],["bip","bop"]]
-- [["foo","bar"],["foobaz","barbip"],["foobazbip","barbipbop"]]
--
-- @since 0.0.3
postscans :: Traversable f => AList s t a b -> FL.Fold a b -> f s -> f t
postscans o f = FL.postscan . o $ f
{-# INLINE postscans #-}

---------------------------------------------------------------------
-- IO
---------------------------------------------------------------------

-- | TODO: Document
--
-- >>> import qualified Control.Exception as Ex
-- >>> f x = if x < 10 then return x else Ex.throw Ex.Overflow
-- >>> exfold = lmapM f (generalize list)
-- >>> xs = [1, 2, 500, 4] :: [Integer]
-- >>> foldlM (halt @Ex.ArithException exfold) xs
-- (Just arithmetic overflow,[1,2])
--
-- @since 0.0.3
halts :: Exception e => MonadUnliftIO m => AList s t a b -> FL.Fold a b -> UnfoldM m r -> (r -> m s) -> m (Maybe e, t)
halts o f (UnfoldM u) r = FL.impurely_ u . halt . FL.premapM r . FL.generalize . o $ f
{-# INLINE halts #-}

halts_ :: MonadUnliftIO m => AList s t a b -> FL.Fold a b -> UnfoldM m r -> (r -> m s) -> m t
halts_ o f (UnfoldM u) r = FL.impurely_ u . halt_ . FL.premapM r . FL.generalize . o $ f
{-# INLINE halts_ #-}

-- @since 0.0.3
skips :: Exception e => MonadUnliftIO m => AList s t a b -> FL.Fold a b -> UnfoldM m r -> (r -> m s) -> m ([e], t)
skips o f (UnfoldM u) r = FL.impurely_ u . skip . FL.premapM r . FL.generalize . o $ f
{-# INLINE skips #-}

skips_ :: MonadUnliftIO m => AList s t a b -> FL.Fold a b -> UnfoldM m r -> (r -> m s) -> m t
skips_ o f (UnfoldM u) r = FL.impurely_ u . skip_ . FL.premapM r . FL.generalize . o $ f
{-# INLINE skips_ #-}



{-


-- | TODO: Document
--
-- @since 0.0.3
postscan :: Traversable f => AList s t a b -> FL.Fold a b -> f s -> f t
postscan o f s = flip FL.postscan s . o $ f
{-# INLINE postscan #-}


listsl o = FL.withFold FL.list $ runsl o
{-# INLINE listsl #-}
runsl o h z k u = flip FL.foldsl u . o $ FL.Fold h z k
{-# INLINE runsl #-}



-- | TODO: Document
--
-- @since 0.0.3
listsl1 :: AList1 s t a (NonEmpty a) -> L1.Unfold1 s -> t
listsl1 o = L1.withFold1 L1.list1 $ runsl1 o
{-# INLINE listsl1 #-}

-- | TODO: Document
--
-- @since 0.0.3
buildl :: Foldable f => AList s t a b -> (x -> a -> x) -> x -> (x -> b) -> f s -> t 
buildl o h z k = runsl o h z k . FL.foldable
{-# INLINE buildl #-}


-}


---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

--ofoldl1Unwrap :: IsSequence s => (x -> Element s -> x) -> (Element s -> x) -> (x -> b) -> NonNull s -> b 
--ofoldl1Unwrap h z k nnull = k (ofoldl' h (z initial) s) where (initial,s) = NN.splitFirst nnull

liftMay :: (a -> Bool) -> (a -> b) -> a -> Maybe b
liftMay prd f a = if prd a then Nothing else Just $ f a

minMay, maxMay :: F.Foldable f => Ord a => f a -> Maybe a
minMay = liftMay F.null F.minimum
maxMay = liftMay F.null F.maximum

minByMay, maxByMay :: F.Foldable f => (a -> a -> Ordering) -> f a -> Maybe a
minByMay = liftMay F.null . F.minimumBy
maxByMay = liftMay F.null . F.maximumBy
