{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}

-- | Left and right carriers are characterized by their representation
-- functors ('Rep' and 'Corep'). 'Iso' sits at the top where both
-- are trivial ('Identity'). 'Adjoint' sits at the bottom where they
-- form a full adjunction (@'Corep' p ⊣ 'Rep' p@). A left-indexed
-- ('Ix') optic threads an index through the left adjoint functor
-- @(,) k@, while a right-indexed ('Cx') optic threads a coindex
-- through the right adjoint functor @(->) k@.
--
-- Profunctor optics for 'Text'.
--
-- @
-- \-\- convert strict Text to lazy Text
-- view lazy myText
--
-- \-\- pack a String into Text
-- review packed "hello"
-- @
module Data.Text.Optic (
    -- * Optics
    -- ** Iso
    short,
    lazy,
    packed,
    utf8,
    reversed,
    lined,
    worded,
    splitOn,

    -- ** Prism
    consed,
    snoced,
    prefixed,
    suffixed,

    -- ** Traversal0
    at,
    found,

    -- ** Traversal
    chars,

    -- ** Fold0
    headed,
    lasted,
    foundIndex,

    -- ** Fold
    folded,

    -- ** Setter
    mapped,
    lowered,
    uppered,
    casefolded,
    titled,

    -- ** Adjoint
    filtered,

    -- * Indexed Optics
    -- ** Ixtraversal
    ixat,
    ixtraversed,

    -- ** Ixfold
    ixfolded,

    -- ** Ixsetter
    ixmapped,

    -- * Coindexed Optics
    -- ** Cxtraversal
    cxtraversed,

    -- ** Cxfold
    cxfolded,

    -- ** Cxsetter
    cxmapped,
    cxfiltered,

    -- * Dual Optics
    -- ** Cotraversal
    zippedText,

    -- * Operators
    -- ** Sort-based
    sortingText,
) where

import Data.ByteString (ByteString)
import Data.Map.Optic (Map)
import Data.Monoid (Sum(..))
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Encoding as TE
import Data.Text.Short (ShortText)
import qualified Data.Text.Short as ST
import Data.Profunctor.Optic hiding (folded, prefixed, filtered)

-- | Iso between strict 'Text' and 'ShortText'.
--
-- 'ShortText' is backed by unpinned @ByteArray#@ — better
-- for GC when storing many small strings.
short :: Iso' Text ShortText
short = iso ST.fromText ST.toText

-- | Iso between strict and lazy 'Text'.
lazy :: Iso' Text TL.Text
lazy = iso TL.fromStrict TL.toStrict

-- | Iso between 'String' and strict 'Text'.
packed :: Iso' String Text
packed = iso T.pack T.unpack

-- | Iso between strict 'Text' and its UTF-8 encoded 'ByteString'.
--
-- Note: 'TE.decodeUtf8' throws on invalid UTF-8. For a safe
-- variant, use 'TE.decodeUtf8'' and handle the error.
utf8 :: Iso' Text ByteString
utf8 = iso TE.encodeUtf8 TE.decodeUtf8

-- | Split on newlines.
lined :: Iso' Text [Text]
lined = iso T.lines (T.intercalate "\n")

-- | Split on spaces.
worded :: Iso' Text [Text]
worded = iso T.words (T.intercalate " ")

-- | Split on an arbitrary delimiter.
splitOn :: Text -> Iso' Text [Text]
splitOn delim = iso (T.splitOn delim) (T.intercalate delim)

-- | 'Text' is reversible.
reversed :: Iso' Text Text
reversed = iso T.reverse T.reverse

---------------------------------------------------------------------
-- Prisms
---------------------------------------------------------------------

-- | Prism for cons-cell view of 'Text'.
--
-- @
-- 'review' 'consed' (c, t) = 'T.cons' c t
-- 'preview' 'consed' t = 'T.uncons' t
-- @
consed :: Prism' Text (Char, Text)
consed = prism' T.uncons (uncurry T.cons)

-- | Prism for snoc-cell view of 'Text'.
--
-- @
-- 'review' 'snoced' (t, c) = 'T.snoc' t c
-- 'preview' 'snoced' t = 'T.unsnoc' t
-- @
snoced :: Prism' Text (Text, Char)
snoced = prism' T.unsnoc (uncurry T.snoc)

-- | Prism matching a prefix.
--
-- @
-- 'preview' ('prefixed' "foo") "foobar" = Just "bar"
-- 'review' ('prefixed' "foo") "bar" = "foobar"
-- @
prefixed :: Text -> Prism' Text Text
prefixed p = prism' (T.stripPrefix p) (p <>)

-- | Prism matching a suffix.
--
-- @
-- 'preview' ('suffixed' "bar") "foobar" = Just "foo"
-- 'review' ('suffixed' "bar") "foo" = "foobar"
-- @
suffixed :: Text -> Prism' Text Text
suffixed s = prism' (T.stripSuffix s) (<> s)

---------------------------------------------------------------------
-- Traversal0, Fold0
---------------------------------------------------------------------

-- | /O(n)/. Affine traversal into the character at a position.
at :: Int -> Traversal0' Text Char
at i = traversal0' sa sbt
  where
    sa t = if i >= 0 && i < T.length t then Just (T.index t i) else Nothing
    sbt t c = let (l, r) = T.splitAt i t
              in  if T.null r then t else l <> T.singleton c <> T.tail r

-- | Affine traversal into the first character matching a predicate.
found :: (Char -> Bool) -> Traversal0' Text Char
found p = traversal0' (T.find p) (\t c -> T.map (\x -> if p x then c else x) t)

-- | First character, if non-empty.
headed :: Fold0 Text Char
headed = fold0 (\t -> if T.null t then Nothing else Just (T.head t))

-- | Last character, if non-empty.
lasted :: Fold0 Text Char
lasted = fold0 (\t -> if T.null t then Nothing else Just (T.last t))

-- | Index of the first character matching a predicate.
foundIndex :: (Char -> Bool) -> Fold0 Text (Sum Int)
foundIndex p = fold0 (fmap Sum . T.findIndex p)

---------------------------------------------------------------------
-- Indexed optics
---------------------------------------------------------------------

-- | Indexed affine traversal at the incoming index.
ixat :: Ixtraversal0' (Sum Int) Text Char
ixat = ixtraversalVl0 $ \point f k t ->
  let i = getSum k
  in  if i >= 0 && i < T.length t
      then fmap (\c -> let (l, r) = T.splitAt i t
                       in  l <> T.singleton c <> T.tail r) (f k (T.index t i))
      else point t

-- | Indexed traversal over characters with positional index.
ixtraversed :: Ixtraversal (Sum Int) Text Text Char Char
ixtraversed = ixtraversalVl $ \f k t ->
  T.pack <$> traverse (\(i, c) -> f (k <> Sum i) c) (zip [0..] (T.unpack t))

-- | Indexed fold over characters with positional index.
ixfolded :: Ixfold (Sum Int) Text Char
ixfolded = ixfoldVl $ \f k t ->
  traverse (\(i, c) -> f (k <> Sum i) c) (zip [0..] (T.unpack t))

-- | Indexed setter over characters with positional index.
ixmapped :: Ixsetter (Sum Int) Text Text Char Char
ixmapped = ixsetter $ \f k t ->
  T.pack $ zipWith (\i c -> f (k <> Sum i) c) [0..] (T.unpack t)

---------------------------------------------------------------------
-- Setters / Adjoints
---------------------------------------------------------------------

-- | Case-fold all characters.
casefolded :: Setter' Text Text
casefolded = setter $ \f -> f . T.toCaseFold

-- | Lower-case all characters.
lowered :: Setter' Text Text
lowered = setter $ \f -> f . T.toLower

-- | Upper-case all characters.
uppered :: Setter' Text Text
uppered = setter $ \f -> f . T.toUpper

-- | Title-case all characters.
titled :: Setter' Text Text
titled = setter $ \f -> f . T.toTitle

-- | Filter characters by predicate.
filtered :: Adjoint Text Text Char Bool
filtered = adjoint T.filter

-- | Traversal over individual characters.
--
-- @chars = re packed . traversed@
chars :: Traversal' Text Char
chars = re packed . traversed

-- | Fold over individual characters.
--
folded :: Fold Text Char
folded = fold_ T.unpack

-- | Setter over individual characters.
--
-- @over mapped f = T.map f@
mapped :: Setter' Text Char
mapped = setter T.map

---------------------------------------------------------------------
-- Coindexed optics
---------------------------------------------------------------------

-- | Coindexed traversal over characters with positional coindex.
cxtraversed :: Cxtraversal (Sum Int) Text Text Char Char
cxtraversed = cxtraversalVl $ \fakb k fs ->
  let t0 = copure fs
  in  T.pack $ zipWith (\i c -> fakb (fmap (\t -> if i < T.length t then T.index t i else c) fs) (k <> Sum i))
        [0..] (T.unpack t0)
{-# INLINE cxtraversed #-}

-- | Coindexed fold over characters with positional coindex.
cxfolded :: Cxfold (Sum Int) Text Char
cxfolded = cxfoldVl $ \fakb k fs ->
  let t0 = copure fs
  in  T.pack $ zipWith (\i c -> fakb (fmap (\t -> if i < T.length t then T.index t i else c) fs) (k <> Sum i))
        [0..] (T.unpack t0)
{-# INLINE cxfolded #-}

-- | Coindexed setter over characters with positional coindex.
cxmapped :: Cxsetter (Sum Int) Text Text Char Char
cxmapped = cxsetter $ \f k t ->
  T.pack $ zipWith (\i c -> f (k <> Sum i) c) [0..] (T.unpack t)
{-# INLINE cxmapped #-}

-- | Coindexed filter over characters with positional coindex.
cxfiltered :: Cxsetter (Sum Int) Text Text Char Bool
cxfiltered = cxsetter $ \f k t ->
  T.pack [c | (i, c) <- zip [0..] (T.unpack t), f (k <> Sum i) c]
{-# INLINE cxfiltered #-}

---------------------------------------------------------------------
-- Dual optics
---------------------------------------------------------------------

-- | Pointwise 'Cotraversal' over characters of two 'Text' values.
--
-- @'T.zipWith' :: (Char -> Char -> Char) -> Text -> Text -> Text@
--
-- Truncates to the shorter text, like 'ZipList'.
--
zippedText :: Cotraversal Text Text Char Char
zippedText = cotraversalVl $ \fab fs ->
  let t = copure fs
      n = T.length t
  in  T.pack [ fab (fmap (\t' -> T.index t' i) fs) | i <- [0..n-1] ]
{-# INLINE zippedText #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Sort a 'Text' by a key on each character.
--
sortingText :: Ord k => (Char -> k) -> Text -> Map k Text
sortingText = sortingRep T.length T.index T.pack
{-# INLINE sortingText #-}
