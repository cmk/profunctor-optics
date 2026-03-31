{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}

-- | Profunctor optics for lazy 'Text'.
--
-- See "Data.Text.Optic" for the strict variant.
module Data.Text.Lazy.Optic (
    -- * Optics
    -- ** Iso
    strict,
    packed,
    reversed,
    chunked,
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
    zipped,

    -- * Operators
    -- ** Sort-based
    sortingText,
) where

import Data.Int (Int64)
import Data.Map.Optic (Map)
import Data.Monoid (Sum(..))
import qualified Data.Text as TS
import qualified Data.Text.Lazy as T
import Data.Text.Lazy (Text)
import Data.Profunctor.Optic hiding (folded, prefixed, filtered, zipped)

-- | Iso between lazy and strict 'Text'.
strict :: Iso' Text TS.Text
strict = iso T.toStrict T.fromStrict

-- | Iso between 'String' and lazy 'Text'.
packed :: Iso' String Text
packed = iso T.pack T.unpack

-- | Lazy 'Text' is reversible.
reversed :: Iso' Text Text
reversed = iso T.reverse T.reverse

-- | Iso between lazy 'Text' and its strict chunks.
chunked :: Iso' Text [TS.Text]
chunked = iso T.toChunks T.fromChunks

-- | Split on newlines.
lined :: Iso' Text [Text]
lined = iso T.lines (T.intercalate "\n")

-- | Split on spaces.
worded :: Iso' Text [Text]
worded = iso T.words (T.intercalate " ")

-- | Split on an arbitrary delimiter.
splitOn :: Text -> Iso' Text [Text]
splitOn delim = iso (T.splitOn delim) (T.intercalate delim)

---------------------------------------------------------------------
-- Prisms
---------------------------------------------------------------------

-- | Prism for cons-cell view of lazy 'Text'.
consed :: Prism' Text (Char, Text)
consed = prism' T.uncons (uncurry T.cons)

-- | Prism for snoc-cell view of lazy 'Text'.
snoced :: Prism' Text (Text, Char)
snoced = prism' T.unsnoc (uncurry T.snoc)

-- | Prism matching a prefix.
prefixed :: Text -> Prism' Text Text
prefixed p = prism' (T.stripPrefix p) (p <>)

-- | Prism matching a suffix.
suffixed :: Text -> Prism' Text Text
suffixed s = prism' (T.stripSuffix s) (<> s)

---------------------------------------------------------------------
-- Traversal0, Fold0
---------------------------------------------------------------------

-- | /O(n)/. Affine traversal into the character at a position.
at :: Int64 -> Traversal0' Text Char
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
foundIndex :: (Char -> Bool) -> Fold0 Text (Sum Int64)
foundIndex p = fold0 (\t -> fmap (Sum . fromIntegral) . TS.findIndex p . T.toStrict $ t)

---------------------------------------------------------------------
-- Indexed optics
---------------------------------------------------------------------

-- | Indexed affine traversal at the incoming index.
ixat :: Ixtraversal0' (Sum Int64) Text Char
ixat = ixtraversalVl0 $ \point f k t ->
  let i = getSum k
  in  if i >= 0 && i < T.length t
      then fmap (\c -> let (l, r) = T.splitAt i t
                       in  l <> T.singleton c <> T.tail r) (f k (T.index t i))
      else point t

-- | Indexed traversal over characters with positional index.
ixtraversed :: Ixtraversal (Sum Int64) Text Text Char Char
ixtraversed = ixtraversalVl $ \f k t ->
  T.pack <$> traverse (\(i, c) -> f (k <> Sum i) c) (zip [0..] (T.unpack t))

-- | Indexed fold over characters with positional index.
ixfolded :: Ixfold (Sum Int64) Text Char
ixfolded = ixfoldVl $ \f k t ->
  traverse (\(i, c) -> f (k <> Sum i) c) (zip [0..] (T.unpack t))

-- | Indexed setter over characters with positional index.
ixmapped :: Ixsetter (Sum Int64) Text Text Char Char
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
chars :: Traversal' Text Char
chars = re packed . traversed

-- | Fold over individual characters.
folded :: Fold Text Char
folded = fold_ T.unpack

-- | Setter over individual characters.
mapped :: Setter' Text Char
mapped = setter T.map

---------------------------------------------------------------------
-- Coindexed optics
---------------------------------------------------------------------

-- | Coindexed traversal over characters with positional coindex.
cxtraversed :: Cxtraversal (Sum Int64) Text Text Char Char
cxtraversed = cxtraversalVl $ \fakb k fs ->
  let t0 = copure fs
  in  T.pack $ zipWith (\i c -> fakb (fmap (\t -> if i < T.length t then T.index t i else c) fs) (k <> Sum i))
        [0..] (T.unpack t0)
{-# INLINE cxtraversed #-}

-- | Coindexed fold over characters with positional coindex.
cxfolded :: Cxfold (Sum Int64) Text Char
cxfolded = cxfoldVl $ \fakb k fs ->
  let t0 = copure fs
  in  T.pack $ zipWith (\i c -> fakb (fmap (\t -> if i < T.length t then T.index t i else c) fs) (k <> Sum i))
        [0..] (T.unpack t0)
{-# INLINE cxfolded #-}

-- | Coindexed setter over characters with positional coindex.
cxmapped :: Cxsetter (Sum Int64) Text Text Char Char
cxmapped = cxsetter $ \f k t ->
  T.pack $ zipWith (\i c -> f (k <> Sum i) c) [0..] (T.unpack t)
{-# INLINE cxmapped #-}

-- | Coindexed filter over characters with positional coindex.
cxfiltered :: Cxsetter (Sum Int64) Text Text Char Bool
cxfiltered = cxsetter $ \f k t ->
  T.pack [c | (i, c) <- zip [0..] (T.unpack t), f (k <> Sum i) c]
{-# INLINE cxfiltered #-}

---------------------------------------------------------------------
-- Dual optics
---------------------------------------------------------------------

-- | Pointwise 'Cotraversal' over characters of two lazy 'Text' values.
zipped :: Cotraversal Text Text Char Char
zipped = cotraversalVl $ \fab fs ->
  let t = copure fs
      n = T.length t
  in  T.pack [ fab (fmap (\t' -> T.index t' i) fs) | i <- [0..n-1] ]
{-# INLINE zipped #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Sort a lazy 'Text' by a key on each character.
sortingText :: Ord k => (Char -> k) -> Text -> Map k TS.Text
sortingText f = sortingRep TS.length TS.index TS.pack f . T.toStrict
{-# INLINE sortingText #-}

