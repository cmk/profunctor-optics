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
    lined,
    worded,
    splitOn,

    -- ** Traversal
    chars,

    -- ** Fold
    folded,

    -- ** Setter
    mapped,

    -- * Dual Optics
    -- ** Cotraversal
    zippedText,

    -- * Operators
    -- ** Sort-based
    sortingText,
) where

import Data.ByteString (ByteString)
import Data.Map.Optic (Map(..))
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Encoding as TE
import Data.Text.Short (ShortText)
import qualified Data.Text.Short as ST
import Data.Profunctor.Optic hiding (folded)

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
