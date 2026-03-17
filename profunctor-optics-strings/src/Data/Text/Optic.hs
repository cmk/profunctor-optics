{-# LANGUAGE FlexibleContexts #-}

-- | Profunctor optics for 'Text'.
--
-- @
-- \-\- convert strict Text to lazy Text
-- view lazy myText
--
-- \-\- pack a String into Text
-- review packed "hello"
-- @
module Data.Text.Optic (
    -- * Lazy\/strict iso
    lazy,

    -- * Packing
    packed,

    -- * UTF-8 encoding
    utf8,
) where

import Data.ByteString (ByteString)
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Encoding as TE
import Data.Profunctor.Optic

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
