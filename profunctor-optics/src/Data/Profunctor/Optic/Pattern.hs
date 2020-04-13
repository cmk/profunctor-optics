{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE PatternSynonyms       #-}
module Data.Profunctor.Optic.Pattern where

import Control.Exception (Exception(..), SomeException)
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.View
import Data.Profunctor.Optic.Fold
import Data.Profunctor.Optic.Prism
import Data.Profunctor.Optic.Import
import Data.Word
import qualified Data.ByteString            as BS
import qualified Data.ByteString.Char8      as CS
import qualified Data.ByteString.Lazy       as BL
import qualified Data.ByteString.Lazy.Char8 as CL

pattern Bytes :: BL.ByteString -> [Word8]
pattern Bytes b <- (view bytes -> b) where Bytes b = review bytes b

pattern Chars :: CL.ByteString -> String
pattern Chars b <- (view chars -> b) where Chars b = review chars b

pattern Bytes' :: BS.ByteString -> [Word8]
pattern Bytes' b <- (view bytes' -> b) where Bytes' b = review bytes' b

pattern Chars' :: CS.ByteString -> String
pattern Chars' b <- (view chars' -> b) where Chars' b = review chars' b

pattern Chunked :: BL.ByteString -> [BS.ByteString]
pattern Chunked a <- (view chunked -> a) where Chunked a = review chunked a

pattern Exception :: Exception a => a -> SomeException
pattern Exception e <- (preview exception -> Just e) where Exception e = review exception e

pattern Asynchronous :: Exception a => a -> SomeException
pattern Asynchronous e <- (preview asynchronous -> Just e) where Asynchronous e = review asynchronous e
