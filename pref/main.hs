{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}

import Control.Monad.IO.Unlift
import Data.Bifunctor (first)
import Data.Profunctor.Optic
import Data.Profunctor.Reference.PRefs
import Data.Profunctor.Reference.PStreams
import Data.Profunctor.Reference.Global
import Data.Profunctor.Reference.Types
import Data.Text (Text)
import Data.Validation

import System.IO.Streams (InputStream, OutputStream)
import System.IO.Unsafe --TODO use Global

import qualified Data.Text.Read as T
import qualified Data.Text as T
import qualified System.IO.Streams as S
import qualified System.IO.Streams.Combinators as SC

{-

>  connectPStreams parseref fromInteger
Right 0
Right 1
Right 2
"nada"

>  matchPStreams parseref 
Left "input does not start with a digit"
Nothing
> previewPStreams' parseref 
Nothing
> previewPStreams parseref 
Nothing

-}
main :: IO ()
main = connectPStreams parseref fromInteger

--TODO use Global
inp :: InputStream Text
inp = unsafePerformIO $ SC.unfoldM (\n -> return $ if n < 3 then Just ((T.pack $ "lol" ++ show n ++ "oops"), n + 1) else Nothing) 0

--TODO use Global
out :: OutputStream (Either Text Int)
out = unsafePerformIO $ S.makeOutputStream $ maybe (print "nada") print 

toValidation :: Either String a -> Validation Text a
toValidation = first T.pack . fromEither

decimal_ :: Text -> Validation Text Integer
decimal_ = toValidation . fmap fst . T.decimal

--validated :: (s -> Validation e a) -> (Validation e b -> t) -> Prism s t a b
parser :: Prism Text (Either Text b) Integer b
parser = validated decimal_ toEither

-- type PStreams c b a = PRefs c OutputStream InputStream b a
parseref :: PStreams Choice Int Integer
parseref = PRefs parser inp out
