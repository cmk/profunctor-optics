module Main (main) where

import System.Exit (exitFailure, exitSuccess)

import qualified Test.Prop.Word as Word
import qualified Test.Prop.ByteString as ByteString
import qualified Test.Prop.Text as Text

main :: IO ()
main = do
    ok <- and <$> sequence
        [ Word.tests
        , ByteString.tests
        , Text.tests
        ]
    if ok then exitSuccess else exitFailure
