module Main (main) where

import System.Exit (exitFailure, exitSuccess)

import qualified Test.Prop.Sort as Sort

main :: IO ()
main = do
    ok <- and <$> sequence
        [ Sort.tests
        ]
    if ok then exitSuccess else exitFailure
