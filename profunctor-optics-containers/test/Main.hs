module Main (main) where

import System.Exit (exitFailure, exitSuccess)
import qualified Test.Prop.Container as Container

main :: IO ()
main = do
    ok <- Container.tests
    if ok then exitSuccess else exitFailure
