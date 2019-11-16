--{-# OPTIONS_GHC -F -pgmF doctest-discover #-}
{-# LANGUAGE MultiParamTypeClasses #-}
import Test.DocTest

main :: IO ()
main = doctest ["-isrc", "src/Data/Profunctor/Optic/Iso.hs"]
