{-# LANGUAGE CPP #-}

import Test.DocTest
import Prelude (IO)

main :: IO ()
main = doctest 
  [ "-isrc" 
  , "src/Data/Profunctor/Optic/Carrier.hs"
  , "src/Data/Profunctor/Optic/Combinator.hs"
  , "src/Data/Profunctor/Optic/Fold.hs"
  , "src/Data/Profunctor/Optic/List.hs"
  , "src/Data/Profunctor/Optic/Iso.hs"
  , "src/Data/Profunctor/Optic/Lens.hs"
  , "src/Data/Profunctor/Optic/Prism.hs"
  , "src/Data/Profunctor/Optic/Setter.hs"
  , "src/Data/Profunctor/Optic/Traversal.hs"
  , "src/Data/Profunctor/Optic/View.hs"
  , "src/Data/Profunctor/Rep/Fold.hs"
  , "src/Data/Profunctor/Rep/Fold1.hs"
  ]
