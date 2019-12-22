{-# LANGUAGE CPP #-}
import Test.DocTest

main :: IO ()
main = doctest 
  [ "-isrc" 
  , "src/Data/Profunctor/Optic/Operator.hs"
  , "src/Data/Profunctor/Optic/Fold.hs"
  , "src/Data/Profunctor/Optic/Option.hs"
  , "src/Data/Profunctor/Optic/Grate.hs"
  , "src/Data/Profunctor/Optic/Iso.hs"
  , "src/Data/Profunctor/Optic/Lens.hs"
  , "src/Data/Profunctor/Optic/Prism.hs"
  , "src/Data/Profunctor/Optic/Setter.hs"
  , "src/Data/Profunctor/Optic/Traversal.hs"
  , "src/Data/Profunctor/Optic/Cotraversal.hs"
  , "src/Data/Profunctor/Optic/Affine.hs"
  , "src/Data/Profunctor/Optic/View.hs"
  ]
