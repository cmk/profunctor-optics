import Test.DocTest (doctest)
import System.Environment (getArgs)

main :: IO ()
main = do
  args <- getArgs
  doctest $ args ++
    [ "-isrc"
    , "-XConstraintKinds"
    , "-XRankNTypes"
    , "-XMultiParamTypeClasses"
    , "-XFlexibleContexts"
    , "-XFlexibleInstances"
    , "-XExistentialQuantification"
    , "-XNoImplicitPrelude"
    , "-XQuantifiedConstraints"
    , "-XScopedTypeVariables"
    , "-XTupleSections"
    , "-XTypeOperators"
    , "-XTypeApplications"
    , "-XTypeFamilies"
    , "src/Data/Profunctor/Optic/Iso.hs"
    , "src/Data/Profunctor/Optic/Prism.hs"
    , "src/Data/Profunctor/Optic/Lens.hs"
    , "src/Data/Profunctor/Optic/Traversal.hs"
    , "src/Data/Profunctor/Optic/Fold.hs"
    , "src/Data/Profunctor/Optic/Setter.hs"
    , "src/Data/Profunctor/Optic/View.hs"
    , "src/Data/Profunctor/Optic/Carrier.hs"
    ]
