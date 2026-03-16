# Revision history for profunctor-optics

## 0.0.3

* Slim core: removed 5 heavy dependencies (foldl, mono-traversable, strict, newtype-generics, these-skinny).
* Moved Machine, Pattern, Zoom, Rep.Foldl, Rep.Foldl1, and Tuple.Optic modules out of the core library.
* Moved Moore/Mealy type definitions out (to be extracted into a separate library).
* Restored Property module with inlined lawz dependency.
* Added property test suite (hedgehog) for optic laws.
* Fixed all doctests for GHC 9.6 compatibility under NoImplicitPrelude.
* Re-exported adjunctions modules (Data.Functor.Rep, Data.Functor.Adjunction).
* Re-exported Distributive, Coapplicative, and profunctor class hierarchy from hub module.
* GHC 9.6 compatibility: eta-expanded impredicative point-free definitions.
* Bumped cabal-version to 1.22.

## 0.0.2

* Added indexed and co-indexed optic variants.
* Added Moore and Mealy machine optics.
* Added pattern synonyms module.
* Added property testing predicates.

## 0.0.1

* Initial release.
