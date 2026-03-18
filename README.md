[![Haddocks](https://img.shields.io/badge/docs-haddocks-blue)](https://cmk.github.io/profunctor-optics/)
[![CI](https://github.com/cmk/profunctor-optics/actions/workflows/ci.yml/badge.svg)](https://github.com/cmk/profunctor-optics/actions/workflows/ci.yml)

# profunctor-optics

A compact optics library compatible with the typeclasses in [profunctors](https://hackage.haskell.org/package/profunctors).

See the [profunctor-optics README](profunctor-optics/README.md) & library READMEs for details.

## Packages

| Package | Description |
|---|---|
| [profunctor-optics](profunctor-optics/) | Core optics: isos, prisms, lenses, grates, traversals, cotraversals, folds, setters, views |
| [profunctor-optics-strings](profunctor-optics-strings/) | Cotraversal-based optics for ByteString, Text, and Word types |
| [profunctor-optics-containers](profunctor-optics-containers/) | Optics for Map, IntMap, Set, IntSet, Seq, Tree + pattern functors |
| [profunctor-optics-sequences](profunctor-optics-sequences/) | MonoTraversable sequence optics + pattern synonyms |
| [profunctor-optics-folds](profunctor-optics-folds/) | Moore/Mealy machines + strict left folds |
| [profunctor-optics-exceptions](profunctor-optics-exceptions/) | Prisms for the exception hierarchy |
| [profunctor-optics-generics](profunctor-optics-generics/) | Newtype isos via Coercible |
| [profunctor-optics-th](profunctor-optics-th/) | Template Haskell lens/prism generation |
