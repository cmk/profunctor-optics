# TODO

Critical
- test/Test/Carrier.hs imports removed Property module — won't compile
- Types.hs still exports Moore/Mealy types but Machine.hs (their implementation) is removed

High
- ~25 doc references to Data.Profunctor.Optic.Property across Fold, Setter, Iso, Lens, Traversal, Prism
- 1 doc reference to removed Data.Profunctor.Optic.Moore in Traversal.hs
- Package README claims features that no longer exist (indexed variants, property predicates)

Medium
- ChangeLog.md is a placeholder template
- Root README.md just says "see individual packages"
- CI skips doctests, uses old Docker image
- Copyright year stale (2019)

Low
- Vim swap files in src directory


1. Module structure — decide what to do with Moore/Mealy types in Types.hs and the broken Property test import. Do you want to keep the types as stubs, or remove them? And should I comment out /
remove the Property tests, or bring Property.hs back into src/?
2. Stale refs — sweep all the broken doc references
3. Cabal — copyright, version bounds, metadata
4. Haddocks/README — update to reflect current state
5. Test suite — fix or rework once we know what's staying
