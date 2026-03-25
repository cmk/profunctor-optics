# Sprint 22 — string-optics: dual optics for Text and ByteString

## Scope

Fill out the dual (Costar-side) optic surface for Text and ByteString
in the `string-optics` library (renamed from `profunctor-optics-strings`).
Focus on Cotraversal (zipping), Cosetter (accumulating maps), and
Colens (unfolding/generation).

## Rationale

Text and ByteString are monomorphic containers (`Char` and `Word8`
respectively), which limits the polymorphic optic surface. But they
have rich dual-shaped APIs (`zipWith`, `mapAccumL`/`mapAccumR`,
`scanl`/`scanr`, `unfoldr`) that are completely uncovered by the
current library.

## Module conventions

Follow the module conventions from Sprint 21: two sections (Optics,
Operators), ordered by optic type following the canonical ordering in
`Data.Profunctor.Optic.Types`. See Sprint 21 for the full ordering.

The `string-optics` satellite depends on `text`, `bytestring`,
`text-short`, and `scheme-extensions`. It already has `Data.Text.Optic`,
`Data.ByteString.Optic`, and `Data.Word.Optic`.

## Phase 1 — Text dual optics (S22.1–S22.7)

| ID | File | Task |
|----|------|------|
| S22.1 | Text/Optic.hs | `zippedText :: Cotraversal Text Text Char Char` — wraps `Text.zipWith`. Binary pointwise cotraversal. |
| S22.2 | Text/Optic.hs | `scannedL :: (Char -> Char -> Char) -> Char -> Cosetter Text Text Char Char` — wraps `Text.scanl`. Investigate whether scan fits Cosetter or needs a dedicated combinator. |
| S22.3 | Text/Optic.hs | `scannedR :: (Char -> Char -> Char) -> Char -> Cosetter Text Text Char Char` — wraps `Text.scanr` |
| S22.4 | Text/Optic.hs | `accumL :: Cosetter (a, Text) (a, Text) (a, Char) (a, Char)` — investigate `mapAccumL` as a Cosetter with state threading. Type may need refinement. |
| S22.5 | Text/Optic.hs | `unfolded :: Colens Text Text ??? ???` — investigate `Text.unfoldr` as a Colens. The coalgebraic shape `(a -> Maybe (Char, a)) -> a -> Text` may not fit a standard Colens cleanly. |
| S22.6 | Text/Optic.hs | `splitted :: (Char -> Bool) -> Cosetter Text [Text] Char Bool` — investigate `Text.split` / `Text.break` / `Text.span` as Cosetter-like decomposition optics |
| S22.7 | Text/Optic.hs | `encodedUtf8 :: Iso' Text ByteString` — `encodeUtf8`/`decodeUtf8` as an iso (partial: decoding can fail, so may need `Prism` or `Traversal0` instead) |

## Phase 2 — ByteString dual optics (S22.8–S22.13)

| ID | File | Task |
|----|------|------|
| S22.8 | ByteString/Optic.hs | `zippedBS :: Cotraversal ByteString ByteString Word8 Word8` — wraps `BS.packZipWith`. ByteString has the cleanest zip (`packZipWith` stays in ByteString, unlike Text's `zipWith` which returns `Text`). |
| S22.9 | ByteString/Optic.hs | `scannedL1 :: (Word8 -> Word8 -> Word8) -> Cosetter ByteString ByteString Word8 Word8` — wraps `BS.scanl1` |
| S22.10 | ByteString/Optic.hs | `scannedR1 :: (Word8 -> Word8 -> Word8) -> Cosetter ByteString ByteString Word8 Word8` — wraps `BS.scanr1` |
| S22.11 | ByteString/Optic.hs | `accumL :: Cosetter (a, ByteString) (a, ByteString) (a, Word8) (a, Word8)` — wraps `BS.mapAccumL` |
| S22.12 | ByteString/Optic.hs | `accumR :: Cosetter (a, ByteString) (a, ByteString) (a, Word8) (a, Word8)` — wraps `BS.mapAccumR` |
| S22.13 | ByteString/Optic.hs | Investigate `BS.unfoldrN` as bounded Colens |

## Phase 3 — Lazy variants (S22.14–S22.15)

| ID | File | Task |
|----|------|------|
| S22.14 | Text/Optic.hs | Add lazy Text variants where the optic signatures differ (lazy `foldrChunks`/`foldlChunks` have chunk-level shapes that may give Cofold optics) |
| S22.15 | ByteString/Optic.hs | Add lazy ByteString variants |

## Phase 4 — Sort integration (S22.16–S22.17)

| ID | File | Task |
|----|------|------|
| S22.16 | Text/Optic.hs | `sortingText :: Ord k => (Char -> k) -> Sort Int k Char (Map k Text)` — Sort-based text sorting, extending `sortingString` from Sort.hs to Text (not just String) |
| S22.17 | ByteString/Optic.hs | `sortingBS :: Ord k => (Word8 -> k) -> Sort Int k Word8 (Map k ByteString)` — Sort-based ByteString sorting |

## Phase 5 — Properties and tests (S22.18–S22.20)

| ID | File | Task |
|----|------|------|
| S22.18 | Property | Cotraversal zip roundtrip properties for Text and ByteString |
| S22.19 | Test/ | Hedgehog tests for new Text optics |
| S22.20 | Test/ | Hedgehog tests for new ByteString optics |

## Phase 6 — Rename and cleanup (S22.21)

| ID | Task |
|----|------|
| S22.21 | Rename `profunctor-optics-strings` to `string-optics` in cabal file, update all references |

## Open questions

- **Scan optics**: `scanl :: (a -> b -> a) -> a -> [b] -> [a]` produces
  a container of intermediate fold results. This is somewhere between
  a Cosetter and a Cotraversal — it transforms AND accumulates. May
  need a dedicated scan combinator rather than forcing it into an
  existing optic type.

- **mapAccumL threading**: `mapAccumL :: (a -> Char -> (a, Char)) -> a -> Text -> (a, Text)`
  threads state through the traversal. The `(a, Text) -> (a, Text)`
  shape with the `(a, Char) -> (a, Char)` inner shape suggests a
  Cosetter on paired types, but the state threading may need special
  handling.

- **Encoding isos**: `encodeUtf8`/`decodeUtf8` are operationally
  inverse but `decodeUtf8` can throw. Use `Iso` with a note about
  partiality, or `Prism`/`Traversal0` for the decode direction?

## Dependencies

- Sprint 21 (Cx container optics, upstream migration)
- `text`, `bytestring`, `text-short`, `scheme-extensions`

## Deliverables

- Cotraversal zips for Text and ByteString
- Cosetter scans and accumulating maps
- Sort-based sorting for Text and ByteString
- Renamed `string-optics` package
