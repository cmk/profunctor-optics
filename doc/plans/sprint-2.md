# Sprint 2 — String splitting and line/word optics

## Scope

Add splitting optics for ByteString and Text: `lined`, `worded`,
`splitOn`, `breakOn`, plus traversals over characters and bytes.
These complement Sprint 1's bit-level cotraversals and isos.

## Rationale

The most common string operations are splitting on delimiters
(lines, words, substrings) and mapping over characters/bytes.
These are traversals (variable-length output), not cotraversals
(fixed-size), so they use the `Traversing` constraint rather
than `Closed`/`Cotraversing`.

## Stories

| ID   | Module / target          | Description                                      |
|------|--------------------------|--------------------------------------------------|
| S2.1 | Data.ByteString.Optic    | `lined`, `worded` — split on newlines/spaces     |
| S2.2 | Data.ByteString.Optic    | `splitOn` — split on arbitrary delimiter          |
| S2.3 | Data.ByteString.Optic    | `bytes` — traversal over individual bytes        |
| S2.4 | Data.Text.Optic          | `lined`, `worded` — split on newlines/spaces     |
| S2.5 | Data.Text.Optic          | `splitOn` — split on arbitrary delimiter          |
| S2.6 | Data.Text.Optic          | `chars` — traversal over individual characters   |
| S2.7 | Test.Prop.Split          | Properties for splitting optics                  |

## New functions

```haskell
-- Data.ByteString.Optic
lined  :: Iso' ByteString [ByteString]    -- split/join on newlines
worded :: Iso' ByteString [ByteString]    -- split/join on spaces
splitOn :: ByteString -> Iso' ByteString [ByteString]  -- split/join on delimiter
bytes  :: Traversal' ByteString Word8     -- traverse individual bytes

-- Data.Text.Optic
lined  :: Iso' Text [Text]               -- split/join on newlines
worded :: Iso' Text [Text]               -- split/join on spaces
splitOn :: Text -> Iso' Text [Text]       -- split/join on delimiter
chars  :: Traversal' Text Char            -- traverse individual characters
```

## Hedgehog properties (P1–P12)

| Prop | Description                                                    |
|------|----------------------------------------------------------------|
| P1   | `view lined . review lined = id` for ByteString               |
| P2   | `view worded . review worded = id` for ByteString              |
| P3   | `view (splitOn d) . review (splitOn d) = id` for ByteString    |
| P4   | `over bytes f` agrees with `BS.map f`                          |
| P5   | `view lined . review lined = id` for Text                      |
| P6   | `view worded . review worded = id` for Text                    |
| P7   | `view (splitOn d) . review (splitOn d) = id` for Text          |
| P8   | `over chars f` agrees with `T.map f`                           |
| P9   | `lined` splits on '\n'                                         |
| P10  | `worded` splits on ' '                                         |
| P11  | `bytes` traverses each byte exactly once                       |
| P12  | `chars` traverses each char exactly once                       |

## Work order (TDD)

1. S2.7 — Write P1–P12 skeletons (all red)
2. S2.1 — Implement ByteString lined/worded, green P1–P2, P9–P10
3. S2.2 — Implement ByteString splitOn, green P3
4. S2.3 — Implement ByteString bytes, green P4, P11
5. S2.4–S2.6 — Implement Text equivalents, green P5–P8, P12
6. Commit when P1–P12 all pass
