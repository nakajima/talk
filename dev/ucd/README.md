# Vendored Unicode Character Database extracts

talk's `Character` and text APIs are built from generated Unicode tables;
these are the upstream inputs, pinned per Unicode version. The generator is
under `src/bin/gen_unicode/`.

## Pinned version

**Unicode 17.0.0** (UAX #29 revision 47).

## Files (under `17.0.0/`)

| File | Source URL |
| --- | --- |
| `CaseFolding.txt` | https://www.unicode.org/Public/17.0.0/ucd/CaseFolding.txt |
| `DerivedCoreProperties.txt` | https://www.unicode.org/Public/17.0.0/ucd/DerivedCoreProperties.txt |
| `DerivedGeneralCategory.txt` | https://www.unicode.org/Public/17.0.0/ucd/extracted/DerivedGeneralCategory.txt |
| `DerivedNormalizationProps.txt` | https://www.unicode.org/Public/17.0.0/ucd/DerivedNormalizationProps.txt |
| `emoji-data.txt` | https://www.unicode.org/Public/17.0.0/ucd/emoji/emoji-data.txt |
| `GraphemeBreakProperty.txt` | https://www.unicode.org/Public/17.0.0/ucd/auxiliary/GraphemeBreakProperty.txt |
| `GraphemeBreakTest.txt` | https://www.unicode.org/Public/17.0.0/ucd/auxiliary/GraphemeBreakTest.txt |
| `NormalizationTest.txt` | https://www.unicode.org/Public/17.0.0/ucd/NormalizationTest.txt |
| `PropList.txt` | https://www.unicode.org/Public/17.0.0/ucd/PropList.txt |
| `SpecialCasing.txt` | https://www.unicode.org/Public/17.0.0/ucd/SpecialCasing.txt |
| `UnicodeData.txt` | https://www.unicode.org/Public/17.0.0/ucd/UnicodeData.txt |
| `WordBreakProperty.txt` | https://www.unicode.org/Public/17.0.0/ucd/auxiliary/WordBreakProperty.txt |
| `WordBreakTest.txt` | https://www.unicode.org/Public/17.0.0/ucd/auxiliary/WordBreakTest.txt |

## Regenerating

```
cargo run --bin gen_unicode
```

writes `core/unicode_data.tlk` (all packed grapheme, property, word-break,
case-mapping, and normalization tables) and
`tests/unicode/grapheme_conformance.tlk` (the official grapheme-break test as a
self-checking talk program). Both are committed; review the diff like any
source change. The generator's Rust tests verify the official word-break and
normalization suites.

## Upgrading Unicode

1. Create `dev/ucd/<new version>/` and download the files above with the
   version substituted.
2. Bump `UCD_VERSION` in `src/bin/gen_unicode/main.rs`.
3. `cargo run --bin gen_unicode`, review the diff, run `cargo test`.
