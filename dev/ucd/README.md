# Vendored Unicode Character Database extracts

talk's `Character` type (extended grapheme clusters, UAX #29) is built from
generated tables; these are the upstream inputs, pinned per Unicode
version. The generator is `src/bin/gen_unicode.rs`.

## Pinned version

**Unicode 17.0.0** (UAX #29 revision 47).

## Files (under `17.0.0/`)

| File | Source URL |
| --- | --- |
| `GraphemeBreakProperty.txt` | https://www.unicode.org/Public/17.0.0/ucd/auxiliary/GraphemeBreakProperty.txt |
| `emoji-data.txt` | https://www.unicode.org/Public/17.0.0/ucd/emoji/emoji-data.txt |
| `DerivedCoreProperties.txt` | https://www.unicode.org/Public/17.0.0/ucd/DerivedCoreProperties.txt |
| `GraphemeBreakTest.txt` | https://www.unicode.org/Public/17.0.0/ucd/auxiliary/GraphemeBreakTest.txt |

## Regenerating

```
cargo run --bin gen_unicode
```

writes `core/UnicodeData.tlk` (the packed break-category table) and
`tests/unicode/grapheme_conformance.tlk` (the official break test as a
self-checking talk program). Both are committed; review the diff like any
source change.

## Upgrading Unicode

1. Create `dev/ucd/<new version>/` and download the four files from the
   URLs above with the version substituted.
2. Bump `UCD_VERSION` in `src/bin/gen_unicode.rs`.
3. `cargo run --bin gen_unicode`, review the diff, run `cargo test`.
