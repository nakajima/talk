# 0052 - Deep string methods and text primitives

Status: proposed

Date: 2026-08-08

## Context

Talk's Unicode model is sound but its text interface is shallow. ADR 0012 made
`String` a UTF-8 buffer, made `Character` an extended grapheme cluster, put
byte access behind `utf8()`, and deliberately rejected integer character
indexing. Those decisions remain correct.

The Core surface has not grown to match that model. `core/String.tlk` currently
provides:

- `StringMethods`, with `as_substring`, `utf8`, forward byte-offset search,
  and prefix/suffix tests;
- `String: StringMethods`, while `Substring` independently repeats several of
  the same methods without declaring the conformance;
- grapheme and scalar iteration plus O(n) grapheme `count()`;
- byte equality and `String + String`; and
- `String.from_bytes`, which constructs a string without reporting invalid
  UTF-8.

`StringMethods` is the existing shared text interface. Adding a parallel
`StringProtocol` would create two owners for the same behavior. The problem is
that `StringMethods` is shallow: nearly every useful operation remains in its
callers, and its current requirements have no default implementations to give
`String` and `Substring` parity.

The missing depth is visible in ordinary application code and in Talk's own
self-hosting work. Callers repeatedly implement line splitting, trimming,
prefix removal, reverse search, safe slicing, joining, and text accumulation.
Parsers additionally build local cursors around `CharacterIterator` and raw
storage merely to obtain lookahead, marks, and source slices. Deleting those
local modules would spread the same implementation back across every parser;
they are compensating for a missing standard text module.

Construction has the same problem. `String` carries a `capacity` field but has
no append or reserve interface, and repeated `+` allocates and copies the whole
prefix. ADR 0043 required a safe growable string builder before the self-hosted
frontend, but the completed stage-0 list contains `String.from_bytes` rather
than a builder. Frontend and application code can therefore remain quadratic
when assembling computed text.

The standard libraries of Swift, Rust, Python, Kotlin, Java, JavaScript, Go,
and C# converge on a broad set of operations: safe slicing, search, split,
trim, prefix/suffix manipulation, replacement, joining, case conversion,
classification, parsing, and efficient construction. Talk should provide the
common core once without abandoning ADR 0012's Unicode and complexity model.

## Decision

### 1. `StringMethods` remains the one shared read-only string interface

Talk expands the existing `StringMethods`; it does not add a parallel string
protocol.

```talk
pub protocol StringMethods {
    // Supplies the canonical borrowed representation used by every shared default.
    func as_substring() -> Substring

    // Makes byte-oriented work explicit so callers do not confuse bytes with characters.
    func utf8() -> UTF8View
}
```

Both owned and borrowed text conform:

```talk
extend String: StringMethods { ... }
extend Substring: StringMethods { ... }
```

`as_substring()` is the primitive view operation. Read-only algorithms are
default protocol methods expressed through that view, grapheme iteration,
scalar iteration, or explicit UTF-8 access as appropriate. Concrete adapters
may override a default only for a measured implementation reason; behavior and
complexity remain identical at the interface.

`Substring.as_substring()` returns itself. Non-transforming extraction methods
return `Substring` so they preserve a borrowed view and allocate nothing.
Methods that change text return an owned `String`.

The protocol does not promise mutation. Mutation and construction sit behind
the separate builder interface in section 8.

### 2. Character, scalar, and byte positions remain distinct

ADR 0012 is retained:

- `Character` means an extended grapheme cluster;
- `count()` and ordinary iteration are grapheme-based;
- `scalars()` is explicit Unicode-scalar iteration;
- `utf8()` is explicit byte access; and
- Talk does not add `string[n]` or any other integer character subscript with a
  hidden O(n) cost.

Talk adds opaque boundary-safe positions for operations that must identify a
location rather than return a view:

```talk
pub struct StringIndex

pub struct StringRange {
    pub let start: StringIndex
    pub let end: StringIndex
}
```

Their representation is private. An index records a valid boundary in one
string snapshot; applying it to unrelated storage is rejected. Moving by one
index means moving by one grapheme cluster. Byte offsets remain `Int` values
only on `UTF8View`.

The current `String.find`/`find_from` byte-offset result is retained during
migration but is not the long-term character-shaped interface. New search
methods return `StringIndex`, `StringRange`, `Substring`, or `Bool`. Explicit
byte search moves behind `utf8()`.

### 3. The shared interface covers the common read-only catalog

The names below describe the required capability families. Exact labels may be
adjusted to match ADR 0041, but implementations must not omit a family by
adding an ad hoc spelling elsewhere.

#### State and access

```talk
func is_empty() -> Bool
// Safely handles empty text and avoids the repeated iterator-plus-next() ceremony for the first
// grapheme.
func first() -> Character?
// Centralizes the reverse grapheme-boundary scan, which callers cannot implement correctly with
// a final byte offset.
func last() -> Character?
// Is needed by Unicode algorithms and diagnostics whose unit is code points rather than
// user-perceived characters.
func scalar_count() -> Int
// Makes encoded-size queries available through the shared interface without exposing storage
// fields; it is the capacity and I/O unit.
func utf8_count() -> Int
```

```talk
// Provides a valid initial grapheme boundary without exposing the underlying byte zero.
func start_index() -> StringIndex
// Provides the canonical exclusive end boundary needed by slicing, cursors, and empty ranges.
func end_index() -> StringIndex
// Advances by one grapheme while preserving boundary validity and making end-of-input explicit
// with Optional.
func index(after: StringIndex) -> StringIndex?
// Owns reverse grapheme traversal, needed by suffix and reverse-search operations without byte
// guessing.
func index(before: StringIndex) -> StringIndex?
// Supports deliberate O(n) movement from a known boundary; the spelling exposes that it is
// traversal rather than array indexing.
func index(_ index: StringIndex, offset_by: Int) -> StringIndex?
// Counts graphemes between validated boundaries and prevents callers from subtracting UTF-8
// offsets as if they were character counts.
func distance(from: StringIndex, to: StringIndex) -> Int
// Reads at a validated boundary and safely rejects an end or foreign index.
func character(at: StringIndex) -> Character?
// Is the zero-allocation bridge from positions back to text and is the operation that gives
// StringRange practical value.
func slice(_ range: StringRange) -> Substring
```

#### Prefixes, suffixes, and slices

```talk
// Handles the common one-grapheme test without allocating a temporary one-character String.
func starts_with(_ character: Character) -> Bool
// Handles literal prefixes and protocol markers with one boundary-safe implementation.
func starts_with(_ text: String) -> Bool
// Owns the nontrivial final-grapheme lookup and avoids temporary strings.
func ends_with(_ character: Character) -> Bool
// Handles literal suffixes without requiring callers to calculate a start position.
func ends_with(_ text: String) -> Bool

// Returns the first graphemes as a borrowed view and makes truncation at a grapheme boundary
// routine.
func prefix(_ count: Int) -> Substring
// Provides the corresponding reverse operation, whose correct UTF-8 implementation should not
// be repeated by callers.
func suffix(_ count: Int) -> Substring
// Expresses cursor-style consumption of one grapheme and safely returns empty text for a
// one-character input.
func drop_first() -> Substring
// Supports token and field removal without allocating or exposing indices.
func drop_first(_ count: Int) -> Substring
// Removes one complete final grapheme rather than one byte.
func drop_last() -> Substring
// Provides safe suffix truncation and underlies padding, clipping, and delimiter removal.
func drop_last(_ count: Int) -> Substring

// Captures the maximal leading run used by lexers, validators, and field parsers while
// returning a view.
func prefix(while: (Character) -> Bool) -> Substring
// Returns the complement of prefix(while:) without forcing a caller to run the predicate twice
// or recover an index.
func drop(while: (Character) -> Bool) -> Substring

// Combines a test and zero-allocation removal; Optional distinguishes absence from a present
// prefix leaving empty text.
func stripping_prefix(_ prefix: String) -> Substring?
// Provides the reverse test-and-view operation and centralizes reverse boundary handling.
func stripping_suffix(_ suffix: String) -> Substring?
// Is the owned convenience for transformation pipelines where the source view must not escape.
func removing_prefix(_ prefix: String) -> String
// Is the symmetric owned convenience and avoids hand-built suffix ranges.
func removing_suffix(_ suffix: String) -> String
```

Count-based slicing is explicitly O(n) in the number of traversed graphemes.
Index/range slicing is O(1) after index validation.

#### Search

```talk
// Is the allocation-free membership test used by delimiter and validation code.
func contains(_ character: Character) -> Bool
// Expresses the common Boolean question without making a caller inspect an index it does not
// need.
func contains(_ text: String) -> Bool
// Supports classification searches such as whitespace or control characters without first
// constructing a CharacterSet.
func contains(where: (Character) -> Bool) -> Bool

// Returns a reusable location for the first matching grapheme.
func first_index(of: Character) -> StringIndex?
// Returns both boundaries of a substring match; returning only its start would force the caller
// to reconstruct the end.
func first_range(of: String) -> StringRange?
// Provides the positional form of predicate search for parsers and validators.
func first_index(where: (Character) -> Bool) -> StringIndex?

// Supports suffix-oriented parsing and removal without reversing or materializing the string.
func last_index(of: Character) -> StringIndex?
// Provides a complete reverse substring match for replacement and partitioning.
func last_range(of: String) -> StringRange?
// Owns reverse predicate traversal and avoids caller buffers.
func last_index(where: (Character) -> Bool) -> StringIndex?

// Supplies all validated matches once, including the specified overlap policy, instead of
// letting callers write subtly different search loops.
func ranges(of: String) -> [StringRange]
// Counts matches without allocating the ranges array when positions are irrelevant.
func occurrences(of: String) -> Int
// Is a standard comparison primitive for paths, completion, and diffing and can return a
// borrowed view.
func common_prefix(with: String) -> Substring
// Supports extension/path and diagnostic work while centralizing reverse grapheme traversal.
func common_suffix(with: String) -> Substring
```

Empty-needle behavior is specified once and tested identically for `String`
and `Substring`. Search never splits a grapheme or returns an invalid UTF-8
boundary.
The compatibility **`find`** and **`find_from`** methods remain temporarily only
because existing callers consume byte offsets. They are not duplicated as new
character methods: `first_range` is the safe replacement, while byte search
belongs on `UTF8View`.

#### Splitting, lines, and partitioning

```talk
// Covers the dominant delimiter case without allocating a delimiter string.
func split(separator: Character) -> [Substring]
// Supports multi-character delimiters such as CRLF or language tokens.
func split(separator: String) -> [Substring]
// Supports whitespace and classification-driven splitting without a separate preprocessing
// pass.
func split(where_separator: (Character) -> Bool) -> [Substring]
// Is the policy-complete primitive: bounded splitting and empty-field preservation are required
// for records, command lines, and protocols and cannot be recovered after an unconditional
// split.
func split(
    separator: String,
    maximum_splits: Int,
    omitting_empty: Bool
) -> [Substring]

// Parses key/value and head/tail forms in one scan and avoids an unnecessary result array.
func split_once(separator: Character) -> (Substring, Substring)?
// Provides the same one-scan result for multi-character separators.
func split_once(separator: String) -> (Substring, Substring)?
// Handles extensions, qualified names, and final path segments without splitting every earlier
// occurrence.
func split_once_from_end(separator: String) -> (Substring, Substring)?

// Preserves the matched separator as a view, which is necessary when a parser must distinguish
// absence, spelling, and the two surrounding regions.
func partition(separator: String)
    -> (before: Substring, separator: Substring, after: Substring)?
// Provides that result shape for the last match and avoids a second reverse search.
func partition_from_end(separator: String)
    -> (before: Substring, separator: Substring, after: Substring)?

// Standardizes LF/CRLF handling and removes a commonly duplicated parser utility.
func lines() -> [Substring]
// Serves formatters and source tools that must preserve exact newline spelling; that
// information cannot be reconstructed after ordinary line splitting.
func lines(keeping_terminators: Bool) -> [Substring]
// Uses Unicode word-boundary semantics for human-language text; it is distinct from whitespace
// splitting because punctuation and scripts do not define words solely by spaces.
func words() -> [Substring]
// Provides the simpler maximal-Unicode-whitespace-run behavior expected by configuration,
// command, and numeric text parsing.
func split_whitespace() -> [Substring]
```

`lines()` recognizes at least LF and CRLF. Unicode line-separator policy is
specified with its implementation rather than inferred from platform behavior.

#### Trimming

```talk
// Removes Unicode whitespace at both ends, the standard cleanup operation, while preserving an
// allocation-free view.
func trimmed() -> Substring
// Supports indentation-insensitive and left-field parsing without altering meaningful trailing
// whitespace.
func trimmed_start() -> Substring
// Supports line and display cleanup without altering meaningful leading indentation.
func trimmed_end() -> Substring

// Handles domain-specific boundary sets in one scan without repeated contains predicates at
// call sites.
func trimmed(_ characters: CharacterSet) -> Substring
// Provides one-sided set trimming for prefix parsers.
func trimmed_start(_ characters: CharacterSet) -> Substring
// Provides one-sided set trimming for suffix parsers.
func trimmed_end(_ characters: CharacterSet) -> Substring

// Supports custom Unicode/domain policies without forcing construction of a reusable set.
func trimmed(where: (Character) -> Bool) -> Substring
// Is the custom one-sided leading form.
func trimmed_start(where: (Character) -> Bool) -> Substring
// Is the custom one-sided trailing form.
func trimmed_end(where: (Character) -> Bool) -> Substring
```

The no-argument forms use Unicode whitespace, matching
`Character.is_whitespace()` rather than an ASCII-only list.

#### Whole-string classification

```talk
// Lets callers select ASCII fast paths and wire formats without iterating bytes themselves.
func is_ascii() -> Bool
// Validates blank fields using the same Unicode policy as Character.is_whitespace().
func is_whitespace() -> Bool
// Supports identifiers and human-text validation across scripts.
func is_alphabetic() -> Bool
// Exposes Unicode numeric classification for whole fields, including non-decimal numeric
// characters.
func is_numeric() -> Bool
// Covers the common identifier/code validation rule without duplicating alphabetic-or-numeric
// loops.
func is_alphanumeric() -> Bool
// Distinguishes decimal digits suitable for positional number parsing from the broader Unicode
// numeric category.
func is_decimal() -> Bool
// Determines whether all cased characters are lowercase while following a documented
// empty/uncased policy.
func is_lowercase() -> Bool
// Is the symmetric uppercase predicate.
func is_uppercase() -> Bool
// Validates titlecase text, which is not equivalent to testing only the first character.
func is_titlecase() -> Bool
// Supports diagnostics, escaping, terminals, and source rendering without local
// control-character tables.
func is_printable() -> Bool
// Applies Talk's canonical lexical policy so tools and macros do not drift from the language
// lexer.
func is_identifier() -> Bool
```

The empty-string result for each predicate is documented and covered by a
shared conformance suite. Identifier classification follows Talk's own lexical
identifier policy rather than a host language's policy.

### 4. Owned transformations allocate through one builder path

The following common transformations are part of the target `StringMethods`
surface and return `String`:

```talk
// Is the standard all-occurrences transform and can precompute/build output linearly.
func replacing(_ target: String, with replacement: String) -> String
// Avoids scanning and rebuilding after the first replacement when only one protocol marker or
// field is intended.
func replacing_first(_ target: String, with replacement: String) -> String
// Is the primitive editor/parser transform over an already known match and avoids searching for
// text again.
func replacing(_ range: StringRange, with replacement: String) -> String
// Is the allocation-aware convenience for replacing a literal with empty text.
func removing(_ target: String) -> String
// Supports sanitization and filtering by Unicode property without an intermediate character
// collection.
func removing(where: (Character) -> Bool) -> String

// Can reserve exact capacity and is the standard basis for separators, indentation, and
// padding.
func repeated(_ count: Int) -> String
// Performs grapheme-cluster reversal, preserving each user-perceived character instead of
// reversing its UTF-8 bytes or scalars.
func reversed() -> String
// Supports one-to-one grapheme transforms with a builder-backed result.
func map(_ transform: (Character) -> Character) -> String
// Supports transforms that expand or delete graphemes, including Unicode and escaping
// operations.
func flat_map(_ transform: (Character) -> String) -> String
// Is the direct selection transform and avoids repeated immutable concatenation.
func filter(_ predicate: (Character) -> Bool) -> String

// Implements right alignment with grapheme-aware width and exact capacity planning.
func padded_start(to length: Int, with fill: Character) -> String
// Implements left alignment symmetrically.
func padded_end(to length: Int, with fill: Character) -> String
// Owns the odd-padding distribution rule so output is consistent across callers.
func centered(to length: Int, with fill: Character) -> String
// Is column-dependent and easy to implement inconsistently; a shared method defines tab-stop
// behavior once.
func expanding_tabs(tab_width: Int) -> String
```

These methods append into `StringBuilder`; they do not form output through a
loop of `String + String`.

Character translation is included as a general operation once a dictionary
key protocol is available:

```talk
// Performs many character substitutions or deletions in one pass, which is materially more
// efficient and expressive than chained replacement calls.
func translating(_ table: Dictionary<Character, String?>) -> String
```

Text algorithms such as wrapping, dedenting, edit distance, and natural sort
remain outside Core.

### 5. Joining is a standard operation

Joining is provided without forcing callers to hand-roll separator state:

```talk
extend StringMethods {
    // Owns separator placement, empty-input behavior, capacity planning, and linear
    // construction. Those four concerns recur in nearly every caller that currently carries a
    // first flag and repeated + operations.
    func join<T: Iterable>(_ values: T) -> String
        where T.Element: StringMethods
}
```

If the required higher-kinded or associated constraints are not yet
expressible, v1 provides concrete `[String]` and `[Substring]` overloads. Both
use `StringBuilder` and precompute capacity when cheaply possible.

### 6. Unicode case conversion and normalization are explicit

The target Unicode interface includes:

```talk
// Provides full Unicode lowercase mappings, including expansions, instead of an incorrect
// ASCII-only caller loop.
func lowercase() -> String
// Provides the corresponding full Unicode uppercase mapping.
func uppercase() -> String
// Applies Unicode titlecase mappings across word boundaries; some characters have titlecase
// forms distinct from uppercase.
func titlecase() -> String
// Performs the common first-word/first-cased-character presentation transform and is
// intentionally not a synonym for titlecasing every word.
func capitalized() -> String
// Supplies locale-independent caseless matching; lowercase alone is not sufficient for
// Unicode-insensitive comparison.
func casefolded() -> String

// Produces canonical composed text, the common storage and comparison normalization.
func normalized_nfc() -> String
// Produces canonical decomposition for algorithms that operate on combining sequences.
func normalized_nfd() -> String
// Performs compatibility composition for search and identifier policies that deliberately erase
// compatibility distinctions.
func normalized_nfkc() -> String
// Exposes the corresponding compatibility-decomposed form for analysis and transliteration.
func normalized_nfkd() -> String

// Lets callers validate or avoid allocating when text is already in canonical composed form.
func is_normalized_nfc() -> Bool
// Lets callers validate or avoid allocating when text is already in canonical decomposed form.
func is_normalized_nfd() -> Bool
// Lets callers validate or avoid allocating when text is already in compatibility-composed
// form.
func is_normalized_nfkc() -> Bool
// Lets callers validate or avoid allocating when text is already in compatibility-decomposed
// form.
func is_normalized_nfkd() -> Bool
```

Case conversion returns `String`, including on `Character`, because one input
cluster may expand to multiple output clusters. Locale-sensitive casing and
collation do not enter Core; they require an explicit locale module.

ADR 0012's byte equality remains unchanged. Normalization and case folding are
caller-selected transformations, not implicit equality behavior.

Unicode normalization needs generated data beyond the current grapheme and
classification tables. It is a staged implementation item, not permission to
ship ASCII-only methods under Unicode-shaped names.

### 7. `Character` receives the matching scalar and classification surface

`Character` is expanded with the commonly required predicates:

```talk
// Cheaply identifies a single-byte ASCII cluster for syntax and wire-format fast paths.
func is_ascii() -> Bool
// Supplies the language/protocol ASCII letter rule without scalar magic numbers.
func is_ascii_alphabetic() -> Bool
// Combines ASCII letters and digits for lexical rules.
func is_ascii_alphanumeric() -> Bool
// Distinguishes protocol ASCII whitespace from the existing Unicode whitespace predicate.
func is_ascii_whitespace() -> Bool
// Exposes the Unicode lowercase property used by the whole-string predicate.
func is_lowercase() -> Bool
// Exposes the Unicode uppercase property used by the whole-string predicate.
func is_uppercase() -> Bool
// Exposes the Unicode titlecase property used by the whole-string predicate.
func is_titlecase() -> Bool
// Identifies Unicode decimal digits; it is narrower than the existing is_numeric() and suitable
// for positional parsing.
func is_decimal() -> Bool
// Exposes the intermediate Unicode digit category used by languages such as Python and by
// compatibility numeral processing.
func is_digit() -> Bool
// Supports tokenization, wrapping, and escaping without local Unicode category tables.
func is_punctuation() -> Bool
// Distinguishes symbols from punctuation and letters for rendering and identifier policies.
func is_symbol() -> Bool
// Identifies non-rendering control clusters for diagnostics and sanitization.
func is_control() -> Bool
// Is the direct positive rendering test and centralizes Unicode category policy.
func is_printable() -> Bool
// Gives lexers and tools the canonical first-cluster rule.
func is_identifier_start() -> Bool
// Gives them the canonical subsequent-cluster rule; it differs from the start rule for digits
// and marks.
func is_identifier_continue() -> Bool
// Tells scalar-oriented algorithms whether the grapheme can be handled without expansion or
// iteration.
func is_single_scalar() -> Bool
// Reports cluster complexity without requiring callers to drain an iterator.
func scalar_count() -> Int
// Exposes every scalar in a multi-scalar grapheme for Unicode algorithms while preserving
// Character as the ordinary iteration unit.
func scalars() -> ScalarIterator

// Returns String because one character's Unicode lowercase mapping may expand to multiple
// characters.
func lowercase() -> String
// Returns String because one character's Unicode uppercase mapping may expand to multiple
// characters.
func uppercase() -> String
// Returns String because one character's Unicode titlecase mapping may expand to multiple
// characters.
func titlecase() -> String
```

The unfinished `Character + String` implementation that returns the literal
`"hi"` is removed or correctly implemented before conformance tests claim
concatenation support.

### 8. Core provides a growable `StringBuilder`

Core adds one safe, growable construction module:

```talk
pub struct StringBuilder {
    // Creates the common empty builder with no capacity estimate.
    pub init()
    // Lets parsers, joiners, and transforms avoid growth when they know an encoded-size
    // estimate.
    pub init(capacity: Int)

    // Supports estimates discovered after construction and preserves amortized linear append
    // behavior.
    pub mut func reserve_capacity(_ capacity: Int)
    // Copies one complete grapheme's UTF-8 encoding without forcing a temporary owned string.
    pub mut func append(_ character: Character)
    // Is the primary owned-text accumulation operation.
    pub mut func append(_ string: String)
    // Preserves the zero-allocation view path until bytes are copied once into final output.
    pub mut func append(_ substring: Substring)
    // Centralizes newline insertion and removes repeated append-plus-newline call pairs from
    // diagnostics and generators.
    pub mut func append_line(_ string: String)
    // Permits safe builder reuse while retaining capacity, important in lexers and repeated
    // formatting loops.
    pub mut func clear()

    // Transfers the accumulated buffer into an immutable String and is the ownership operation
    // that avoids a final copy.
    pub consuming func finish() -> String
}
```

Appending has amortized linear total cost. `finish()` transfers or reuses the
builder buffer rather than copying it when ownership permits. Builder methods
are safe Core code; callers do not allocate raw storage or use `#_ir`.

`String` remains a value-semantic owned snapshot. This ADR does not require a
full mutable `String` interface. If mutation is added later, it uses the same
copy-on-write storage rules as `Array` and delegates growth to the builder
implementation rather than introducing a second allocator.

### 9. UTF-8 construction distinguishes validation policies

`String.from_bytes` is supplemented with explicit decoding operations:

```talk
// Is the validating constructor required to uphold a valid-text invariant and report malformed
// external input.
pub static func decoding_utf8(_ bytes: &[Byte]) -> Result<String, UTF8Error>
// Provides the deliberate replacement-character policy needed for diagnostics and resilient
// file/tool input.
pub static func decoding_utf8_lossy(_ bytes: &[Byte]) -> String
// Returns owned bytes for I/O and protocols without exposing or aliasing internal storage.
pub func encoded_utf8() -> [Byte]
```

A constructor that promises valid `String` text must validate. Lossy decoding
uses the replacement policy already documented by ADR 0012. A deliberately
raw byte-preserving buffer is a byte-buffer type, not an ambiguously valid
`String`.

UTF-16, UTF-32, legacy encodings, C strings, and platform codecs belong in an
encoding or FFI package rather than the minimal Core interface.

### 10. `CharacterSet` and `TextCursor` are standard text modules

Core or the minimal standard library provides:

```talk
pub struct CharacterSet {
    pub static let whitespace: CharacterSet
    pub static let newlines: CharacterSet
    pub static let alphanumerics: CharacterSet
    pub static let punctuation: CharacterSet

    // Is the one operation trimming, splitting, lexing, and validation need from a reusable
    // set; construction and predefined sets can evolve without exposing its representation.
    pub func contains(_ character: Character) -> Bool
}
```

## Implementation stages

Every stage leaves the suite green and adds one shared conformance matrix that
runs against both `String` and `Substring`.

1. **Consolidate the existing interface.** Add
   `Substring: StringMethods`, implement `Substring.as_substring()`, move the
   duplicated search/prefix/suffix behavior into defaults, and preserve current
   behavior.
2. **Builder first.** Implement `StringBuilder`, allocation-balance tests, and
   linear-growth tests. Migrate computed-string loops in Core and the
   self-hosted frontend away from repeated `+`.
3. **Foundational views.** Add `is_empty`, first/last, prefix/suffix/drop,
   stripping prefix/suffix, trim, split, split-once, lines, contains, and join.
   These return `Substring` wherever no transformation is required.
4. **Indices and ranges.** Add opaque `StringIndex`/`StringRange`, safe
   index/range slicing, forward and reverse search, and explicit `UTF8View`
   byte search. Migrate byte-offset `String.find` callers and then remove or
   rename the compatibility methods.
5. **Owned transforms.** Add replace/remove/repeat/pad/reverse/map/filter on the
   builder path.
6. **Classification and parsing.** Complete `Character` predicates, add
   whole-string predicates, `FromString`, lexicographic comparison, and
   hashing.
7. **Unicode transforms.** Generate and verify case, case-folding, and
   normalization data; add conformance tests from the pinned Unicode version.
8. **Standard text modules.** Add `CharacterSet` and `TextCursor`; migrate
   parser-local cursor and trimming/splitting implementations, then apply the
   deletion test to ensure the complexity actually disappears from callers.

## Verification

The implementation is complete when:

1. `String` and `Substring` both conform to `StringMethods` and pass the same
   read-only behavior suite;
2. no shared read-only algorithm has separately maintained owned and substring
   implementations without a documented measured reason;
3. view-producing methods allocate nothing and preserve the source snapshot;
4. boundary-safe operations never split a UTF-8 sequence or extended grapheme
   cluster;
5. methods document whether their cost is byte-based, scalar-based, or
   grapheme-based;
6. builder-based construction is linear in total appended bytes and balance
   tests report no leaks or double frees;
7. validated UTF-8 decoding rejects malformed input and lossy decoding matches
   ADR 0012's replacement policy;
8. Unicode case and normalization methods pass the official data-driven tests
   for Talk's pinned Unicode version;
9. byte equality, comparison, and hashing remain mutually consistent;

## Consequences

- `StringMethods` becomes a deep module: one small shared interface hides
  grapheme traversal, UTF-8 boundaries, borrowed slicing, and common text
  algorithms.
- Callers gain leverage from one implementation, and maintainers gain locality
  for Unicode behavior, allocation strategy, and edge-case tests.
- `Substring` becomes the ordinary zero-allocation result of slicing, search,
  split, and trim rather than a second-class type that duplicates selected
  methods.
- Transformations allocate predictably through one builder implementation.
- The public surface becomes larger, but default protocol methods keep the
  implementation concentrated and give every conformer the same behavior.
- Opaque indices add types and validation but prevent byte/character unit
  confusion and preserve ADR 0012's rejection of integer character indexing.
- Unicode case and normalization increase generated data size; they are staged
  rather than replaced with incorrect ASCII-only behavior.

## Alternatives rejected

### Add a new `StringProtocol`

Rejected because `StringMethods` already owns this seam. A parallel protocol
would split behavior and conformance. The existing interface is deepened and
may be renamed only as a source migration, never duplicated.

### Add methods independently to `String` and `Substring`

Rejected because current duplication already demonstrates the maintenance
failure. The deletion test favors shared defaults: deleting `StringMethods`
would redistribute every algorithm into both concrete types and their callers.

### Expose integer grapheme subscripting

Rejected by ADR 0012. It hides O(n) traversal and invites accidental quadratic
code. Opaque indices, iteration, and explicitly O(n) count-based prefix/suffix
operations cover the use cases without pretending strings are arrays.

### Keep byte offsets as the general string position

Rejected because callers then mix `count()` in graphemes with search results in
bytes and can slice through invalid boundaries. Byte positions remain explicit
on `UTF8View`.

### Make equality normalization-aware

Rejected for this decision. ADR 0012's byte equality remains predictable and
cheap. Callers may normalize or case-fold explicitly before comparison.

### Put regex, escaping, locale, and every codec on `StringMethods`

Rejected because format- and environment-specific behavior would make the
shared interface broad but shallow. Those modules use the string interface;
they do not become part of every conformer's requirements.

### Let every parser build its own cursor

Rejected because each implementation repeats UTF-8 lifetime, boundary,
lookahead, and slicing logic. `TextCursor` is one deep module with parser-facing
leverage and a shared test surface.

## Relationship to earlier ADRs

- **ADR 0012:** retains extended grapheme-cluster `Character`, iteration-first
  strings, explicit UTF-8 access, byte equality, and no integer character
  indexing. This ADR adds opaque indices and moves new character-shaped search
  away from raw byte offsets.
- **ADR 0018:** ordinary string and substring parameters remain borrowed by
  default. View results retain the source snapshot under the existing borrowed
  value rules.
- **ADR 0021:** `String` and `Substring` remain first-class iterables over
  `Character`; shared methods build on that iteration model.
- **ADR 0041:** final argument labels follow callable-label conventions; the
  catalog records capability families rather than freezing every draft label.
- **ADR 0043:** `StringBuilder` completes the safe linear string-construction
  prerequisite described by the self-hosted frontend decision, and
  `TextCursor` consolidates parser-local text traversal exposed by that port.
- **ADR 0044:** builder growth, owned snapshots, borrowed views, and index
  validity follow the unified memory model and copy-on-write ownership rules.
