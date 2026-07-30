# 0043 - Self-host the source frontend before procedural macros

Status: accepted; implemented (2026-07-27)

Date: 2026-07-26

## Context

Talk's lexer and parser are currently implemented in Rust. They produce the
source AST, spans, node identities, parser diagnostics, recovery nodes, and
metadata consumed by formatting, highlighting, imports, name resolution, type
checking, and editor features.

The planned procedural macro system needs to expose token trees and
category-specific parsing to Talk macro code. If those APIs are described by
handwritten Talk declarations while lexing and parsing remain implemented in
Rust, the compiler has two representations of its source language. Token
kinds, compound-token behavior, source spans, parser entry points, recovery,
and syntax categories can drift. Contract tests can detect some drift, but do
not establish one owner for the language grammar.

The desired macro boundary makes this more important. A macro must be able to
parse part of its input as an ordinary Talk expression, pattern, type, or block
item. Those operations must have exactly the same behavior as the compiler's
normal parser. Reimplementing the source grammar in a macro library, or
publishing a manually synchronized view of the Rust parser, would make syntax
accepted by macros differ from syntax accepted in source files.

Moving the source frontend into Talk introduces a bootstrap cycle: Talk source
is needed to build the parser, but a parser is needed to compile that source.
The compiler already has a portable, validated bytecode execution path. A
checked-in frontend bytecode artifact can break the cycle while keeping the
canonical implementation in Talk.

## Decision

### 1. The source frontend is implemented in Talk

The canonical lexer and parser implementation moves to ordinary, macro-free
Talk source. "Source frontend" in this ADR means lexing, token-tree capture,
parsing, parser recovery, source spans, syntax metadata, and parser diagnostics.
It does not include name resolution, type inference, ownership checking,
lowering, or bytecode generation.

The source layout is conceptually:

```text
compiler-frontend/
  Syntax.tlk
  Lexer.tlk
  TokenTree.tlk
  Parser.tlk
  Diagnostics.tlk
```

The exact directory names are implementation details. The ownership boundary
is not: these Talk files are the single implementation of source lexing and
parsing used by the compiler, LSP, formatter-facing parse path, and future
procedural macros.

The frontend sources may use the ordinary language subset supported by the
checked-in bootstrap artifact, but compiling the frontend may never require expanding
a user macro. This is the permanent bootstrap kernel boundary.

### 2. The compiler executes a checked-in frontend artifact

The repository carries a versioned, checked-in bytecode artifact built from the
frontend Talk sources. A normal compiler build validates and loads that
artifact; it does not compile the frontend sources from scratch.

Conceptually:

```text
bootstrap/
  frontend.tbc
  frontend.manifest
```

The manifest records at least:

- the frontend ABI version;
- a digest of the canonical frontend sources;
- a digest of the bytecode artifact;
- the compiler/bytecode format version needed to load it; and
- the generated bridge-schema version.

The bytecode decoder validates the artifact before execution even though it is
shipped with the compiler. A missing, stale, incompatible, or invalid artifact
is a build or startup error. The compiler never silently falls back to a
second parser.

### 3. Bootstrap regeneration is explicit and reaches a fixed point

A dedicated bootstrap command rebuilds the frontend artifact. Regeneration is
not an implicit side effect of `cargo build`.

The bootstrap sequence is:

```text
checked-in frontend artifact (stage 0)
  -> parse and compile frontend sources
  -> candidate frontend artifact (stage 1)
  -> parse and compile the same sources again
  -> verification artifact (stage 2)
```

Stage 1 and stage 2 must be identical under the canonical deterministic
encoding. If unavoidable non-semantic metadata exists, the comparison uses a
specified normalized representation rather than omitting the fixed-point
check.

The command updates the artifact, manifest, and generated bridge data together.
CI regenerates them and rejects a diff. Editing a frontend source without
regenerating its artifact therefore cannot pass validation.

The checked-in artifact is a bootstrap seed, not a second source of language
semantics. Its provenance is the reviewed Talk source plus the reproducible
regeneration procedure.

### 4. The frontend exposes one versioned service ABI

The frontend artifact exports category-specific operations rather than one
file-only parser:

```text
parse_file
parse_expr
parse_pattern
parse_type
parse_block_items
```

The concrete names may differ, but the capabilities are required. Parse
operations accept an explicit mode for strict compilation versus lenient
editor recovery and an explicit trivia/comment policy where relevant.

Tokens and token trees are internal to the frontend and do not cross the
ABI in production. The compiler consumes parse results, which already
carry the comment tokens and node-meta token extents downstream passes
need, so no token serialization format or token-kind numbering is shared
across the boundary. A `lex` export exists as a validation and tooling
surface: the differential harness compares it against the reference
lexer during migration, and narrow editor queries (identifier
validation, token scans) become purpose-built operations rather than a
token-stream export. Token trees are the macro system's substrate inside
the frontend; expansion runs where they live, so they never need a wire
representation.

Every result preserves the information currently required downstream:

- byte-accurate source spans and full token extents;
- stable node identities within a parsed file;
- delimiter structure and exact token spelling;
- comments and boundary metadata required by formatting;
- structured diagnostics with recovery positions; and
- incomplete syntax used by editor analysis.

The future macro system calls these same category entry points when it treats a
token range as embedded Talk. It does not contain another expression, pattern,
or type parser.

### 5. Talk declarations own the frontend data schema

The canonical token, token-tree, syntax-category, diagnostic, and parsed-result
schemas are declared with the frontend Talk sources. Rust does not maintain a
handwritten mirror that can silently diverge.

The bootstrap process emits a machine-readable ABI descriptor and generated
Rust bridge code from those declarations. The generated bridge is checked in
or generated from the checked-in descriptor before the compiler crate is
compiled. It is build output, not an independently edited model.

The Rust side checks the ABI version and schema digest before accepting a
frontend result. Unknown variants, missing fields, invalid spans, invalid node
identities, and malformed arena references fail closed at this trust seam.

Rust may convert the validated frontend result into private compiler data
optimized for downstream passes. That conversion is an adapter, not a parser,
and it may not reinterpret source text or reconstruct grammar decisions.

### 6. Rust retains the host, not a production parser

After cutover, Rust owns:

- loading and validating the frontend bytecode and ABI descriptor;
- supplying source bytes and deterministic allocation;
- executing the frontend through the bytecode runtime;
- validating and adapting returned frontend data;
- import discovery and the later compiler pipeline; and
- host integration for CLI, LSP, C, Swift, and browser consumers.

The existing Rust lexer and parser remain only during migration for
differential testing. They are removed from the normal compiler and editor
paths once the self-hosted frontend reaches parity. They are then deleted
rather than retained as a fallback or compatibility parser. Git history
preserves the bootstrap implementation if it is needed for investigation.

### 7. Frontend execution is deterministic and capability-limited

The source frontend is not arbitrary compile-time application code. Its host
surface provides source bytes, deterministic allocation, and structured
frontend diagnostics. It has no filesystem, environment, network, process,
clock, randomness, or application host access.

Inline IR and `@unsafe` are not admitted in the frontend source set. Frontend
execution has explicit instruction, recursion, and allocation budgets. Budget
exhaustion is a structured compiler failure attributed to the parsing
operation, not permission to invoke an ambient panic or IO capability.

These restrictions are enforced by the frontend build profile and validated
artifact interface, not by filename conventions alone.

### 8. This project precedes the procedural macro project

The self-hosted source frontend is completed before token-tree procedural
macros are implemented. The macro design may rely on:

- balanced token trees produced by the canonical lexer;
- exact token spellings and full spans;
- category-indexed syntax values;
- category parser entry points; and
- deterministic execution of compiler-shipped Talk bytecode.

This ADR does not define macro declaration syntax, hygiene, macro-file imports,
quotation, expansion ordering, or exported macro artifacts. Those remain a
separate decision after the frontend boundary is real.

ADR 0026's existing expression-template macro slice remains historical and may
continue to operate during migration. A later procedural macro ADR may
supersede its invocation and expansion model. The self-hosted parser must not
depend on either system.

## Migration

### Stage 0 - Close the core gaps the frontend subset requires

ADR §7 bars `@unsafe` and inline IR from the frontend source set. Core
currently builds every `String` through `_alloc`/`_copy` behind `@_ir`, so
that restriction leaves frontend code unable to construct a string from
computed bytes at all, and able to concatenate only in O(n²). The following
core and language work precedes the frontend port:

1. A safe growable string builder in Core, plus a `[Byte] -> String`
   constructor. No frontend source may allocate raw buffers.
2. `Int`-to-`Byte` conversion, so byte-level lexing does not route through
   `_toInt()` or `@_ir { cmp Byte }`.
3. `Substring: Equatable<Substring>`, so comparing two source slices does not
   allocate.
4. `Array` stack operations (`pop`, `last`), required for delimiter-stack
   token-tree capture.

These are language and Core deficiencies of exactly the kind this ADR's
Consequences anticipate ("Parser development uses Talk's own type, effect,
ownership, and module systems, exposing deficiencies that matter for
self-hosting"). They are fixed in Core rather than worked around in the
frontend, because a workaround would either re-admit `@unsafe` or bake
quadratic string building into the compiler's hot path.

Match guards are a known ergonomic gap in the same area and are deliberately
excluded: a guarded arm is always expressible as an `if` inside the arm body,
and threading guards through exhaustiveness checking risks incorrect coverage
diagnostics across every existing `match`. That work is independent of the
bootstrap path.

### Stage 1 - Freeze the frontend contract

Record the existing lexer/parser behavior required by compilation and tooling:
strict and lenient parsing, comment preservation, node identities, metadata,
diagnostics, formatting inputs, and import extraction. Add black-box fixtures
for category parsing and token-tree capture before porting behavior.

### Stage 2 - Build the Talk frontend and ABI

Implement the syntax schema, lexer, token-tree capture, diagnostics, and parser
in macro-free Talk. Establish the versioned frontend service ABI and generated
Rust bridge. Produce the first checked-in artifact using the current compiler.

### Stage 3 - Differential validation

Run the Rust and Talk frontends over the same repository corpus, parser tests,
malformed-input fixtures, Unicode cases, and editor recovery cases. Compare
normalized tokens, trees, spans, metadata, and diagnostics. Differences require
an explicit language decision; migration does not silently bless whichever
implementation produced the new result.

### Stage 4 - Cut over every consumer

Route the compiler driver, formatter parse path, highlighter parse path, LSP,
REPL, package manifest parser, C embedding, Swift embedding, and browser
embedding through the frontend service. No consumer selects a parser by target
or feature flag.

### Stage 5 - Remove the Rust implementation

Delete the Rust lexer/parser implementation after all validation gates pass.
Keep only the generated ABI bridge and private result adapter. Establish the
stage-1/stage-2 fixed-point check as a required CI gate.

Only then does the procedural macro project begin.

## Consequences

- Talk has one owner for source grammar and parser recovery.
- Compiler parsing and macro embedded-Talk parsing cannot drift by using
  different implementations.
- Parser development uses Talk's own type, effect, ownership, and module
  systems, exposing deficiencies that matter for self-hosting.
- The compiler distribution includes a reviewed bootstrap bytecode artifact
  and its manifest.
- Frontend source changes require explicit artifact regeneration.
- Compiler startup and editor latency now include loading and invoking the
  bytecode frontend; performance must be measured during migration.
- The Rust/Talk ABI becomes a real trust seam and therefore requires validation,
  versioning, and generated bindings.
- The frontend source subset remains intentionally macro-free, even after
  macros exist, to keep the bootstrap graph acyclic.
- This project delays procedural macros, but removes the permanent duplicated
  grammar that would otherwise underlie them.

## Alternatives rejected

### Keep the Rust parser and mirror its API in Talk

Rejected because token kinds, parser categories, spans, and recovery behavior
would have two independently edited representations. Generated declarations
would reduce signature drift but leave the parser implementation and macro
view with different owners.

### Keep both parsers permanently and test for parity

Rejected because differential tests detect known cases but do not create one
semantic owner. Recovery and editor behavior would eventually diverge, and a
fallback would make failures target-dependent.

### Describe a grammar in Talk and generate a Rust parser

Rejected as the end state because a grammar description does not own parser
recovery, contextual parsing, metadata, or diagnostics unless it grows into a
second parser implementation language. Code generation may be useful inside
the Talk frontend, but the executable parser remains Talk code.

### Compile the frontend from source during every normal build

Rejected because it does not break the bootstrap cycle and makes ordinary
builds depend on an undeclared prior parser. Bootstrap regeneration must be an
explicit, reviewable operation.

### Let procedural macros provide the frontend parser

Rejected because parsing must precede macro discovery and expansion. The
frontend is the macro system's substrate and must not depend on it.

## Validation

The self-hosting project is complete when:

1. the canonical lexer and parser sources are macro-free `.tlk` files;
2. a versioned frontend artifact and manifest rebuild to a stage-2 fixed point;
3. CI rejects stale source, artifact, ABI descriptor, or generated bridge data;
4. strict parsing, lenient recovery, comments, spans, node identities,
   diagnostics, and metadata pass the existing parser and tooling suites;
5. the repository corpus and malformed-input corpus pass differential review;
6. every compiler and tooling consumer uses the frontend service;
7. no production path contains or selects the old Rust lexer/parser;
8. malformed or incompatible frontend artifacts and results fail closed;
9. frontend execution has no inline IR, `@unsafe`, or ambient host capability;
10. no frontend source constructs a `String` through raw allocation, and
    string building in the lexer and diagnostics path is linear;
11. `cargo check --workspace --exclude www` and
    `cargo test --workspace --exclude www` pass; and
12. measured parse and editor latency are recorded and accepted before cutover.

## Status

Accepted 2026-07-26 and implemented 2026-07-27 on branch
`self-hosted-frontend`. Stages 0 through 5 are complete; the implementation
record below is retained for validation and migration context.

### Stage 0 — done

`String.from_bytes`, `Int._toByte` (new `itob` IR op), `Substring:
Equatable<Substring>`, and `Array.pop`/`last`, each with tests.

### Host platform — done

- **Service compilation and the call ABI.** `compile_service(exports,
  allowed_effects)` compiles named public functions into a module export
  table (wire format v4, with v3 compatibility and validation on decode); `Executable::run_export`
  calls one on a fresh machine with scalar and string arguments and
  reads structured results (including strings) while the machine is
  alive. Each export wraps in the ordinary `_with_host` entry machinery,
  so effects behave exactly as in a script run.
- **Capability list.** An export's published effect row must stay within
  `allowed_effects`; typing is the denial, and no second host wrapper
  exists. Known gap: an effect reaching an export only through protocol
  dispatch vanishes into the generalized row tail and is not denied —
  the restrictive host `IO` implementation remains the runtime boundary,
  as section 7 already requires.
- **Budgets.** `Budgets { instructions, frames, memory_bytes }` on
  `run_export`; exhaustion is an ordinary VM error attributed to the
  call. Script runs are unchanged.
- **Determinism and provenance.** Byte-identical rebuilds are verified
  across separate compiler processes; `ArtifactManifest` records the
  wire-format version plus source and artifact digests, with fail-closed
  verification distinguishing version skew, artifact tampering, and
  source edits.
- **Bootstrap.** `talk bootstrap <dir> -o <artifact> --export …
  [--allow-effect …] [--check]` compiles the source set twice with fresh
  pipelines, requires the byte-identical fixed point, and writes the
  artifact and manifest together; `--check` is the CI gate. Until the
  self-hosted frontend drives parsing, the fixed point is a determinism
  guarantee; the command already has the stage-0/stage-1 shape.

### Stage 1 (freeze the frontend contract) — done

Normalized parse dumps (tokens, tree with spans and meta extents,
comments, diagnostics) with a golden corpus under `tests/parser/`;
public category entry points (`parse_expr`, `parse_pattern`,
`parse_type`, `parse_block_items` — whole-input, imports rejected in
block items); `parse_lenient` freezing the per-file degradation inside
the parser; token trees (`group`/`capture`, strict imbalance errors
carrying both spans); macro-expansion diagnostics evicted from
`ParserError` into `MacroError` so the parser's diagnostic schema has
one owner; and parser messages rewritten to be user-readable before
being pinned in the goldens.

### Stage 2 (the Talk frontend) — in progress

`stdlib/syntax/Lexer.tlk` implements the lexer and token trees. The `lex`
and `trees` validation exports reproduce the reference dumps
byte-for-byte over the whole corpus — `tests/parser/**` (including
unicode identifiers and lexer errors), `core/`, `stdlib/`, and both
example directories — with no known divergences.

The parser port is underway on the same differential loop, one dump
category at a time. The frontend is now a multi-file package —
`Lexer.tlk`, `Ast.tlk`, `Parser.tlk`, `Dump.tlk`, linked with ordinary
`use package::…` imports (verified to resolve for the bootstrap
command's in-memory sources). **Every dump category is now in**: all
seven corpus directories (`tests/parser` root, `unicode/`, `lenient/`,
`block/`, `expr/`, `pattern/`, `type/`) are harness-covered
byte-for-byte, alongside `lex` and `trees` over the whole corpus. The
slices, in landing order:

- **Block items**: let declarations, literal and binding patterns, the
  Pratt expression core (full operator precedence ladder, unary
  operators, calls with labeled arguments, close-paren recovery
  diagnostics), and import rejection, byte-identical to
  `dump_block_items` over its corpus directory.
- **Expressions**: the whole-input category entry, member access
  (named, positional, leading-dot, and the trailing-dot
  `Expr::Incomplete` recovery), tuples with both closer-recovery paths,
  block expressions with the block-argument rollback probe, and the
  malformed-expression error shapes.
- **Patterns**: the full pattern grammar except explicit generics —
  dotted variant paths, labeled payload fields, struct patterns with
  shorthand and rest, record patterns, or-patterns, tuples, and the
  leading-dot form.
- **Types**: the full annotation grammar except the static-value
  language — borrows and `*T`, function types with ownership-mode
  parameters (borrow-by-default applied at parse time) and effect rows,
  tuples, `?` and `[T]` sugar, record types, nominal paths with generic
  arguments (including the `>>` split for nested closers), and
  `any P<Assoc = T>`. Typed `let` declarations ride along in the
  block-items category.
- **Statements and control flow**: `match` with arm blocks and
  `-> expr` bodies, `if`/`else`/`else if` (boolean chains fold into
  nested statements with synthesized inner spans; pattern-bearing ifs
  desugar at parse time into two-arm matches with `@synthesized` arms,
  exactly like the reference), `loop`, `for`-in with iterable ownership
  markers and the block-arg pattern-replacement quirk (whose replaced
  pattern inherits the Parameter's inverted meta extents —
  `tokens=16..15` — pinned as-is), `return`/`break`/`continue`/
  `'continue`, assignment statements (which escape the reference's
  expression grammar as `Node::Stmt`; the port carries them in a
  one-slot field with a `require_expr` guard reproducing `into_expr`'s
  `parser.cannot-assign` at every expression-required site), range
  operators, array literals, subscripts (including subscript
  assignment), and the trailing-block context stack that keeps a
  control-flow header's `{` attached to its body. A member assignment's
  statement span starts at the RHS (the reference pushes its location
  after the `=`) — pinned, not fixed.
- **Declarations**: `func` (labels, ownership modes, generics with
  bounds and defaults, capture lists, effect rows, where clauses,
  signature-vs-body split in protocol bodies), `struct`/`enum`/
  `protocol` with tick attributes (`'heap`, `'linear`), conformance
  gating, and members (properties, inits, methods with `mut`/
  `consuming`/`static` and the explicit-`self` rejection), `extend`
  with binders and heads, enum variants (labels, multi-case lines, GADT
  results), `typealias`, `effect`, `associated`, top-level `macro`
  rules, and the full ADR 0042 `pub` admission matrix with its error
  ladder. The `Func` node renders its body's span with the
  declaration's extents as `tokens=` — the only place the corpus
  exercises meta extents besides the for-loop quirk.
- **The file category and the remaining directories**: the whole-file
  strict parse (`parse_with_comments`) with file-level imports, the
  comments section (the Talk lexer now preserves dropped line-comment
  spans), lexer-error surfacing as `parser.lexer` with the reference's
  1-based-line/0-based-CHARACTER-counted-column rendering (including
  the consume-before-error position for unexpected characters), and the
  reference's lazy-pull masking rule — a lex failure replaces a
  downstream parse error exactly when the parse's cursor reached the
  truncation point (its 2-token lookahead), modeled as
  `pos + 1 >= token_count` at failure time. `parse_lenient` wraps the
  same parse, degrading a hard failure to an empty tree plus one
  diagnostic.
- **Whole-file `core/` and `stdlib/` coverage**: everything the live
  corpus exercises from the former `unported` list, landed
  feature-by-feature against new pinned fixtures (a temporary
  env-gated survey test reported each file's first divergence until
  all 37 files were clean, then was deleted). Trailing-block calls
  (`foo { … }`, `foo(x) { y in … }`, and the popped parenthesized
  final block argument) with `$N` positional-parameter synthesis via a
  `max_positional_block_arg` walk (synthesized `Parameter
  @synthesized` nodes; trailing blocks themselves are not walked
  into); paren-less leading-string-argument calls; generic call
  arguments with the adjacency contract and `Expr::Constructor`
  references via `flatten_type_path` (per-segment argument lists,
  padded to the dotted path); `as` casts; postfix `?` propagation and
  `!` force-unwrap (whose hidden failure renders as
  `Expr::Unreachable` spanning the bang); float-lexed positional
  member chains (`x.0.1` splits into two members, both spanning the
  chain); `_:` argument labels and call-site ownership modes (which
  also veto the trailing-block pop); effect calls
  (`'io(request: …)`, `'alloc<Int>(n)` — the node's span starts after
  the sigil); record literals with `...spread` (the Talk lexer gained
  the reference's `DotDotDot` token; `{ x: Int in … }` in expression
  position stays a record-literal collision error, pinned);
  block-parameter type annotations (reachable only through
  closure-position blocks); let-else and or-pattern lets desugared to
  the reference's synthesized single/two-arm match with binder
  collection; multi-clause `if` folding in both positions — the
  else-block duplication that motivated the deep-copy deferral turned
  out to need only a value copy, since the reference's
  `freshened_block` renews node ids but never spans; `@handle`
  effect handlers (`Stmt::Handling`, span starting after the `@`);
  the full `@_ir` instruction set (disjoint dest/dest-less tables,
  every `ir_value` form including `void`; only binds render as dump
  children, and the node's span ends before the closing brace); and
  ADR 0035 `static N: Int` generic parameters with the
  uppercase-initial check. Static generic *arguments*, comparison
  predicates, static parameter defaults, and `[T; N]` inline-array
  types keep their `unported` markers — nothing in `core/`, `stdlib/`,
  or the corpus exercises them.

Grammar not yet ported fails with a distinctive `talk-parser.unported`
code so a divergence names the missing construct instead of silently
mismatching. The Talk AST stores nodes as plain values with
self-recursive links routed through arrays (region storage does not
scan array elements, so `'heap` nodes cannot sit in them); parse
results remain the real product, the dump renderer only its validation
view.

Several dump-format cleanups landed with the slices, each an
unreproducible-by-design leak removed before goldens could pin it: the
`duplicate node ids` line (reported the reference parser's internal
`NodeID` allocation — statement wrappers deliberately share their
payload expression's id); the missing-expression error that embedded
the `Debug` dump of the entire AST; `consume_any`'s expected-token
list rendered via `Debug` rather than as token spellings; the
record-pattern fallthrough error, which printed a token kind's `Debug`
form; the effect-row error, which printed a whole token's `Debug`
form; and the node-to-declaration conversion error, which printed the
entire offending node's `Debug` form (now just "could not convert node
to Decl", pinned by a stray-statement-in-struct fixture). Two behavior fixes rode along rather than being enshrined: a
token that cannot begin an expression now errors immediately, where the
reference previously spun the infix loop against a progress guard
(consuming nothing) and reported a misleading `infinite-loop`
diagnostic; and a struct pattern with a colon field no longer reports a
span skewed onto its last field (the field pushed a source location
that only the shorthand branch ever popped — a stale entry the pattern's
own span then consumed).

The Consequences section's prediction has already paid out: porting the
frontend exposed (and led to fixes for) two compiler bugs — a
recursive-group skeleton that lost parameter borrows under mutual
recursion, and a double release of borrowed match payloads bound through
loop elements.

Further compiler findings from the port — ALL FIXED OR RESOLVED
(2026-07-27, per the fix-before-moving-on rule):

- **`let x = f()?` loses its binding — STALE, could not reproduce.**
  Every variant (bare, annotated, method-chained, tuple/array element
  position) now binds correctly; the historical symptom reproduces
  only when a leading-dot line follows the `let` and reads as member
  continuation of the initializer (reference-faithful parsing, making
  the binding self-referential), which is a spelling issue, not a
  resolution bug. Pinned as `parity_propagate_in_let`. The Talk
  parser's explicit failure field stays — it predates the fix and is
  the clearer design for a fail-closed parser.
- **Cross-enum variant names break leading-dot if-lets — FIXED.**
  `check_variant_pattern`'s metavariable case only had the
  exactly-one-owner heuristic; several owners bailed with "enum not
  yet known" even though the scrutinee's member constraint would pin
  the enum one solver step later. Now the ambiguous case defers: the
  sub-patterns bind fresh payload variables and a `HasVariant`
  constraint hands resolution to the solver — the same machinery
  leading-dot construction and for-loop elements already used
  (`defer_variant_pattern`, src/types/generate/pattern.rs). No GADT
  refinement flows from the deferred path (an unknown head has no
  givens). Pinned as `parity_cross_enum_leading_dot`.
- **Borrow donation misses array literals in argument position —
  STALE, could not reproduce.** Fixed by the uniform-borrow-donation
  change (the deleted cheapness gate); call-argument, constructor,
  and method-context shapes all accept. Pinned as
  `parity_array_literal_borrow_donation`.
- **Irrefutable if-let warning spans are useless — FIXED.** The
  unreachable arm was the desugared conditional's SYNTHESIZED wildcard
  (span = SYNTH → rendered 1:1). Synthesized unreachable arms now
  route to a dedicated `IrrefutableConditionalPattern` warning ("This
  pattern always matches: the implicit else branch never runs")
  attributed to the nearest preceding written pattern
  (src/types/generate/mod.rs check_matches). Real written arms keep
  `UnreachableMatchArm`. Test:
  `irrefutable_if_let_warns_at_the_written_pattern`.
- **Same-statement double consume of one owned local — FIXED.**
  `Pair(a: xs, b: xs)` in one call: every read precedes the first
  consume, so use counting saw no remaining uses and BOTH consumes
  moved (checker-accepted double release; the MIR balance verifier
  ICE'd). Now `consume_operand` detects the re-consume of an
  already-moved local: ordinary values share (retain + Def/Move flow
  events — the same net shape as the sequential two-let spelling under
  Rule 1), linear and unique values reject with "use of moved value:
  consumed twice in one call". Fixtures:
  `allows_owned_value_in_two_constructor_slots_in_one_call`,
  `rejects_linear_value_consumed_twice_in_one_call` (flow corpus).

**`core/` and `stdlib/` are now parse-covered whole-file**: both
directories sit in the harness's parse-category table alongside the
seven `tests/parser` directories, every file byte-identical.

**The grammar port is complete — no `unported` markers remain.** The
final sweep landed the pieces the live corpus never exercised, each
against new pinned fixtures: the full ADR 0035 static language
(static generic arguments with the `+`/`-`/`*` index grammar,
parenthesized groups and the `(N) * 2` reinterpretation, unqualified
cases, static parameter defaults, and `<`/`<=` comparison
where-predicates — `StaticExpr` is not a dump-visited node, so only
nested Path annotations render, at the surrounding depth); `[T; N]`
inline-array types (an implied `InlineArray` head, like `[T]` implies
`Array`); qualified pattern heads with per-segment generic arguments
(`Opt<Int>.some(x)`, `Outer<Int>.Inner { … }`, with the reference's
variant-takes-no-generics and bare-generic-head errors pinned — their
`actual` fields turn out to be dead: `UnexpectedToken`'s Display names
the token itself, so no Debug leak existed); the `unreachable` and
`#macro(...)` expression prefixes; and `@"…"` quoted identifiers in
the Talk lexer (an ordinary Identifier token whose full span includes
the `@` and quotes while its lexeme excludes them, with the
empty/unterminated/backslash error positions pinned). With every reference prefix handler ported, the
`talk-parser.unported` machinery itself is deleted — the prefix
fallthrough now reports the reference's own expected-an-expression
error.

**The checked-in artifact and its regeneration loop are live** (§2–3):
`bootstrap/frontend.tbc`, `frontend.manifest`, and `frontend.abi` are
generated by the bare `talk bootstrap` command through one frontend
profile (`compiling::frontend` owns the source set, the eight service
exports, the `alloc`/`panic` capability list, the schema root, and the
artifact paths — the CLI, the differential harness, and the loader all
go through it). Regeneration requires the stage-1/stage-2 fixed point,
and a fresh process reproduces the artifact byte-for-byte (the first
cross-process determinism check — it held). Default tests reject inconsistent
checked-in state with a fast digest test
(`checked_in_frontend_artifact_matches_sources` — manifest vs sources, bytes,
ABI text, and bytecode format), and they verify that the artifact loads and
runs. Compiler codegen drift does not fail `cargo test`; the explicit
`talk bootstrap --check` workflow owns that repository-staleness gate.
`compiling::frontend::load` is the fail-closed loading seam Stage 4 consumers
will call: manifest verification
against sources, image, ABI descriptor, and format version, then
decode — no fallback.

**The ABI descriptor exists** (§5, first half of the bridge):
`compiling::abi::describe` walks the typed frontend program from the
`ParseOutcome` schema root and renders every reachable frontend-owned
type — 49 structs and enums, fields and variants in declaration order,
each stamped with the symbol identity its runtime values carry —
into `bootstrap/frontend.abi`. Core types cross as leaf names
(`String`, `Int`, `[T]`, `T?`); functions, borrows, and open rows fail
closed; generic schema types are rejected. The descriptor is computed
in both bootstrap stages (the fixed point covers it), and its digest
rides in the manifest.

**Structured results cross the boundary, and the validator holds the
seam** (§5, second half of the bridge): the artifact now exports
`parse_file_source`, returning the `ParseOutcome` value graph itself
rather than rendered text. The runtime gained three narrow bridge
accessors on `RunOutcome` (a memory word, a raw byte, a boxed-arena
slot) — enough to walk array storage out of a returned value.
`compiling::abi::parse_schema` reads the checked-in descriptor back
into a schema model, and `compiling::bridge::ResultValidator` walks a
returned result against it fail-closed: record identities, variant
tags, payload arities, field counts, array bounds and element
references, `Optional` shape, and string UTF-8 all checked; unknown
types and malformed references are errors, per §5's trust-seam
requirement. `structured_results_validate_over_corpus` runs every
corpus file (parser fixtures, `core/`, `stdlib/`, both example
directories) through the checked-in artifact's structured export and
validates the result — the seam is exercised by real crossings, not
just the schema's round trip.

**The adapter is in, round-trip proven**: `compiling::bridge::adapt`
converts a validated result into the compiler's own `parsing` AST —
node ids minted on the Rust side, node meta recorded exactly where
token extents diverge from spans (`Func` declaration extents, the
for-loop pattern replacement), the trailing-block / spread / receiver
one-element-array conventions unwrapped back into options and boxes,
positional call-arg labels reconstructed by ordinal, and the full
`@_ir` instruction set rebuilt. The dump machinery gained a
`render_bridged` seam (tree, comments, and diagnostics sections over
an already-built AST, byte-compatible with the parser's own path), and
`bridged_results_render_identically_over_corpus` proves the whole
pipeline: every corpus file's structured result, bridged and rendered,
is byte-identical to what the Rust parser's own AST renders — with the
token section excluded on both sides, since tokens do not cross the
ABI.

**The field-completeness pass is DONE and ungated**:
`bridged_results_carry_full_fidelity_over_corpus` Debug-renders the
bridged AST and the Rust parser's AST with node identities normalized
away (including `Expr`'s inline compact-Debug ids) and requires them
identical — every span, label, mode, and origin, not just what the
dump shows; it runs unconditionally and is green over the whole
corpus. The sweep added name/label/mode span Ints and the
`bare_string` flag across ~25 node kinds in `Ast.tlk` (enum cases
carry `Int` span pairs positionally; structs carry `*_start`/`*_end`
fields; `-1` = none/synthesized), captured in `Parser.tlk` via an
`identifier_token()` helper plus tuple-returning `arg_mode`/
`param_mode`, and threaded through the adapter (`opt_span`,
`int_array` for `[Int]` payloads — the generic `array()` reads boxed
handles and must not touch raw-word arrays). Reference span quirks
pinned and reproduced: a positional call argument's `label_span` is
the argument's own span; a positional member's (`x.0`) span is the
FOLLOWING token's; a float-split member (`x.0.1`) gets digit
sub-spans; `use` path spans end at the START of the token after the
path; macro `$param` spans include the sigil; `[T]` sugar's Array head
has a synthesized name span while `T?` sugar's Optional name span is
the node's own span; `consume mut` mode spans cover both words;
effect-name token spans include the `'` sigil while their lexeme spans
exclude it. One reference cleanup (fix-not-enshrine): the
anonymous-func fallback name was a Debug leak
(`#fn_Some(Token { .. })`, baking token line/col into a *name*); the
reference now mints position-keyed `#fn_<start>_<end>` (the resolver
only depends on the `#fn_` prefix) and the frontend reproduces it.
Separately, consumer scouting
found what the formatter and LSP need beyond spans: per-node meta
token positions *and lines*, and per-node identifier token lists.

**Decided: the frontend owns full meta (option A).** Parse results
will carry it; the adapter stays a converter. The architecture, sized
against the reference's actual machinery rather than a wholesale
location-stack port:

- The reference's meta start/end tokens are redundant with spans
  (`span.start` *is* `meta.start.start` by construction, and the port
  reproduces every span byte-for-byte), so a Talk-side **post-parse
  annotator** recovers them from the token stream: the token at
  `span.start`, the token ending at `span.end` — with the `>>`-split
  closers as the known special case. Token line/col (the reference
  stamps them at `make()` time: 0-based line, character-counted col,
  reset on newline) are computed by a position pass over the token
  list. This derivation runs *inside the frontend*, so §6's
  adapter-must-not-reinterpret rule is untouched.
- The one irreducible new recording is the **identifier log**: the
  reference pushes identifier tokens onto the *top* location-stack
  frame from exactly three ports — `identifier()`, and `consume`/
  `consume_any` when the consumed kind is Identifier. The Talk parser
  mirrors those three ports into a flat append-only log; the
  annotator attributes each logged token to the deepest meta-bearing
  node whose span contains it (children claim theirs first), which
  matches top-of-stack attribution for every construct analyzed —
  and the gate below adjudicates any residue empirically, including
  the id-sharing statement wrappers whose meta the payload owns.
- `ParseOutcome` gains a `metas` array in the canonical pre-order the
  bridge adapter already walks; the adapter zips them onto the nodes
  it builds (converting token kinds through a full kind table),
  populating `NodeMetaStorage` for every node instead of the current
  sparse two cases.
- Validation: the `TALK_FIDELITY` gate grows a meta comparison —
  bridged versus Rust-parsed meta rendered in tree order — holding
  meta to the same byte-identical standard as everything else.

**Meta slices A and B are DONE**: `ParseOutcome.metas` carries one
entry per adapter-constructed node (pre-order, children in Ast
payload order), produced by a Talk-side deriving annotator — the
token at `span.start`, the token ending at `span.end` (with the
`>>`-split second-half Greater fabricated at full-`>>` ends), and
line/col from a position pass (state at each token's END,
character-counted columns). The adapter zips the stream at every
adapt-function entry (fail-closed if it runs dry) and fills
`NodeMetaStorage` for every node; the fabricated `extent_meta`
machinery is deleted. Nodes the reference builds literally with real
spans carry a no-meta marker: the borrow-by-default wrapper (a
`.borrow` sharing its inner's exact span), everything below a
desugaring-copied block (`Block.copied`, set by `copy_block`), the
force-unwrap hidden failure expression, and all synthesized spans. A
`TALK_META=1`-gated comparison in the fidelity test pairs nodes
positionally across the two Debug renderings and requires start/end
meta tokens byte-identical — green over the whole corpus.

**Slice C — identifier attribution — is DONE and the gate is
dropped**: the meta comparison (start/end tokens, line/col, and
identifier lists) runs unconditionally in the fidelity test and is
green over the whole corpus. Attribution derives the reference's
top-of-stack semantics from the flat log: each node claims the
unclaimed logged tokens inside its extent after its children claimed
theirs, taking at most one entry per token (preferring the last — a
rolled-back block-args probe re-consumes, and the reference leaves
the probe's entry in the block's frame, so probe-tagged entries are
claimable only by blocks). Wrappers that share the payload's node id
in the reference copy its list: expression statements, the inline-IR
chain, method declarations, and init requirements — while plain func
declarations, signature declarations, and method requirements keep
separate frames. Constructor expressions discard their path-segment
identifiers, whose owning nodes the reference's `Path<Args>`
reinterpretation orphans.

**Stage 4's driver seam is BUILT and measured; activation waits on a
core parse cache.** `frontend::parse_source` (a process-wide session
verifying and decoding the checked-in artifact and parsing its ABI
once, then `run_export` + `bridge::adapt` per file, with per-file
`FileID` threaded through every minted id and span) and the driver's `frontend_parse` assembly
(AST construction, id-generator continuation above the bridge's
watermark, failures and recovery diagnostics as the new
`ParserError::Frontend`) are landed and pinned by
`frontend_parse_matches`; the strict arm is one line away from
activation. Two findings from wiring it:

- **The bridge must not consult host core.** Resolving Optional's
  runtime identity by compiling core deadlocked the moment the driver
  parsed *core itself* through the bridge (the lazy core compile
  re-entered its own initializer). The ABI descriptor now carries the
  artifact's own Optional identity (`optional: enum:M.L`, required by
  `parse_schema`), so validation is self-contained — and identity
  changes in future compilers regenerate cleanly, because the old
  descriptor still names the old artifact's identity. The one-time
  migration regenerated the artifacts with the strict arm temporarily
  on the Rust parser.
- **Measured cost (2026-07-27, debug build): ~450ms per file through
  the interpreted artifact — ~13s per `talk` invocation** (28 core/
  stdlib files parse per compile), resolved by the systemic fix
  below.

**The driver cutover is ACTIVE, carried by compiled-core and
compiled-stdlib disk caches.** Core's and stdlib's compile products
are pure functions of (sources, compiler), so
`target/.talk-cache/{core,stdlib}.bin` store the serialized
`(Module, TypedProgram)` products keyed by a SHA-256 of the source
contents (the `TALK_CORE_PATH`/`TALK_STDLIB_PATH` overrides hash the
on-disk files) plus this binary's identity — the running executable's
modification stamp and length — so ANY compiler rebuild invalidates
the cache; the historical `core.bin` trap of hashing sources only is
designed out. The serialization sweep made `TypedProgram` (typed
files, `ResolvedNames` minus the editor-only `scopes` and
`diagnostics`, `TypeOutput`) and the parse-node closure serde-
serializable; writes are atomic (process-unique temp + rename) for
concurrent cache-cold processes. Measured: cold `talk run` pays the
one-time ~13s interpreted core parse per compiler build; **warm runs
are 0.32s — 4.5× faster than the 1.4s pre-cutover baseline** (core's
whole parse/resolve/type cost is gone), and the integration suite
dropped from ~117s to ~57s. The strict compile path now parses
exclusively through the frontend artifact; the lenient editor path
migrates with the LSP consumer.

**Every parse consumer is cut over.** `frontend::parse_ast` (strict),
`parse_ast_with_comments` (the formatter's entry — comments cross the
ABI as byte ranges), and `parse_ast_lenient` (the frozen editor
contract: a hard failure degrades to an empty AST carrying the
failure as a diagnostic — no new export was needed, since recoverable
problems already come back as diagnostics from the strict parse)
serve the compiler driver's both arms, the
package lockfile reader, the REPL's incomplete-input probe
(`is_incomplete_input` recognizes the bridged failures by code and
frozen message spellings), the formatter, and the highlighter's parse
side. The wasm and C embeddings route through `format_string` and are
covered transitively — enabled by **embedding the artifact triplet in
the compiler binary** (`include_bytes!` of
`bootstrap/frontend.{tbc,manifest,abi}`): the immutable decoded module and
ABI are shared by every compiler thread. Bytecode constant pools use a
scalar-only runtime type, rather than local `Rc`-backed `Value`s, so the
module is `Send + Sync` without adding synchronization to VM values.
The runtime session needs no filesystem, installed binaries and wasm
are self-contained, and in a development checkout the embedded manifest is additionally verified
against the on-disk frontend sources, so editing them without
regeneration and rebuild fails closed.

**Structured diagnostics cross the ABI, and the LSP is cut over.**
`Fail` carries a source position and an optional expected token kind —
one span plus one kind turned out to cover everything the editor
reads: diagnostic ranges (`parser_error_range` reads the bridged span
directly) and all three parser quick fixes (delimiter/else insertion
keys on the expected kind; the legacy-`public` rewrite and the
explicit-`self` removal key on the span). The parser populates them at
the failure sites, which already hold the offending tokens; every
other diagnostic defaults to no position, matching the reference's
fallback range. The LSP's parser workspace now parses through
`parse_ast_lenient` like every other consumer. One correction along
the way: the embedded session verifies only its own manifest
consistency — checking disk sources from the runtime session broke
bootstrap's stage 0, whose entire point is parsing edited frontend
sources with the old artifact; staleness lives in the harness gates.

**The token-level consumers are cut over** through a new `lex_tokens`
export: the frontend returns the token stream as `MetaToken`s (already
in the schema), with comments merged back in as a new `line_comment`
token kind and a sentinel marking scan failures. The highlighter's
lexed pass, both LSP code-action delimiter scans, identifier
validation in rename (valid = the whole string lexes to exactly one
identifier), and the REPL's declaration probe all read
`frontend::lex`. No production code path touches the Rust lexer or
parser any longer.

**Stage 5 is COMPLETE: the Rust lexer and parser are deleted**
(−14,654 lines net in the final slice). The golden corpus now runs
the frontend's own dump exports against the pinned `expected/` files;
the differential harness's reference side is retired, with regeneration and
fixed-point validation kept in the explicit `talk bootstrap --check` workflow;
the bridged
fidelity and round-trip comparisons — migration instruments whose
job was done — are deleted with their reference; and the parser test
suite went with its subject, leaving a slim assertion-DSL module
whose `parse` runs the frontend. Kept: `Token`/`TokenKind`, the
keyword table (the formatter reads it), `LexerError` and
`BlockContext` (moved to surviving modules; `ParserError` payloads),
and the node/meta/span data model. Talk is now the single owner of
the source grammar, end to end — the precondition this ADR set for
the procedural-macro project.

**The canonical sources are also the public `syntax` stdlib module.**
`stdlib/syntax/{Lexer,Ast,Parser,Dump}.tlk` is the one source set used
both by bootstrap regeneration and by ordinary Talk imports. On first import,
the stdlib compiles and separately caches the four files as one module, so
consumers can import the typed
parser API directly with `use syntax::{ parse_expr_source, Item }`; the
checked-in `bootstrap/frontend.*` artifacts continue to break the compiler's
bootstrap cycle.
