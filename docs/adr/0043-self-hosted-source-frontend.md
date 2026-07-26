# 0043 - Self-host the source frontend before procedural macros

Status: proposed

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

This is a separate architecture project. Hiding it inside the procedural macro
implementation would combine parser replacement, bootstrap design, syntax
hygiene, compile-time execution, and package integration in one migration.

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

The frontend sources remain macro-free. They may use the ordinary language
subset supported by the checked-in bootstrap artifact, but compiling the
frontend may never require expanding a user macro. This is the permanent
bootstrap kernel boundary.

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
lex
capture_token_tree
parse_file
parse_expr
parse_pattern
parse_type
parse_block_items
```

The concrete names may differ, but the capabilities are required. Parse
operations accept an explicit mode for strict compilation versus lenient
editor recovery and an explicit trivia/comment policy where relevant.

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
10. `cargo check --workspace --exclude www` and
    `cargo test --workspace --exclude www` pass; and
11. measured parse and editor latency are recorded and accepted before cutover.
