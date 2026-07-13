# Single sources of truth: inventory and consolidation queue

Status: pass in progress (2026-07-12). Five-subsystem audit complete;
first four consolidations landed (marker field-check → conformance
rows, parser `condition()`, parser `at_implicit_statement_end()`,
unreached-block drop classification). Open items below, ranked.

## Context

A full-codebase audit for multiple-source-of-truth defects — the same
judgment computed, stored, or spelled in more than one place, such that
the copies can disagree. This is the systemic condition behind the
talk-syntax port findings (P1/P2 were duplicated condition parsing,
P10/P16 a duplicated conformance judgment, P4–P6 a duplicated ownership
judgment) and behind Track 7 of `ownership-soundness-plan.md`, which
this extends beyond the ownership system.

Line numbers were verified on the 2026-07-12 working tree and will
drift; symbol names are the stable anchors.

## Landed (verified on disk, all with tests)

- **Marker (Copy/CheapClone) field-check** consults conformance rows
  and their where-clause contexts instead of a hand-rolled
  `grade_of`/`has_bare_conformance` + per-argument rule
  (`types/generate/collect.rs::satisfies_marker`,
  `marker_context_satisfied`; `catalog.rs` gained `intrinsic_copy` and
  the `grade_of` decomposition). Fixes port findings P10 and P16.
- **One `condition()` helper** for `if`-stmt, `if`-expr, and `loop`
  (`parsing/parser.rs`) — was three spellings, one missing the
  `ParseContext` push and all three capping precedence at `Or`. Fixes
  P1 (`||` in conditions) and P2 (expr-`if` trailing-block misparse).
  Assignment-in-condition is a clean `CannotAssign`.
- **One `at_implicit_statement_end()`** shared by `return`/`continue`
  (was two diverged token lists). Fixes P3.
- **Unreached-block drop candidates classify `Dead`**
  (`flow/cfg.rs::check_body`, after the Record pass): the recording
  pass only visits fixpoint-reached blocks, so candidates at a
  dataflow-unreachable join (match whose arms all `return`) reached
  lowering unelaborated and tripped the no-silent-fallback assertion.
- **O3 landed**: `flow/grades.rs::is_cheap_clone` and clone-witness
  selection (`solve/member.rs`) now decide from
  `catalog.cheap_clone_rows` — conformance rows WITH their where-clause
  contexts — instead of the context-blind bare-key lookup; the full
  marker judgment (`ty_satisfies_marker`) moved from `CatalogBuilder`
  to `TypeCatalog` so collect, flow, and member selection share one
  spelling. A conditional row whose context fails no longer legalizes
  tier-2 extraction (regression pair in types_tests).
- **O4 landed**: `catalog.coerce_kind` / `bounds_coerce_kind` classify
  tier-2 once; the four `coerce_clones` sites (`solve/unify.rs`,
  `solve/mod.rs` Param+Nominal, `generate/finalize.rs`) and
  `grades.rs::param_copies_out_of_borrow` map from them.
  `copies_out_of_borrow` delegates.
- **O5 landed**: `MoveState::borrowed_root_perm` is the one
  consultation for "does this root name borrowed storage"; both
  move-out-of-borrow spellings (`loans.rs`, `moves.rs::take_expr`)
  read through it.
- Previously landed by the wave-2 work, verified during the audit:
  M2 (shadow drop authority — `Ctx::drop_stack` demoted to metadata),
  M4 (borrow/CheapClone predicate re-spellings → `GradeView`),
  M6 (embedded-body context → one `StatementScope` swap),
  M3 (node-type triad documented + guarded; `binder_ty` the binder
  authority), place resolution (`flow/place.rs`, single definition).

## Open inventory, ranked by leverage

### O1. Pattern-compiler ownership model (LARGE — needs design)

The one remaining place drops are emitted outside flow's authority.
`lower/patterns.rs` computes its own per-occurrence `borrowed` flag
(`Occurrence::new`) and `WildcardCell::{Drop,Ignore}` model, and
`leaf` calls `lower_drop_value_then` directly — no
`DropElaboration` gate. `lower/mir.rs::arm_release_binders` is a third
binder-ownership walk. `patterns.rs` itself diagnoses "pattern
alternatives disagree on binder ownership" — the code anticipates its
own copies disagreeing. This is the S3/B8 enum-payload double-free
surface (port findings P4–P6).

Shape: flow mints per-occurrence and arm-binder `DropCandidate`s with
elaborations; `patterns.rs::leaf`/`make_arm` consume them through
`lower_candidate_drop_then` instead of deciding locally.

### O2. check/LSP vs run/test/build pipelines (MEDIUM-LARGE)

- `talk check` is not package-aware: it builds one flat `Workspace`
  module (`analysis/workspace.rs`), so per-module compilation and
  instantiation-forced solving from test files never happen — the
  "check passes, test fails" class (port P8, P15's discrepancy).
  LSP diagnostics = check diagnostics, same blindness.
- The parse→resolve→type_check→(gate)→lower sequence is hand-spelled
  five times: `bin/talk.rs` (run), `driver.rs::compile_bytecode_sources`
  and `lower_for_display`, `package.rs::lower`,
  `testing.rs::compile_sources`.
- Diagnostics render four ways: `cli/diagnostics.rs` (pretty),
  raw `{:?}` Debug (single-file `talk run`), joined `.to_string()`
  (package paths), `lsp_diagnostic_for_analysis`. Single-file `run`
  printing Debug output is user-visible today.

Shape: one `Driver` front-end shared by check and build (check opts
out of lowering explicitly, or better, opts IN so lowering-stage
diagnostics reach editors); `cli::diagnostics` the only renderer.

### O3–O5: landed (see the Landed list above)

### O2a. Lowering fallthroughs that should be typing diagnostics (SMALL, residual)

Bare method references on VALUE receivers (`"fizz".add`) are now a real
typing diagnostic (`type.method-reference`, visible to check/LSP with a
span) instead of lowering's "member is not a stored field" internal
error. Residual: TYPE-name receivers — a bare payload-carrying variant
constructor (`let f = Optional.some`) or static method used as a value —
still reach the lowering fallthrough (`lower/mod.rs` Member arm →
`values.rs::field_read` → None). Scoped out to keep `Optional.none`
(payload-less variant values, legal everywhere) safe; the fix wants the
variant/static member machinery to classify value-position uses the
same way. Principle worth keeping: `self.diagnostics.push(format!(...))`
in `src/lower/` is an internal-error channel, not a user diagnostic —
anything a user can trigger belongs in typing with a node id.

### O6. Field/payload enumeration walk (MEDIUM)

The θ-substituting struct-field/enum-payload walk exists 3-4×:
`GradeView::payload_types`, `field_types_for`
(`lower/statements.rs`), `lower_enum_payloads_then`, plus
`collect.rs::marker_checked_fields`. They agree by construction, but
teardown emits positional `GetField(index)`/`GetPayload(index)` — an
ordering drift frees the wrong slot while whole-type `needs_drop`
still matches. Shape: one public enumerator (extend
`GradeView::payload_types`) consumed by all walks.

### O7. Balance-verifier drift-proofing (MEDIUM)

`lambda_g/balance.rs` intentionally re-derives balance, but it
pattern-matches hardcoded lowering shapes: `free(get_field(...))`
chains, `cell_new(const bool)` drop flags, `Extract(var, arity)`
return continuations, the scheduler's chunk grouping. A lowering shape
change silently degrades to skips (or misses, e.g. the F-A retain
blind spot). Shape: named glue-shape constructors/predicates in
`lambda_g/` used by both emitter and verifier; plus one per-`Op`
ownership-effect table (`expr.rs` doc comments promoted to a spec)
that `eval.rs`, `interp.rs`, and `balance.rs` all cite, with an
exhaustiveness test so a new op can't be forgotten by one of the four.

### O8. Fuzzer DEFAULT_SKIPS as shadow bug tracker (MEDIUM)

`tests/fuzz.rs::DEFAULT_SKIPS` duplicates the plan doc's F-findings
(prose + index lists in two places). Shape: each skipped index becomes
a named expected-fail test that flips red when fixed; the skip array
derives from those names.

### O9. Keyword set (MEDIUM)

Four in-tree membership copies: `keywords.rs` (authority),
`precedence.rs` handler table, `highlighter.rs` classification,
`formatter.rs` re-spelling keyword STRINGS by hand (a rename in
keywords.rs would silently format the old word). The shipped editor
grammars disagree with each other today: `dev/editors/nvim/syntax`
lists the full set, the vscode tmLanguage regex is missing
`for in where effect handling consuming mut static public associated
typealias as`. Shape: a `TokenKind → &'static str` inverse of
keywords.rs the formatter renders from; grammars generated from the
same table.

### O10. Small ones (each < half a day)

- `collect.rs` `Storage|Array` CheapClone carve-out covers Array and
  Storage but not String (String's CheapClone flows through the core
  declaration path instead — two paths for the same judgment). Key
  off a buffer attribute instead of symbol identity, or add String.
- String-family predicate spelled twice (`exhaustiveness.rs`,
  `solve/mod.rs`).
- `.test.tlk` suffix spelled 3× (`testing.rs`, `analysis/workspace.rs`,
  `name_resolver.rs`); test-root policy split between `package.rs` and
  the loose runner.
- `bin/talk.rs`: `LLM_REFERENCE` hand-restates the clap CLI surface;
  `--offline`/package-gate/module-name-default copy-pasted per
  subcommand; format width `80` spelled 3×.
- ADR status headers: 0023 (packages) and 0022 (sugar) say "proposed"
  though shipped; 0024/0026 have no Status line.
- `driver.rs::qualified_local_module_path` re-implements a check that
  belongs on `LocalModulePaths`.

## Verified non-findings (checked, intentionally plural or already single)

Two execution engines (differential oracle — the redundancy is the
test); balance verifier independence (its purpose); `testing.rs` vs
`test_utils.rs` (different jobs); per-phase error enums (each message
lives once); `common/text.rs` span math; `compiling/module_path.rs`;
compiler version (clap derives from Cargo.toml); package-manifest
parsing (one parser, template re-parses through it); the
declared-vs-structural Copy dual (`grades.rs` header — deliberate,
but its CONSUMERS must not re-derive either side, which is what O3
finishes). Note: `ownership-soundness-plan.md`'s header residual list
("F-A/F-C/F-D" + R9) is consistent — F-B is R9's repro; an earlier
draft of this audit misflagged it.

## Suggested order

O6 → O2 → O10 as filler → O7/O8 alongside → O9 when touching the
formatter anyway → O1 last, behind a design conversation, with the
S3/B8 repros as its acceptance tests.

## Port findings still open (tracked in talk-syntax/FINDINGS.md)

P4–P6 (borrowed-payload match double frees — O1's acceptance
criteria), P7 (mutually-recursive dump ICE), P8 (cross-SCC inference
ordering; O2 adjacent), P9 (`'heap` values in Arrays), P11 (`mut`
param positions), P12 (user `show()` loses to derived), P13/P14 (core
Array/parse gaps), P15's for-loop half (implicit copyability not
reaching for-binder positions).
