# Commit 090: `40593fdf` - Wave 2: record patterns and record destructuring

| Field | Value |
|---|---|
| Commit | `40593fdfed0c52254c8cdc92798befea6fa56ec4` |
| Parent reviewed | `c8c4d005c2159a87ef70ca8103647a997573e5e4` |
| Author date | 2026-07-17T01:37:42-07:00 |
| Author | Pat Nakajima |
| Patch size | 4 files, +441 / -97 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

One backend helper (record_cells) owns the name-to-slot rule; match
tests, owned-match settlement, let destructuring, and the global-slot
walk expand records to positional cells over the existing tuple
machinery. label: pattern binds the label as well as the sub-pattern,
matching the reference lowering; open rows and double-ownership cells
reject fail-closed. Ports the reference's record pins and pins the
StructuralTyping example in G5. Deepening pass: variant_case dedupes
variant tag/payload resolution across the test and settle arms;
tuple_element_tys and strip_borrows replace hand-rolled copies on the
pattern paths.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: A: 1, M: 3.
- Production Rust: 1 files (+336/-96): `src/backend/mir.rs`.
- Tests and test oracles: 2 files (+87/-1): `tests/examples/expected/StructuralTyping.stdout`, `tests/talk_tests.rs`.
- Documentation and plans: 1 files (+18/-0): `docs/lean-backend-rebuild-plan.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 336 | 96 |
| `tests/talk_tests.rs` | 86 | 1 |
| `docs/lean-backend-rebuild-plan.md` | 18 | 0 |
| `tests/examples/expected/StructuralTyping.stdout` | 1 | 0 |

### Representative declarations touched

- `fn free_locals(nodes: &[&Node], enclosing: &FxHashMap<Symbol, LocalId>) -> Vec<S`
- `fn pattern_bindings_with_tys(pattern: &Pattern, ty: &Ty) -> Vec<(Symbol, Ty)> {`
- `fn pattern_bind_symbols(pattern: &Pattern) -> Vec<Symbol> {`
- `fn strip_borrows`
- `fn tuple_element_tys`
- `struct RecordCell`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn record_cells`
- `fn variant_case`
- `fn run_renders_a_tuple_result_in_talk_syntax() {`
- `fn run_matches_record_patterns`
- `fn run_destructures_records_with_let`
- `fn examples_corpus_matches_frozen_stdout() {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (12s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `run_matches_record_patterns`, `run_destructures_records_with_let`.
- Added Talk/expected-output fixtures: `tests/examples/expected/StructuralTyping.stdout`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

Acceptable within the branch sequence. No commit-local changes are requested.
