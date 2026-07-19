# Commit 076: `d5e822df` - Close every reachable backend gap (group F)

| Field | Value |
|---|---|
| Commit | `d5e822df2fe1803703bd0edec0f410014f7addbe` |
| Parent reviewed | `6dfabcc21200c32fab7cc19f405debc5f49519ef` |
| Author date | 2026-07-16T16:30:31-07:00 |
| Author | Pat Nakajima |
| Patch size | 4 files, +1220 / -249 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

Probe-driven sweep: every backend rejection was tested against the
frontend; whatever typing accepts now executes, each shape pinned by a
black-box test.

- Witness edges: closures inherit their frame's witnesses and
  conformance dictionaries through their environments; glue for
  compound rigid types captures inner witnesses (compound re-performs
  work).
- Constrained effect generics: full conformance-dictionary passing
  (Wadler & Blott, POPL 1989) — requirement closures ride after
  [drop, retain], so one clause body calls requirements on every
  instantiation and packs rigid values into existentials from the
  same dictionary.
- Enum retains: CheapClone of payload enums dispatches on the tag.
- Place chains: nested projection assignment (o.inner.v = 5) and mut
  arguments naming projected places (bump(mut b.n)); copy-on-write
  records write back up value links, stopping at 'heap links.
- Record rows: label-sorted tuple layout — reads, assignment (tuple
  rebuild), drop/retain/copy glue, witness walks.
- Named-entry globals get the script's LINK-02 slot discipline
  (ordered init, non-literal initializers, mutation, teardown);
  function values stored in globals call indirectly.

[Commit body truncated here; the patch inventory below is based on the complete diff.]

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 4.
- Production Rust: 1 files (+1070/-247): `src/backend/mir.rs`.
- Tests and test oracles: 1 files (+92/-0): `tests/talk_tests.rs`.
- Documentation and plans: 2 files (+58/-2): `docs/backend-parity-ledger.md`, `docs/lean-rebuild-wave-reports.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 1070 | 247 |
| `tests/talk_tests.rs` | 92 | 0 |
| `docs/lean-rebuild-wave-reports.md` | 49 | 0 |
| `docs/backend-parity-ledger.md` | 9 | 2 |

### Representative declarations touched

- `fn contains_buffer_guarded(`
- `fn needs_drop_inner(builder: &ProgramBuilder<'_>, ty: &Ty, borrowed: bool) -> bo`
- `fn is_linear(builder: &ProgramBuilder<'_>, ty: &Ty) -> bool {`
- `fn contains_object_guarded(`
- `fn free_locals(`
- `fn pattern_bindings_with_tys`
- `fn ty_has_projection(ty: &Ty) -> bool {`
- `struct PlaceChain`
- `struct PlaceLink`
- `fn witness_params(subst: &[(Symbol, Ty)]) -> Vec<Symbol> {`
- `fn glue_witness_params`
- `pub(crate) fn build(`
- `impl<'a> ProgramBuilder<'a> {`
- `fn wrap_with_teardown`
- `fn build_named_entry`
- `fn rigid_constraints`
- `struct FunctionBuilder<'p, 'a> {`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- ...and 17 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (4s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (15s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `run_assigns_through_nested_places`, `run_executes_record_rows`, `run_initializes_globals_for_named_entries`, `run_calls_function_values_stored_in_globals`, `run_clones_enum_values_with_payloads`, `run_dispatches_constrained_generic_effects`.
- Existing test surfaces changed: `tests/talk_tests.rs`.
- Author-reported validation (not independently treated as proof for the exact commit):
  - 931 workspace tests + 4 Swift tests pass; total <=12,742 of the

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

Acceptable within the branch sequence. No commit-local changes are requested.
