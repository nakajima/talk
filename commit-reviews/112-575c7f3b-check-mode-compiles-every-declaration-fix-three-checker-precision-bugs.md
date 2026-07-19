# Commit 112: `575c7f3b` - Check mode compiles every declaration; fix three checker precision bugs

| Field | Value |
|---|---|
| Commit | `575c7f3b3a628d6f4221e07ee5b200aff12890f5` |
| Parent reviewed | `2476d132ea031d46702156b22ce8930607252c33` |
| Author date | 2026-07-17T10:21:45-07:00 |
| Author | Pat Nakajima |
| Patch size | 2 files, +114 / -6 |
| Review result | **Standalone defect, repaired later** |

## Intent and sequence context

TALK_CHECK_ALL compiles every user callable (generics rigidly) with a
synthesized entry for declaration-only programs - the reference's
whole-program flow pass, opt-in; the flow corpus runner uses it, so
the 44 declaration-only rejects now exercise their rules. The new
coverage surfaced three precision bugs, fixed: the arm-merge union
seeded itself with the pre-branch state, so a value reassigned on
every branch stayed moved; borrow-typed bindings marked their source
moved (consume_binding now only unregisters rvalue temporaries);
and borrow-annotated lets (let b: &T = s) now bind as loans. Global
move flags are path-sensitive through the same ArmEnd machinery as
local moves.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 2.
- Production Rust: 1 files (+110/-6): `src/backend/mir.rs`.
- Tests and test oracles: 1 files (+4/-0): `tests/talk_tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 110 | 6 |
| `tests/talk_tests.rs` | 4 | 0 |

### Representative declarations touched

- `pub(crate) fn build(programs: &[ProgramInput<'_>], entry: Entry) -> Result<Progr`
- `struct ArmEnd {`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn assert_flow_corpus(programs: &str, known_failing: &[&str], minimum: usize) {`
- `fn reference_flow_corpus_holds() {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (17s): `reference_flow_corpus_holds`, `run_enforces_capture_list_modes`.
- The persistent `run_enforces_capture_list_modes` failure is inherited from `cabfc772`. Any additional failure attributable to this patch is assessed in Findings below.
- `git diff --check` passed for this commit against its first parent.
- Existing test surfaces changed: `tests/talk_tests.rs`.

## Findings

### 1. [P1] Regenerate the flow gate when enabling whole-program check mode

- Location: `tests/talk_tests.rs::reference_flow_corpus_holds`
- Status: **Fixed by the next commit, `8150b4b8`**
- Impact: Setting `TALK_CHECK_ALL=1` changes which declaration-only fixtures are exercised, but this commit does not fully regenerate `KNOWN_FAILING`. The gate expects `protocol_default_method_receiver_is_borrowed_param` to pass even though the backend still rejects it for missing conformance dictionaries. The next commit adds it to the measured 60-case remainder.
- Evidence: The isolated `reference_flow_corpus_holds` test failed twice; the full exact-checkout run has this failure in addition to the inherited capture-list failure.
- Recommended correction: Land the measured `KNOWN_FAILING` update from `8150b4b8` together with the `TALK_CHECK_ALL` switch.

## Disposition

Do not use this as an independently mergeable/bisectable commit. The cited later commit repairs the defect, but the history should ideally be squashed or reordered so every retained commit is green.
