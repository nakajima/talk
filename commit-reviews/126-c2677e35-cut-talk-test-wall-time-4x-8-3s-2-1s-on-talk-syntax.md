# Commit 126: `c2677e35` - Cut `talk test` wall time 4x (8.3s -> 2.1s on talk-syntax)

| Field | Value |
|---|---|
| Commit | `c2677e35ca11d1ddbab9dd019ab5d035147f25e4` |
| Parent reviewed | `e1b38381d05f7cfb2f1b0811436e3f07169b98d0` |
| Author date | 2026-07-17T14:26:08-07:00 |
| Author | Pat Nakajima |
| Patch size | 3 files, +149 / -79 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

Three hot spots, measured with perf on the talk-syntax suite:

Backend symbol lookups (57% of compile): struct_def, enum_def,
variant_tag, and conforms_to each scanned every program's whole
catalog per query, canonicalizing every key on the way — quadratic in
catalog size. ProgramBuilder now builds canonical-symbol indexes once
(structs, enums, variant tags, conformance pairs with rigid bounds
folded in) and the four lookups are hash probes. First-wins insertion
preserves the scan order's duplicate handling. Compile of
parser.test.tlk: 4.9s -> 0.56s.

TALK_TRACE_MEM (15% of execution): the flag was a getenv on every
interpreter instruction; it is read once per process now.

Call-frame allocation (~30% of execution): every call collected its
arguments into a Vec, allocated a zeroed register frame, and moved
the arguments across — two allocations and a drop per call.
call_regs builds the callee frame in one allocation (arguments cloned
into the low slots, Void fill above), and the region-teardown pump is
gated on an inline finalizing() check instead of an outlined call per
instruction.

All gates hold: 952 workspace, 18 core, 225 talk-syntax, 1 talk-html.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 3.
- Production Rust: 3 files (+149/-79): `src/backend/mir.rs`, `talk-runtime/src/interp.rs`, `talk-runtime/src/objects.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 77 | 58 |
| `talk-runtime/src/interp.rs` | 65 | 21 |
| `talk-runtime/src/objects.rs` | 7 | 0 |

### Representative declarations touched

- `fn contains_buffer_guarded(`
- `struct ProgramBuilder<'a> {`
- `impl<'a> ProgramBuilder<'a> {`
- `fn trace_mem`
- `fn run_loop(module: &Module, machine: &mut Machine) -> Result<Value, String> {`
- `impl Machine<'_> {`
- `fn exec_local(`
- `fn vm_object_error(error: ObjectError) -> String {`
- `fn call_regs`
- `impl<V: Clone> Objects<V> {`
- `fn finalizing`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (40s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- No test files or executable language test fixtures changed in this patch.
- Coverage note: production behavior changes without a directly changed test surface in this commit; confidence therefore comes from existing suites and later integration coverage.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
