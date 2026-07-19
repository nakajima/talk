# Commit 045: `bd5ac7c0` - e2: initialize linked scalar globals

| Field | Value |
|---|---|
| Commit | `bd5ac7c03371cebd60af4a7e81f549073923a7f9` |
| Parent reviewed | `481f2c2ac4b14774314521424cfa4079455d1199` |
| Author date | 2026-07-15T09:57:40-07:00 |
| Author | Pat Nakajima |
| Patch size | 22 files, +2168 / -203 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 22.
- Production Rust: 14 files (+1918/-102): `src/bytecode/mod.rs`, `src/compiling/module.rs`, `src/compiling/typed_program/build.rs`, `src/compiling/typed_program/contract.rs`, `src/mir/generate.rs`, `src/mir/mod.rs`, `src/mir/verify.rs`, `src/talk_ir/linking.rs`, and 6 more.
- Tests and test oracles: 1 files (+38/-0): `tests/talk_tests.rs`.
- Documentation and plans: 7 files (+212/-101): `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md`, `docs/backend-parity-ledger.md`, `docs/backend-parity-plan.md`, `docs/backend-status.md`, `docs/e1-scalar-execution-plan.md`, `docs/e1-talk-runtime-reuse-audit.md`, `docs/stage-0-contract-types.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/talk_ir/mod.rs` | 472 | 0 |
| `src/talk_ir/linking.rs` | 293 | 25 |
| `src/bytecode/mod.rs` | 237 | 25 |
| `src/talk_ir/lowering.rs` | 164 | 18 |
| `src/compiling/typed_program/contract.rs` | 163 | 1 |
| `talk-runtime/src/scalar.rs` | 144 | 3 |
| `src/mir/generate.rs` | 97 | 15 |
| `docs/stage-0-contract-types.md` | 82 | 25 |
| `src/compiling/typed_program/build.rs` | 102 | 3 |
| `talk-runtime/src/bytecode.rs` | 84 | 3 |
| `docs/backend-status.md` | 47 | 26 |
| `src/mir/verify.rs` | 66 | 4 |
| `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md` | 42 | 26 |
| `talk-runtime/src/interp.rs` | 50 | 1 |
| `tests/talk_tests.rs` | 38 | 0 |

### Representative declarations touched

- `pub struct TypedProgram {`
- `pub enum TypedFunctionImplementation {`
- `pub struct TypedGlobal {`
- `pub struct MirGlobal {`
- `enum MirGlobalInitializer`
- `pub struct MirExport {`
- `pub struct TalkIrModule {`
- `pub struct IrGlobal {`
- `enum IrInitializer`
- `pub enum TalkIrInvariant {`
- `impl ValidatedBytecodeModule {`
- `pub(crate) fn compile(`
- `fn preflight(module: &TalkIrModule, entry: IrFunctionId) -> Result<(), BytecodeL`
- `fn preflight_instruction(`
- `fn preflight_terminator(`
- `fn global_kind`
- `impl Pools {`
- `fn synthesize_initialization_entry`
- ...and 88 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (6s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (26s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `executes_constant_and_dynamic_global_initializers_once_in_order`, `executes_a_source_constant_global_through_the_initializer_schedule`, `executes_a_source_dynamic_global_initializer_once`, `producer_publishes_global_initialization_order_without_duplicating_the_expression`, `links_scalar_globals_and_preserves_the_initializer_schedule`, `rejects_module_initialization_cycles`, `verifier_rejects_invalid_global_initializer_contracts`, `validates_scalar_globals_and_enforces_initialization_and_kind`, `run_initializes_scalar_globals_once_in_source_order`, `run_rejects_a_global_read_before_source_order_initialization`.
- Existing test surfaces changed: `tests/talk_tests.rs`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
