# Commit 137: `af7f9817` - Register-or-constant operands: constants stop costing an instruction

| Field | Value |
|---|---|
| Commit | `af7f9817778821448b74a577a8c55bf7d88262e1` |
| Parent reviewed | `352ec1275063ccf630b878c12de8680c007fa0f3` |
| Author date | 2026-07-17T20:34:52-07:00 |
| Author | Pat Nakajima |
| Patch size | 6 files, +206 / -44 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

Lua 5's RK operand design (Ierusalimschy, de Figueiredo & Celes,
The Implementation of Lua 5.0, J.UCS 2005): when an operand field's
high bit is set, its low 15 bits index the module constant pool;
otherwise it names a frame register. RK positions are the
arithmetic/comparison operands (Add/Sub/Mul/Div/Cmp a and b) and
every argument-pool entry, so constants flow into scalar ops, calls,
and constructions with no materializing instruction. Lowering
encodes via rk() with fallback materialization for pool indexes past
15 bits and for register-only positions (conversions); the decoder
validates RK fields against the pool; the disassembly renders k[n].

This is the deliberate fix for the wave-11 constants finding: the
hot constant loads were per-call materializations in leaf functions,
unreachable by any placement pass. Executed Const: 4.18M -> 1.39M;
total executed VM instructions: ~21M -> ~16M, meeting the wave-11
execution target. Shape test pins `n + 1` compiling without a const
instruction. All gates green: 965 workspace, 18 core, 225
talk-syntax, 1 talk-html.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 6.
- Production Rust: 4 files (+137/-42): `src/backend/lower.rs`, `talk-runtime/src/bytecode.rs`, `talk-runtime/src/interp.rs`, `talk-runtime/src/lib.rs`.
- Tests and test oracles: 1 files (+57/-0): `tests/talk_tests.rs`.
- Documentation and plans: 1 files (+12/-2): `docs/lean-backend-rebuild-plan.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/lower.rs` | 50 | 12 |
| `tests/talk_tests.rs` | 57 | 0 |
| `talk-runtime/src/interp.rs` | 27 | 22 |
| `talk-runtime/src/lib.rs` | 38 | 6 |
| `talk-runtime/src/bytecode.rs` | 22 | 2 |
| `docs/lean-backend-rebuild-plan.md` | 12 | 2 |

### Representative declarations touched

- `impl Lowering<'_> {`
- `fn rk`
- `fn demote_rk`
- `impl Insn {`
- `impl Module {`
- `impl Register {`
- `fn check_rk`
- `fn exec_local(`
- `fn call_regs(`
- `fn arg_values(`
- `pub enum MemKind {`
- `fn rk_display`
- `fn assert_parity_program(name: &str) {`
- `fn constant_operands_read_the_pool_directly`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (41s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `constant_operands_read_the_pool_directly`.
- Existing test surfaces changed: `tests/talk_tests.rs`.
- Author-reported validation (not independently treated as proof for the exact commit):
  - instruction. All gates green: 965 workspace, 18 core, 225

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
