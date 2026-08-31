# Mincodex baseline evidence

Step: B0

Recorded against inventory revision
`85cf295d46f160efaf4453e05f01e8f61531a455` (`Refactor unwind parking in
MIR and runtime`). The only working-tree changes before this step were the
salvage-plan rewrite and its target-architecture reference.

## Toolchain

```text
rustc 1.99.0-nightly (73dc9167f 2026-08-01)
cargo 1.99.0-nightly (7c83d4cc0 2026-07-29)
talk 0.1.109
talk executable sha256 3e935915198471051e62b642f12103b955fad92a638cc60d886f678ff5f4ebb1
```

The `talk` executable was
`/home/nakajima/apps/talk/target/release/talk`; its version agrees with the
workspace package version.

## Baseline gate

Both passes used worktree-local `TALK_CORE_PATH` and `TALK_STDLIB_PATH`.
The two passes had identical exit status and failure class.

| Command | Pass 1 | Pass 2 | Evidence |
| --- | ---: | ---: | --- |
| `cargo fmt --all -- --check` | 1 | 1 | identical rustfmt diff; 66 files |
| `cargo check --workspace` | 0 | 0 | passed |
| `cargo test --workspace --no-fail-fast` | 101 | 101 | 1,712 passed; 1 failed; 4 ignored |
| `cargo test --release --workspace --no-fail-fast` | 101 | 101 | 1,703 passed; 1 failed; 4 ignored |
| `cargo check --target wasm32-unknown-unknown` | 101 | 101 | identical `errno` target failure |

The exact existing test failure in both debug and release passes was:

```text
thread 'formatter_tests::core_smoke_test' (...) panicked at crates/talk-front/tests/front_suite/formatter_tests.rs:1013:13:
assertion `left == right` failed: formatter changed /home/nakajima/apps/talk/crates/talk-front/../../core/unicode_data.tlk

failures:
    formatter_tests::core_smoke_test

test result: FAILED. 750 passed; 1 failed; 1 ignored; 0 measured; 0 filtered out
```

The exact wasm failure in both passes was:

```text
error: The target OS is "unknown" or "none", so it's unsupported by the errno crate.
 --> /home/nakajima/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/errno-0.3.12/src/sys.rs:8:1
  |
8 | compile_error!("The target OS is \"unknown\" or \"none\", so it's unsupported by the errno crate.");
  | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

error: could not compile `errno` (lib) due to 1 previous error
```

The rustfmt failure was byte-identical on both passes (output SHA-256
`a48bfad6266dec725cffa1c76aaaf313e55948c4a7ff40e05a64aa67ffaef9ba`).
It reports formatting drift in 66 existing Rust files across `crates/talk-front`,
`crates/talk-vm`, `crates/wasm`, `src`, and `tests`. No file was changed by the
check.

Every ignored test, identical in debug and release, was:

```text
analysis::completion::scratch_tests::scratch_dump_incomplete_member
    debugging scaffold: dumps completion internals and panics
compiling::bootstrap::tests::checked_in_frontend_artifacts_are_a_fixed_point
    explicit artifact gate; use `talk bootstrap --check`
compiling::frontend::tests::write_vm_stats_profile
    run by scripts/frontend-vm-stats.sh
name_resolver_tests::tests::resolves_Optional
    requires core
```

These baseline failures are not absorbed by a feature step. Their failure
classes must remain unchanged until separately approved.

## Bootstrap fixed point

`talk bootstrap --check` passed twice. Both runs reported:

```text
/home/nakajima/apps/talk/bootstrap/frontend.tbc is up to date
```

The working tree and all recorded artifact hashes were unchanged, so the
checked-in bootstrap is already a fixed point.

## Artifact hashes

### MIR goldens

```text
48e30d33cdfc86614dfea5fb6cb3fcf0eebd9676f711bf69dd2a3033ef35ee53  tests/mir/expected/arithmetic_and_calls.mir
9462698196fc6bd3d34d487e238a6b85272e6ea79606f79d68d51d888d128a92  tests/mir/expected/arrays_and_subscripts.mir
b7430d846780f323252a2cb4bfe99dc84db0a9170f07d62a151e98857f82710a  tests/mir/expected/borrowed_parameters.mir
f0d3b26171998596cbeed948611a27565031653487c1eb34e8a6c178607373a0  tests/mir/expected/closures_with_cells.mir
634d13d574212352017746add57097fd9cfd669ca4afe2c28e1c20368d4770ed  tests/mir/expected/consuming_parameters_and_drop_glue.mir
aa9c9e2695e8ddedc3df9d96a2912170605310faf49b59244d8e7255d3789149  tests/mir/expected/derived_show_and_equality.mir
d2fafe322e52c68b84763c819bd7c022b9540a143b73e65c5234c3f3498eeb2c  tests/mir/expected/effect_handlers.mir
9cb7686a7e4c5711907f42fa9e5644bdf4e57bf15978d1e221d0c1d7c09a1291  tests/mir/expected/enum_construction_and_match.mir
0dda88358f0b340311ef152a6d7999151885e9da1bdd50ed5690756ddbea8b19  tests/mir/expected/existential_pack_and_dispatch.mir
5adf37af803c9561440c0931d30723451039d72d41c47651ae329f3cf381908f  tests/mir/expected/for_loops.mir
21d59fbbd222ec04102776401784bdf011ec89cddc1abecbb3aae14b68dcbb14  tests/mir/expected/generic_identity_and_instantiation.mir
8247de83d4e551e1f3b7d237901374510bbb6f4226fc34cd9752e39b87828c90  tests/mir/expected/globals_and_initialization_order.mir
9d1d1353e21c35da28a0fe8aa432657b4f5558e24ec4eae770884f1b86834609  tests/mir/expected/match_with_guards_and_binders.mir
2eaa83a30d526820ee62adb0d9cf56c20064bf9ac9ef9eb14b2003c29df58baa  tests/mir/expected/mut_writeback.mir
41ceb4084e005ab7ac9b65c4719cf69c3c335a7c00f5ef89047728b7c4a55119  tests/mir/expected/optional_propagation.mir
e2ea7469f3acd66e1641543ab600b34253e9b81273a3e997c4d76cd9773aa15d  tests/mir/expected/protocol_witness_dispatch.mir
0293618791f9f76fe6151edff47b3533cbf7fdd68a431c04286c55450d9c51e1  tests/mir/expected/string_match_arms.mir
ec1fc7e312a64c1e92cdac171004e57c49da488bf5883c7211a2ae874c3dc5c5  tests/mir/expected/string_values.mir
c4a67fc849ca1c64c8f18892d32e692751f303f114e0f62d8879e30bc4b19a64  tests/mir/expected/struct_construction_and_fields.mir
bc1037e9493fe43026001c10b72dff27a2bd5e652ab4730d7c321ec20187ae08  tests/mir/expected/tuples_and_projection.mir
```

### Bootstrap manifests

```text
eea976e1b8884f8221330beb3e066fc966b455a5d7b9eeaa40e39fe4a99b1619  bootstrap/core.manifest
e509154bf4bf37ee6aaa56f98a4c1bcc8e6787c41841d1dba70d13def3070a4f  bootstrap/frontend.manifest
```

### Generated frontend artifacts

```text
369724d24e2dd18245d2fff1956c28c2eaf364d15006f49d03a432563cc70184  bootstrap/frontend.abi
ae16d0f1c87ceee92b039d5e402b4cd1eb93efabb098a61555ac56eebd3b8c3b  bootstrap/frontend.c
e44fe3da412256d4a39a1179e9622e79bba960e6522afd2a0633a17418d09929  bootstrap/frontend.tbc
```

## Current-owner inventory verification

The inventory in the execution plan matches this revision:

- Pattern diagnostics are owned by
  `types/exhaustiveness.rs` and `generate::Generator::check_matches`.
- Runtime match control and settlement are owned by
  `FunctionBuilder::compile_match`, `compile_pattern_test`, and
  `settle_owned_match`.
- The checked occurrence is `core::ExprKind::Match`, built by
  `core::build`.
- `CoreProgram` stores `Core<Nested>`, while `Nested`, `Flat`, `Closed`, and
  `Mono` all use `FileProgram`; no phase transition exists.
- `ProgramBuilder` owns `demand`, its `Instance` keys and worklist, and
  `drain_worklist`; `FunctionBuilder`, `entries`, and `glue` demand while
  emitting MIR.
- `OwnershipSites`, `FlowEvent`/`FlowRecord`, `release::Plan`, verifier entry
  replay, and unwind release realization are separate current owners.
- `mir::cfg::Cfg` is shared and includes unwind successors.
- No explicit pre-final ownership-marker representation exists.

No required seam was contradicted by baseline inspection. B1 remains
responsible for proving every exact data shape, consumer, replacement owner,
and differential oracle before source work begins.
