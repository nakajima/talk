# Backend extraction baseline

Recorded 2026-08-02 at commit `cb487f98` (stage 0 of the
[backend crate extraction plan](backend-crate-extraction-plan.md), ADR 0047).
No production behavior changed by the recording.

Environment note: the recording shell must point `TALK_STDLIB_PATH` and
`TALK_CORE_PATH` at the checkout being tested. Two stdlib-recognition tests
(`compiling::driver::tests::new_does_not_import_bundled_stdlib_when_compiling_stdlib_source`,
`analysis::workspace::tests::stdlib_source_does_not_import_bundled_stdlib_into_itself`)
resolve stdlib paths through those variables and fail when they name a
different checkout (for example when direnv exports the main checkout's paths
inside a worktree).

## Post-extraction accounting (final state)

Recorded after stage 8 (`bash scripts/size_report.sh`; code = nonblank,
non-comment `.rs` lines, in-file test tails split out):

| Module | Production | In-file tests | Comments |
| --- | --- | --- | --- |
| Compiler MIR work (`src/compiling/mir`) | 12,224 | 2,934 | 2,348 |
| Public MIR data (`talk-mir/src`) | 603 | 0 | 199 |
| Bytecode adapter (`talk-bytecode/src`) | 1,611 | 136 | 160 |
| C adapter (`talk-c/src`) | 2,126 | 0 | 282 |
| VM (`talk-vm/src`) | 8,449 (code) | — | 702 |
| Native runtime (`talk-native-runtime/src`) | 3 (code) | — | 5 |

The native runtime's C source (`runtime.c`, ~1,900 nonblank lines) is
outside the script's `.rs` accounting, as `c_prelude.c` was before the
extraction.

## Package dependency graph (cargo tree, normal dependencies, depth 1)

```text
talk (root)
    talk-runtime (path)
    anyhow, async-lsp, bincode, clap, clap_complete, derive-visitor, flate2,
    futures, generational-arena, ignore, indexmap, itertools, miette,
    num-bigint, petgraph, profiling, rustc-hash, rustyline, serde, sha2, tar,
    tokio, tower, tracing, tracing-subscriber, tracing-tree

talk-runtime
    libc, profiling, rustc-hash

talk-static
    talk-runtime

talk-c (embedding; becomes talk-ffi)
    talk, talk-runtime

talk-llvm
    talk

talk-wasm (wasm/)
    console_error_panic_hook, js-sys, talk, wasm-bindgen, web-sys

builder (www/)
    comrak
```

## Nonblank production line counts (`.rs`/`.c`/`.h`, tests included in tree)

| Module | Nonblank lines |
| --- | --- |
| Compiler MIR (`src/backend/mir`) | 14,109 |
| Compiler optimize (`src/backend/optimize`) | 2,305 |
| Compiler regalloc (`src/backend/regalloc.rs`) | 995 |
| Compiler backend root (`src/backend/mod.rs`) | 315 |
| Codegen model + projection (`src/codegen.rs`, `src/backend/codegen.rs`) | 889 |
| C adapter (`src/backend/c.rs`) | 2,937 |
| Native prelude (`src/backend/c_prelude.c`) | 1,938 |
| Bytecode adapter (`src/backend/lower.rs`, `src/backend/checked_indexed_load.rs`) | 1,748 |
| VM (`talk-runtime/src`) | 9,151 |
| LLVM (`talk-llvm/src`) | 2,183 |
| FFI (`talk-c/src`) | 2,308 |
| talk-static (`talk-static/src`) | 62 |
| wasm (`wasm/src`) | 339 |

## ABI migration oracle

The 100 exported `talk_*` symbols in `target/debug/libtalk_c.a` are recorded
in [abi-symbol-oracle.txt](abi-symbol-oracle.txt)
(`nm -g --defined-only target/debug/libtalk_c.a | grep ' T talk_'`).
Stage 2's acceptance compares against this list plus the new
`talk_ffi_abi_version` symbol.

## Driver backend-method caller inventory (stage 0, plan fix 4)

| Method | Callers |
| --- | --- |
| `compile_executable` | `src/bin/talk.rs` (CLI), `src/repl.rs`, `src/testing.rs`, `src/compiling/driver.rs` (self), `src/compiling/package.rs`, `talk-c/src/lib.rs`, `tests/procedural_macro_tests.rs`, `talk-llvm/tests/backend.rs` |
| `compile_service` | `src/compiling/bootstrap.rs`, `src/procedural_macros.rs`, `src/compiling/driver.rs` (self) |
| `render_c` | `src/bin/talk.rs` |
| `render_c_service` | `src/bin/talk.rs` |
| `codegen` | `src/compiling/package.rs` |
| `codegen_binary` | `talk-llvm/src/main.rs` |
| `render_mir` | `src/bin/talk.rs`, `src/testing.rs`, `talk-c/src/lib.rs`, `wasm/src/lib.rs` |
| `check_ownership` | `src/analysis/workspace.rs` |
| `execute_module` | `src/bin/talk.rs`, `src/repl.rs`, `src/testing.rs`, `src/compiling/driver.rs` (tests) |
| `execute_image` | `src/bin/talk.rs` |

The LSP server (`src/lsp`) calls none of these; it goes through
`src/analysis` and needs no `compile_mir` migration. `bench/` is `.tlk`
fixtures only; there are no Rust benches consuming the backend.

## Baseline validation results

Commands from the plan's mandatory gates, run at `cb487f98` with
`TALK_STDLIB_PATH`/`TALK_CORE_PATH` set to this checkout.

One pre-existing finding: the checked-in `bootstrap/frontend.tbc` at
`cb487f98` was stale — last regenerated at `7324298e`, with three later
commits (`a969626d`, `bfd5929b`, `f4f7ee5b`) changing code generation.
Regeneration from two independent checkouts produced byte-identical
artifacts, so the compiler is deterministic and the fixed point holds after
regeneration. Stage 0 commits the regenerated artifact and manifest so the
per-stage oracle starts green; no compiler code changed.

A second pre-existing finding: the clang sweep failed at `cb487f98` because
the C emitter printed whole-struct self-assignments (`x6 = x6;`) when
register reuse unified a copy's endpoints, which clang rejects under
`-Wself-assign`. GCC accepted them, so the gcc sweep was green. Stage 0
fixes the emitter to skip self-copies (`src/backend/c.rs`, `Inst::Copy`) so
the clang gate starts green; generated programs are otherwise byte-identical
and the differential sweep remains the behavior gate.

| Command | Result |
| --- | --- |
| `cargo build --workspace --locked` | pass |
| `cargo test --workspace --all-targets --locked` | pass |
| `target/debug/talk bootstrap --check` | pass after regenerating the stale checked-in artifact (see above) |
| `./scripts/c-backend-sweep.sh` | pass |
| `./scripts/c-backend-sweep.sh --cc clang` | pass after the self-assignment emitter fix (see above) |
| `cargo test -p talk-llvm --locked` | pass (covered by workspace run) |
| `cargo test -p talk-ffi --locked` | n/a until stage 2 (package is `talk-c`; `cargo test -p talk-c --locked` passes) |
| `swift test -Xlinker -L -Xlinker "$PWD/target/debug"` | pass |
| `./talk-swift/scripts/build-xcframework.sh` | not run locally: Apple targets unavailable on Linux; CI gate |
| `swift package reset && swift test` | pass |
| `xcodebuild ... iOS Simulator` | not run locally: no Xcode on Linux; CI gate |
| `git diff --check` | clean |
