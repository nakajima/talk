# 0031 - Reset to a frontend-only compiler

Status: implemented (2026-07-13)

## Context

The compiler implementation after type checking had accumulated four tightly
coupled modules:

- `src/flow` mixed ownership diagnostics, dataflow, cleanup planning, and facts
  consumed by code generation;
- `src/lower` owned structural MIR, checked MIR, specialization, dispatch,
  pattern compilation, closure conversion, effects, and memory management;
- `src/lambda_g` supplied both an IR and a second execution engine;
- `src/vm` scheduled that IR into the bytecode types in `talk-runtime`.

The compiler driver hid much of this work inside `type_check()`, which returned
`CheckedMir` and `FlowFacts` in addition to a typed program. Execution features
then coupled the CLI, REPL, package runner, C interface, wasm interface, tests,
and benchmarks to those implementation details.

Incremental repairs had continued to increase the amount of interface knowledge
each module required. Deleting one module moved its complexity into several
callers rather than concentrating it behind a smaller interface.

The last green version of the old backend, including the final Never-valued
match-arm fix, is commit `96249e71` and tag
`pre-backend-reset-2026-07-13`.

## Decision

The `bigdiff` branch becomes frontend-only.

The frontend pipeline ends at:

```text
parse -> name resolution and desugaring -> type checking -> TypedProgram
```

`Driver<Typed>` contains only the `TypedProgram` and parser, name-resolution,
and type diagnostics. Type checking does not build control-flow IR or run a
post-typechecking ownership pass.

The following compiler modules are deleted rather than retained as legacy code:

- `src/flow`;
- `src/lower`;
- `src/lambda_g`;
- `src/vm`.

Execution-oriented compiler interfaces and tests coupled to those modules are
also deleted. Frontend consumers continue to provide parsing, formatting, name
resolution, type checking, hover, completion, definition, rename, package
resolution, and source installation.

Compatibility interfaces in `talk-c`, wasm, and the REPL return explicit errors
when callers request execution, bytecode, or lowered output. The CLI does not
advertise unavailable backend commands.

Flow-sensitive ownership diagnostics and ownership inlay hints are unavailable.
The frontend must not imply that accepted programs have passed ownership or
borrow checking.

## Runtime disposition

The separate `talk-runtime` and `talk-static` crates remain in the workspace.
They have no dependency on the compiler and their direct tests continue to run.
They are quarantined legacy runtime candidates, not a required target for a new
backend. Their current bytecode, continuation, unwind, object-region, and value
representations must be reconsidered before reuse.

## Test disposition

Frontend tests remain active. Direct `talk-runtime` tests remain active. Source
fixtures and expected outputs remain available under `examples`, `core`, and
`tests/programs` for future black-box backend contracts.

Tests whose interface was old MIR, flow annotations, lambda-G, the reference
evaluator, scheduling, or compiler-to-VM execution are deleted. Git history and
the reset tag preserve them for consultation without making them part of the
new architecture.

## Superseded decisions

This ADR supersedes the live backend architecture in ADRs 0009, 0010, 0011,
0015, 0017, 0019, 0027, and 0030. Their historical reasoning remains in the
repository, but their implemented module shapes are no longer current.

ADR 0008 remains the source-language direction for managed storage and FFI, but
its sections describing the deleted ownership, lowering, lambda-G, and VM
implementation are historical.

ADR 0029 remains rejected. This reset does not adopt its attempted uniform
reference-counting baseline.

## Consequences

Talk cannot currently execute source, compile bytecode, build standalone
executables, or run Talk source tests. REPL type queries and completion remain,
but expression evaluation reports the frontend-only state.

The next backend starts from the `TypedProgram` seam without compatibility
requirements from the deleted modules. Any new ownership analysis, IR, runtime
adapter, or execution engine requires a new decision and must earn its module
interface from current requirements rather than preserve the old decomposition.

## Validation

The reset is complete when:

1. none of the four deleted module directories exists;
2. the root compiler has no dependency on `talk-runtime`;
3. `cargo check --workspace --exclude www` is warning-free;
4. `cargo test --workspace --exclude www` passes frontend and direct runtime
   tests;
5. unavailable embedding calls fail explicitly rather than panic or silently
   succeed.
