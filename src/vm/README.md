# How the bytecode VM works

This directory is the compiler-facing half of the bytecode engine. It takes
the lambda-G program produced by `src/lower` and schedules it into the
runtime bytecode structures. The bytecode definitions and interpreter live
in the `talk-runtime` crate; `src/vm/mod.rs` re-exports those types and
provides the compiler-to-runtime `Symbol` bridge. The exact `talk ir`
listing format is documented alongside `@_ir` and lambda-G in
`../../docs/ir-and-lambda-g-format.md`.

There are two engines for the same lowered program: the bytecode VM and the
reference evaluator in `src/lambda_g/eval.rs`. Tests compare them on the
same programs and IO boundary so the slow engine keeps the fast one honest.

Files to know:

- `schedule.rs` — lambda-G to bytecode scheduling; this crate's main logic.
- `mod.rs` — re-exports `talk-runtime` types and maps compiler symbols to
  runtime symbols.
- `talk-runtime/src/lib.rs` — instruction set, `Chunk`, `Module`, and the
  bytecode listing renderer.
- `talk-runtime/src/bytecode.rs` — binary bytecode encoding/decoding.
- `talk-runtime/src/interp.rs` — the frame-stack interpreter and value
  rendering for the REPL/playground.
- `talk-runtime/src/memory.rs` and `talk-runtime/src/objects.rs` — raw
  byte memory and region-managed `'heap` object storage.
- `talk-runtime/src/io.rs` — the IO trait plus host-backed `StdioIO` and
  deterministic `CaptureIO`.
- `talk-runtime/src/symbol.rs` — runtime symbol ids.

## The instruction set

Instructions are a plain Rust enum with fixed fields. Registers are `u16`
indices into the current frame; variable-length things (argument lists,
switch targets, constants, trap messages) live in side pools in the
`Module`, referenced by index. There is no byte packing in the in-memory
form: dispatch is a Rust `match` over instructions. Packed encodings are
handled separately by `bytecode.rs`.

Instruction families:

- constants and moves (`Const`, `Move`);
- arithmetic/comparison (`Add`, `Sub`, `Mul`, `Div`, `Cmp`) and conversions
  (`Trunc`, `IToF`, `BToI`);
- cells (`CellNew`, `CellGet`, `CellSet`) for assignment-converted mutable
  bindings;
- value aggregates: boxed records (`RecordNew`, `GetField`, `SetField`),
  enum variants (`VariantNew`, `GetTag`, `GetPayload`), tuples
  (`TupleNew`, `Extract`), and protocol existentials (`ExistentialPack`,
  `ExistentialWitness`, `ExistentialPayload`);
- raw byte memory (`Alloc`, `Free`, `Retain`, `IsUnique`, `Load`, `Store`,
  `Copy`) used by strings, buffers, and low-level core code;
- `'heap` objects and regions (`ObjectNew`, `SetFinalizer`, `ObjectGet`,
  `ObjectSet`, `RegionAcquire`, `RegionRelease`);
- IO (`Io`) with one opcode parameter for read/write/open/close/sleep,
  polling, sockets, cwd/env/argv, directory operations, and exit;
- control (`Call`, `MakeClosure`, `EnvGet`, `CallIndirect`, `Jump`,
  `Branch`, `Switch`, `Ret`), plus `MakeCont`/`CallCont` for reified
  one-shot return continuations used by captured effect-handler delimiters;
- `Trap`, a deliberate runtime hole for unsupported or impossible lowered
  paths.

## Scheduling: from a soup of functions to chunks and blocks

lambda-G does not distinguish source functions from the tiny continuation
functions the lowerer creates for sequencing, branches, joins, and handlers.
Running every continuation as a VM call would be too expensive, so
`schedule.rs` sorts labels into two kinds:

- **Chunks** — labels the lowerer says must get their own bytecode unit and
  frame: demanded specializations, `main`, escaping function values,
  finalizer thunks, and other closure-forming labels.
- **Blocks** — non-chunk continuation labels uniquely reachable from a
  chunk. They become labeled blocks inside that chunk and share its register
  frame. Calling one writes its parameter register and emits a `Jump`.

Calls then reconstruct into ordinary VM control flow. A call to another
chunk is `Call`; a call to a block in the same chunk is `Jump`; a call to
the chunk's return continuation is `Ret`; a computed function value is a
closure and uses `CallIndirect`. A continuation used as a value cannot be a
block, so the scheduler emits a closure. Capturing the current chunk's own
return continuation materializes a one-shot continuation with `MakeCont`.

Block ownership is computed by function-reference reachability from each
chunk-forming label. If two chunks would share the same non-chunk
continuation, scheduling rejects the program instead of silently creating a
shared mutable frame.

## The interpreter

`interp.rs` runs a stack of heap-allocated frames. Each frame has a chunk,
program counter, register file, closure environment, destination register in
its caller, and a unique frame id. Important representation choices:

- **Frames are plain data.** Direct and indirect calls push frames; `Ret`
  pops. `MakeCont` records the current frame index/id, and `CallCont`
  unwinds back to that live frame and returns a value from it. If the frame
  is gone, the continuation traps cleanly.
- **Cells live in an arena outside frames**, so closures and captured
  continuations see the same mutable boxes as the original frame.
- **Values are immutable except for explicit cell/object operations.**
  Record updates are copy-on-write functional updates; `'heap` object fields
  mutate in the region/object arena by design.
- **Region teardown is part of the machine.** `RegionRelease` can trigger
  finalizer frames, then bulk-free a region when its ledger reaches zero.

The interpreter also owns rendering (`render_value` and friends): the REPL
and `print` format runtime values in Talk syntax — `Person(age: 123)`,
`Optional.some(1)` — using display-name tables the checker exported.

## The IO boundary

Both engines execute IO through one trait (`talk-runtime/src/io.rs`) with
POSIX conventions: a non-negative result is the operation's value, and a
negative result is a negated errno.

- `StdioIO` uses host stdout/stderr and Unix/POSIX syscalls where available.
- `CaptureIO` simulates stdout, files, descriptors, sockets, cwd/env/argv,
  and directory queries in memory. Tests and expected-output fixtures run
  against this, so two-engine tests are deterministic and need no sandbox.

Because the boundary is the trait and not the engine, the evaluator and the
VM cannot drift apart on IO semantics — they call the same implementation.

## Further reading

Register bytecode over a stack machine: Shi, Casey, Ertl & Gregg,
*Virtual Machine Showdown* (VEE 2005), and the Lua 5.0 design notes
(Ierusalimschy et al., 2005). `match`-based dispatch vs threaded code:
Ertl & Gregg (2003). Call/return reconstruction from CPS is Thorin's
(Leißa, Köster & Hack, CGO 2015); continuations-as-blocks is the
join-points story (Maurer, Downen, Ariola & Peyton Jones, PLDI 2017).
Flat closures: Cardelli (1984). One-shot continuations and heap frames are
in the lineage of Hieb, Dybvig & Bruggeman (PLDI 1990), adapted here to a
frame-stack VM.
