# How the bytecode VM works

This directory is the execution engine: it takes the λ_G program the
lowerer produced (see `src/lower/README.md` and
`src/lambda_g/README.md`) and turns it into register bytecode, then
runs it on a frame-stack interpreter. The exact `talk ir` listing
format is documented alongside `@_ir` and λ_G in
`../../docs/ir-and-lambda-g-format.md`. There are two engines for every
program — this VM and the reference evaluator in `src/lambda_g/eval.rs`
— and the test suite requires them to produce identical results, so
the slow-but-obvious one keeps the fast one honest.

- `mod.rs` — the instruction set and the compiled `Module`, plus the
  bytecode listing `talk ir file.tlk` prints.
- `schedule.rs` — λ_G → bytecode translation.
- `interp.rs` — the interpreter, plus value rendering for the REPL.
- `io.rs` — the IO boundary both engines share.

## The instruction set

Instructions are a plain Rust enum with fixed fields — registers are
`u16` indices into the current frame, and variable-length things
(call arguments, switch targets, constants, trap messages) live in
side pools in the `Module`, referenced by index. No byte packing: an
instruction is decoded by `match`, and the dispatch loop is a `match`
too. (Packed encodings and threaded dispatch are well-understood
speedups; they're deliberately left for later because they're
mechanical and would obscure the semantics now.)

The families:

- arithmetic/comparison (`Add`, `Cmp`, …) and conversions
  (`Trunc`, `IToF`);
- cells (`CellNew`/`CellGet`/`CellSet`) — the heap boxes that mutable
  bindings lowered to;
- aggregates: heap records (`RecordNew`/`GetField`/`SetField` —
  `SetField` is a functional update, copy-on-write under the hood),
  enum variants (`VariantNew`/`GetTag`/`GetPayload`), tuples
  (`TupleNew`/`Extract`);
- raw byte memory (`Alloc`/`Load`/`Store`/`Copy`) — a flat bump-
  allocated byte array used by strings and the io layer;
- `Io` — one instruction per operation in the io dialect (read,
  write, open, close, sleep, poll, ctl, socket, bind, listen,
  connect, accept);
- control: `Call` (static, to a known chunk), `MakeClosure` /
  `CallIndirect` / `EnvGet` (closures are a chunk plus a flat list of
  captured values), `Jump`, `Branch`, `Switch` (jump-table dispatch
  on an enum tag), `Ret`;
- `Trap` — a deliberate hole. Anything the pipeline couldn't lower
  lands here with a message, so partial programs fail loudly at the
  exact spot instead of misbehaving.

## Scheduling: from a soup of functions to chunks and blocks

λ_G makes no distinction between "real" functions and the tiny
continuation functions the lowerer materialized for sequencing,
branching, and joins. Running every one of those as an actual call
would be hopeless, so `schedule.rs` sorts them into two kinds:

- **Chunks** — functions that get their own bytecode unit and
  register frame. These are exactly the specializations the lowerer
  demanded, plus `main`.
- **Blocks** — every other function (branch arms, join points,
  argument receivers) becomes a labeled block *inside* the chunk that
  references it, sharing the chunk's register frame. Calling one is a
  `Jump`, and its parameters are just registers the predecessor
  writes before jumping.

Then calls reconstruct into conventional control flow by looking at
the callee: a call to another chunk is a `Call` (push a frame); a
call to one of the chunk's own blocks is a `Jump`; a call to the
chunk's return continuation is a `Ret`. The "function that never
returns" fiction from the IR completely disappears in the bytecode —
what's left looks like ordinary calls, jumps, and returns. A
continuation used as a value (stored, passed somewhere unexpected)
can't be a block, so it becomes a real closure instead.

Block ownership is computed by reachability from each chunk: which
non-chunk functions does this chunk reference? Two chunks referencing
the same continuation would mean a shared mutable frame, so that's
rejected as a construction error rather than silently miscompiled.

## The interpreter

`interp.rs` runs a stack of frames; each frame is the register file
for one chunk invocation plus its return position. Three
representation choices matter:

- **Frames are plain data.** No native-stack recursion, no pointers
  into the Rust stack. That's what makes resumable effect handlers
  affordable: capturing "the rest of this computation" is copying
  frames, and resuming is putting them back.
- **Cells live in an arena outside the frames**, so a captured
  continuation and the original frames see the same mutable boxes —
  copies of a frame share state where they should and own state where
  they should.
- **Values are immutable**; record "mutation" is copy-on-write
  functional update, which is exactly the value semantics the
  language promises.

The interpreter also owns rendering (`render_value` and friends): the
REPL and `print` format runtime values in Talk syntax —
`Person(age: 123)`, `Optional.some(1)` — using display-name tables
the checker exported.

## The IO boundary

Both engines execute io through one trait (`io.rs`) with POSIX
conventions: non-negative result is the value, negative result is a
negated errno. Two implementations:

- `StdioIO` — real file descriptors via libc (Unix only).
- `CaptureIO` — a simulated world: captured stdout, in-memory file
  descriptors, a loopback network. Tests and the expected-output
  files run against this, which is why two-engine tests are
  deterministic and need no sandbox.

Because the boundary is the trait and not the engine, the evaluator
and the VM can't drift apart on io semantics — they're calling the
same code.

## Further reading

Register bytecode over a stack machine: Shi, Casey, Ertl & Gregg,
*Virtual Machine Showdown* (VEE 2005), and the Lua 5.0 design notes
(Ierusalimschy et al., 2005). `match`-based dispatch vs threaded
code: Ertl & Gregg (2003). Call/return reconstruction from CPS is
Thorin's (Leißa, Köster & Hack, CGO 2015); continuations-as-blocks is
the join-points story (Maurer, Downen, Ariola & Peyton Jones, PLDI
2017). Copyable frames for continuation capture: Hieb, Dybvig &
Bruggeman (PLDI 1990); cells hoisted out of frames is assignment
conversion from ORBIT (Kranz et al., 1986). Flat closures: Cardelli
(1984).
