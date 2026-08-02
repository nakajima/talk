# C backend

The ahead-of-time target. `talk c` emits one self-contained C translation
unit from the same optimized, register-allocated program `lower::lower`
turns into bytecode, and `talk build --native` drives that through the
host C compiler to an executable.

It began as a spike to measure what native code buys over the VM and to
find which parts of the IR resist translation. It now covers the entire
instruction set, and the answer to the second question turned out to be
"none of it".

`src/backend/c.rs` is 898 lines and `src/backend/c_prelude.c` 1270;
`tests/c_backend_tests.rs` (563 lines) is the contract. The change to
existing compiler code is 47 added lines across three files, all
additive — the backend is a sibling of `lower`, not a modification of
it.

## Using it

```sh
talk build --native prog.tlk -o prog     # emit C, drive cc, produce ./prog
./prog

talk c prog.tlk > prog.c                 # or just look at the C
```

`--cc` selects the compiler (default `$CC`, else `cc`; clang works),
`--cflag` appends flags, and `--keep-c` leaves the generated translation
unit beside the executable. The result depends on nothing but libc — no
Talk runtime is linked, and there is no bytecode in the binary.

### Cross-compiling

```sh
talk build --native prog.tlk -o prog --target aarch64-linux-musl
```

The host toolchain is the default because the generated file is ordinary
self-contained C and whatever the machine already has will build it.
Cross-compiling is the case that needs more than a compiler — headers and
a libc for the target as well — so `--target` goes through `zig cc`,
which carries its own. Without zig the build fails with an explanation and
an install link rather than a "command not found" from a child process,
and `--cc` remains an escape hatch for anyone who already has a cross
toolchain.

Verified from x86-64 Linux: `x86_64-linux-musl`, `aarch64-linux-musl`,
`aarch64-macos`, `riscv64-linux-musl`, `x86_64-windows-gnu`, and 32-bit
`x86-linux-musl`. The musl targets link statically — `ldd` reports "not a
dynamic executable" — which is what makes them shippable.

### The ABI the generated C assumes

Shippable binaries make the assumptions worth stating, so the prelude
asserts them and a target that breaks one fails to compile rather than
misbehaving:

```c
_Static_assert(CHAR_BIT == 8, ...);
_Static_assert(sizeof(int64_t) == 8, ...);
_Static_assert(sizeof(double) == 8, ...);
_Static_assert(sizeof(void *) <= 8, ...);
```

Pointers only have to *fit*: MIR sizes every non-byte memory element at
eight bytes, so a narrower pointer leaves the rest of its slot unused.
That is why 32-bit targets work, and the 32-bit build is in the verified
list above precisely because the reasoning deserved a measurement rather
than an argument.

Ahead-of-time cost is about 0.29s for a bench program, against 0.025s to
write a bytecode image; the difference is `cc`.

The emitted file needs no runtime library and no build system: MIR locals
become one `TalkValue l[]` array per activation, basic blocks become labels
and `goto`s, and the C compiler does the register allocation and
instruction selection.

## Coverage

Every MIR instruction is translated. Across `tests/programs/`, `bench/`,
`examples/`, and the `tests/reference/` corpora: **229 programs compile and
agree with the interpreter, none disagree, and none are rejected for a
backend limitation.** The 94 that do not compile are 78 compile-only
fixtures with no `main` and 16 deliberate checker-error cases — programs
the checker refuses, which never reach a backend.

The instruction match is exhaustive rather than defaulting: a variant
added to MIR later is a compile error in the backend, not a program that
quietly does something else.

## What it accepts

The whole scalar set (integer, boolean, byte, float), aggregates, closures
and indirect calls, effect handlers, managed memory, static literal data,
program globals, host IO, `'heap` objects with merge-only regions, cells,
and existentials.

Three things are deliberately partial rather than absent:

- **All 24 host IO operations are implemented** on unix — files, sockets,
  poll, directories, environment, process arguments — as POSIX wrappers
  matching the runtime's return conventions (negated errno, entries sorted
  by name, symlink-before-directory classification). On a non-unix host
  everything but stdio returns `EPERM`, which is what the runtime does.
- **Value aggregates are never reclaimed during a run** (see below).
- **A use-after-teardown is undefined** rather than a clean trap, since
  buffers and objects use machine pointers. Same trade as the memory
  model; the checker is what prevents it.

## Effects on the C stack

Effects needed three things the C stack does not provide: frame identity, a
handler stack, and a way to leave several activations at once. None of it
required `setjmp`.

A `Value::Cont` is `(frame_index, frame_id)` — a one-shot, outward-only
*return* continuation, not a resumable coroutine. So frame identity is a
shadow stack: a function pushes a fresh id on entry and pops on every exit,
and a continuation is live exactly when the frame at its depth still has
its id, which is the VM's own liveness test.

Unwinding is a return-status protocol, because MIR already models it
explicitly — calls carry an optional cleanup block and `Term::UnwindRet`
ends one. `AbortTo` sets a global unwind target and returns; every call
site asks whether it is the target (deliver the value as this frame's
return) or not (run the cleanup block, keep unwinding). Aborting to the
aborting frame's own continuation is special-cased to an ordinary return,
matching the VM's "target is the executing frame" path.

Resumption needs nothing at all: a perform site is `FindHandler` + floor
save/set + `CallIndirect` + floor restore, so a clause that returns
normally *is* the resume, and its value is the perform expression's value.

Only functions containing `MakeCont`, `PushHandler`, or `AbortTo` carry
frame bookkeeping — continuations only ever name the frame that created
them, so nothing else can be a target. Hot leaf functions pay nothing, and
the per-call `if (talk_unwinding)` check is a predictable branch on a hot
global: the benchmark numbers below are unchanged from before effects
landed.

## Results

Four archetypes from `bench/`, rewritten as zero-argument entries in
`bench/c-spike/` with iteration counts unchanged. Every C answer matches
the pinned `bench/expected/*.stdout`. `exec_ms` is the interpreter's wall
time minus its measured 20ms fixed cost (parse, check, compile, startup),
so it compares execution against execution.

| Program | interpreter | exec only | C | speedup |
| --- | ---: | ---: | ---: | ---: |
| `arith` (1M) | 206ms | 186ms | 2ms | ~93x |
| `arith` (10M) | 1849ms | 1829ms | 4ms | ~450x |
| `calls` (fib 26) | 84ms | 64ms | 2ms | ~32x |
| `calls` (fib 30) | 431ms | 411ms | 10ms | ~41x |
| `fields` (300k) | 230ms | 210ms | 20ms | ~11x |
| `dispatch` (400k) | 216ms | 196ms | 7ms | ~28x |

Ahead-of-time cost is 21-29ms to emit plus 35-48ms for `cc -O2`, i.e.
56-77ms total for 320-430 lines of C.

### Whole programs

The table above measures entry functions in isolation. Whole programs,
with script entry and `print` through the ambient IO handler, against the
frozen `bench/expected/*.stdout`:

| program | VM | C | speedup |
| --- | ---: | ---: | ---: |
| `arith` | 210ms | 1ms | 210x |
| `strings` | 457ms | 11ms | 42x |
| `calls` | 84ms | 4ms | 21x |
| `effects` | 62ms | 3ms | 21x |
| `dispatch` | 213ms | 11ms | 19x |
| `arrays` | 271ms | 18ms | 15x |
| `fields` | 241ms | 9ms | 27x |
| `drops` | 236ms | 38ms | 6x |

### Frame allocation for non-escaping aggregates

A record, tuple, or enum payload is a value, and the backend picks its
storage. The default is the arena, which is not reclaimed until exit — and
at three million iterations of `bench/fields.tlk` that showed up as kernel
time exceeding user time: the cost was page faults, not the bump.

`src/backend/c_escape.rs` finds the construction sites whose value
provably never leaves the frame, and gives each one a storage slot in the
activation, reused on every execution of that site. `fields` went from
19ms to 9ms, and at three million iterations system time fell from 107ms
to 1ms. This is ADR 0044's rule 3 applied to value aggregates, and the
ADR is clear that MIR should eventually own the decision rather than a
backend.

Two details that turned out to matter:

- **Parameter summaries are read before register allocation.** Whether a
  callee lets a parameter outlive the call is a property of the callee,
  not of its register assignment — but after `reuse_locals` a parameter's
  slot can be recycled for a temporary that happens to be returned, which
  makes the parameter look escaping and costs every caller its frame
  allocation. Measured on `fields`: reading the summary post-allocation
  put one of the two `Point`s back in the arena. The per-site analysis
  still runs on the allocated program, where slot reuse can only be
  conservative.
- **Flow into a block parameter counts as an escape.** A site has one
  storage slot, so a value that crosses a loop's back edge would be
  observed after the slot was reused. This is why `dispatch` does not
  benefit: its variants reach the accumulator through block parameters.
  Handling that is where the next increment of this optimization is.

### The scalar number is a VM finding, not a C finding

450x is not a claim about code generation quality. The `arith` loop body is
exactly 8 bytecode instructions (`talk bytecode --entry bench`), and the VM
runs 10M iterations in 1829ms:

    1829ms / 10M iterations / 8 instructions = ~23ns per bytecode instruction

At this machine's clock that is roughly **100 cycles per bytecode
instruction**. A switch-dispatched register VM is normally 5-20. The gap
between this VM and native code is dominated by per-instruction cost, not
by anything a compiler backend is uniquely able to fix — which means most
of that 450x is reachable from inside the VM.

The disassembly confirms the C side is honest: GCC compiles the loop to six
instructions with `cmp $0x989680` / `jne`, no vectorization and no
final-value replacement. It runs at ~1.2 cycles per iteration because the
only loop-carried dependency is a single-cycle `add`.

### The tagged union costs nothing in scalar code

`TalkValue` is a 16-byte `{uint8_t tag; union {int64_t i; TalkAgg *agg;}}`.
In `arith` it disappears entirely — GCC's SROA scalarizes it and not one
tag store survives into the object code. The representation only costs
where values reach memory, which is why `fields` (11x) sits an order of
magnitude below `arith` (450x): its 600k records are real allocations, and
the ratio there measures allocator against allocator rather than dispatch
against native code.

## Aggregate memory, stated correctly

An earlier draft of this document called the arena a shortcut, on the
grounds that MIR emits no `Free` for records. That was the wrong framing.

MIR *does* derive releases from the CFG (`mir/release.rs`), but only for
types that own something: `needs_drop` is false for a nominal struct with
no buffer field and no `Deinit` hook. `Point { x: Int, y: Int }` owns
nothing, so no drop glue is synthesized and no release is emitted — not
because the information is missing, but because there is no resource. A
record is a *value* with mutable value semantics; ADR 0044 does not even
list value aggregates among the substrates, and its only real substrate
choices are closure environments and cells.

So the `Rc` in `Value::Record` is not a lifetime the C backend failed to
recover. It is the VM's chosen representation for making value copies O(1)
with copy-on-write on update. The arena is a different representation of
the same semantics. `SetField` copying unconditionally is likewise a valid
copy-on-write implementation, at a worse constant, because there are no
counts to consult.

### The VM had the same unbounded growth, and no longer does

Investigating the arena turned up the same property in the VM, for the
substrate MIR *does* track. `Allocations::allocate` always appended at
`mem.len()`, `free` only marked the record dead, and no record was ever
reclaimed — so an allocate/free loop grew memory forever even with every
buffer correctly freed and the exit balance satisfied. `'heap` objects
were worse, at roughly 175 bytes per object against 24 per buffer.

Both are fixed in `talk-vm`, and both are now flat:

| | before | after |
| --- | ---: | ---: |
| buffers, 4M iterations | 285.5 MB | 30.1 MB |
| `'heap` objects, 1.6M iterations | 590.5 MB | 30.2 MB |

Freed spans go on a size-keyed free list, and records live in a map keyed
by a never-reused id, removed when the count reaches zero. Reuse is not a
weakening: every access resolves its record through the pointer's
*provenance*, which is still minted fresh per allocation, so a dangling
pointer finds its own dead record however many times the address is handed
out again. Objects got the same treatment, plus tracking of the region ids
`union` absorbs so teardown reclaims a merged tree whole.

Measured no regression on the memory-heavy programs: `drops` 234→239ms,
`strings` 454→455ms, `arrays` 261→267ms.

### The real fix is not reference counting

Because value aggregates are values, the right answer is not to reproduce
`Rc` in C — it is to stop boxing them. `fields.tlk` builds two `Point`s per
iteration that never escape; GCC already proves it can scalarize
`TalkValue` completely when nothing reaches memory. Emitting a record of
scalars as a C struct by value would make that loop allocate nothing at
all, which is exactly why `fields` (11x) trails `arith` (450x).

What blocks it is representation, not analysis: `TalkValue` is a uniform
16-byte tagged union, so unboxing needs per-symbol C struct types and
therefore a type for every MIR local — and MIR locals are untyped `u16`
slots. A local's type is inferable from its defining instruction, but
`regalloc::reuse_locals` merges slots across types before the backend sees
them. In the emitted `fields.c`, `l[5]` holds a `Point` and then an `Int`.
Emitting before `reuse_locals` and inferring local types is the path; it is
a real piece of work, and it is where the remaining order of magnitude on
aggregate-heavy code is.

## Distance to full parity

Measured against the whole oracle corpus (`tests/programs/*.tlk` with
frozen stdout, plus `bench/` and `examples/` — 58 programs), the union of
MIR instructions is ~40 kinds. What is left, in the order the work
naturally falls:

**Done since.** Static data for `StringLit`/`BytesLit`, program globals,
and managed memory
(`Alloc`/`Free`/`RetainPtr`/`IsUnique`/`Load`/`Store`/`PtrAdd`/`MemCopy`,
including `Boxed` slots that reuse their cell). Buffers are `malloc` with a
reference-counted header; a pointer into the static blob is never retained
or freed, matching provenance zero.

The exit balance check runs in the generated program: a scalar result owns
no buffers, so any live allocation at exit is a leak and fails the run.
Every differential test is therefore also a leak test, and the
string-concatenation loop passes — MIR's release placement translates
faithfully.

**Done since.** Cells, existentials, `GetElement`, byte and float
arithmetic, `'heap` objects with merge-only regions, the host IO table,
and result rendering for aggregates. Coverage is complete: every MIR
instruction is translated.

**Settled: no new dependence on `talk-vm`.** Buffers use machine
pointers with a reference-counted header rather than the VM's simulated
byte memory, and the 24 `Io` operations are POSIX wrappers in the prelude
— which is where they are most natural anyway. Result rendering needs the
type and member names, which the emitter writes out as static tables.

The cost of that choice is the VM's per-access bounds and provenance
checking, which is what makes `unsafe` Talk trap deterministically instead
of corrupting. It should come back as an opt-in compile-time mode in the
prelude rather than be dropped. There is a concrete case already: a script
whose result is a `let`-bound String has that buffer released before the
result is displayed, and where the VM reports "display through invalid
pointer", the generated C reads the freed bytes and prints them. The
underlying release placement is a pre-existing bug — the VM behaves the
same way before any of this work — but the C backend's inability to *see*
it is exactly what the checked mode would fix.

### Known divergences

Everything below was found by running both targets and comparing stdout,
stderr, and exit status, not by reading the code.

**Permanent, by construction:**

- `RawPtr(n)` prints the VM's simulated address and this target's machine
  pointer. Object identity, by contrast, *is* recoverable: `<object #n>`
  uses the allocation ordinal, which counts the same way in both.
- Trap wording. Exit codes agree — both 1 — but the VM adds the chunk and
  offset and a balance report, where the generated program prints the bare
  message. A trap that comes from a MIR `Trap` string, such as an array
  bounds check, is identical in both.
- Execution budgets. `Budgets::instructions` and `memory_bytes` have no
  equivalent in generated C. Not reachable through `talk run`, which
  leaves them at their maxima, but an embedder that sets them gets
  enforcement from one target only.

**Waiting on the checked mode:**

- Reading memory after its buffer was released. A script whose result is a
  `let`-bound String has that buffer released before the result is
  displayed: the VM reports "display through invalid pointer", the
  generated C reads the freed bytes and prints them. The release placement
  is a pre-existing MIR bug — the VM behaves identically before any of
  this work — but only one target can currently *see* it.
- The exit leak fence is weaker here. The generated program checks live
  allocations only when the result is a scalar, because it cannot compute
  an aggregate's footprint; the VM computes `result_allocations` and
  always checks against it.

**Closed:**

- Runaway recursion used to take SIGSEGV here against a clean
  `call stack overflow` from the VM. Every function now checks its
  remaining stack on entry, and both exit 1 with a diagnostic. The bound
  is on stack *bytes* rather than a frame count: the VM's million frames
  against a typical eight-megabyte stack would fault long before the count
  was reached, and emitted frames vary in size. It measures the distance
  from an anchor taken in `main`, which costs a subtraction and a compare
  on entry and needs nothing undone on the way out — no benchmark moved.
  The budget is read from `RLIMIT_STACK` at startup rather than assumed,
  because a compiled-in figure crashes on any host with a smaller stack;
  verified from `ulimit -s 8192` down to `256`.
  `-DTALK_STACK_BUDGET=<bytes>` pins it where the limit cannot be read.
- Protocol existentials rendered their witness table. They now carry the
  protocol's display identity and render as their payload, as the runtime
  does.
- String rendering copied bytes straight through. A Talk string is bytes,
  so slicing one mid-character leaves a sequence that is not valid UTF-8;
  the runtime converts through `String::from_utf8_lossy` first. The
  renderer now applies the same maximal-subpart rule, one U+FFFD per
  invalid subpart.

One incidental finding from the same sweep: `i64::MIN` renders as a bare
`-`, a bug in core's `Int` rendering. Both targets reproduce it
identically, which is some evidence the translation is faithful enough to
carry core's bugs and not just its correct behaviour.

### Worth doing regardless

Measure the VM against the ~23ns-per-bytecode-instruction figure. If that
comes down to a normal 5-20 cycles, a large part of the gap closes without
a second backend to maintain.

## What would make this mergeable

Coverage is no longer the question. What remains is product decisions
rather than translation work:

1. **An opt-in bounds-checking mode**, to give back the deterministic trap
   the VM's simulated memory provides for `unsafe` Talk. The prelude is the
   natural place for it.
2. **Block-parameter flow in the escape analysis**, which is what still
   sends `dispatch`'s variants and `drops`'s pairs to the arena.
3. **Windows and macOS coverage in the sweep.** Cross-compiling to them
   is verified, but nothing runs the resulting binaries; the host IO
   layer is POSIX and returns `EPERM` off it.

`scripts/c-backend-sweep.sh` compiles all 335 corpus programs through both
targets and fails on a byte of disagreement; it runs in about ten seconds
across twelve cores, under both gcc and clang, and both are CI jobs. The
clang lane earned its place on the first run by catching a GNU extension
gcc had accepted.
