# Profiling findings

Current state as of commit `7bc48b90` (2026-07-18), measured on the
talk-syntax suite (225 tests) and the benchmark corpus (`bench/`).
Full history and method live in the published profile report; this
file records where things stand and what each finding rests on.
Instruction counts are the load-bearing metric throughout — the
measurement machine throttles under sustained benchmarking, and wall
clocks drifted up to 20% across batches at identical instruction
counts.

## Headline

| Measure | Value |
| --- | --- |
| Native instructions, full suite run | 5.81 G (was 13.15 G at first profile) |
| VM instructions executed | 15.2 M (was 28.8 M) |
| Wall clock (best of 5, throttled) | 0.68 s (was 8.28 s) |
| Backend compile (direct timers) | 66 ms (was ~400 ms) |
| Emitted bytecode | 50,280 instructions (was 215,508) |
| Widest frame | 148 registers (was 48,824) |
| Peak RSS | 101 MB |

## The shape of a run

VM execution 51.3% (~3.34 G native instructions), frontend compile
~28% (type check 15.7%, name resolution 7.4%, parse 6.1%, desugar
3.6%), backend compile 10.3%, harness/misc ~10%. Backend passes:
`mir_build` 50.4 ms, `inline` 1.2 ms, `regalloc` 10.5 ms (fusion
deletes ≈5,200 copies; the pass now removes more instructions than
any pass adds), `lower` 3.5 ms.

## What the VM executes

GetField 2.25 M (14.8%), Add 2.16 M (14.2%), Branch+Cmp 3.60 M
(23.7%), Const 1.49 M (9.8%, non-RK positions only), Call+Ret 1.44 M
(9.5%), Load 0.79 M, Mul/Div/Sub/BToI 1.83 M, Jump 0.25 M (was
1.61 M before threading), RecordNew/SetField/Extract 0.59 M, Move
under 0.17 M (was 29% of all execution at its peak). The scalar-loop
archetype runs 8 VM instructions per iteration with no moves and no
constant loads; `fib` is 10 instructions total with its parameter,
base-case join, and recursive sum coalesced onto one register.

## Per-instruction implementation costs

Measured by delta microbenchmarks: paired 2M-iteration programs with
K and 2K occurrences of one construct, compiled to images with
`talk build`, instruction-counted with `perf stat` on
`talk run-image`, differenced — `(I_2K − I_K) / (N·K)` is exact and
sampling-free. Costs include all dispatch work.

| Construct | Native insns / execution | Handler notes |
| --- | --- | --- |
| Const | 159 | pool index + Value clone + register write — near the dispatch floor |
| GetField | 163 | record match, Rc-fields index, Value clone, register write |
| Div (RK) | 204 | direct inline match, no helper |
| Add / Mul | 227–228 | `arith()` takes the ops as **function pointers** — uninlinable indirect call per instruction |
| Cmp + Branch + Jump | ≈436 for the trio | ≈145 each; near-floor handlers |
| Call + Ret pair | ≈543 | pool pop, per-argument clone, frame push; delivery and recycle |
| RecordNew (2 fields) | ≈729 | argument Vec + Rc allocation — one malloc per construction |
| match, 2-arm enum | ≈955 composite | GetTag + Cmp + Branch + GetPayload + arm + join |

### Finding: the dispatch floor is ~145–160 native instructions, ≈65% of execution

The cheapest handlers bound the fixed per-instruction machinery:
bounds-checked fetch, four `frames[frame_index]` lookups, the
finalizer-pump gate, the `trace_mem` OnceLock atomic, the jump-table
match, and (for local instructions) an outlined `exec_local` call
that saves five registers and a 472-byte stack frame. At ~150 × 15.2 M
dispatches ≈ 2.3 G of the 3.34 G execution instructions, the floor —
not handler work — dominates. Hardware counters agree the rest is
already ideal: 0.79% branch misses, zero L1-dcache misses.

### Finding: arithmetic pays an indirect call per instruction

`interp::arith()` receives `ints: fn(i64, i64) -> i64` and a float
counterpart as function pointers, so every Add/Sub/Mul makes an
uninlinable indirect call to run one machine instruction of real
work — measured ~24 instructions worse than Div, whose handler
matches inline. ≈70 M wasted instructions per suite run.
Monomorphized generics (`impl Fn`) or direct per-opcode matches
remove it.

## Ranked opportunities

1. **Solver instrumentation** (type checker, 15.7% of run) — the
   largest unexplained mass; profile is flat, so measure constraint
   volume/wakeups/re-examination per binding group before touching
   anything. Representation changes were probed and declined on
   evidence (`Ty` sharing: ~300 edit points for 15–20 ms).
2. **Dispatch-loop frame caching** (~4% of run) — cache the current
   frame's chunk/pc/regs in locals between frame switches.
3. **Finalizer gate onto region-release/return events; `trace_mem`
   flag into a loop local** (~1.5%).
4. **Plain-loop argument collection; monomorphized `arith()`** (~2%).
5. **Switch-based match dispatch** — the VM's `Switch` instruction is
   never emitted; wide-enum matches (the parser's 60-way `Kind`
   dispatch) still run cmp chains inside Branch+Cmp's 23.7%.
6. **Loop-invariant `FindHandler`** — parked: sound hoisting needs
   loop inversion (a missing-handler trap must not fire early on
   zero-iteration loops).
7. **The ceiling** — with prediction and caches perfect, only
   baseline compilation (copy-and-patch, Xu & Kjolstad OOPSLA 2021)
   removes the interpretation tax.

## Infrastructure

- `bench/` — eight archetype programs with pinned outputs
  (`bench_corpus_runs`) and pinned code shapes
  (`bench_bytecode_is_tight`): the analysis surface for IR
  (`talk mir`) and bytecode (`talk bytecode`) reading.
- Probes are temporary and env-gated (opcode histogram in the
  dispatch loop, pass timers around the backend), added for a
  measurement and removed in the same session; none live in tree.
