# Profiling findings

Status: current frontend runtime snapshot after owned RK materialization
(2026-07-30). Exact frontend bytecode counts and detailed methodology are in
[`frontend-vm-report.md`](frontend-vm-report.md); the full generated report is
[`profiles/frontend-vm/d2bd469efa5d-dirty-a6b49355f2ef.txt`](../profiles/frontend-vm/d2bd469efa5d-dirty-a6b49355f2ef.txt).

Native instruction counts are the load-bearing metric. The measurement machine
throttles under sustained work, while instruction and branch counts are highly
reproducible. Wall time and sampled attribution are supporting evidence.

## Current headline

| Measure | Current |
| --- | ---: |
| Native instructions, root library suite | 748.512 B |
| Native cycles | 370.319 B |
| CPU task time | 87.779 s |
| Native branches | 112.431 B |
| VM instructions, frontend corpus | 175,259,482 |
| Emitted frontend bytecode | 96,851 instructions |
| Frontend artifact | 836,288 bytes |

The native workload runs the root library test executable directly with 12
fixed test threads, one warmup, and five `perf stat` repetitions. Cargo and
build time are excluded. The exact VM workload parses the four sorted
`stdlib/syntax/*.tlk` files through a twice-built fixed-point candidate.

## Shape of the critical path

Per-test timing identifies
`compiling::bridge::tests::structured_results_validate_over_corpus` as the
12-thread library suite's wall-time gate. An isolated five-run A/B reduced that
test's elapsed time from 8.900 to 8.499 seconds (-4.50%), native instructions
by 4.00%, cycles by 3.96%, and branches by 4.36%. A single parallel suite run
can hide this gain through scheduler contention.

The frame-pointer capture after forwarding but before owned RK materialization
attributes 97.59% of this test's weighted cycles to the frontend VM.
Overlapping inclusive costs were `rk` at 13.19%, `call_regs` at 11.06%,
`arg_values` at 8.81%, and `deliver_return` at 3.91%. The owned RK change then
reduced the isolated critical path by another 6.03% elapsed, 6.38% cycles, and
3.15% native instructions. This attribution must now be refreshed.

## Improvements retained in this profiling round

### Owned RK materialization

`rk_value` directly produces owned register and constant operands for calls and
aggregate construction, while arithmetic and comparisons keep borrowed `rk`.
`arg_values` now uses a pre-sized explicit loop instead of collecting an
iterator of `Result`s. The isolated critical-path A/B reduced elapsed time by
6.03%, cycles by 6.38%, instructions by 3.15%, branches by 3.76%, and branch
misses by 26.06%. Full-suite native instructions fell 2.77% and cycles 6.05%.

### Transparent forwarding calls

A strict whole-program MIR pass retargets direct calls through one-block,
unwind-free identity forwarders. Forty static rewrites remove 6,764,604 exact
dispatches and 3,382,302 frame round trips without changing artifact size. The
conservative adjacent native A/B reduced instructions by 2.62%, cycles by
2.77%, CPU task time by 2.61%, and branches by 2.84%. Branch-miss direction was
inconsistent and is not claimed as an improvement.

### Checked indexed loads

Thirty-seven structural access sites execute 3,477,483 times. Replacing their
replay-safe success paths with `CheckedIndexedLoad` reduced exact dispatches
from 213,321,433 to 182,024,086 (-14.67%) while increasing the artifact by
2,146 bytes (+0.26%). Native instructions fell approximately 8.2% in the
isolated A/B. Failure still jumps to the original source-owned bounds helper,
so Talk's catchable `'panic` semantics are unchanged.

### Frame-cached code slices

Each frame now stores its immutable instruction slice. Dispatch no longer
reconstructs a chunk and `Vec<Insn>` slice on every instruction. The isolated
A/B reduced native instructions by 16.01%, cycles by 12.62%, CPU task time by
12.18%, branches by 16.90%, and branch misses by 19.38%. The old `interp::chunk`
hotspot fell from 6.16% to approximately 0.62% inclusive.

### Provenance-carrying pointers

Pointers carry an address and allocation token in the existing eight-byte raw
pointer cell. Access checks index the append-only allocation record directly
and validate provenance, liveness, and range. The isolated A/B reduced native
instructions by 9.82%, cycles by 9.94%, CPU task time by 8.73%, branches by
10.14%, and branch misses by 15.14%.

`Allocations::check_access` is now 1.13% inclusive, down from 7.56%, and the
6.87% `record_containing` predecessor lookup is absent. Further memory-check
micro-optimization is no longer high priority.

## What the VM executes

| Opcode | Executions | Share |
| --- | ---: | ---: |
| `GetField` | 41,678,989 | 23.78% |
| `Branch` | 23,760,887 | 13.56% |
| `Cmp` | 18,752,400 | 10.70% |
| `Add` | 12,280,221 | 7.01% |
| `Ret` | 11,204,762 | 6.39% |
| `Call` | 11,204,754 | 6.39% |
| `Jump` | 10,208,983 | 5.83% |
| `Const` | 10,102,982 | 5.76% |
| `Load` | 5,250,828 | 3.00% |
| `CheckedIndexedLoad` | 3,477,483 | 1.98% |

Calls and returns together are now 12.79% of dispatches. Owned RK
materialization is runtime-only, so these exact opcode counts do not change.

The dominant successful checked access is now six instructions:

```text
GetField
GetField
GetField
CheckedIndexedLoad
Jump
Ret
```

The checked operation itself is compressed, but its success `Jump` executes
3,477,483 times and remains a concrete direct-emission opportunity.

## Ranked opportunities

1. **Refresh the critical-path frame-pointer profile.** The prior `rk`,
   `call_regs`, and `arg_values` weights predate the retained owned-value path.
2. **Semantic checked indexed loads in MIR.** Direct emission can remove the
   structural matcher, make success fall through instead of executing
   3,477,483 `Jump`s, and cover unit-width accesses while retaining the
   original source-owned failure target.
3. **Call-frame construction.** Only investigate register initialization or
   pool changes if the refreshed profile still identifies them as material.
   Ownership and continuation behavior remain hard constraints, and checked
   register access must remain safe Rust.

Every runtime optimization remains subject to a direct 12-thread, five-run
native-counter A/B. Exact dispatch reductions alone are necessary but not
sufficient.

## Capturing a Tracy profile

The compiler and runtime use the `profiling` facade. Instrumentation is a no-op
in normal builds; the root `profile-tracy` feature enables Tracy consistently
for both crates:

```text
cargo run --features profile-tracy -- run path/to/program.tlk
cargo test --lib --features profile-tracy TEST_FILTER
```

Start the Tracy viewer before the profiled operation, then connect to the
process. Current scopes cover parsing, name resolution, type checking, service
compilation, bootstrap stages, frontend artifact loading and execution, bridge
adaptation, backend work, and VM export execution. Tracy's timer fallback is
enabled for machines without invariant TSC support.

## Reproducible infrastructure

- `scripts/frontend-vm-stats.sh` builds and profiles a fixed-point frontend
  candidate without overwriting checked-in artifacts.
- `profiles/frontend-vm/` stores commit-addressed exact reports.
- `VmStats` owns exact opcode, chunk, and instruction-site accounting in the
  runtime; normal execution can use the no-statistics path.
- `bench/` contains pinned archetype programs for MIR and bytecode inspection.
- `talk bootstrap --check` is the explicit checked-in artifact gate.
