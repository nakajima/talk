# 0034 - Lean bytecode backend architecture

Status: proposed for review (2026-07-16)

Supersedes the implementation-shape requirements of ADR 0019 and ADR 0032.
Semantic decisions in those ADRs remain in force; see "What this ADR does not
change" below.

Plan: [Lean backend rebuild plan](../lean-backend-rebuild-plan.md)

Behavior inventory: [Backend parity ledger](../backend-parity-ledger.md)

## Context

The frontend-only reset (ADR 0031) removed the archived backend. The rewrite
that followed restored only scalar execution while adding roughly 48,000 lines
against fewer than 5,000 deleted since `a1d20d27`. The cost was structural:
the canonical TypedProgram duplicated frontend meaning into a second
representation, private single-producer seams received serialization-grade
validators, and every narrow behavior paid producer, validator, verifier,
fixture, handshake, and documentation costs across four public contracts.

Parnas's information-hiding criterion says modules should hide design
decisions likely to change, not expose them as inter-module contracts
[Parnas 1972, "On the Criteria To Be Used in Decomposing Systems into
Modules"]. Ousterhout's depth criterion says a module is valuable when its
interface is much smaller than its implementation [Ousterhout 2018, *A
Philosophy of Software Design*]. The G0-G5 contract stack inverted both: the
interfaces between private phases were larger and more rigid than the phases
themselves.

Measured at the reset checkpoint (2026-07-16, non-blank non-comment `.rs`
lines, dedicated test files excluded):

| Corpus | Production code | Test-file code | Comments |
| --- | --- | --- | --- |
| Archived backend (`96249e71`: `src/flow`, `src/lower`, `src/lambda_g`, `src/vm`) | 21,657 | 6,986 | 3,388 |
| Archived runtime (`96249e71`: `talk-runtime/src`) | 5,141 | 0 | 326 |
| Rewrite backend at `65c93acf` (mir, talk_ir, bytecode, contract stack, provenance, scalar runtime) | 27,809 | 1,587 | 67 |
| Reset branch after removal (whole `src`, `talk-runtime`, `wasm`, `talk-c`; frontend + runtime, no backend) | 56,050 | 11,574 | 3,363 |

The rewrite spent more production code than the entire archived backend to
restore a minority of its behavior.

## Decision

### 1. One deep backend interface

The compiler exposes exactly two backend entry points:

```text
compile(typed frontend output, entry, target configuration)
    -> executable module or diagnostics
execute(executable module, host interface)
    -> result or runtime failure
```

Everything between frontend output and the executable module is a private
implementation detail of one crate-internal backend module. No phase
representation is a public type, a serialization format, or an extension
point. This is the depth criterion applied: the interface stays two calls
wide while the implementation grows toward parity.

### 2. Private phases, not public artifacts

The backend may use internal stages:

```text
frontend result
  -> source MIR with ownership checking
  -> monomorphic lowering
  -> bytecode encoding
  -> validated bytecode execution
```

- MIR is the one source-level control-flow graph and owns moves, borrows,
  cleanup, pattern control flow (compiled following Maranget 2008, "Compiling
  Pattern Matching to Good Decision Trees"), and ownership diagnostics
  (ADR 0010, ADR 0032 source memory model). Ownership checking follows the
  substructural discipline surveyed by Walker [2005, "Substructural Type
  Systems", *ATTAPL*]: affine locals, explicit moves, no borrow escape.
- Monomorphization is whole-program, as in MLton-style whole-program
  compilation and TIL [Tarditi et al. 1996, PLDI]: generic bodies specialize
  against concrete instantiations discovered from the entry's reachable call
  graph. There is no separate public target-neutral IR module unless a second
  real target adapter requires one.
- Bytecode is the reference execution target. Effects use dynamic
  nearest-handler routing with one-shot resumptions [Plotkin & Pretnar 2013,
  "Handling Algebraic Effects"; Bruggeman, Waddell & Dybvig 1996,
  "Representing Control in the Presence of One-Shot Continuations"].

A new internal seam is introduced only when at least two real consumers
require it. A stage that one function can express is a function, not a
module.

### 3. Trust policy

Full validation belongs at real trust seams only:

- source and module data loaded from outside the process;
- bytecode loaded from bytes, which is untrusted and must validate before
  execution, exactly as bytecode verification is placed in the JVM
  [Leroy 2003, "Java Bytecode Verification: Algorithms and Formalizations"];
- host calls and unsafe memory interfaces;
- separately compiled module artifacts and serialized IR, if ever introduced.

Values produced and consumed inside one compiler invocation rely on
construction invariants, focused assertions, and tests through the public
backend interface. A semantic rule has one owner; no phase re-proves an
upstream phase's decisions. Ownership checking is mandatory semantic work; a
second checker that replays it is not.

### 4. Provenance policy

Successful ownership and borrow explanations are answered by querying MIR
operations on demand. Rejected programs build their explanation while the
ownership checker still holds the failed transition. There is no eagerly
materialized whole-program provenance graph, no fixture-only provenance
representation, and no verifier for a graph derived from already-checked MIR.

### 5. Target policy

Bytecode is the only parity backend. `talk run`, package execution, source
tests, the REPL, standalone executables, C/Swift embedding, and the browser
embedding all call the same `compile`/`execute` pair. Independent Wasm, C
translation, Cranelift, and LLVM adapters wait until required parity and the
size budget are both met.

### 6. Size budget and accounting

The archived production baseline is 26,798 lines (21,657 backend + 5,141
runtime). The full-parity budget for the new backend — including frontend
code added solely to feed it and runtime adapters added solely to execute it
— is:

```text
13,400 production lines (50% of the archived baseline)
```

Production code, test code, comments, blanks, generated code, and
documentation are reported separately on every wave, so reductions cannot be
manufactured by moving lines between categories. Crossing the budget stops
implementation for an explicit architecture review; the plan's per-wave stop
conditions apply unchanged.

### 7. What is superseded

From ADR 0019: the requirement that type checking publish a standalone
`TypedProgram` artifact and that lowering consume a public `CheckedMir`
enum surface. The frontend hands the backend its existing typed output; the
backend derives what it needs privately.

From ADR 0032, the implementation-shape sections are superseded:

- the `TypedProgram` contract (canonical item store, exported scalar
  implementation recipes, serialization-grade validators);
- the `CheckedMir` contract as a public validated artifact;
- the MIR-to-Talk-IR lowerer contract and the `TalkIrModule` contract;
- the cross-artifact laws and per-seam negative-fixture obligations;
- the parallel implementation agreement and the G0-G5 gate checklist;
- the migration plan's artifact-first sequencing.

## What this ADR does not change

All accepted source-language semantics stand, including:

- frontend authority over parsing, names, types, conformance selection, use
  and capture modes, and effect rows (ADRs 0001-0007, 0013-0016, 0018,
  0020-0026);
- the ADR 0032 source memory model, effect and control-flow linearity rules,
  memory-effect vocabulary, and target-neutral scalar intrinsic semantics;
- ownership and cleanup semantics (ADRs 0010, 0011, 0014, 0015, 0017-0019
  semantic content, 0021, 0025, 0027, 0028, 0030);
- runtime and storage decisions: signed 64-bit `Int`, borrowed
  extended-grapheme `Character` (ADR 0012), rejection of uniform reference
  counting (ADR 0029), managed buffers, type-specific copy-on-write,
  merge-only heap regions, lifecycle hooks, and host-resource accounting
  (ADR 0008, 0009, 0033);
- package supply and deterministic initialization (ADR 0023).

## Consequences

- The backend restores behavior wave by wave from the parity ledger, each
  wave starting from a failing black-box test through the public interface.
- Deleting an internal phase must force its complexity into multiple callers;
  if deletion simply removes code, the phase was too shallow to keep.
- The archived implementation and the removed rewrite remain quarries: code
  may be copied after review, but no interface returns merely because it
  exists in history.
- Editor features that explained ownership through the provenance graph now
  query MIR; their user-visible behavior is preserved, their implementation
  is not.
