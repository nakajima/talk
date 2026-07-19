# E1 talk-runtime reuse audit

Status: completed design audit; fail-closed scalar runtime profile, Talk IR
adapter, and internal G5 source execution integrated (2026-07-14)

E1 contract: [E1 scalar execution plan](e1-scalar-execution-plan.md)

Reset authority: [ADR 0031](adr/0031-frontend-only-backend-reset.md)

Backend authority: [ADR 0032](adr/0032-single-artifact-ownership-and-lowering-pipeline.md)

`talk-runtime` survived the frontend reset as a quarantined legacy candidate.
This audit identifies the conventional scalar subset that may be reused for E1
and explicitly leaves every later runtime mechanism quarantined.

## Audit rule

Reuse is based on whether an implementation fits behind the new Talk IR target
interface. Existing code, tests, or apparent convenience do not make an old
representation authoritative.

The compiler-facing target seam is conceptually:

```text
verified TalkIrModule
  -> bytecode target adapter
  -> validated BytecodeModule
  -> runtime execution
```

The frontend, MIR, and Talk IR modules do not read runtime values, registers,
opcodes, memory records, or frames.

## Current runtime inventory

The crate currently contains:

- `lib.rs`: one broad register instruction enum and module/chunk representation;
- `bytecode.rs`: version-2 explicit encoding, decoding, and structural index
  validation;
- `interp.rs`: frame-stack interpreter, scalar values, aggregates, cells,
  closures, objects, continuations, memory, and IO dispatch;
- `memory.rs`: byte memory allocation records and type-specific CoW reference
  counts;
- `objects.rs`: old object-region graph and finalization implementation;
- `io.rs`: host and captured IO adapters;
- `symbol.rs`: legacy compiler symbol identity copied into bytecode.

Only the direct scalar subset is considered for E1.

## Reuse decisions

| Runtime area | E1 decision | Conditions |
| --- | --- | --- |
| Unit/Void, Bool, Byte, I64, F64 runtime values | Reuse | Meanings must match the E1 scalar contract exactly |
| Frame-stack direct calls and returns | Reuse implementation | Must be entered only with a validated E1 bytecode module |
| Register storage | Reuse | Registers are target mechanics, never Talk IR or source identities |
| Const and Move instructions | Reuse | E1 constants only; unsupported constant kinds rejected by profile validation |
| Add/Sub/Mul/Div arithmetic kernels | Reuse implementation | Integer and float semantics are normative in E1; pointer arithmetic is excluded |
| Compare kernel | Reuse implementation | E1 type/operation restrictions come from the adapter and verifier |
| Trunc, Int-to-Float, Byte-to-Int kernels | Reuse implementation | Conversion semantics fixed by E1 |
| Call, Jump, Branch, Switch, Ret, Trap | Reuse implementation | Strengthened control-target and profile validation required |
| Argument and switch pools | Reuse target mechanism | Every range and every contained target/register must validate |
| Explicit bytecode encoding pattern | Reuse design | No compatibility promise for version 2; serialization is not required for E1 |
| Captured IO adapter | Reuse later test utility | E1 has no source IO operation; result capture may use it harmlessly |
| Scalar rendering | Reuse formatting rule | TOOL-06 uses Talk syntax, suppresses Unit, and never exposes runtime enum names |
| Broad `Insn` enum as the accepted E1 interface | Reject as-is | E1 needs a validator-approved subset; old opcodes cannot pass silently |
| Legacy `Symbol` in bytecode | Reject for new linkage | E2 uses stable Talk IR import/export identities, not old compiler symbols |
| Cells | Deferred to H1 | No closure mutation in E1 |
| Records, tuples, variants | Deferred to L2 | Their old `Rc<Vec<Value>>` representation is not authority |
| Existentials and witness vectors | Deferred to D1 | Must follow the adopted witness representation |
| Closures and indirect calls | Deferred to H1 | Must follow new closure conversion and calling convention |
| Byte memory and pointer operations | Deferred to R1/K1 | No pointer-shaped E1 Talk IR values |
| Allocation records, retain, is-unique | Deferred to R1 | Type-specific CoW may be reused only after the managed-storage decision |
| IO opcodes and host marshalling | Deferred to K1 | Stable host-import contract not yet defined |
| Object arena and region graph | Quarantined | R1 must decide heap/cycle semantics before any reuse |
| Finalizer pump | Quarantined | Generated glue and deinit ordering must be adopted first |
| MakeCont, CallCont, unwind tables | Quarantined | C1 continuation representation is backend-private and not inherited |
| Version-2 serialized bytecode compatibility | Not required | The new compiler may introduce a new profile/version at T1 |
| Old scheduler assumptions | Rejected | Lambda-G and the scheduler remain deleted |

## Accepted E1 instruction profile

A validated E1 bytecode module may contain only the target equivalents of:

```text
Const
Move
Int/Float Add, Sub, Mul, Div
Int/Float/Byte Compare
Bool Equal/NotEqual
FloatToIntTrunc
IntToFloat
ByteToInt
Call
Jump
Branch
Switch
Return
Trap
```

The existing runtime may continue to use overloaded Add, Compare, and conversion
opcodes internally. The Talk IR adapter must start from an explicitly typed
`ScalarIntrinsic`, and E1 profile validation rejects every opcode outside the
accepted list before execution.

Unit return may use a Void constant and ordinary Return. Talk IR Never and
Unreachable lower to control flow or Trap; the target never materializes a
Never value.

E1 modules contain:

- no statics required by source semantics;
- no unwind entries;
- no closures or environments;
- no memory allocations;
- no object records;
- no IO operations;
- no legacy symbols;
- no unresolved imports.

## Validation findings

### R-E1-1: broad old instruction set - resolved for the E1 seam

`Module::decode_bytecode` validates indices for the old format but intentionally
accepts cells, aggregates, memory, IO, objects, continuations, and unwind
instructions. That is unsuitable as the E1 target gate.

`ValidatedBytecodeModule::new` now consumes a raw module and admits only the E1
scalar profile. The wrapper privately owns the module and exposes rendering and
counted execution. Legacy direct runtime tests may still construct raw modules;
the compiler target adapter returns only the wrapper.

Legacy direct runtime tests may continue constructing raw modules internally.
They do not establish compiler support.

### R-E1-2: branch and switch target validation - resolved for the E1 seam

The existing decoder checks that a jump target converts to `usize`, but not that
it is within the current chunk. Switch validation checks the pool range but not
each target value.

The E1 profile validates every Jump and Branch target, every claimed Switch
pool target including fallback, reachable fallthrough, entries, direct calls,
call arity, registers, constants, and fully claimed argument/switch pools before
execution.

### R-E1-3: opcode operand types are checked dynamically

The old bytecode format does not carry register types. Arithmetic and comparison
kernels return runtime errors when values have the wrong kind.

E1 decision:

- the Talk IR verifier is the static type authority for compiler-produced code;
- the bytecode adapter has one typed mapping per Talk IR operation;
- the runtime retains dynamic kind checks as defense against malformed modules;
- serialized bytecode validation may add target type metadata at T1, but E1 does
  not create a second source type system in the runtime.

No dynamic mismatch may panic.

### R-E1-4: overloaded arithmetic includes pointer behavior

The old Add/Sub implementation also accepts Ptr plus Int. E1 has no pointer
values and the profile excludes pointer constants and memory operations. The
adapter cannot select pointer arithmetic, and the profile/runtime checks reject
it if a malformed module attempts it.

### R-E1-5: version-3 bytecode records the E2 scalar-global extension

Format version 2 included legacy symbols, aggregates, objects, continuations,
unwind tables, and IO. Reusing its encoding unchanged would have made those
shapes a new compiler compatibility promise. E1 therefore relied only on the
in-memory validated seam.

E2 adds typed scalar global descriptors plus `GlobalGet` and `GlobalSet`, and
bumps serialization to version 3. The decoder rejects version-2 images; no
backward-compatibility promise is implied. Legacy opcode families remain encoded
for quarantined runtime tests but remain outside `ValidatedBytecodeModule`.
Future standalone compatibility and packaging policy still belongs to T1.

### R-E1-6: the compiler currently has no runtime dependency

ADR 0031 required the frontend-only compiler to have no `talk-runtime`
dependency. ADR 0032 permits a future bytecode target but does not require the
frontend or IR modules to depend on runtime details.

Accepted dependency direction for E1:

```text
talk compiler target adapter -> talk-runtime bytecode interface
talk-runtime -/-> talk compiler
```

Only the bytecode target adapter may import runtime target types. Frontend, MIR,
and Talk IR implementations remain independent. This dependency change lands as
part of the accepted E1 G0-G5 stack, not as an unrelated Cargo edit.

A new workspace crate is not required for E1. If bytecode format evolution later
forces compiler/runtime coupling beyond the target adapter, revisit a dedicated
format module then. One adapter does not justify that split today.

## Validated bytecode module interface

The deep target module should hide register allocation, edge copies, bytecode
pools, and profile validation behind one interface. Exact Rust names may differ:

```text
bytecode::compile(verified TalkIrModule, target config)
  -> Result<ValidatedBytecodeModule, BytecodeLoweringError>

runtime::run(ValidatedBytecodeModule, host)
  -> Result<RuntimeResult, RuntimeError>

driver::ScalarExecutable::run(host)
  -> checked zero-resource result with optional Talk-syntax rendering
```

The validated wrapper proves target-level structural validity and E1 profile
membership. It carries no new source semantic facts.

The raw runtime `Module` can remain available to legacy direct tests during
migration, but the new compiler path never bypasses validation.

## Talk IR adapter requirements exposed by the audit

The old bytecode has no Talk IR stack-slot address abstraction or block
parameters. The adapter implements them explicitly:

- every scalar stack slot receives target-local register storage;
- AddressOfSlot/Load/Store fold into target-local register operations;
- E2 AddressOfGlobal/Load/Store lower to dedicated typed scalar global slots,
  never legacy linear memory;
- E2 initialization actions lower to a private wrapper that runs once before
  the selected entry;
- SSA ValueIds receive disjoint target registers;
- edge arguments lower as parallel copies;
- branch/switch-specific copies use adapter labels;
- copy cycles use a dedicated temporary register;
- call results flow through normal-edge transfer;
- unlinked callable imports and external global imports reject;
- complete-module preflight rejects every form outside the accepted scalar
  E1-plus-E2 profile before emission.

These are target mechanics and do not justify changing Talk IR to resemble the
old register VM.

## E1 runtime tests required before acceptance

### Reuse pins

- wrapping Int add/subtract/multiply;
- Int division toward zero, divide-by-zero trap, and MIN/-1 wrapping;
- Float arithmetic including zero division and NaN comparison behavior;
- signed Int, unsigned Byte, Float, and Bool comparisons;
- conversion edge cases;
- direct and recursive call;
- branch, switch, loop, and trap;
- frame-limit error.

### Profile rejection

For E1, reject modules containing:

- cells;
- aggregate or existential operations;
- closure or indirect call operations;
- allocation, memory, or IO operations;
- object/region operations;
- continuation or unwind operations;
- statics or unsupported constants that imply later representations;
- unresolved imports.

### Structural rejection

- invalid entry or call target;
- invalid register and constant index;
- invalid argument-pool range or register;
- invalid branch target;
- invalid switch-pool range or target;
- call arity mismatch;
- reachable fallthrough;
- malformed runtime value kind returns an error, never a panic.

### End-to-end

- source scalar fixture -> Talk IR -> bytecode -> result;
- source CFG fixture -> bytecode -> result;
- source direct-call fixture -> bytecode -> result;
- scalar runtime reports zero allocations and zero objects;
- unsupported source form never reaches bytecode compilation.

## Audit conclusion

The old runtime contains a reusable conventional scalar execution kernel, but
its broad bytecode interface is not accepted wholesale.

E1 may reuse:

- scalar values;
- direct frame-stack calls;
- scalar arithmetic/comparison/conversion kernels;
- register-based CFG dispatch;
- error-return discipline;
- selected encoding/validation techniques.

E1 must add:

- a fail-closed scalar profile;
- a validated bytecode wrapper;
- stronger control-target checks;
- the Talk IR target adapter;
- normative scalar semantics and edge-case tests.

Everything involving aggregates, memory, CoW, objects, regions, closures,
continuations, effects, IO, or legacy symbol identity remains quarantined until
its own parity slice and design gate.
