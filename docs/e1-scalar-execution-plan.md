# E1 scalar execution plan

Status: E1 G0-G5 complete; E2 scalar globals extend the same validated target seam (2026-07-14)

Execution roadmap: [Backend feature-parity plan](backend-parity-plan.md)

Parity accounting: [Backend parity ledger](backend-parity-ledger.md)

Runtime audit: [E1 talk-runtime reuse audit](e1-talk-runtime-reuse-audit.md)

Semantic authority: [ADR 0032](adr/0032-single-artifact-ownership-and-lowering-pipeline.md)

This document fixes the intended scope of the first executable vertical slice.
It is not yet a normative contract amendment. E1 reaches G0 only when the same
facts land together in ADR 0032, the Stage 0 contract, Rust types, validators,
verifiers, printers, tests, and the implementation ledger.

## Goal

Execute the existing verified scalar CFG through an audited bytecode reference
backend without restoring old lowering or runtime semantics:

```text
source with checked scalar intrinsics
  -> TypedProgram
  -> CheckedMir
  -> TalkIrModule
  -> validated scalar bytecode module
  -> bytecode interpreter
  -> result or runtime trap
```

E1 proves the target seam early. It does not claim broad source-language parity.
Normal overloaded operator syntax now publishes and reaches MIR with its
selected implementation, but still depends on L1 specialization and E2 supply
linking before Talk IR execution.

## E1 scope

### Real producer scope

- Unit, Bool, Int, and Float constants;
- scalar locals;
- branches, literal switches, loops, goto, and unreachable;
- local direct calls;
- consumed scalar parameters and results;
- trusted scalar inline-IR bodies whose operations are canonicalized before the
  TypedProgram seam.

### Contract and fixture scope

- Byte values and Byte comparison/conversion operations may be represented and
  verified by fixtures;
- they do not pass G1/G3 until a real source producer emits a Byte value, which
  is expected with managed memory and Unicode work.

### Explicitly outside E1

- Character values: Talk `Character` is a borrowed grapheme view under ADR
  0012, not a machine scalar;
- String and other aggregates;
- affine or linear runtime values;
- source borrows;
- generic calls and monomorphization;
- normal protocol/operator execution that requires specialization and imported
  implementation supply;
- imports and multi-module linking;
- globals;
- closures, existentials, effects, memory, IO, and host calls;
- bytecode serialization and standalone packaging, which belong to T1.

Unsupported forms remain rejected before partial target emission.

### Post-E1 E2 extension

E2 widens this target-neutral scalar path after linking: verified modules may
carry literal and generated-function scalar global initializers. Talk IR verifies
the schedule and linked supplier-before-consumer order. The bytecode adapter
uses dedicated typed global slots and a private once-before-entry wrapper.
Unlinked imports, external global imports, non-scalar globals, and legacy memory
remain outside the accepted profile. This extension does not retroactively add
globals or linking to the E1 exit gate.

## Contract audit findings

### E1-C1: TypedProgram scalar inline IR is canonical - resolved

Type checking now selects `ScalarIntrinsic` in a temporary producer map that is
consumed during canonical construction. `TypedProgram::InlineIr` contains the
checked operation and canonical operands; it no longer contains
`InlineIRInstructionKind`, source `TypeAnnotation`, or parser registers.

Trusted memory, IO, ownership, and other deferred operations become an
`Unsupported` marker with no parser instruction payload. MIR remains
fail-closed for that marker. Malformed scalar source receives a frontend
diagnostic, is retained as `InvalidScalar`, and cannot validate for MIR.

### E1-C2: parameter and explicit-bind operands have canonical identity - resolved

Core scalar operations use both forms:

```text
@_ir { %? = add Int %0 %1 }
@_ir(lhs, rhs) { %? = add Int $0 $1 }
```

`%N` means callable parameter N. `$N` means explicit inline-IR bind N. Literal
operands such as `0`, `0.0`, and `false` are also valid.

The canonical node translates these to semantic operands:

- `%N` -> the enclosing callable contract's parameter `BindingId` plus
  producer-selected `CopyEvidence::Intrinsic`;
- `$N` -> an index into the node's ordered, once-evaluated checked bind list
  plus producer-selected `CopyEvidence::Intrinsic`;
- integer and boolean literals -> typed constants without Copy evidence;
- float literals -> exact binary64 bits.

The validator checks the operation's exact arity and result, every bind type,
parameter membership in the enclosing callable, and every Copy proof.
Out-of-range registers or binds, unsupported scalar values, invalid evidence,
and destinations other than `%?` diagnose and cannot validate. MIR receives no
parser register vocabulary and does not select Copy evidence.

### E1-C3: protocol-static calls publish the selected witness - resolved through MIR

Protocol-static calls such as the `Add.add(1, 2)` operator desugaring retain the
receiver variable during checking. Finalization uses the solved receiver and
canonical protocol application to select exactly one conformance-row witness.
TypedProgram publishes its conformance, requirement, and concrete implementation
IDs, and validation proves that exact requirement/implementation pair exists in
the selected row. MIR materializes the published implementation ID without
conformance search.

The core implementation is an imported callable whose generic contract still
requires L1 specialization and E2 supplier linking. Talk IR therefore continues
to reject normal `+`, `-`, `*`, `/`, comparison, and protocol-default execution
fail closed. E1 source execution continues to use trusted direct scalar
intrinsic functions; the remaining blocker is no longer witness selection.

### E1-C4: Int literal range is validated at the frontend seam - resolved

Integer expressions and patterns now remove `_` separators and parse to signed
64-bit values during type checking. Unary minus directly on an integer token
folds before operator lowering, so `-9223372036854775808` is canonical and
valid. The adjacent positive value and the next negative value diagnose with
`type.integer-literal-out-of-range`, retain `InvalidInt` recovery, and cannot
validate for MIR.

TypedProgram, MIR, and Talk IR carry `i64`; no backend parses integer source
text. Boundary values have a real source-to-Talk-IR preservation test.

### E1-C5: Character must leave the scalar milestone

Talk IR currently has an `IrType::Character`, but ADR 0012 defines Character as
a borrowed storage/start/byte-count view. E1 does not assign it a scalar
bytecode representation. Character constants and operations remain rejected
until O2/R1/K1 provide the borrowed aggregate representation.

## Scalar semantic contract

### Value types

| Type | E1 meaning |
| --- | --- |
| Unit | One value, represented by the target as Void or an equivalent zero-data value |
| Never | No value; a reachable attempt to materialize one is invalid |
| Bool | Exactly `false` and `true` |
| Byte | Unsigned 8-bit value, fixture-only until a real producer exists |
| Int | Signed 64-bit two's-complement value |
| Float | IEEE 754 binary64 value |

### Integer arithmetic

- add, subtract, and multiply wrap modulo 2^64;
- integer division truncates toward zero;
- division by zero produces a deterministic runtime trap;
- `Int::MIN / -1` wraps to `Int::MIN`, matching baseline `wrapping_div`;
- comparisons are signed;
- no target may substitute host-language debug-overflow behavior.

### Float arithmetic

- add, subtract, multiply, and divide use IEEE 754 binary64 behavior;
- division by positive or negative zero follows IEEE infinity/NaN behavior and
  does not use the integer division-by-zero trap;
- comparisons use ordered IEEE behavior: comparisons with NaN are false except
  not-equal, which is true;
- bytecode constants preserve exact binary64 bits.

### Bool and Byte

- Bool supports equal and not-equal comparison only;
- Byte comparisons are unsigned;
- Byte-to-Int zero-extends.

### Conversions

- Float-to-Int truncates toward zero;
- NaN converts to zero;
- values above or below the Int range saturate to `Int::MAX` or `Int::MIN`;
- Int-to-Float uses IEEE binary64 round-to-nearest, ties-to-even behavior;
- Byte-to-Int is exact.

The conversion rules intentionally describe the baseline Rust conversion
behavior so Wasm, C, and native adapters cannot drift later.

## Proposed canonical intrinsic vocabulary

Use the shared target-neutral operation identity across TypedProgram, MIR, and
Talk IR. The adopted Rust vocabulary is:

```text
ScalarIntrinsic
  IntAdd | IntSub | IntMul | IntDiv
  FloatAdd | FloatSub | FloatMul | FloatDiv
  IntCompare(ScalarComparison)
  FloatCompare(ScalarComparison)
  ByteCompare(ScalarComparison)
  BoolEqual | BoolNotEqual
  FloatToIntTrunc
  IntToFloat
  ByteToInt

ScalarComparison
  Equal | NotEqual | Less | LessEqual | Greater | GreaterEqual
```

The validator restricts Bool comparison to equality through the dedicated
variants. The producer may translate source Bool-not into `BoolEqual(false)`;
E1 does not need a second boolean-negation semantic operation.

Short-circuit `&&` and `||` remain CFG behavior, not eager intrinsics.

## Artifact representation

### TypedProgram

A checked intrinsic expression contains:

- one `ScalarIntrinsic`;
- ordered canonical operand expressions or parameter bindings;
- exact checked operand and result types;
- source-backed origin for source operations;
- generated origin naming the source operation for synthesized constants or
  parameter references.

The producer validates all parser-level registers, binds, source annotations,
and literals while constructing this node. Retained source syntax may still
contain the original inline IR for formatting and code actions.

### CheckedMir

Use the existing explicit intrinsic rvalue shape with the shared operation:

```text
Rvalue::Intrinsic {
  operation: ScalarIntrinsic,
  operands: Vec<Operand>
}
```

MIR generation preserves source evaluation order for explicit bind expressions.
Parameter operands are ordinary Copy operands with producer-selected Copy
evidence. Scalar literal operands are constants.

The MIR verifier checks:

- exact arity;
- exact operand and result types;
- initialized operands;
- Copy evidence where the operand reads a place;
- operation support in the current verified subset.

### Talk IR

Talk IR uses the same operation identity:

```text
InstructionKind::Intrinsic {
  operation: ScalarIntrinsic,
  operands: Vec<ValueId>
}
```

Copy evidence has already ended at MIR verification and does not appear. The
Talk IR verifier checks exact value types, result presence, and arity.

### Bytecode

The bytecode adapter maps each operation exactly once to the accepted scalar
bytecode subset. It may use overloaded target opcodes internally, but the
adapter mapping starts from an explicit typed `ScalarIntrinsic` and the runtime
must trap cleanly if a malformed bytecode module supplies values of the wrong
target kind.

## Bytecode adapter obligations

The adapter owns target mechanics only:

- assign scalar SSA values to registers;
- represent each Talk IR stack slot as target-local scalar storage, without
  exposing source places to the runtime;
- lower AddressOfSlot/Load/Store pairs without creating a general pointer
  representation;
- implement block parameters with edge-local parallel copies;
- create edge adapter blocks when branch or switch successors require different
  copies;
- lower a call terminator to call, normal-edge copies, and control transfer;
- reject imports until E2;
- lower Unit returns through the target's Void representation;
- lower reachable Unreachable to a deterministic trap;
- preserve source origins in target diagnostics where the target format allows.

Parallel-copy lowering must handle cycles using a temporary register. It may not
silently rely on a register allocation order.

## E1 source fixtures

Normal overloaded arithmetic is deliberately not an E1 handshake. E1 uses
trusted direct helpers so the intrinsic seam is tested without downstream
conformance search.

Required real-producer fixtures:

1. direct Int add/subtract/multiply/divide helper;
2. direct Float arithmetic helper;
3. Int, Float, and Bool comparison helper;
4. Float-to-Int and Int-to-Float helper;
5. branch and loop using direct comparison/arithmetic helpers;
6. local direct call returning a scalar;
7. Unit-returning function;
8. division-by-zero runtime trap;
9. out-of-range Int literal frontend diagnostic;
10. unsupported inline memory/IO operation rejected before MIR.

Byte operations begin with validated fixtures. Their source handshake moves to
Integrated only when a real Byte producer exists.

## Negative contract tests

### TypedProgram

- source annotation disagrees with checked operand type;
- unsupported scalar type for an operation;
- wrong operand count;
- out-of-range `%N` parameter;
- out-of-range `$N` bind;
- unsupported parser value or destination;
- out-of-range Int literal;
- recovery intrinsic cannot validate for MIR.

### CheckedMir

- wrong operand type;
- wrong result type;
- wrong arity;
- uninitialized operand;
- invalid Copy evidence;
- unsupported intrinsic operation rejected fail closed.

### Talk IR

- wrong operand ValueId type;
- missing or unexpected result;
- wrong arity;
- unsupported operation;
- operation/type mismatch.

### Bytecode

- unsupported old opcode in the E1 profile;
- invalid register, constant, function, argument-pool, branch, and switch index;
- call arity mismatch;
- malformed scalar operand traps without panic;
- fallthrough and malformed control flow reject deterministically.

## E1 gate sequence

### G0

- promote this scalar contract into ADR 0032 and Stage 0;
- add shared operation types;
- canonicalize TypedProgram inline IR;
- add validators, verifiers, printers, and negative tests;
- add INTR capability rows to the parity ledger.

### G1

- real source producer emits checked intrinsic nodes;
- MIR generator emits verified scalar intrinsic rvalues;
- out-of-range and unsupported source forms diagnose before MIR.

The scalar trusted-inline-IR producer-to-MIR handshake is integrated, including
ordered bind evaluation, parameter/bind Copy evidence preservation, constants,
and exact MIR signature verification. Signed 64-bit source literals and their
recovery contract are also integrated.

### G2

- Talk IR lowerer accepts verified intrinsic fixtures;
- Talk IR verifier rejects malformed intrinsic instructions;
- bytecode target module accepts only the E1 profile.

The Talk IR intrinsic fixture, negative verifier, fail-closed bytecode profile,
and Talk IR target adapter are integrated.

### G3

- real source intrinsic identity, operand order, types, and origins survive
  TypedProgram -> MIR -> Talk IR exactly;
- Copy evidence is verified in MIR and absent from Talk IR.

The real three-artifact scalar intrinsic handshake is integrated. It compares
operation identity, operand order, and source origin across MIR and Talk IR;
Talk IR has no Copy-evidence field.

### G4

Run all required frontend, LSP, MIR, Talk IR, workspace, formatting,
diagnostics, parity inventory, and smoke suites from rebased `bigdiff`.

Passed on the integrating checkout: 932 library tests with 3 ignored, 38 runtime
tests, 10 parity integration tests, all workspace targets, formatting and diff
checks, structured diagnostics, plus `talk-syntax` and `talispk` smoke checks.

### G5

The E1 source fixtures execute through validated bytecode and assert results,
clean division traps, and zero resource deltas. CFG, direct and recursive calls,
source loop and switch forms, Unit return, and the parallel-copy cycle fixture
are covered. The driver and `talk run` use the same validated path, render
scalars with Talk syntax, suppress Unit, and reject unsupported normal operators
without fallback. Normal operator syntax remains an explicit L1 unsupported
case.

## Implementation order

1. Land the G0 contract amendment and canonical intrinsic producer shape.
   Integrated.
2. Implement and verify TypedProgram-to-MIR scalar intrinsic generation.
   Integrated.
3. Implement and verify MIR-to-Talk-IR scalar intrinsic lowering. Integrated.
4. Enforce the signed 64-bit source literal and recovery rule. Integrated.
5. Add the bytecode E1-profile validator and validated runtime wrapper.
   Integrated.
6. Add the Talk IR-to-bytecode adapter for constants, slots, CFG, calls, and
   intrinsics. Integrated.
7. Add G5 source handshakes. Integrated.
8. Rebase, run G4/G5, and update both ledgers in the integrating commit.
   Integrated.
