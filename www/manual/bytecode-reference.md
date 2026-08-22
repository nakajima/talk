# C. Bytecode Reference

TalkTalk's default executable artifact is a validated register-bytecode image. `talk build` writes it, `talk run-image` decodes and validates it, and `talk bytecode` prints the disassembly produced directly from source.

```sh
talk build program.tlk -o program.tbc
talk bytecode program.tlk
talk run-image program.tbc
```

This page describes bytecode format 11. The exact encoder, decoder, instruction tags, and validator in `talk-vm/src/bytecode.rs` and `talk-vm/src/lib.rs` are authoritative.

## Compatibility policy

Every image begins with the seven bytes `TALKBC\0`, followed by a 32-bit format version. The current encoder writes version 11, and the current loader accepts version 11. A different magic, unsupported version, truncated field, invalid tag, invalid index, integer overflow, malformed UTF-8 string, or trailing byte rejects the image before execution.

The format is experimental. Opcode layout can change when the format version changes; producers and consumers should use matching TalkTalk releases rather than treating `.tbc` as a long-term distribution ABI.

Version 10 introduced handler clause kind and clause-derived suspension. Version 11 changes Int arithmetic opcodes to trap on overflow. The compatibility floor is version 11, so a runtime never executes older arithmetic under the new semantics.

## Primitive encoding

Multibyte integers and Float bit patterns are encoded little-endian. Lengths and most table indexes use unsigned 32-bit fields. Registers and compact counts use unsigned 16-bit fields where the validator enforces their range. Booleans use one byte.

Strings are a 32-bit byte length followed by UTF-8 bytes. Arbitrary static data is length-prefixed bytes and need not be UTF-8.

Every enum-like field has a one-byte tag. Unknown tags are errors; the decoder never preserves an instruction or constant it does not understand.

## Image order

After magic and version, a module is encoded in this order:

1. entry chunk index;
2. host-callable exports;
3. chunks;
4. scalar constant pool;
5. argument pool;
6. switch-target pool;
7. trap strings;
8. static bytes; and
9. aggregate layouts.

The decoder consumes exactly one value from each section and then requires end of file.

## Exports

Each export is a UTF-8 name followed by a chunk index. Export names are host dispatch identities, unlike diagnostic chunk names. The referenced wrapper chunk must exist and satisfy the generated service convention.

The entry is a separate chunk index used for ordinary executable evaluation.

## Chunks and registers

A chunk contains:

- diagnostic name;
- source arity;
- register count;
- instruction count and instruction stream; and
- an unwind table.

A register index is local to one frame. Instructions read and write numbered registers. Calls create new frames; return writes the result to the destination established by the caller.

The unwind table contains sorted `(suspension_pc, cleanup_pc)` pairs. When an effect abort or cancelled resumption crosses a frame suspended at that program counter, the VM enters the cleanup code once before removing the frame.

## Constants and RK operands

The constant pool contains only immutable scalar values:

- signed 64-bit Int;
- 64-bit Float bits;
- Bool;
- Byte;
- Void; and
- a pointer offset into module static data.

Arithmetic operands and argument-pool entries use an RK encoding inspired by Lua. If the high bit of a 16-bit field is clear, the field names a register. If it is set, the low 15 bits index the constant pool. A large constant-pool index is first materialized with `Const`.

This keeps common literal arguments and arithmetic constants out of temporary registers.

## Shared pools

Variable-length instruction operands live in module-level pools:

- the argument pool stores RK operands used by calls, closures, aggregate construction, object construction, suspension, and existential packing;
- the switch pool stores branch targets for `Switch`;
- the trap table stores UTF-8 messages referenced by `Trap`; and
- static bytes hold literals and immortal data.

An instruction carries a start and length into its pool. Validation checks the complete half-open range, including overflow.

## Layout table

Each layout has an optional display symbol, total slot width, and one body:

- `Product`: ordered field offsets and shapes;
- `Sum`: one ordered payload layout per variant; or
- `Unshaped`: an identity not constructed as a flat aggregate.

A field shape is one slot or a nested layout spliced inline. Sum values reserve slot zero for the variant tag. Products use tag zero.

Instructions use `NO_LAYOUT` (`u32::MAX`) when a member occupies one ordinary slot; any other value identifies the spliced child layout. Validation checks layout references, widths, offsets, and construction arity.

## Instruction families

The bytecode currently has 72 instruction variants. The following groups describe their execution contract; disassembly uses the names shown here.

### Values and scalar operations

- `Const`, `Move`
- `Add`, `Sub`, `Mul`, `Div`
- `And`, `Or`, `Xor`, `Shl`, `Shr`, `Not`
- `Cmp`
- `Trunc`, `IToF`, `BToI`, `IToB`

Arithmetic uses RK operands where encoded. Int addition, subtraction, multiplication, and the overflowing division case trap; Float arithmetic follows IEEE 754. Explicit `unchecked_*` Int methods are Core routines built from bitwise operations rather than separate opcodes. `Cmp` carries Eq, Ne, Lt, Le, Gt, or Ge selected for the operand representation by MIR lowering.

### Cells and closures

- `CellNew`, `CellGet`, `CellSet`
- `MakeClosure`, `EnvGet`
- `Call`, `CallIndirect`

A closure stores a chunk and ordered captured values. Cells provide shared mutable storage for captures whose source binding is assigned.

### Control flow

- `Jump`
- `Branch`
- `Switch`
- `Ret`
- `Trap`

Targets are absolute instruction indexes inside the current chunk. `Switch` indexes its target slice by a nonnegative tag and uses the final encoded default target when no listed target applies. Validation requires every target to land on an instruction boundary in the same chunk.

### Aggregates and existentials

- `AggNew`, `StringLit`
- `Field`, `FieldIndex`, `GetElement`, `GetTag`
- `SetField`, `SetFieldIndex`
- `ExistentialPack`, `ExistentialWitness`, `ExistentialPayload`

Aggregates are copy-on-write values under published layouts. Offset-addressed field operations use static MIR decisions. Index operations are reserved for dynamically shaped boundaries. `StringLit` interns a complete immutable String-shaped value over static bytes.

### Managed memory

- `Alloc`, `Free`, `Retain`, `IsUnique`
- `Load`, `CheckedIndexedLoad`, `Store`, `Copy`, `Swap`

A memory operation carries Byte, I64, F64, Bool, pointer, or boxed element kind. The VM tracks live allocations and rejects out-of-bounds access, use after free, double free, and incompatible element interpretation. `CheckedIndexedLoad` branches to compiled TalkTalk failure code instead of turning an ordinary bounds failure into a VM trap.

### Heap objects and regions

- `ObjectNew`, `ObjectGet`, `ObjectSet`
- `SetFinalizer`
- `RegionAcquire`, `RegionRelease`

Heap objects have identity and participate in merge-only managed regions. Region claims determine teardown; finalizers run through generated typed glue.

### Effects, continuations, and resumptions

- `MakeCont`, `CallCont`, `UnwindRet`
- `PushHandler`, `FindHandler`
- `GetFloor`, `SetFloor`
- `Suspend`, `Resume`, `Cancel`

`PushHandler` records the effect, clause closure, delimiter, and whether the clause binds a resumption. `FindHandler` searches the nearest live matching entry below the current floor and returns all four routing values.

Tail-resumptive clauses call and continue in place. A binding clause uses `Suspend` to store the delimited frame segment in a one-shot slot. `Resume` consumes that slot and supplies the performed operation's result. `Cancel` consumes it and runs unwind cleanup. A second use traps even if malformed input evaded source linearity.

`CallCont` implements abortive return to a delimiter, entering unwind-table cleanup for crossed frames. `UnwindRet` is valid only while such cleanup is active.

### Tasks and channels

- `TaskSpawn`, `TaskJoin`, `TaskWidth`
- `ChanSend`, `ChanTake`, `ChanCtl`

Task handles and channel handles are runtime-minted and generation-checked. They cannot be forged by putting an integer in the bytecode. Spawn and join transfer only layouts admitted by compiler-published `Send` facts; the VM uses isolated worker machines and structural transfer packets.

`ChanCtl` multiplexes channel creation, status, endpoint counts, receive and send registration, reservation, deadline registration, and worker parking. The numeric operations are a private Core/runtime protocol, not a source API.

### Host I/O

`Io` contains an `IoOp` and three register operands. The 29 operations, in wire order, are:

```text
Read, Write, Open, Close, Sleep, Poll, Ctl,
Socket, Bind, Listen, Connect, Accept,
CwdLen, CwdCopy, GetenvLen, GetenvCopy,
Argc, ArgLen, ArgCopy,
DirCount, DirEntryKind, DirEntryLen, DirEntryCopy,
Exit, RealpathLen, RealpathCopy, Seek, FileSize,
MonotonicNanos
```

This order matches Core's `IORequest` cases and the host operation table. Unknown indexes reject during decoding.

## Validation

Decoding is followed by whole-module validation. Among other invariants, validation checks:

- entry and export chunk indexes;
- chunk arity and register operands;
- constant, pool, string, static, layout, and trap indexes;
- RK constant bounds;
- jump and switch targets;
- argument ranges and callable arity;
- memory kinds and layout shape;
- handler and effect operands;
- legal unwind-table ordering and cleanup instructions;
- task, channel, continuation, and resumption operand forms; and
- absence of integer overflow while computing any encoded range.

The VM executes only a validated module. Compiler-produced invalid bytecode is a backend bug; malformed external bytes are an input error.

## Execution model

The machine owns module-immutable tables and one worker state per running task worker. A frame contains its chunk, program counter, registers, return destination, closure environment, and handler/unwind state. Values include scalars, aggregates, closures, cells, objects, pointers, continuations, and resumption slots.

The interpreter checks runtime invariants that remain dynamic: allocation liveness, object and handle generation, channel readiness, continuation lifetime, one-shot resumption use, and trap conditions. Source-level type and ownership checking normally prevents these failures; validation and runtime checks defend the untrusted bytecode boundary.

## Disassembly versus encoded bytes

`talk bytecode` compiles source and renders the in-memory module. It shows chunk names, arity, register count, program counters, and readable operands. Pool contents and numeric opcode tags are intentionally abstracted.

A `.tbc` file contains the exact wire representation described above. There is no command that treats disassembly text as input, and editing the text cannot create a bytecode image.

For compiler debugging, inspect MIR first when the question is semantic selection, ownership, cleanup, or layout. Inspect bytecode when the question is register lowering, pool use, concrete VM control flow, encoded validation, or interpreter behavior.
