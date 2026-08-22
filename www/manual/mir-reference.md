# B. MIR Reference

MIR is TalkTalk's finalized, target-independent middle representation. The compiler publishes it after type checking, ownership checking, cleanup insertion, optimization, register allocation, and frame shaping. Bytecode and C consume this same artifact; targets do not inspect source types or repeat semantic decisions.

Inspect it with:

```sh
talk mir source.tlk
talk mir --no-opt source.tlk
talk mir --debug source.tlk
```

The text printed by `talk mir` is diagnostic output, not a stable file format. The public in-process data model in `talk-mir/src/lib.rs` and `talk-mir/src/layout.rs` is authoritative.

## Pipeline position

The relevant pipeline is:

```text
source
  -> parsed and resolved program
  -> inferred typed program
  -> ownership-checked source MIR
  -> optimized, register-allocated finalized MIR
  -> bytecode or C
```

By the finalized seam:

- generic call sites have concrete specialization plans;
- protocol and member choices are fixed;
- moves, retains, releases, and cleanup edges are explicit;
- aggregate layouts and field offsets are fixed;
- effect handler routing operations are explicit;
- source-only types, predicates, and parser nodes are gone.

A target may reject malformed manually constructed MIR, but it may not reinterpret source semantics or silently repair invalid ownership.

## Module

A `Module` contains:

- `functions`: every reachable finalized function;
- `entry`: the function run for the executable;
- `global_slots`: the number of program-global value slots;
- `exports`: host-callable name and wrapper-function pairs;
- `layout_table`: aggregate layouts indexed by `LayoutId`;
- display metadata for structs, enums, strings, and arrays;
- well-known String and Storage identities; and
- optional source files and source text for debug rendering.

MIR symbol identities are compact `(kind, module, local)` triples. They identify structs, enums, effects, and protocols across modules. Display names are metadata and never linkage identity.

## Functions, blocks, and locals

A `Function` declares its name, source arity, frame locals, basic blocks, parameter representations, return representation, frame-local aggregate sites, and optional debug names.

A local is a numbered frame slot. `LocalInfo.layout` is either a concrete inline layout or `None` for the uniform tagged representation. `frame_local` proves the value never leaves its frame, allowing a backend to reuse frame storage.

A basic block has:

- block parameters receiving values from predecessor `Goto` edges;
- an ordered instruction list; and
- exactly one terminator after construction is complete.

Block parameters provide SSA-style merge edges while locals keep the register-oriented representation convenient for backends.

## Operands and constants

An operand is either a local or one of four MIR constants: Unit, Bool, signed 64-bit Int, or 64-bit Float. Other source values are represented by explicit construction instructions or static data.

Operands state where an instruction reads. Ownership-changing behavior is represented by the selected instruction and cleanup plan rather than inferred from a reused local number.

## Layouts

A layout describes how an aggregate occupies slots. Products cover structs, tuples, closed records, and inline arrays. Sums cover enums: slot zero is the tag and payload slots follow it. A field is either one uniform slot or a nested inline aggregate spliced into its parent.

`Aggregate` carries a `LayoutId`, tag, and arguments. `Field` and `SetField` carry the already-resolved container, slot offset, and optional child layout. Targets never search for a field label or infer an offset from surrounding instructions.

An unshaped layout entry keeps table identities aligned for values that are not constructed as flat aggregates.

## Scalar instructions

`Copy` writes a constant or local value to a destination. `Scalar` performs one selected primitive operation:

- Int and Float arithmetic;
- Int and Byte bitwise operations;
- comparison over Int, Float, Byte, Bool, or pointers; and
- numeric conversions among Float, Int, and Byte.

The operation identity is selected before MIR. Int addition, subtraction, multiplication, negation-as-subtraction, and the overflowing division case are potentially trapping operations; optimizers preserve them even when their result is unused. A target maps each operation to its own instruction or generated code without protocol lookup.

## Calls and closures

`Call` invokes a known function ID. `CallIndirect` invokes a function value. Both carry argument operands and an optional unwind block entered when an abort crosses the call.

`MakeClosure` pairs a function ID with an ordered environment. `EnvGet` reads a captured value. Mutable captured locals use explicit `CellNew`, `CellGet`, and `CellSet`; no backend rediscovers which captures require shared cells.

## Aggregate and existential instructions

The aggregate family includes:

- `Aggregate`, `Blank`, `GetTag`;
- `Field`, `FieldIndex`, `GetElement`;
- `SetField`, `SetFieldIndex`;
- `StringLit` and `BytesLit`; and
- global loads and stores.

`Blank` creates the initialization cell used by an explicit struct initializer before its fields are assigned. `FieldIndex` forms exist only where the container shape is dynamic, notably existential writeback.

`ExistentialPack` stores a payload with its ordered witness closures. `ExistentialWitness` and `ExistentialPayload` project those components. Witness slots and protocol identity are fixed before the target seam.

## Managed memory

The raw managed-buffer family is:

- `Alloc`, `Free`, and `RetainPtr`;
- `IsUnique` for copy-on-write decisions;
- typed `Load` and `Store`;
- `MemCopy`; and
- scaled `PtrAdd`.

Each access carries a slot kind such as Byte, Int, Float, Bool, pointer, or boxed value. The kind determines representation and transfer behavior; it does not weaken bounds or lifetime requirements.

Heap objects use `ObjectNew`, `ObjectGet`, and `ObjectSet`. `RegionAcquire` and `RegionRelease` update claims on every region reachable from object handles. `SetFinalizer` installs type-specific teardown behavior.

## Effects and control capture

Effect handlers lower to explicit delimiter and handler-stack operations:

- `MakeCont` reifies the current return delimiter;
- `PushHandler` installs an effect clause and records whether it binds a resumption;
- `FindHandler` finds the nearest live entry and returns its clause, delimiter, index, and clause kind;
- `GetFloor` and `SetFloor` enforce delegation outside the current clause;
- `AbortTo` returns through a delimiter while unwinding intervening frames.

A resumption-binding path uses `Suspend` to capture the delimited extent. `Resume` supplies the effect result and runs that extent again; `Cancel` abandons it through the same cleanup edges used by abort unwinding.

Tail-resumptive clauses use an ordinary call path. This distinction is selected from the handler clause shape, not an effect declaration attribute.

## Tasks, channels, and host operations

MIR exposes only target-neutral runtime operations:

- `TaskSpawn`, `TaskJoin`, and `TaskWidth`;
- `ChanSend`, `ChanTake`, and scalar `ChanCtl`; and
- `Io` with one operation-table index and three scalar operands.

Scheduling policy remains in TalkTalk source or the runtime. A target decides whether a parallel worker is an OS thread or a sequential fallback, but it preserves structured join and `Send` transfer semantics.

The I/O operation index follows Core's `IORequest` case order. It includes files, environment, arguments, directories, sockets, process exit, and monotonic time.

## Terminators

Every block ends with one of:

- `Goto(target, args)`, passing one value per target block parameter;
- `Branch`, selecting between two blocks from a Boolean operand;
- `Switch`, dispatching a nonnegative enum tag with a default edge;
- `Return`, returning one operand;
- `Trap`, terminating with a compiler-provided message; or
- `UnwindRet`, ending one cleanup frame during an abort or cancellation.

A terminator owns control flow. Instructions do not have implicit fallthrough across basic blocks.

## Ownership and cleanup

Finalized MIR makes cleanup executable. Releases and type-specific destruction occur on normal block exits, control-flow edges, function epilogues, unwind paths, and cancellation paths. Drop flags and initialization analysis ensure a value is destroyed exactly when live.

Call-like and suspension instructions name unwind blocks. Those blocks destroy values belonging to the crossed scope and end with `UnwindRet`. This shares one cleanup mechanism across panic-like aborts and cancelled resumptions.

The compiler verifies use-after-move, initialization, loan exclusivity, linear consumption, cleanup balance, block arguments, layouts, and instruction structure before publication. Compiler-produced invalid MIR is an internal compiler error, not a target-dependent program result.

## Debug metadata

`talk mir --debug` retains source provenance through optimization. Each instruction can point to a source span or a generated reason, including closure capture, handler delimiter, function epilogue, cleanup, global initialization, export adaptation, heap teardown, derived protocol glue, and enum construction.

Local debug names list all bindings represented by a reused register. Debug source spans use 1-based line and column positions plus byte offsets into the recorded source.

Debug metadata is optional and does not affect identity or execution.

## Optimized and unoptimized views

The default dump shows the same optimized finalized MIR targets consume. `--no-opt` disables optimization but still shows checked MIR in the finalized public shape. It is useful for seeing source-like control flow and cleanup before dead-code elimination and instruction simplification.

Register allocation and frame shaping may make one local represent several source bindings. Use `--debug` when relating either view back to source.

## Target contract

A backend must preserve:

- scalar operation and trap behavior;
- block and call control flow;
- aggregate layouts and value semantics;
- explicit memory and region operations;
- cleanup and unwind order;
- handler lookup, floors, aborts, suspension, resumption, and cancellation;
- task and channel transfer semantics; and
- global initialization and exported wrapper identities.

Bytecode lowering maps MIR to a validated register machine. C emission maps the same functions, layouts, and runtime operations to generated C. Agreement tests run common programs through both targets.
