# 0032 - Single-artifact ownership and lowering pipeline

Status: accepted; implementation in progress

## Context

ADR 0031 reset the compiler to a frontend-only pipeline ending at
`TypedProgram`. That reset removed the old flow, lowering, lambda-G, and
compiler-facing VM modules so the replacement backend would not inherit their
interfaces.

The remaining frontend seam is not yet suitable for that replacement.
`TypedProgram` owns a typed tree, but it also retains `TypeOutput` and
`ResolvedNames`. Editor and module consumers can split those structures back
out through `types()`, `resolved_names()`, and `into_semantic_parts()`. Semantic
facts therefore still have two homes: typed nodes and maps keyed by `NodeID` or
`Symbol`.

The replacement pipeline must support one Talk IR with several consumers:

- Talk bytecode executed by `talk-runtime` and exposed through embedding APIs;
- WebAssembly;
- C;
- future Cranelift and LLVM backends.

It must also support deterministic ownership, borrowing, and algebraic effects
without making liveness, lowering, or the runtime a second authority for source
semantics. Type checking, MIR generation, and Talk IR lowering should be able to
proceed in parallel once their artifact contracts are implemented.

## Research basis

The design combines established divisions of responsibility rather than
introducing one novel all-purpose analysis:

- Rust selects move/copy behavior before MIR borrow checking. Its MIR borrow
  checker computes move data, region constraints, active loans, and diagnostics
  over a CFG.
- Swift Ownership SSA assigns ownership kinds and lifetime-ending behavior to
  IR values and operands, then verifies those structural facts.
- Koka and Flix infer interprocedural effects during type checking. Flix models
  mutable heap regions as effects and masks effects for local regions that do
  not escape.
- Talpin and Jouvelot, Tofte and Talpin, Cyclone, and the Capability Calculus
  establish the type/region/effect-to-explicit-capability lineage for memory
  safety.
- Brachthaeuser and Leijen's qualified effect types and Tang, Hillerstrom,
  Lindley, and Morris's control-flow linearity connect effect rows with the
  number of times a captured continuation may be entered.
- Hillerstrom and Lindley distinguish deep handlers, which reinstall the
  handler around a resumption, from shallow handlers, which do not.
- Leijen's deep finalization, OCaml's `continue`/`discontinue` discipline, and
  the RAII resource-modality work show why abandoning a continuation must run
  structured cleanup instead of silently discarding suspended frames.

## Decision

The compiler pipeline is:

```text
ParsedProgram
    -> TypedProgram
    -> CheckedMir
    -> TalkIrModule
    -> BytecodeModule | WasmModule | C translation | future native backend
```

Each phase consumes one semantic artifact and produces one semantic artifact.
Diagnostics accompany a phase outcome, but diagnostics are not a semantic
input to the next phase.

The normative phase interfaces are:

```text
type_check(NameResolvedProgram) -> PhaseOutcome<TypedProgram>
mirgen(TypedProgram)             -> PhaseOutcome<CheckedMir>
lower(CheckedMir)                -> Result<TalkIrModule, InternalCompilerError>

PhaseOutcome<T>
  artifact: optional T
  diagnostics: ordered diagnostics
```

Type checking supplies a recovery `TypedProgram` to editor callers even when it
also reports errors. MIR generation supplies no `CheckedMir` when source
ownership errors occur. A later phase receives only the contained artifact, not
the `PhaseOutcome` or its diagnostics.

The Rust signatures may borrow rather than move their inputs while the
implementation is being brought up. The ownership rule is conceptual: a
consumer may depend only on the immediately preceding artifact, never on an
older artifact or a side channel from an earlier phase.

A phase may use temporary maps, constraint stores, worklists, and indexes while
constructing its result. Those structures are destroyed at the phase seam.
They are not part of the artifact contract.

A canonical arena whose entries are the semantic entities referred to by IDs
is permitted. A disposable lookup index derived from an artifact is permitted.
Neither may duplicate a semantic fact with a second independently mutable
answer.

## Source memory model

### Grades

Talk retains three source grades:

- `Copy`: a value may be duplicated freely;
- `Affine`: a value has one owner, may be moved, and may be destroyed by
  deterministic cleanup;
- `Linear`: a value has one owner and must be explicitly consumed exactly once.

`Deinit` does not, by itself, make a strict linear value implicitly droppable.
A future explicit cancellation or abort-safe resource protocol may define a
canonical consuming action. Until then, an abort path may not abandon a live
strict linear value.

Cheap cloning is type-specific. An implicit CheapClone remains an explicit
coercion in `TypedProgram` and an explicit operation in `CheckedMir`; it is not
selected later by liveness.

### Passing and capture modes

Every checked value edge that can read a place has one selected mode:

```text
Copy
Move
BorrowShared
BorrowMut
Discard
```

Function parameters and call arguments use the corresponding checked passing
modes. Closure and handler captures use:

```text
Copy
Move
BorrowShared
BorrowMut
```

Source spelling may omit a mode. The type checker must select one before
publishing `TypedProgram`. MIR generation validates the selected behavior; it
does not reinterpret a plain use as move, copy, or clone based on last use.

Every selected Copy use carries `CopyEvidence`. Evidence is a checked proof,
not a cached grade. It is one of: a closed intrinsic-scalar fact, a non-linear
payload-free enum fact, a predicate index for a quantified type parameter, a selected Copy
conformance with its exact substitution and recursively proven context, or a
structural tuple/closed-record proof. Capture modes carry the same evidence.
`Grade::Copy` on a nominal declaration remains a declaration summary and is
never sufficient evidence for a concrete use.

The TypedProgram validator and MIR verifier use the same proof checker with
artifact-specific canonical-item adapters. They check the proof against the
exact used type and canonical items and do not rerun conformance search. This makes
conditional conformance explicit, permits phantom arguments only where the
proof says they are runtime-inert, and keeps witness selection owned by type
checking.

For v1:

- borrowed values may not escape through returns, stored closures, or longer
  lived storage;
- an ordinary active borrow across a `perform` or a call that may perform a
  user effect is rejected;
- a deep handler may capture Copy values and shared borrows only;
- a handler-captured shared borrow is the sole suspension exception: it is an
  explicit loan for the complete handled extent, prevents mutation of its
  referent throughout that extent, and ends on normal exit or discontinue;
- a deep handler may not own affine or linear captures and may not capture a
  mutable borrow;
- user-visible field extraction may not leave a source aggregate partially
  moved. A consuming destructure or match consumes the whole aggregate and
  explicitly moves or destroys every payload.

### Cleanup

Cleanup is deterministic and follows reverse completed-initialization order.
A move deinitializes its source place. Assignment evaluates the right-hand side
first, then destroys the old destination if it is live, then initializes the
destination with the new value. Immutable storage may be initialized at most
once within one `StorageLive` lifetime; Move, Destroy, and their reason labels
do not reset that history.

Affine values receive cleanup on normal return, early return, loop exits, and
discontinue paths. Strict linear values must already have been consumed on
every finite exit path.

Cleanup and `Deinit` code may not expose an unhandled user effect in v1. This
keeps cleanup from recursively abandoning cleanup. Core runtime operations used
by cleanup are not user-handleable effects.

Divergence uses partial-correctness semantics: a value held forever by a
diverging computation has not been duplicated or discarded on a finite path.
Control-flow linearity therefore constrains finite exits; it is not a
termination guarantee.

## Effects and control-flow linearity

### Handler semantics

V1 handlers are dynamically routed, deep, and one-shot:

1. the nearest dynamically enclosing handler receives a performed operation;
2. the handler clause executes outside the handler it implements;
3. performing the same effect in that clause routes to an outer handler;
4. resuming reinstalls the current handler around the suspended continuation;
5. subsequent operations of the same effect are handled by that handler;
6. the continuation cannot be stored, copied, or resumed more than once.

The old backend's behavior of making a handler body resolve its own effect to
itself is not part of the language contract.

On every finite handler exit, the captured continuation is consumed exactly
once by one of:

- `continue`, which enters the suspended continuation once;
- `discontinue`, which enters its compiler-generated cleanup path once and
  delivers the handler's abort result to the handler delimiter.

A diverging clause retains the continuation indefinitely and has no finite
exit. Returning normally from a handler clause without `continue` means
`discontinue`. If a nested effect exits a handler clause before it explicitly
continues or discontinues, deep finalization discontinues the current
continuation automatically.

### Behavior and requirements

A handler has one inferred finite-path behavior:

```text
Abort   - at least one finite exit exists and every finite exit discontinues
Linear  - every finite exit resumes exactly once
Affine  - finite exits include both resume and discontinue
```

A handler with no finite exit is classified Linear by convention: the Linear
condition holds vacuously under partial correctness and this is the strongest
safe contract for callers. Diverging paths otherwise contribute no finite
outcome. Multi-shot or `Wild` handlers are not part of v1.

A performed effect entry carries a resume requirement, not a globally fixed
handler behavior:

```text
AtMostOnce
ExactlyOnce
```

`AtMostOnce` accepts Abort, Linear, or Affine behavior. `ExactlyOnce` accepts
only Linear behavior. A strict linear value used by the continuation after an
effect requires `ExactlyOnce`. Copy and affine state require only
`AtMostOnce`; affine state is cleaned if the handler aborts.

Handler bodies are effect-aware. A clause that contains one textual `continue`
is not Linear if a nested call or effect can abort before reaching it. Residual
effect rows and their control requirements compose into the inferred handler
behavior. A handler boundary discharges an effect only when its inferred
behavior satisfies every incoming requirement.

The type/effect checker owns this interprocedural inference. It uses qualified
constraints between value grades, effect-row entries, and handler behaviors.
MIR generation verifies the resulting concrete control flow and reports a
compiler error if the published contract and CFG disagree.

## Memory-effect vocabulary

Not every memory operation belongs in a function effect row.

### Function contracts

A typed function contract contains:

- checked parameter passing modes;
- checked result ownership;
- checked capture modes and types;
- a row of user and core effects;
- resume requirements on user effect entries.

V1 core effects include the existing runtime effects such as allocation, IO,
and async behavior. `Alloc` remains an inferred core effect even though the
runtime supplies its implicit handler.

Mutation through an explicit mutable parameter or capture is represented by
that passing or capture mode. Local mutation that cannot escape is not an
outward function effect. Borrowing is represented by types, passing modes, and
MIR loans. Escape is an ownership relation checked by MIR generation, not an
unordered effect-row label.

Region-indexed `Read(region)`, `Write(region)`, and `Alloc(region)` effects are
reserved for a future language design with region identities, region
polymorphism, and outlives constraints. V1 does not invent hidden region types
solely for the backend.

### Ordered resource actions

`CheckedMir` represents ordered local memory behavior directly:

```text
Initialize
Read
Write
Move
Copy
BorrowShared
BorrowMut
EndBorrow
Clone
Destroy
Escape
```

These are intrinsic semantics of MIR operations, not a parallel effect set.

## Target-neutral scalar intrinsics

Scalar operation identity is one closed semantic vocabulary shared directly by
TypedProgram, CheckedMir, and Talk IR. A phase may reject a cataloged operation
until its complete slice is verified, but it may not replace the identity with
a source spelling, parser type annotation, callable name, runtime opcode, or
target-specific operation.

```rust
pub enum ScalarType {
    Bool,
    Byte,
    Int,
    Float,
}

pub enum ScalarComparison {
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
}

pub enum ScalarIntrinsic {
    IntAdd,
    IntSub,
    IntMul,
    IntDiv,
    FloatAdd,
    FloatSub,
    FloatMul,
    FloatDiv,
    IntCompare(ScalarComparison),
    FloatCompare(ScalarComparison),
    ByteCompare(ScalarComparison),
    BoolEqual,
    BoolNotEqual,
    FloatToIntTrunc,
    IntToFloat,
    ByteToInt,
}
```

The signature is derived only from the operation:

- Int and Float arithmetic take two values of their named type and return that
  type;
- Int, Float, and Byte comparisons take two values of their named type and
  return Bool;
- Bool equality and inequality take two Bool values and return Bool;
- Float-to-Int, Int-to-Float, and Byte-to-Int take one value and return the
  type named by the destination.

Int is signed 64-bit. Add, subtract, and multiply wrap modulo 2^64; division
truncates toward zero, traps on zero, and maps `Int::MIN / -1` to `Int::MIN`.
Float operations use IEEE 754 binary64. Float-to-Int truncates toward zero,
maps NaN to zero, and saturates outside the Int range. Int-to-Float uses
binary64 round-to-nearest, ties-to-even. Byte-to-Int zero-extends. Int
comparisons are signed, Byte comparisons are unsigned, and Float comparisons
use IEEE ordered behavior, with NaN unequal to every value including itself.

Short-circuit boolean operations are CFG, not eager scalar intrinsics.
Character is an extended-grapheme-cluster borrowed view under ADR 0012 and is
not a scalar intrinsic type.

Source integer literals remove `_` separators and must denote one signed 64-bit
value. Unary minus directly on an integer token folds before protocol-operator
lowering, making `-9223372036854775808` valid while
`9223372036854775808` and `-9223372036854775809` diagnose. The canonical
frontend, MIR, and Talk IR representations carry `i64`, never source text.
Out-of-range expressions and patterns retain `InvalidInt` recovery for editor
continuity and cannot validate for MIR. A backend may not be the first phase to
parse or reject an integer literal.

The shared catalog alone does not enable execution. For a scalar trusted
inline-IR expression, type checking selects the `ScalarIntrinsic`. TypedProgram
publishes ordered operands only as an explicit-bind index with selected
`CopyEvidence`, enclosing-callable parameter `BindingId` with selected
`CopyEvidence`, or typed scalar constant. Bind and parameter reads use the
frontend-selected `CopyEvidence::Intrinsic`; constants create values and carry
no Copy proof. Float constants publish their binary64 bits. Parser registers,
source type annotations, and raw inline-IR instruction kinds do not cross the
seam.

A trusted operation outside the adopted scalar catalog becomes a semantic
`Unsupported` marker with no parser instruction payload. This keeps frontend
checking available without allowing MIR to reinterpret deferred memory, IO,
ownership, or target operations. A selected scalar operation with a malformed
bind, parameter, destination, literal, arity, or type becomes `InvalidScalar`,
receives a frontend diagnostic where source checking can identify the mismatch,
and cannot validate for MIR. Validation also proves that parameter operands
belong to the enclosing callable contract.

MIR and Talk IR verifiers must accept the exact signature before a producer or
lowerer may emit the operation. A module interface may publish
`ScalarIntrinsicImplementation` only when the exported function's complete body
is one validated scalar intrinsic over callable parameters or typed scalar
constants. The recipe contains the operation and parameter indexes, not source
syntax, parser registers, or a generic body. Its validator proves exact operand
and result types, no captures or concrete effects, no type parameters or
predicates, and an owned scalar result. Imported calls evaluate arguments once
in source order and materialize the recipe as `Rvalue::Intrinsic`; no callable
import or specialization demand remains.

For protocol-static calls, including operator desugarings, type-checker
finalization uses the solved receiver and canonical protocol application to
publish exactly one `(conformance, requirement, implementation)` selection.
TypedProgram validation proves that pair belongs to the selected conformance
row. MIR materializes that exact implementation, either as the validated scalar
recipe above or as a callable ID; no downstream phase may search for a witness.
General generic specialization and external supplier linking remain separate
L1/E2 obligations.

## `TypedProgram` contract

### Purpose

`TypedProgram` is the sole semantic frontend artifact. It is source-faithful
enough for editor features and explicit enough for MIR generation. Surface
syntax may remain for display and rewriting, but no downstream compiler phase
may treat a surface annotation as the checked meaning when a checked field
exists.

A valid `TypedProgram` contains:

```text
TypedProgram
  module identity
  files
  items: ItemStore
  entrypoints
  semantic source occurrences

TypedFile
  source identity and text length
  source-faithful typed roots

TypedItem
  stable item ID / symbol
  source origin
  name
  visibility
  checked scheme or contract
  checked item kind and body
```

The canonical `ItemStore` owns definitions for functions, structs, enums,
variants, protocols, requirements, effects, properties, type aliases,
conformances, and imported interfaces. File roots and nested declarations refer
to item IDs. Imported items may omit executable bodies, but their complete
checked interface is present in the store.

A function has exactly one implementation form: `Body`, `GlobalInitializer`,
`GlobalReader`, `Intrinsic`, `ScalarIntrinsic`, or `External`. `GlobalReader`
is generated only for a public immutable monomorphic Unit, Bool, Int, or Float
global and names that canonical global by `ItemId`. `ScalarIntrinsic` is the complete
validated implementation recipe for the narrow exported scalar case above. An
external callable records a stable module identity, exported name, and whether
the build expects source compilation or a precompiled Talk IR module. Function role and implementation are independent: role describes
source semantics such as method, handler, or generated function; implementation
describes where executable code comes from. There is no body-plus-linkage option
pair whose combinations need interpretation. Closure, handler, and script roles
require `Body`; a local generated role may use `Body`, `GlobalInitializer`, or
`GlobalReader`, while interface erasure may replace a generated reader with
`External`. External export names are non-empty.

A module interface is the serializable exported subset of canonical items. It
is not a separate scheme map plus catalog plus symbol-name map.

### Canonical source occurrences

Editor-facing source names are canonical `SemanticOccurrence` nodes in
`TypedProgram`, not a retained resolver map and not an unvalidated lookup table.
Each occurrence contains:

- a constrained `SemanticTarget`: an existing `ItemId`, an existing `BindingId`,
  or a declared type parameter;
- an exact source-token origin and a source selection span;
- a role distinguishing a definition, an ordinary source reference, a checked
  expression/member/pattern resolution, or a checked call-argument label;
- whether rename edits that token (import aliases may resolve to a target while
  remaining unedited).

The producer deduplicates only fully identical occurrence facts. The validator
requires registered source-node origins, in-bounds spans, a selection containing
the exact token origin, existing targets of the declared kind, one definition
per target, and agreement between definition occurrences and canonical
item/binding origins. Every source-backed canonical definition and resolution
must have a corresponding occurrence. Resolution-role occurrences must agree
with the canonical expression, member, pattern, capture, or call resolution at
their source node. Call-argument labels must agree with the selected initializer
and canonical property item. Every struct initializer entry must name a
`FunctionRole::Initializer`, and every such callable must have exactly one
owning struct. Calls lowered to a struct initializer use that validated owner to
require the struct's source occurrence rather than an occurrence naming the
initializer callable. Selection spans are half-open for both validation and
lookup. Equal-priority overlapping selections with different targets are
invalid, so lookup cannot depend on insertion order.

A position-to-occurrence map may be built for performance, but it is disposable
and derived only from validated occurrences. Retained source ASTs provide
syntax and ranges; they do not supply resolved names to editor consumers.

### Callable link suppliers

One canonical supplier plan is derived from the program's public exports and
the dependency-reachable callable items in its module interface. A source body
in that plan has one `CallableSupplier { item, export }`:

- a public callable uses its public export name unchanged;
- a generated callable or private witness uses `ItemId::callable_link_name`, a
  stable internal name in the reserved `talk-internal:` namespace derived from
  item kind and module-local identity, excluding session-local `ModuleId`;
- an exported scalar global's generated reader uses exactly
  `talk-global-reader:<public-export>`, so the accessor ABI follows the global's
  stable export identity rather than a display name or regenerated local ID;
- an intrinsic has no supplier and never becomes `External`.

Module-interface body erasure normally publishes `ExternalCallable` using that
plan. The sole executable-body exception is an exact
`ScalarIntrinsicImplementation`, which is published as a closed canonical
recipe and needs no link supplier at the call site. Import reconstruction
preserves either that exact recipe or the exact module/export pair instead of
recomputing either one. MIR exports are produced from the same supplier plan, and Talk
IR lowering preserves each MIR export/import name exactly. Thus a source-backed
external interface item and its emitted MIR/Talk IR supplier have the same
stable module ID, link name, and compatible callable signature. Display names
and `TypedItem::name` are never a second link-name authority.

### Required node facts

For a program eligible for MIR generation:

- every source name is resolved to a canonical item or binding ID;
- every expression has a zonked non-error type;
- every value-producing edge has a checked use mode;
- every call has a resolved callable kind, checked passing modes, type
  instantiation, and selected witness evidence where applicable;
- every member and pattern field has its resolved item;
- every binding and parameter has a checked type and mutability;
- every function and declaration has its checked scheme or contract;
- every closure and handler has checked captures with modes and types;
- every effect entry has its type arguments and resume requirement;
- every handler has its inferred behavior;
- every implicit clone and existential pack is an ordered explicit coercion;
- every source-derived node retains source provenance;
- every synthesized node carries provenance naming the source construct and
  reason that created it.

Imports and source annotations remain available as source syntax. MIR
generation ignores imports and reads checked item contracts rather than
reinterpreting type annotations. Trusted inline IR must contain checked
semantic types before this seam; MIR generation does not lower source type
annotations.

### Validity and editor recovery

Type checking may produce a recovery `TypedProgram` containing explicit error
nodes or `Ty::Error` so the LSP can continue serving a broken document. An
explicit `copy` use or capture for which the producer cannot select
`CopyEvidence` is retained as `UseMode::InvalidCopy` or
`CaptureMode::InvalidCopy`. The type-checking outcome carries a frontend
`NotConforming<Copy>` diagnostic; the invalid source choice is never rewritten
as Move and the capture is never omitted.

`mirgen` accepts only an error-free program that passes the `TypedProgram`
validator. `InvalidCopy` always fails that validator, so no `CheckedMir` is
published for the recovery program. The validator rejects missing checked fields, unresolved names,
`Ty::Error`, solver variables, invalid item references, and surface-only
execution forms. It does not consult diagnostics to establish validity.

`NodeID` and spans are provenance and links between canonical occurrence nodes
and canonical typed nodes only. No semantic consumer may use a `NodeID` to
obtain a type, resolution, instantiation, coercion, ownership mode, or
control-flow fact from a temporary or retained side map.

### Side-table disposition

The current fields are migrated as follows:

| Current fact | Canonical destination |
| --- | --- |
| `TypeOutput::node_types` | typed expressions, parameters, bindings, and items |
| `TypeOutput::schemes` | owning canonical items |
| `TypeOutput::instantiations` | call/member expression nodes |
| `TypeOutput::member_resolutions` | member and pattern nodes |
| `TypeOutput::for_plans` | type-checker temporary consumed before the seam |
| `TypeOutput::synthetic_floors` | typed-tree construction temporary |
| `TypeOutput::coerce_clones` | ordered expression coercions |
| `TypeOutput::local_tys` | owning bindings and parameters |
| `TypeOutput::existential_packs` | ordered expression coercions |
| `TypeOutput::imported_globals` | imported canonical `TypedGlobal::mutability` and `reader`; consumed before the seam |
| `TypeOutput::display_names` | canonical item and binding names |
| `TypeOutput::catalog` | canonical item definitions and relationships |
| `ResolvedNames::scopes` | typed block/item structure or disposable index |
| `ResolvedNames::symbol_names` | canonical item and binding names |
| `ResolvedNames::symbols_to_node` | disposable reverse index |
| `ResolvedNames::child_types` | canonical item relationships |
| `ResolvedNames::mutated_symbols` | checked bindings and explicit assignments |
| `ResolvedNames::public_symbols` | item visibility |
| name-resolution diagnostics | phase diagnostics only |

Derived catalog indexes such as `conformances_by_head`, `member_owners`, and
`extend_members` are not canonical semantic stores. Queries derive them from
canonical items or use disposable indexes whose removal cannot change an
answer.

### Forbidden `TypedProgram` interfaces

The migration removes:

- `TypedProgram::types()`;
- `TypedProgram::resolved_names()`;
- `TypedProgram::into_semantic_parts()`;
- public compiler access to `TypeOutput` after type checking;
- public compiler access to `ResolvedNames` after type checking;
- thread-local or global display-name installation as a requirement for
  rendering semantic types.

## `CheckedMir` contract

### Purpose and phase ownership

MIR generation is the ownership and borrow-checking phase:

```text
mirgen(TypedProgram) -> PhaseOutcome<CheckedMir>
```

It may privately construct an unchecked CFG, run dataflow, and rewrite that CFG.
No unchecked or partially annotated MIR leaves the module. On ownership errors,
it returns diagnostics and no `CheckedMir` eligible for lowering.

MIR generation owns:

- flattening expression evaluation in source order;
- compiling patterns into control flow;
- making places, moves, copies, clones, and borrows explicit;
- loan and initialized-place analysis;
- partial-move rejection;
- closure and handler capture validation;
- control-flow-linearity verification;
- normal and discontinue cleanup elaboration;
- drop flags where initializedness is path-dependent;
- source-level ownership diagnostics and explanations.

It does not own type inference, member lookup, witness selection, handler-mode
inference, implicit clone selection, or source evaluation-order decisions.
Those facts must be present in `TypedProgram`.

### Program shape

`CheckedMir` owns everything the lowerer requires:

```text
CheckedMir
  canonical MIR item/type/effect definitions
  generic function bodies
  handler bodies
  entrypoints and exports
  source provenance
```

A MIR callable item owns its `CallableContract` exactly once and has exactly one
implementation: `Defined(MirFunctionId)`, `Intrinsic`, or
`External(ExternalCallable)`. A defined `MirFunction` points back to its owning
`ItemId`; it does not duplicate the contract. Direct and witness-selected calls
refer to callable `ItemId`s so bodyless callables remain representable.
Operations that semantically require an in-module CFG body, such as closure or
handler construction, continue to require `MirFunctionId`.

For v1, all source bodies compiled as part of the current build are present in
one `CheckedMir`. An external callable remains self-contained through its
stable module/export identity. Reachable source or precompiled dependencies
contribute separate verified Talk IR modules; the Talk IR linker must provide
exactly one export with a compatible signature. The lowerer never asks
`TypedProgram` for a missing body, and target backends never resolve source
module identities themselves.

The initial E2 scalar linker accepts a set of individually verified
`(StableModuleId, TalkIrModule)` inputs and one root ID. Every callable import
must match exactly one function export by stable module ID and export name, with
an exactly compatible scalar signature. Duplicate module identities, missing
suppliers, and signature mismatches reject. Linking remaps module-local
function, signature, and global IDs once, rewrites direct and imported function
references, removes all imports, retains only root exports and entrypoints, and
re-verifies the combined `TalkIrModule`. It does not create another semantic
IR.

Scalar globals have one explicit initialization schedule. A literal initializer
remains the constant on `IrGlobal`; a dynamic initializer is a verified
zero-parameter function whose result initializes exactly one named global.
For a public immutable monomorphic Unit, Bool, Int, or Float global,
TypedProgram also owns one private generated zero-parameter `GlobalReader` with
that exact result type. The module interface preserves the global `ItemId`,
mutability, and reader relation while replacing the reader body with its exact
source-backed `ExternalCallable`. Consumer MIR lowers a read to that callable;
it never creates an external static place, external MIR global form, or Talk IR
global import. The MIR verifier rejects any external static place that bypasses
the reader.

Actions within one source module follow the TypedProgram producer's source-file
and declaration order. Linking traces reader imports reachable from initializer
functions exactly like existing callable imports, initializes suppliers before
consumers, and uses stable module ID as the deterministic tie break for
unrelated modules. Recursive initializer calls, global reads before their
scheduled action, duplicate immutable initialization, missing or incompatible
reader supply, and module-initialization dependency cycles reject before target
lowering. Target execution uses dedicated typed scalar global slots, not legacy
linear memory, and runs the linked schedule once before the selected entrypoint.
Mutable globals, writes, aggregates, managed storage, precompiled-only global
access, effects, and closure forms remain fail-closed.

A source function with no explicit effect annotation may retain exactly one
quantified open effect tail and no concrete effect entries. The scalar path may
erase that tail from its target signature only after MIR generation accepts the
body's effect-free subset; any concrete effect entry, effect operation, or
other non-type generic row still rejects. This permits the ordinary
`func main() -> Int` spelling without weakening the fail-closed effect boundary.

MIR remains generic. Function and item type parameters, qualified predicates,
call-site type instantiations, and selected witness evidence are explicit.
Reachability and monomorphization belong to the MIR-to-Talk-IR lowerer.

### Functions, blocks, places, and values

A MIR function contains:

- its canonical item ID, whose callable item owns the checked contract;
- typed parameters with passing modes;
- typed locals, temporaries, drop flags, and loan IDs;
- an entry block;
- basic blocks containing ordered statements and exactly one terminator;
- checked closure and handler capture descriptions;
- source provenance.

A `Place` is a typed storage path rooted at a parameter, local, temporary
storage slot, captured field, or static item, followed by checked projections
such as a stored field, enum payload, dereference, or indexed element. Projection
steps identify canonical fields or variants; they do not contain source labels
that require lookup.

An `Operand` is one of:

- a typed constant;
- an explicit Copy use of a place;
- an explicit Move use of a place;
- a temporary value;
- a direct function/item reference;
- an already checked borrowed value.

Borrow creation is an explicit statement producing a borrowed value and loan
ID. It is not inferred from an unclassified operand.

### Required operation families

Exact Rust enum names may differ, but the following distinctions are
normative.

Statements represent:

```text
StorageLive / StorageDead
Initialize place from rvalue
Begin shared or mutable borrow
End borrow
Explicit CheapClone or other selected clone
Aggregate and enum construction
Checked projection or payload extraction
Destroy affine value
Set or clear drop flag
Conditionally destroy using a drop flag
Install or remove deep handler
```

Move and Copy are explicit operand/use forms. Every MIR Copy operand carries
the `CopyEvidence` selected on its TypedProgram edge. Constants are value
creation, not Copy uses, and therefore need no Copy evidence. Assignment is
represented by right-hand-side evaluation followed by an explicit
destroy-if-live and initialization; the lowerer never infers replacement
cleanup from an assignment shape.

Terminators represent:

```text
Goto
Branch on operand
Switch on operand
Call
Perform
Return
Resume
Discontinue
Unreachable
```

Loops are CFG edges, not a distinct semantic loop evaluated by lowering.
Branches and switches contain operands whose evaluation already occurred in
statements.

Calls distinguish direct, witness-selected, and indirect callables. Every call
contains checked type arguments, witness arguments, passing modes, destination,
normal successor, and, when it may suspend under a user effect, a discontinue
cleanup successor.

`Perform` contains the concrete effect entry, arguments, result destination,
normal resumption successor, and discontinue cleanup successor.

`Resume` consumes a handler's resumption and supplies the effect result.
`Discontinue` consumes the resumption, runs its cleanup path, and supplies the
handler's abort result to the delimiter. No other operation may consume a
resumption.

Handler installation identifies the effect, checked handler body, inferred
behavior, captures, and delimiter extent. Every finite exit balances handler
installation structurally. The handler body itself does not run under the
handler it implements; a resumed continuation does.

### Cleanup representation

All executable cleanup is structural MIR:

- ordinary blocks contain explicit borrow endings and destroys;
- early exits target cleanup blocks;
- each suspension-capable call or perform has an explicit discontinue cleanup
  successor;
- path-dependent initializedness uses explicit drop flags and conditional
  destroy operations;
- match payloads are moved, borrowed, or destroyed explicitly in each arm;
- no outer aggregate drop implicitly owns a payload already extracted.

The lowerer receives no drop candidates, liveness sets, loan tables, scope
stacks, or cleanup side maps.

### Provenance

Every MIR function, local, block-changing source operation, memory operation,
call, effect operation, and synthesized cleanup carries an `Origin` containing:

- a primary source span;
- zero or more related source spans;
- a reason such as source use, argument transfer, implicit clone, closure
  capture, handler capture, assignment replacement, scope cleanup, early exit,
  discontinue cleanup, or pattern payload cleanup.

### Complete borrow provenance

The complete provenance of every borrow is part of the checked MIR semantics
and must be queryable by the LSP. A borrow explanation is a graph, not only the
span where the loan began. It includes every applicable event:

```text
owner/storage declaration
  -> initial shared or mutable borrow
  -> projection or reborrow
  -> argument-to-parameter transfer
  -> closure or handler capture
  -> each use that requires the loan to remain live
  -> every control-flow-specific EndBorrow
```

For a rejected borrow, the graph also includes the conflicting Move, Write,
Borrow, Destroy, Escape, or suspension operation and the path that kept the
loan active until that conflict.

`BeginBorrow` defines a canonical `LoanId` and records the borrowed place,
mutability, source owner, optional parent `LoanId`, and origin. Every borrowed
operand, projection, reborrow, call argument, parameter binding, and capture
structurally identifies the loan it carries. Every `EndBorrow` identifies the
loan and its origin. Abstract borrowed parameters and captures identify their
contract provenance, allowing an LSP query at a concrete call or closure
construction to join the caller loan to the callee or closure's abstract loan.
A body with several call sites therefore has a provenance graph with several
incoming edges rather than a fabricated single source.

The MIR operations are the canonical graph edges. `CheckedMir` does not
publish a second `LoanId -> BorrowFacts` answer. An LSP may build a disposable
index over loan definitions, uses, transfers, and endings, but deleting that
index and traversing the MIR must produce the same graph.

MIR generation may fail before producing `CheckedMir`. In that case every
borrow diagnostic carries the relevant partial provenance graph using the same
event and origin vocabulary, so invalid programs retain complete explanations
for all facts involved in the error.

Borrow subjects are globally unambiguous within a CheckedMir. A concrete subject
is `(MirFunctionId, LoanId)`; abstract imported or bodyless contracts use
`(ItemId, parameter index)` or `(ItemId, capture index)`. Every provenance event
also has a structural location: contract parameter/capture, local, statement,
or terminator. Cross-call and closure edges connect concrete and abstract
subjects rather than pretending that function-local `LoanId`s are global.

The artifact query is `BorrowProvenanceQuery { subject }` and returns
`BorrowProvenanceResult { subject, focus, provenance }`. `focus` identifies the
events selected by the query and `provenance` is their complete connected graph.
An LSP source-position index maps origins to subjects and locations, then invokes
this artifact-level query. The index is disposable and cannot supply graph facts
of its own.

MIR ownership failures use one `OwnershipDiagnostic` shape with a typed
`OwnershipDiagnosticKind`, the failed transition's `Origin` as `primary`, the
failed transition's graph events as `focus`, and the complete relevant
provenance graph. The non-focus graph event kinds derive related
origin roles: owner declaration, borrow source, parent borrow, argument,
parameter, capture, prior use, borrow end, or conflicting use. A `Move` event
derives the prior-use role. A second stored related-span list and free-form
semantic message are forbidden.
Non-borrow ownership errors use owner and move events when declaration or prior
move origins caused the failure; otherwise they may carry an empty graph.
Rejected borrow errors may not carry an empty graph.

`OwnershipDiagnosticKind::ImmutableOverwrite { place }` is the canonical source
error for replacement assignment to immutable storage. Its provenance includes
the storage's owner declaration as a non-focus event. MIR verification tracks
initialization history for each `StorageLive` lifetime and rejects immutable
reinitialization regardless of how a preceding Destroy was labeled. It also
rejects any `AssignmentReplacement` operation whose destination is not
canonically mutable.

A diagnostic therefore names the failed MIR transition and cites the complete
relevant provenance subgraph. Successful LSP explanations derive from the same
operations. Provenance is embedded; it is not a `NodeID`-keyed fact table.

### `CheckedMir` verifier

A `CheckedMir` eligible for lowering has passed a verifier that establishes:

1. every block exists and has exactly one terminator;
2. all referenced items, places, locals, loans, flags, and blocks exist;
3. every operation and edge is well typed;
4. no type contains `Ty::Error`, unresolved solver variables, or source-only
   annotations;
5. evaluation order is represented once in statements;
6. every read is initialized, and immutable storage is initialized at most once
   in each `StorageLive` lifetime;
7. every Move deinitializes exactly one live source;
8. Copy is used only for Copy-grade values;
9. every selected clone is explicit;
10. shared and mutable loans obey exclusivity and end structurally;
11. every borrowed value, projection, reborrow, argument, parameter, and
    capture has an unbroken provenance path to one owner or abstract contract
    origin, and every finite path records where that loan ends;
12. no ordinary loan crosses a suspension-capable operation in v1; a
    handler-capture shared loan spans exactly its balanced handler extent;
13. every affine value is transferred or destroyed on every finite exit;
14. every strict linear value is consumed exactly once on every finite exit;
15. no source aggregate remains partially moved;
16. every normal, early, and discontinue cleanup path is complete and ordered;
17. every finite handler exit consumes its resumption exactly once by Resume
    or Discontinue;
18. every handler CFG agrees with its TypedProgram behavior and effect
    requirements;
19. handler installation is balanced on every finite path;
20. every callable and witness is resolved;
21. every operation required for lowering has provenance.

Verifier failure on compiler-produced MIR is an internal compiler error. Source
ownership violations are diagnosed before constructing the verified artifact.

### Forbidden MIR outputs

`CheckedMir` does not expose or accompany:

- `FlowFacts`;
- a detached borrow or loan fact table that duplicates structural loan events;
- liveness sets;
- drop candidates;
- source AST expressions in terminators;
- source patterns;
- unresolved member names;
- a `TypedProgram` reference required by lowering.

## MIR-to-Talk-IR lowerer contract

The lowerer interface is:

```text
lower(CheckedMir) -> TalkIrModule
```

The lowerer assumes all source typing, ownership, borrowing, handler, and
cleanup invariants above. It does not emit source-correctness diagnostics.
Failure to lower verified MIR is an internal compiler error.

The lowerer owns:

- entrypoint reachability;
- monomorphization and qualified-predicate instantiation;
- witness and protocol dispatch materialization;
- closure environment conversion;
- handler/capability representation lowering;
- concrete type representation and generated clone/destroy/deinit glue;
- lowering explicit MIR cleanup to explicit Talk IR operations;
- production and verification of one target-neutral `TalkIrModule`.

Its private implementation may use temporary work forms. No additional public
semantic IR exists between `CheckedMir` and `TalkIrModule`.

The lowerer may not:

- consult `TypedProgram`, `TypeOutput`, `ResolvedNames`, or source ASTs;
- perform member lookup or type inference;
- choose move versus copy versus borrow;
- infer handler behavior;
- discover missing drops from liveness;
- synthesize ownership semantics from type shape alone;
- silently repair invalid MIR.

## `TalkIrModule` contract

Talk IR is Talk's target-neutral executable IR. It is not shaped around the
current bytecode runtime.

A valid `TalkIrModule` is:

- monomorphic for all reachable executable functions;
- direct-style and CFG-based;
- typed with target-neutral scalar, aggregate, reference, function, and
  continuation representations;
- closure-converted;
- explicit about allocation, loads, stores, clones, destroys, and generated
  cleanup functions;
- explicit about handler installation, perform, one-shot resume, and
  discontinue;
- free of source borrows, source patterns, protocol lookup, generic witness
  selection, and source ownership diagnostics;
- self-contained for a target backend.

Concrete pointer width, ABI details, bytecode registers, WebAssembly locals,
and C or LLVM layout choices belong to target backends. Talk IR operations and
its generated glue define the common executable semantics those backends must
preserve. Talk IR imports retain the external callable's `StableModuleId`,
export name, and monomorphic signature; display names are not link identities.

The bytecode, WebAssembly, C, Cranelift, and LLVM paths consume only
`TalkIrModule` plus an explicit target configuration. No target backend reads
`CheckedMir`.

The scalar bytecode target executes only a `ValidatedBytecodeModule` produced
by a fail-closed profile check. The E1 base accepts scalar constants, register
moves, scalar arithmetic/comparison/conversion, direct calls, CFG control,
returns, and traps. The E2 extension also accepts typed scalar global
descriptors and dedicated `GlobalGet`/`GlobalSet` instructions. It rejects every
other legacy opcode family, statics, unwind data, non-scalar runtime constants,
malformed pool/index/global data, out-of-chunk control targets, call arity
mismatch, nonzero entry arity, and reachable fallthrough. Validation consumes the raw module and keeps it private;
the compiler adapter cannot mutate or bypass the proof wrapper. Runtime scalar
kind checks remain defense in depth and report errors rather than panicking.
The broad legacy runtime module remains quarantined and is not a compiler-facing
contract.

The scalar adapter takes only verified `TalkIrModule` plus one selected
published zero-parameter entry. It preflights the complete module before
emission, assigns scalar SSA values and stack slots to target registers, folds
slot `AddressOfSlot`/`Load`/`Store` into target-local moves, lowers global
addresses to dedicated global gets and sets, lowers direct calls through the
argument pool and normal edge, and implements block-parameter edges as parallel
copies with a cycle-breaking temporary. When an initialization schedule is
present, it synthesizes an internal zero-parameter entry wrapper that performs
each action once in verified order and then calls the selected root entry. Branch and switch edges use
adapter blocks as needed; arbitrary literal switches become ordered scalar
equality branches rather than dense-tag assumptions. Unit return uses runtime Void and reachable Unreachable traps deterministically.
Unlinked imports, Character, aggregates, non-scalar globals, effects,
indirect/discontinuing calls, and all other forms reject fail closed. The adapter's only successful output is a
`ValidatedBytecodeModule`.

The E1 driver exposes that exact path through a `ScalarExecutable`; it does not
construct a second evaluator. `talk run --entry <export>` selects a published
zero-parameter function. Without an explicit name it selects one published
entrypoint, exported `main`, or one unambiguous zero-parameter export, and
rejects ambiguity. Final scalar results render with Talk syntax (`42`, `1.0`,
`true`) and Unit emits no result line. Runtime enum names such as `I64(42)` are
not language output. Counted scalar execution must report zero allocations and
objects. Unsupported source and target forms fail before execution with no
older-backend fallback.

## Cross-artifact laws

Artifact shapes are not sufficient contracts by themselves. Every implemented
slice must satisfy the following relational laws across its seams. A capability
is not `Integrated` merely because each artifact validates independently.

### Semantic authority and derivability law

Each semantic question has one canonical answer in one owning artifact.
Downstream adapters may build disposable indexes, but an index must be derived
from canonical nodes or items, must not change an answer when deleted, and must
not become a second semantic store.

After type checking, retained source ASTs provide syntax, tokens, and rewrite
ranges only. Completion, definition, rename, code actions, diagnostics, MIR
construction, and module export may not obtain semantic answers from resolved
names embedded in that AST. If editor-facing source occurrences are canonical
TypedProgram nodes, their relationship to executable nodes and canonical items
must be represented and validated. If they are indexes, they must be
reconstructible from those nodes and items.

### Identity preservation and external supply law

An identity crossing a seam is preserved exactly or translated by one mapping
owned by the producer. Display names are never identities.

For every source-backed `ExternalCallable { module, export, ... }` published by
a module interface, the supplying module must emit exactly one linkable export
with the same stable module ID, export name, and compatible callable contract.
Public source exports and compiler-generated internal exports may use different
names, but one shared link-name calculation must produce both the importing and
supplying sides. Private witness implementations and generated callables needed
by an exported interface are part of this law. Intrinsics remain intrinsic and
never acquire a fabricated external supplier.

The same identity rule applies to callable items, conformances, witnesses,
loans, blocks, values, effects, and generated glue as they are translated into
downstream dense identities.

### Shape compatibility law

Whenever a consumer changes representation, its adapter must preserve the
producer's callable and control shape. Parameter order, passing mode, result
type, effect/discontinue behavior, witness selection, and monomorphic signature
must agree at both sides of a call. Function-entry adapters may store incoming
parameters, but backedges target parameterless internal blocks and may not
rebind function parameters.

### Ordered ownership law

A downstream phase preserves source evaluation order and the ownership actions
selected upstream. It may materialize values, split edges, or insert adapter
blocks, but those transformations may not reorder argument evaluation, turn
Copy into Move, discard an affine transfer, repeat initialization of immutable
storage, or choose cleanup from liveness. Unsupported materialization is
rejected before partial lowering changes the represented order.

### Recovery and fail-closed law

An invalid explicit source choice remains represented as recovery data, carries
a frontend diagnostic, and cannot validate for MIR. No producer may silently
replace an invalid Copy, capture, borrow, call, or handler choice with a valid
different operation.

Validators and verifiers reject every unsupported or malformed form before
publishing the next artifact. Strengthening a validator invalidates stale
consumer fixtures until those fixtures are corrected; tests may not waive the
new invariant.

### Provenance law

Every source-derived fact that can produce a diagnostic or editor answer keeps
a source-file-backed origin. Generated facts name their source and generation
reason. Diagnostic related origins derive from canonical provenance events, not
from a second stored span list.

### Erasure law

A fact disappears only at the phase named by this ADR. Copy evidence ends after
MIR verification; source borrows end during Talk IR lowering; source syntax and
ownership diagnostics do not enter Talk IR. An erased fact may not reappear
through downstream inference or an older artifact lookup.

Each law requires a positive producer-consumer test and a negative test that
would fail if the two sides drifted. The concrete contract document records the
Rust shapes; this ADR remains the authority for the relationships among them.

## Parallel implementation agreement

The three producer/consumer teams work against these contracts:

| Producer | Produces | Consumer may assume | Consumer must not request |
| --- | --- | --- | --- |
| Type checker | validated semantic nodes, canonical items, contracts, modes, coercions, effect requirements, handler behavior | all source semantic choices are final | `TypeOutput`, `ResolvedNames`, raw annotations as meaning |
| MIR generation | verified CFG, explicit ownership/loans/cleanup/effects/provenance | source program is memory- and control-safe | source AST, flow facts, liveness or drop side tables |
| Lowerer | monomorphic target-neutral Talk IR | target backend need only preserve explicit IR semantics | TypedProgram, CheckedMir, source diagnostics |

Interface fixture builders are permitted in test-only code:

- MIR generation tests may construct valid `TypedProgram` fixtures through a
  builder that runs the TypedProgram validator.
- Lowerer tests may construct `CheckedMir` fixtures through a builder that runs
  the MIR verifier.
- No production constructor may bypass validation or verification.

Artifact printers may be used for debugging and focused contract tests. Broad
snapshot tests of internal structure are not the semantic oracle; black-box
source tests and verifier tests are.

A proposed contract change that makes a consumer ask for an older phase's
artifact requires an ADR amendment, not an ad-hoc parameter.

### Integration gates

Parallel work may be ahead on fixtures, but support crosses a production seam
only through these gates, in order:

1. **G0 - Contract gate**
   - Amend this ADR for any new semantic fact, identity, recovery state, or
     cross-artifact relationship.
   - Update `docs/stage-0-contract-types.md`, Rust contract types, validators,
     printers, and `docs/backend-status.md` in the same stack.
   - Add a negative validator or verifier test for every new invariant.
2. **G1 - Producer gate**
   - The real producer emits the fact without consulting a downstream phase.
   - A producer contract test proves the exact field, identity, mode, origin,
     and error-recovery behavior.
   - Unsupported source forms produce a typed diagnostic rather than a
     downstream internal invariant.
3. **G2 - Consumer gate**
   - The consumer accepts a validator-approved fixture for the slice and
     rejects malformed and unsupported fixtures fail closed.
   - A verifier strengthening reruns all downstream fixture suites before it
     can merge.
4. **G3 - Handshake gate**
   - A real producer artifact is consumed by the real next phase.
   - The test asserts the relevant cross-artifact law, not only that both calls
     returned `Ok`. Identity, link supply, signature, ordering, provenance, and
     erasure are checked where applicable.
5. **G4 - Integrated-head gate**
   - Rebase the complete stack onto the current primary head after all earlier
     lane changes have landed.
   - Run producer, consumer, handshake, LSP, formatting, diagnostics, workspace,
     and external smoke tests from the primary checkout. Branch-local test
     counts are insufficient.
   - Preserve unrelated working-tree changes and rerun path-sensitive tests in
     the primary checkout.
6. **G5 - Execution gate**
   - Once a backend exists, the same source fixture executes through every
     backend claiming the row and produces the same observable result.

A row in `docs/backend-status.md` may move to `Integrated` only after G0 through
G4 pass. Before a backend exists, G5 is marked not connected rather than
waived.

Changes have mandatory impact suites:

| Changed seam | Suites that must rerun |
| --- | --- |
| TypedProgram contract, producer, or validator | frontend producer tests, analysis/LSP semantic queries, MIR generation/verifier, TypedProgram-to-MIR and three-artifact handshakes |
| Module interface or callable linkage | interface serialization, import reconstruction, exact external-supply matching, MIR exports, Talk IR imports/exports |
| CheckedMir shape, generator, or verifier | MIR producer and negative verifier tests, every Talk IR fixture and handshake |
| Talk IR shape, lowerer, or verifier | all lowerer tests and every connected backend adapter |
| Origin or provenance shape | compiler diagnostics, successful provenance queries, rejected-program diagnostics, and LSP rendering |

Consumer fixture work may land ahead of its producer only while production
input remains explicitly rejected. Support for one row lands upstream to
downstream, or as a coordinated stack that passes G4 after rebasing; independent
branch success is not an integration result.

## Migration plan and acceptance

 Stage 0: land contract types first

 One shared change establishes:

 ```text
   TypedProgram
   CheckedMir
   TalkIrModule
   Origin / BorrowProvenance
   ItemId / FunctionId / BlockId / LoanId
   UseMode / PassingMode / CaptureMode
   HandlerBehavior / ResumeRequirement
 ```

 It also provides:

 - private production constructors;
 - validators and verifiers;
 - deterministic artifact printers;
 - test-only fixture builders that run validation;
 - no driver integration yet.

 No team defines local copies of these types.

 Validation wrappers

 Conceptually:

 ```text
   TypedProgram::validate_for_mir()
   mir::verify(candidate) -> CheckedMir
   talk_ir::verify(candidate) -> TalkIrModule
 ```

 A validator wrapper may prove validity, but it contains no additional semantic facts.

 Test fixtures must pass the same validators as real artifacts. There is no unchecked_for_tests() escape hatch.

 Workstream A: type checker and TypedProgram

 Owns

 - canonical ItemStore;
 - checked item contracts;
 - checked use, passing, and capture modes;
 - effect rows and resume requirements;
 - handler behavior inference;
 - node-local types, resolutions, witnesses, and coercions;
 - module interface generation;
 - source-faithful typed syntax;
 - TypedProgram validation.

 Does not own

 - CFG construction;
 - loan endpoints;
 - move/initialization dataflow;
 - drop placement;
 - MIR cleanup;
 - representation or layout.

 Can work independently using

 Existing source tests and direct inspection through the artifact printer:

 ```text
   source -> TypedProgram -> validate
 ```

 Its acceptance test is that the produced artifact satisfies the same validator used by MIR fixtures.

 Substreams

 The type-checker work can itself be divided:

 1. canonical items and module interfaces;
 2. expression/binding/use facts;
 3. effects and handler contracts;
 4. LSP migration;
 5. side-table deletion.

 The old maps remain internal to type checking until the final cutover, but none may escape the phase.

 Workstream B: MIR generation

 MIR development starts immediately after the contract skeleton using hand-built valid TypedProgram fixtures.

 Owns

 - expression flattening and source evaluation order;
 - places, temporaries, blocks, and terminators;
 - explicit Move/Copy/Borrow/Clone operations;
 - pattern decision trees;
 - initialization and move analysis;
 - loan creation, use, transfer, and ending;
 - complete borrow provenance;
 - affine cleanup and drop flags;
 - strict linear validation;
 - handler capture validation;
 - Resume/Discontinue paths;
 - the CheckedMir verifier.

 Does not own

 - selecting move versus copy;
 - type inference;
 - member resolution;
 - effect-row inference;
 - handler behavior inference;
 - witness selection;
 - monomorphization;
 - closure representation.

 Early fixture example

 ```text
   TypedProgram fixture:
     func main() -> Int {
         let x: Int = 42
         return x
     }

   Expected CheckedMir:
     bb0:
       StorageLive(x)
       Initialize(x, Const(42))
       Return(Copy(x))
 ```

 Later fixtures cover borrow provenance independently of the frontend:

 ```text
   Owner(x)
     -> BeginBorrow(loan1, x)
     -> Reborrow(loan2, loan1.field)
     -> CallArgument(loan2)
     -> ParameterLoan(loan2)
     -> Use(loan2)
     -> EndBorrow(loan2)
     -> EndBorrow(loan1)
 ```

 This allows the ownership checker and LSP provenance query to be implemented before the type checker emits such a program.

 Workstream C: MIR-to-Talk-IR lowering

 The lowerer starts against hand-built, verifier-approved CheckedMir.

 Owns

 - reachability;
 - monomorphization;
 - witness materialization;
 - closure conversion;
 - handler representation;
 - generated clone/destroy/deinit functions;
 - target-neutral storage operations;
 - Talk IR verification.

 Does not own

 - source diagnostics;
 - move or borrow inference;
 - loan analysis;
 - cleanup discovery;
 - source type queries;
 - pattern compilation;
 - handler-mode decisions.

 Early fixture example

 ```text
   CheckedMir fixture:
     fn main:
       bb0:
         return Const(Int, 42)

   Expected Talk IR:
     monomorphic function main
     target-neutral Int constant
     direct return
 ```

 The lowerer can therefore establish its representation, verifier, and printer without waiting for real MIR generation.

 Optional parallel observer: LSP provenance

 The LSP work can consume hand-built CheckedMir fixtures at the same time.

 It implements:

 - find the loan at a source position;
 - walk to its owner or abstract parameter;
 - include every projection, reborrow, call transfer, and capture;
 - show uses that keep it live;
 - show all CFG-specific endings;
 - render conflicts and related spans.

 Its index is disposable. The MIR operations remain the canonical graph.

 Feature cadence

 The teams should work one or two slices apart:

 ┌───────┬──────────────────┬──────────────────┬────────────────────────┐
 │ Slice │ Type checker     │ MIR generation   │ Lowerer                │
 ├───────┼──────────────────┼──────────────────┼────────────────────────┤
 │ F0    │ Copy scalars     │ Fixtures         │ Fixtures               │
 ├───────┼──────────────────┼──────────────────┼────────────────────────┤
 │ F1    │ Branches/loops   │ Copy scalars     │ Copy scalars           │
 ├───────┼──────────────────┼──────────────────┼────────────────────────┤
 │ F2    │ Affine values    │ Branches/loops   │ Branches/loops         │
 ├───────┼──────────────────┼──────────────────┼────────────────────────┤
 │ F3    │ Aggregates/match │ Affine values    │ Affine values          │
 ├───────┼──────────────────┼──────────────────┼────────────────────────┤
 │ F4    │ Borrows          │ Aggregates/match │ Aggregates/match       │
 ├───────┼──────────────────┼──────────────────┼────────────────────────┤
 │ F5    │ Closures         │ Borrows          │ Borrows erased/lowered │
 ├───────┼──────────────────┼──────────────────┼────────────────────────┤
 │ F6    │ Effects          │ Closures         │ Closures               │
 ├───────┼──────────────────┼──────────────────┼────────────────────────┤
 │ F7    │ Complete effects │ Effects          │ Effects                │
 └───────┴──────────────────┴──────────────────┴────────────────────────┘

 A downstream implementation may merge before its producer if:

 - it is exercised through validated fixtures;
 - it is not connected to a production fallback;
 - unsupported production input still fails explicitly.

 Handshake tests

 Each slice has four test levels mapped to the integration gates:

 1. Producer contract test

    ```text
      source -> artifact -> validator
    ```

 2. Consumer fixture test

    ```text
      hand-built preceding artifact -> consumer artifact -> verifier
    ```

 3. Handshake test

    ```text
      real producer artifact -> real consumer
    ```

    The assertion names the cross-artifact law under test. Examples include an
    exact callable ID/signature match, an exact external import/export supplier
    match, preserved source argument order, a source-file-backed diagnostic
    origin, or verified erasure of Copy evidence.

 4. Black-box test

    ```text
      source -> TypedProgram -> CheckedMir -> Talk IR -> backend -> result
    ```

 Internal snapshots aid debugging but do not define semantics. A source test, a
 consumer fixture, and a validator can all pass while disagreeing with each
 other; only the handshake test closes that gap.

 Contract change protocol

 If MIR generation needs information missing from TypedProgram:

 1. demonstrate why it cannot be derived from existing checked fields;
 2. amend this ADR with the owning phase and affected cross-artifact laws;
 3. add one canonical field to the TypedProgram contract;
 4. add validator invariants and negative tests;
 5. add producer, consumer-fixture, and real handshake tests;
 6. update the type checker;
 7. pass G4 from the rebased primary checkout.

 It may not temporarily request TypeOutput or ResolvedNames.

 The same rule applies when the lowerer needs information missing from CheckedMir. It may not accept TypedProgram as an extra parameter or reconstruct the fact.

 Critical path

 Stage 0 is the first serialization point: the concrete contract types land
 before implementation branches. Every later production slice has a second
 serialization point at G3/G4, where the real producer-consumer handshake lands
 and the coordinated stack is validated from the current primary head.

 After Stage 0:

 - the type checker can replace its side-table output;
 - MIR generation can operate entirely on fixtures;
 - the lowerer can operate entirely on verified MIR fixtures;
 - the LSP can implement borrow-provenance rendering;
 - integration happens incrementally by feature slice through G0-G4.

 This avoids both a big-bang backend merge and the false confidence of
 independently green branches whose shared seam has drifted.

### Stage 0 - Contract skeleton

Before the three implementations diverge, land one contract-only change that
contains:

1. the canonical IDs, contracts, modes, origins, and item definitions shared by
   the artifacts;
2. the `TypedProgram`, `CheckedMir`, and `TalkIrModule` data shapes required by
   this ADR, with semantic fields private where a validated constructor is
   required;
3. validator/verifier entrypoints and test-only checked fixture builders;
4. artifact printers sufficient to diagnose producer/consumer disagreements;
5. private validated constructors, so production callers can obtain an
   artifact only from its producer or verifier.

The skeleton does not add a second compiler path and does not pretend that an
unimplemented validator has accepted an artifact. Until a validator is real,
only test-only fixtures may cross that seam. Type-checker, MIR-generation, and
lowerer work branches rebase on this skeleton and may not define private copies
of the contract types.

### Stage 1 - TypedProgram cutover

1. Introduce canonical typed items and checked binding/use/capture modes.
2. Preserve source-faithful imports and editor-relevant syntax in typed files.
3. Bake all remaining node-specific type and name facts onto nodes or canonical
   items.
4. Port module export/import to canonical item interfaces.
5. Port hover, completion, definition, rename, code actions, and exhaustiveness
   to `TypedProgram` queries.
6. Delete post-typechecking access to `TypeOutput` and `ResolvedNames`.
7. Delete persistent derived catalog indexes or make them disposable query
   indexes with canonical-item validation.

Stage 1 is accepted only when:

- `TypedProgram::types`, `resolved_names`, and `into_semantic_parts` do not
  exist;
- no compiler or LSP semantic query joins a source node to a `NodeID`-keyed
  type, resolution, instantiation, coercion, or ownership map;
- retained source ASTs are syntax-only: no completion, hover, definition,
  rename, code-action, diagnostic, module, or compiler path reads their resolved
  symbols as semantic authority;
- editor source occurrences are either validated canonical nodes or disposable
  indexes derived solely from canonical nodes, with negative consistency tests;
- module interfaces contain canonical exported items rather than parallel
  scheme/catalog/name maps;
- every source-backed external callable has an exact supplying export under the
  same shared link-name rule, including generated and private witness callables;
- the TypedProgram validator covers every required fact listed in this ADR;
- all existing frontend and LSP tests pass;
- every source file in `~/apps/talk-syntax` and `~/apps/talispk` reaches the
  same or a more precise frontend result, with differences reviewed rather than
  silently accepted.

### Stage 2 - CheckedMir bring-up

1. Add the private unchecked CFG builder and public CheckedMir artifact.
2. Implement Copy-only scalars, direct calls, returns, branches, switches, and
   loops.
3. Add explicit places, affine moves, initialization analysis, and cleanup.
4. Add loans and the v1 no-borrow-across-perform rule.
5. Add aggregates, consuming matches, and explicit payload cleanup.
6. Add closures and checked captures.
7. Add deep handlers, control-flow-linearity verification, Resume, and
   Discontinue cleanup.

Every substage adds source-to-CheckedMir verifier tests. No unverified MIR is
published to the lowerer.

Stage 2 is accepted only when:

- ownership errors carry primary and related source spans;
- every valid borrow has an LSP-queryable provenance graph from owner or
  abstract parameter through all reborrows, projections, transfers, uses, and
  control-flow-specific endings;
- every invalid borrow diagnostic carries the complete conflicting provenance
  subgraph, including why the loan remained live;
- provenance tests cover direct borrows, reborrows, field projections, mutable
  borrows, call arguments, closure captures, handler captures, branch-specific
  endings, and conflicts;
- valid memory facts can be explained from embedded MIR origins;
- every verifier invariant has at least one negative test;
- MIR generation consumes only `TypedProgram`;
- `CheckedMir` is the only post-ownership artifact;
- the two external smoke repositories pass for the implemented language
  subset, and unsupported features fail explicitly.

### Stage 3 - Talk IR lowerer bring-up

1. Define the target-neutral Talk IR data types and verifier.
2. Lower the Copy-only CheckedMir subset.
3. Add monomorphization, witnesses, aggregates, closure conversion, explicit
   cleanup/glue, and effects in the same order as CheckedMir support.
4. Add one black-box source-to-Talk-IR-to-bytecode path using only the adopted
   conventional subset of `talk-runtime`; runtime-specific continuation and
   region policies are not imported into Talk IR.
5. Add WebAssembly as the second independent consumer before treating Talk IR
   as stable for native backends.

Stage 3 is accepted only when:

- lowering consumes only `CheckedMir`;
- target backends consume only `TalkIrModule` and target configuration;
- bytecode and WebAssembly execute the same black-box semantic fixtures for
  their shared implemented subset;
- no second evaluator is introduced as a semantic authority;
- source-to-runtime tests, not internal IR snapshots, define behavior.

### Repository-wide validation

At each mergeable milestone, after rebasing the coordinated stack onto the
current primary head:

- every affected producer-consumer handshake and cross-artifact law test passes;
- `cargo check --workspace --exclude www` passes without warnings;
- `cargo test --workspace --exclude www` passes;
- embedding and Swift tests affected by the milestone pass;
- `git diff --check` passes;
- the working compiler exposes unavailable later phases explicitly rather than
  silently accepting or partially lowering them;
- path-sensitive tests and external smoke repositories are run from the primary
  checkout, not waived based on branch-local failures.

## Consequences

The type checker becomes responsible for publishing a deeper artifact. This is
intentional: source semantic choices belong at the source semantic phase.

MIR generation becomes the sole owner of flow-sensitive memory correctness and
cleanup elaboration. Its diagnostics and LSP explanations come from the same
operations it verifies.

The lowerer can be developed independently against hand-built verified MIR and
cannot regress source ownership by re-deriving it.

The canonical item store replaces several convenient hash maps. Some editor and
compiler queries may initially scan more data or build disposable indexes. That
cost is accepted until profiling demonstrates a need for caches; correctness
does not depend on a cache.

The v1 restrictions on borrowed escape, borrows across effects, deep-handler
captures, partial moves, and effectful cleanup are conservative. Relaxing any of
them requires extending the artifact contract and verifier first, not a lowering
workaround.

## Relationship to earlier ADRs

- ADR 0031 remains the reset and recovery point. This ADR is the new backend
  decision required by its consequences section.
- This ADR replaces ADR 0019's old interface. In particular, lowering receives
  only `CheckedMir`, not `TypedProgram` plus `CheckedMir`, and no `FlowFacts`
  artifact is published.
- ADR 0011 and ADR 0027 remain superseded as implementations. This ADR adopts
  the source-level dynamic, deep, one-shot and discontinue semantics described
  here without adopting capability-passing CPS, lambda-G, or the old VM
  mechanism.
- ADR 0029 remains rejected. Type-specific CheapClone and explicit generated
  cleanup do not imply uniform reference counting.
- ADR 0008 remains the source direction for managed storage and FFI where it
  does not conflict with the stricter artifact and ownership contracts here.
