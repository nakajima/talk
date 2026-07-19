# Stage 0 compiler artifact contract types

Status: canonical TypedProgram, checked MIR, Talk IR, E1 scalar execution, and E2 scalar globals/linking implemented (2026-07-14)

This document turns ADR 0032 into concrete Rust-shaped contracts. It is not an
implementation plan for typing, ownership checking, lowering, or a backend. The
names and field distinctions below are intended to become production types
before the three implementations branch.

The draft deliberately reuses the current `Ty`, `Scheme`, `Predicate`,
`EffectRow`, `Symbol`, `Span`, and `Source` representations where they already
express the required fact. Replacing those representations is outside Stage 0.

All artifact roots are private in production. Accessors expose immutable
semantic data. Only the owning producer can construct an unvalidated candidate.
The implemented skeleton lives in:

- `src/compiling/contracts.rs`;
- `src/compiling/typed_program/contract.rs`;
- `src/mir/mod.rs`;
- `src/talk_ir/mod.rs`.

MIR and Talk IR candidate constructors and structural verifiers are test-only
until their complete semantic verifiers land. Production code therefore cannot
mistake the Stage 0 structural checks for the final validity proof.

## Shared semantic vocabulary

```rust
use crate::compiling::driver::Source;
use crate::compiling::module::ModuleId;
use crate::name_resolution::symbol::Symbol;
use crate::node_id::{FileID, NodeID};
use crate::span::Span;
use crate::types::catalog::Grade;
use crate::types::ty::{EffTail, EffectEntry, EffectRow, Predicate, Scheme, SchemeParam, Ty};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ConformanceId {
    module: ModuleId,
    local: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ExtensionId {
    module: ModuleId,
    local: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ItemId {
    Named(Symbol),
    Conformance(ConformanceId),
    Extension(ExtensionId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BindingId(Symbol);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Mutability {
    Immutable,
    Mutable,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ScalarType {
    Bool,
    Byte,
    Int,
    Float,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ScalarComparison {
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
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

pub struct ScalarIntrinsicSignature {
    operands: &'static [ScalarType],
    result: ScalarType,
}

pub struct ScalarIntrinsicImplementation {
    operation: ScalarIntrinsic,
    operands: Vec<ScalarIntrinsicImplementationOperand>,
}

pub enum ScalarIntrinsicImplementationOperand {
    Parameter { index: u32 },
    Int(i64),
    FloatBits(u64),
    Bool(bool),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CopyEvidence {
    Intrinsic,
    PayloadFreeEnum { enumeration: ItemId },
    TypeParameter { parameter: Symbol, predicate_index: u32 },
    Conformance {
        conformance: ConformanceId,
        substitution: Vec<(Symbol, Ty)>,
        premises: Vec<CopyEvidence>,
    },
    Tuple(Vec<CopyEvidence>),
    Record(Vec<(crate::label::Label, CopyEvidence)>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UseMode {
    Copy(CopyEvidence),
    InvalidCopy,
    Move,
    BorrowShared,
    BorrowMut,
    Discard,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExprDisposition {
    Value(UseMode),
    Place(PlaceContext),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PlaceContext {
    AssignmentDestination,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PassingMode {
    BorrowShared,
    BorrowMut,
    Consume,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CaptureMode {
    Copy(CopyEvidence),
    InvalidCopy,
    Move,
    BorrowShared,
    BorrowMut,
}

pub struct ExternalCallable {
    module: crate::compiling::module::StableModuleId,
    export: String,
    availability: ExternalCallableAvailability,
}

pub enum ExternalCallableAvailability {
    Source,
    PrecompiledTalkIr,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ResultOwnership {
    Owned,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ResumeRequirement {
    AtMostOnce,
    ExactlyOnce,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum HandlerBehavior {
    Abort,
    Linear,
    Affine,
}
```

`ResultOwnership` intentionally has one v1 case. Keeping it explicit prevents a
future borrowed-result feature from silently appearing as an ordinary `Ty`.

`ScalarIntrinsic` is the one operation identity used by every compiler artifact
and target adapter. Its `signature()` method derives the complete operand and
result signature from the operation; there is no second mapping keyed by source
names or runtime opcodes. `ScalarIntrinsicImplementation` is the complete
serializable implementation of an exported callable only when its whole body is
one validated scalar operation. Parameter indexes refer to the callable
contract; call arguments retain their own selected Copy evidence and are
evaluated once before MIR materializes the operation. Validation rejects wrong
arity or types, captures, concrete effects, type parameters, predicates,
non-owned results, and non-scalar signatures. Character is a borrowed grapheme
view and is not a `ScalarType`.

`CopyEvidence` is the type checker's proof for one Copy edge. `InvalidCopy` is
a use/capture error-recovery mode that preserves unproved explicit Copy syntax;
it carries no proof, produces a frontend diagnostic, never validates for MIR,
and therefore cannot publish `CheckedMir`. `Intrinsic` is limited to the
language's closed scalar set. `PayloadFreeEnum` proves a
non-linear enum has no payload and all arguments are phantom at runtime. `TypeParameter` names an exact predicate in
the owning callable contract. `Conformance` names the selected canonical row,
its exact substitution, and recursively proven Copy context. Tuple and record
proofs follow their canonical element/field order. One shared proof checker is
used with TypedProgram and CheckedMir canonical-item adapters; no downstream
phase performs conformance search.

`ExternalCallable` is target-neutral and stable across compilation sessions.
`Source` means the build may compile the supplying module; `PrecompiledTalkIr`
means it must supply an already verified Talk IR module. Both link by stable
module identity and export name.

`CallableContract::has_no_concrete_effects` recognizes either a closed empty
row or exactly one quantified tail parameter with no concrete entries. The
scalar MIR and Talk IR path may erase the latter only because every concrete
effect operation still rejects during body lowering. Other effect parameters,
row parameters, permission parameters, and concrete entries remain unsupported.

`ItemId::Named` wraps existing cross-module symbols. Conformances and extension
groups need their own identities because the current `Symbol` enum has no cases
for them. The
`ItemStore` validator checks that a named item uses an appropriate symbol case;
for example, a struct item cannot use a local-binding symbol.

### Origins

```rust
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Origin {
    primary: Span,
    source_node: Option<NodeID>,
    related: Vec<RelatedOrigin>,
    reason: OriginReason,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelatedOrigin {
    span: Span,
    role: OriginRole,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum OriginRole {
    OwnerDeclaration,
    BorrowSource,
    ParentBorrow,
    Argument,
    Parameter,
    Capture,
    PriorUse,
    BorrowEnd,
    ConflictingUse,
    HandlerDelimiter,
    SynthesizedFrom,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum OriginReason {
    Source,
    Desugared,
    ValueUse,
    Move,
    Copy,
    BorrowCreation,
    Reborrow,
    BorrowUse,
    BorrowEnd,
    MutableWrite,
    ArgumentTransfer,
    ImplicitClone,
    ClosureCapture,
    HandlerCapture,
    AssignmentReplacement,
    Destroy,
    PatternPayload,
    ScopeCleanup,
    EarlyExitCleanup,
    DiscontinueCleanup,
    GeneratedGlue,
}
```

`source_node` is provenance only. No artifact query accepts a `NodeID` as the
key for a semantic fact. Synthetic operations use the source construct that
caused them as `primary`; `Span::SYNTHESIZED` alone is not sufficient for a
memory operation.

### Callable contracts

```rust
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedEffectRow {
    entries: Vec<CheckedEffectEntry>,
    tail: Option<EffTail>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedEffectEntry {
    effect: EffectEntry,
    resume: Option<ResumeRequirement>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParameterContract {
    binding: BindingId,
    name: String,
    ty: Ty,
    passing: PassingMode,
    mutability: Mutability,
    origin: Origin,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CaptureContract {
    binding: BindingId,
    name: String,
    ty: Ty,
    mode: CaptureMode,
    origin: Origin,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallableContract {
    generic_parameters: Vec<SchemeParam>,
    effect_parameters: Vec<Symbol>,
    row_parameters: Vec<Symbol>,
    permission_parameters: Vec<Symbol>,
    predicates: Vec<Predicate>,
    inputs: Vec<ParameterContract>,
    result: Ty,
    result_ownership: ResultOwnership,
    effects: CheckedEffectRow,
    captures: Vec<CaptureContract>,
}

impl CheckedEffectRow {
    pub fn as_type_row(&self) -> EffectRow;
}

impl CallableContract {
    pub fn as_scheme(&self) -> Scheme;
}
```

`CallableContract` is the only authority for a callable's quantified
parameters, predicates, input and result types, latent effects, ownership
modes, and captures. `as_scheme` and `as_type_row` are derived views used by
type unification and compatibility code; their results are never stored beside
the contract.

A user-handleable `CheckedEffectEntry` has `resume: Some(...)`. A non-handleable
core runtime effect has `resume: None`. Entry order is the stable effect
occurrence identity, including duplicate labels at different instantiations.
Validation requires every user effect to have a resume requirement, every core
effect to omit one, and every capture binding to be unique.

## `TypedProgram`

### Top-level shape

```rust
pub struct TypedProgram {
    module_id: ModuleId,
    files: Vec<TypedFile>,
    items: ItemStore,
    entrypoints: Vec<ItemId>,
    global_initialization_order: Vec<ItemId>,
    source_nodes: Set<NodeID>,
    occurrences: Vec<SemanticOccurrence>,
}

pub enum SemanticTarget {
    Item(ItemId),
    Binding(BindingId),
    TypeParameter(Symbol),
}

pub enum SemanticOccurrenceRole {
    Definition,
    Reference,
    Resolution,
    CallArgumentLabel,
}

pub struct SemanticOccurrence {
    target: SemanticTarget,
    origin: Origin,
    selection: Span,
    role: SemanticOccurrenceRole,
    rename: bool,
}

pub struct TypedFile {
    source: Source,
    file_id: FileID,
    source_len: u32,
    roots: Vec<TypedRoot>,
}

pub enum TypedRoot {
    Import(TypedImport),
    Item(ItemId),
}

pub struct TypedImport {
    path: TypedImportPath,
    selection: TypedImportSelection,
    origin: Origin,
}

pub enum TypedImportPath {
    Local(String),
    Package(String),
}

pub enum TypedImportSelection {
    Named(Vec<ImportedBinding>),
    All(Vec<ImportedBinding>),
}

pub struct ImportedBinding {
    source_name: String,
    local_name: String,
    item: ItemId,
    origin: Origin,
}
```

A file root refers to a canonical item rather than owning another declaration.
A source file containing executable top-level forms receives one synthesized
function item whose role is `FunctionRole::Script`. Import path and selection variants preserve source
syntax. Their bindings carry the resolved `ItemId`s; bindings under `All` are
resolved semantic entries rather than invented source names.

`SemanticOccurrence` is a canonical source-name node, not a side table.
`target` is constrained to an existing item, value binding, or declared type
parameter. `origin` is the exact source token edited by rename; `selection` may
additionally include source punctuation accepted by lookup and must contain the
origin. The private `source_nodes` set proves that occurrence and canonical
source origins came from parser metadata; it contains no semantic resolution.
Roles identify which occurrences must agree with canonical expression, member,
pattern, capture, call, or call-label resolution. The producer deduplicates only
fully identical facts. Validation checks target kind and existence, source-file
identity and bounds, unique definitions, agreement with canonical definition
origins, completeness for source-backed definitions and resolutions, and
conflicting equal-priority overlaps with different targets. Every struct
initializer entry must name a function with `FunctionRole::Initializer`, and
every initializer-role function must have exactly one owning struct.
Initializer call completeness projects through that validated owner to the
struct occurrence. Selections use half-open spans for both overlap validation
and position lookup. Definition and rename consumers query these facts and
never inspect semantic names on the source AST. Any position index is
disposable; occurrences are source-only program facts and are not serialized
into module interfaces.

### Canonical item store

```rust
pub struct ItemStore {
    items: indexmap::IndexMap<ItemId, TypedItem>,
}

pub struct ModuleInterface {
    stable_id: crate::compiling::module::StableModuleId,
    name: String,
    exports: indexmap::IndexMap<String, ItemId>,
    items: ItemStore,
}

pub struct TypedItem {
    name: String,
    visibility: Visibility,
    origin: Origin,
    kind: TypedItemKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Visibility {
    Private,
    Public,
}

pub enum TypedItemKind {
    Function(TypedFunction),
    Struct(TypedStruct),
    Enum(TypedEnum),
    Variant(TypedVariant),
    Property(TypedProperty),
    Protocol(TypedProtocol),
    Requirement(TypedRequirement),
    AssociatedType(TypedAssociatedType),
    Effect(TypedEffect),
    Conformance(TypedConformance),
    Extension(TypedExtension),
    TypeAlias(TypedTypeAlias),
    Global(TypedGlobal),
}
```

There is no second scheme map, catalog, symbol-name map, visibility set, or
child-item map. Relationships below use `ItemId` and validation checks both
ends.

`ModuleInterface` contains the exported, transitively required subset of the
same canonical items. Source function bodies and source initializer expressions
are absent, but contracts and item relationships use the same types and IDs. An
exact `ScalarIntrinsicImplementation` may remain because it is a closed checked
implementation fact rather than retained source body syntax. The
subset includes unnamed conformances and extension groups required to interpret
exported types; it is not only the values in `exports`.

### Callable and nominal items

```rust
pub struct TypedFunction {
    role: FunctionRole,
    contract: CallableContract,
    syntax: Option<FunctionSyntax>,
    implementation: TypedFunctionImplementation,
}

pub enum TypedFunctionImplementation {
    Body(Block),
    GlobalInitializer { global: ItemId },
    GlobalReader { global: ItemId },
    Intrinsic,
    ScalarIntrinsic(ScalarIntrinsicImplementation),
    External(ExternalCallable),
}

pub struct CallableSupplier {
    item: ItemId,
    export: String,
}

pub struct FunctionSyntax {
    generics: Vec<crate::node_kinds::generic_decl::GenericDecl>,
    parameters: Vec<SourceParameter>,
    return_annotation: Option<crate::node_kinds::type_annotation::TypeAnnotation>,
    where_clause: Option<crate::node_kinds::where_clause::WhereClause>,
    effects: crate::node_kinds::func::EffectSet,
    attributes: Vec<crate::node_kinds::attribute::Attribute>,
}

pub enum FunctionRole {
    Free,
    Method,
    Initializer,
    RequirementDefault,
    ConformanceWitness,
    Closure,
    Handler {
        effect: ItemId,
        behavior: HandlerBehavior,
    },
    Script,
    Generated,
}

pub struct TypedStruct {
    grade: Grade,
    representation: NominalRepresentation,
    generic_parameters: Vec<SchemeParam>,
    predicates: Vec<Predicate>,
    properties: Vec<ItemId>,
    methods: Vec<ItemId>,
    initializers: Vec<ItemId>,
}

pub struct TypedEnum {
    grade: Grade,
    generic_parameters: Vec<SchemeParam>,
    predicates: Vec<Predicate>,
    variants: Vec<ItemId>,
    properties: Vec<ItemId>,
    methods: Vec<ItemId>,
}

pub enum NominalRepresentation {
    Value,
    Heap,
}

pub struct TypedVariant {
    tag: u32,
    payloads: Vec<VariantPayload>,
    constructor: CallableContract,
}

pub struct VariantPayload {
    label: Option<String>,
    ty: Ty,
    origin: Origin,
}

pub struct TypedProperty {
    is_static: bool,
    ty: Ty,
    default_value: Option<Expr>,
}

pub struct TypedGlobal {
    scheme: Scheme,
    mutability: Mutability,
    initializer: Option<Expr>,
    initializer_function: Option<ItemId>,
    reader: Option<ItemId>,
}
```

`TypedProgram::global_initialization_order` is the producer-owned declaration
order for every local global with an initializer. Literal globals retain their
canonical expression. Every non-literal global admitted by the current pure scalar MIR subset also
names one private generated zero-parameter function whose `GlobalInitializer`
implementation points back to that global and returns its checked type. The expression remains canonical only on the
global; MIR generation lowers it into the generated function without cloning a
second semantic node into TypedProgram. The producer creates that implementation only when the canonical expression and
selected callees prove a closed pure effect row; other valid frontend globals
remain explicit but fail closed during MIR generation. Validation requires
the order to contain each initialized global exactly once and checks the
generated function's shape.

Each public immutable monomorphic Unit, Bool, Int, or Float global also names
one private generated zero-parameter function whose `GlobalReader`
implementation points back to the same global and returns its exact type. The
validator requires public visibility, immutable storage, the closed scalar
type, matching module identity, no parameters, captures, predicates, or
concrete effects, and an owned exact result. A module interface preserves the
global's `ItemId`, mutability, and `reader`, then erases the local reader to an
exact source-backed `ExternalCallable`. Imported-global reconstruction is a
temporary producer input consumed into `TypedGlobal`; it is not retained as a
side table or passed to the linker.

An imported function has `syntax: None` and ordinarily uses
`TypedFunctionImplementation::External`. Local executable functions use `Body`;
compiler-recognized operations use `Intrinsic`. An exported function whose
complete validated body is one scalar intrinsic instead publishes
`ScalarIntrinsic`, allowing an imported selected implementation to materialize
as MIR intrinsic operations without linkage. `FunctionRole` does not repeat
that implementation choice. Closure, handler, and script roles require `Body`;
a local generated role may use `Body`, `GlobalInitializer`, or `GlobalReader`,
while interface erasure may replace a generated reader with `External`.
External export names must be non-empty.

`TypedProgram::callable_suppliers` is the one derived link plan used by module
interface body erasure and MIR export production. Public callable suppliers use
the public export name. Dependency-reachable generated callables and private
witness implementations use `ItemId::callable_link_name(None)`, producing a
stable name in the reserved `talk-internal:` namespace from the item kind and
module-local identity; session-local `ModuleId` is excluded. A generated global
reader instead uses exactly `talk-global-reader:<public-export>`, tying its ABI
to the exported global's stable identity. Import reconstruction
preserves that exact `ExternalCallable`; Talk IR copies MIR import/export names
without recalculation. Intrinsics never appear in the supplier plan. Parent items' ordered property, variant, method,
initializer, requirement,
associated-type, and extension-member vectors are the authority for ownership
relationships. Child items do not repeat an `owner`; reverse queries scan those vectors or use
a disposable index. Nominal parent vectors contain lexically declared members
only. Extension members live only in `TypedExtension::members`; member lookup
combines both sources as a derived query.

### Protocol, effect, and alias items

```rust
pub struct TypedProtocol {
    generic_parameters: Vec<SchemeParam>,
    parameter_defaults: Vec<Option<Ty>>,
    predicates: Vec<Predicate>,
    supers: Vec<crate::types::ty::ProtocolRef>,
    associated_types: Vec<ItemId>,
    requirements: Vec<ItemId>,
}

pub struct TypedRequirement {
    contract: CallableContract,
    default_implementation: Option<ItemId>,
}

pub struct TypedAssociatedType {
    predicates: Vec<Predicate>,
}

pub struct TypedEffect {
    operation: CallableContract,
}

pub struct TypedConformance {
    generic_parameters: Vec<SchemeParam>,
    self_ty: Ty,
    protocol: crate::types::ty::ProtocolRef,
    context: Vec<Predicate>,
    witnesses: Vec<WitnessBinding>,
    associated_types: Vec<AssociatedTypeBinding>,
}

pub struct WitnessBinding {
    requirement: ItemId,
    implementation: ItemId,
}

pub struct AssociatedTypeBinding {
    associated_type: ItemId,
    ty: Ty,
}

pub struct TypedExtension {
    generic_parameters: Vec<SchemeParam>,
    extended: Ty,
    context: Vec<Predicate>,
    members: Vec<ItemId>,
    conformances: Vec<ConformanceId>,
}

pub struct TypedTypeAlias {
    generic_parameters: Vec<SchemeParam>,
    predicates: Vec<Predicate>,
    aliased: Ty,
}
```

### Required typed-node additions

The contract's owned typed nodes are the function-body representation.
Declarations and closures refer to canonical items rather than owning duplicate
definitions:

```rust
pub enum Node {
    Item(ItemId),
    Let(TypedLet),
    Stmt(Stmt),
    Expr(Expr),
}

pub struct TypedLet {
    pattern: Pattern,
    type_annotation: Option<crate::node_kinds::type_annotation::TypeAnnotation>,
    value: Option<Expr>,
    origin: Origin,
}

pub struct Expr {
    kind: ExprKind,
    origin: Origin,
    ty: Ty,
    disposition: ExprDisposition,
    coercions: ValueCoercions,
}

pub enum Literal {
    Int(i64),
    InvalidInt(String),
    Float(String),
    Bool(bool),
    String(String),
    Character(String),
}

pub struct InlineIr {
    binds: Vec<Expr>,
    operation: CheckedInlineIrOperation,
    origin: Origin,
}

pub enum CheckedInlineIrOperation {
    Scalar {
        operation: ScalarIntrinsic,
        operands: Vec<ScalarIntrinsicOperand>,
    },
    Unsupported,
    InvalidScalar,
}

pub enum ScalarIntrinsicOperand {
    Bind {
        index: u32,
        evidence: CopyEvidence,
    },
    Parameter {
        binding: BindingId,
        evidence: CopyEvidence,
    },
    Int(i64),
    FloatBits(u64),
    Bool(bool),
}

pub enum ResolvedValue {
    Binding(BindingId),
    Item(ItemId),
}

pub struct CallFacts {
    callee: CallableResolution,
    instantiation: Vec<(Symbol, Ty)>,
    arguments: Vec<CheckedArgument>,
}

pub enum CallableResolution {
    Direct(ItemId),
    Witness {
        conformance: ConformanceId,
        requirement: ItemId,
        implementation: ItemId,
    },
    Indirect(CallableContract),
}

pub struct CheckedArgument {
    label: crate::label::Label,
    value: Expr,
    parameter_index: u32,
    origin: Origin,
}
```

For a protocol-static call such as an operator desugaring, type checking retains
the fresh receiver variable until solving completes. Finalization resolves the
canonical protocol application against that solved receiver and publishes the
unique conformance-row witness as `CallableResolution::Witness`. Validation
requires the exact requirement/implementation pair in that conformance. MIR
uses `implementation` directly and never searches the catalog. If the selected implementation is an exact `ScalarIntrinsic`, MIR evaluates the
call arguments once and materializes that recipe directly. Any other selected
implementation that remains generic or external still requires later
specialization/linking or rejects fail closed.

```rust
pub struct SourceParameter {
    binding: BindingId,
    type_annotation: Option<crate::node_kinds::type_annotation::TypeAnnotation>,
    origin: Origin,
}

pub struct Pattern {
    kind: PatternKind,
    ty: Ty,
    origin: Origin,
}

pub enum PatternKind {
    Binding(TypedBinding),
    Variant {
        variant: ItemId,
        fields: Vec<Pattern>,
    },
    Struct {
        structure: ItemId,
        fields: Vec<(ItemId, Pattern)>,
        rest: bool,
    },
    Record {
        fields: Vec<(crate::label::Label, Pattern)>,
        rest: bool,
    },
    Tuple(Vec<Pattern>),
    Or(Vec<Pattern>),
    Literal(Literal),
    Wildcard,
}

pub struct TypedBinding {
    id: BindingId,
    name: String,
    scheme: Scheme,
    mutability: Mutability,
    origin: Origin,
}

pub struct HandlerFacts {
    function: ItemId,
    instantiation: Vec<(Symbol, Ty)>,
}
```

For scalar trusted inline IR, type checking selects `ScalarIntrinsic` from the
checked source annotation and opcode. Canonical construction then resolves
`$N` to `Bind { index: N, evidence }`, `%N` to
`Parameter { binding, evidence }` for the enclosing callable, and scalar
literals to typed constants. Type checking selects `CopyEvidence::Intrinsic`
for every bind or parameter read; constants create values and carry no Copy
proof. Float constants store their exact binary64 bits. The parser instruction,
source `TypeAnnotation`, register spelling, and runtime opcode do not cross the
TypedProgram seam.

Integer literal checking removes `_` separators and parses exactly one signed
64-bit value. A unary minus directly applied to an integer token folds into the
literal before operator lowering, so `-9223372036854775808` is valid without
requiring the positive out-of-range magnitude to exist. Expressions and
patterns publish `Literal::Int(i64)`. Out-of-range source receives
`type.integer-literal-out-of-range`, publishes `InvalidInt` recovery, and cannot
validate for MIR. MIR and Talk IR also carry `i64`, so no backend reparses
integer source text.

`Unsupported` is the fail-closed marker for trusted memory, IO, ownership, and
other operation families that do not yet have an adopted checked vocabulary.
It contains no source instruction that a downstream phase could reinterpret.
`InvalidScalar` is recovery for a selected scalar operation with a malformed
bind, parameter, destination, or constant and cannot validate for MIR. The
validator checks exact arity, result type, bind type, and that every parameter
operand belongs to the enclosing callable contract.

`ExprKind::Variable`, item references, members, projections, constructors, and
patterns carry `ResolvedValue`, `ItemId`, or `BindingId` directly. Binding
patterns own their one `TypedBinding`; aggregate patterns do not cache a second
flattened binder list. A call owns
one `CallFacts`, including its argument expressions; there is no separate
instantiation, argument-mode, or member-resolution map.
`ExprKind::Func` becomes an `ItemId` referring to a canonical closure function.
Nested declarations become `Node::Item`. Source parameter annotations remain
through `SourceParameter`, while their checked type and modes live only in the
owning `CallableContract` input with the same `BindingId`.

A binding's `Scheme` is its one checked type authority; monomorphic bindings
use `Scheme::mono`. Expression occurrences carry the selected instantiation.

Every `UseMode::Copy` owns the `CopyEvidence` for that exact expression type.
Every `CaptureMode::Copy` does the same for the capture type. Constants create
values and do not require evidence unless a later edge copies the resulting
place.

`ExprDisposition::Value` records how an expression result is consumed at its
parent edge. Assignment destinations use the explicit place context instead.
Pattern destinations are patterns, not expressions. A strict linear expression
cannot validate with `UseMode::Discard`.

A checked argument identifies the selected callee parameter. The parameter's
passing mode comes from the one resolved `CallableContract`. The child
expression's value disposition says how that contract is fulfilled: for
example, a consuming parameter may receive `Move`, `Copy`, or `BorrowShared`
followed by a selected CheapClone coercion, depending on the checked type
judgment.

### Typed validation proof

```rust
pub struct ValidatedTypedProgram<'program> {
    program: &'program TypedProgram,
}

impl TypedProgram {
    pub fn validate_for_mir(
        &self,
    ) -> Result<ValidatedTypedProgram<'_>, Vec<TypedProgramInvariant>>;
}

pub enum TypedProgramInvariant {
    MissingItem(ItemId),
    WrongItemKind { item: ItemId, expected: &'static str },
    DuplicateItem(ItemId),
    DuplicateBinding(BindingId),
    ErrorType { origin: Origin },
    UnsolvedType { origin: Origin },
    MissingDisposition { origin: Origin },
    InvalidDisposition { origin: Origin, disposition: ExprDisposition, ty: Ty },
    MissingResolution { origin: Origin },
    InvalidInstantiation { origin: Origin },
    InvalidWitness { origin: Origin },
    InvalidCallableContract { item: ItemId },
    InvalidCopyEvidence { origin: Origin, ty: Ty },
    InvalidCallableImplementation { item: ItemId },
    InvalidHandlerContract { origin: Origin },
    MissingSemanticOccurrenceTarget { origin: Origin, target: SemanticTarget },
    InvalidSemanticOccurrenceOrigin { origin: Origin },
    InvalidSemanticOccurrenceResolution { origin: Origin, target: SemanticTarget },
    DuplicateSemanticOccurrenceSelection { origin: Origin },
    DuplicateSemanticDefinition { target: SemanticTarget },
    InvalidSemanticDefinition { origin: Origin, target: SemanticTarget },
    InvalidEntrypoint(ItemId),
}
```

`ValidatedTypedProgram` is a proof view, not another semantic artifact. It adds
no fields and cannot outlive its program. MIR generation accepts this view so
its precondition is visible in the Rust interface.

## `CheckedMir`

### Identity and top-level shape

```rust
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MirFunctionId(u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BlockId(u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LocalId(u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LoanId(u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DropFlagId(u32);

pub struct CheckedMir {
    items: MirItemStore,
    functions: Vec<MirFunction>,
    entrypoints: Vec<MirFunctionId>,
    exports: Vec<MirExport>,
}

pub struct MirItemStore {
    items: indexmap::IndexMap<ItemId, MirItem>,
}

pub struct MirItem {
    name: String,
    visibility: Visibility,
    origin: Origin,
    kind: MirItemKind,
}

pub enum MirItemKind {
    Function(MirCallable),
    Struct(MirStruct),
    Enum(MirEnum),
    Variant(MirVariant),
    Property(MirProperty),
    Protocol(MirProtocol),
    Requirement(MirRequirement),
    AssociatedType(MirAssociatedType),
    Effect(MirEffect),
    Conformance(MirConformance),
    Extension(MirExtension),
    TypeAlias(Ty),
    Global(MirGlobal),
}

pub struct MirCallable {
    contract: CallableContract,
    implementation: MirCallableImplementation,
}

pub enum MirCallableImplementation {
    Defined(MirFunctionId),
    Intrinsic,
    External(ExternalCallable),
}

pub struct MirStruct {
    grade: Grade,
    representation: NominalRepresentation,
    generic_parameters: Vec<SchemeParam>,
    predicates: Vec<Predicate>,
    properties: Vec<ItemId>,
    methods: Vec<ItemId>,
    initializers: Vec<ItemId>,
}

pub struct MirEnum {
    grade: Grade,
    generic_parameters: Vec<SchemeParam>,
    predicates: Vec<Predicate>,
    variants: Vec<ItemId>,
    properties: Vec<ItemId>,
    methods: Vec<ItemId>,
}

pub struct MirVariant {
    tag: u32,
    payloads: Vec<Ty>,
    constructor: CallableContract,
}

pub struct MirProperty {
    is_static: bool,
    ty: Ty,
}

pub struct MirProtocol {
    generic_parameters: Vec<SchemeParam>,
    parameter_defaults: Vec<Option<Ty>>,
    predicates: Vec<Predicate>,
    supers: Vec<crate::types::ty::ProtocolRef>,
    associated_types: Vec<ItemId>,
    requirements: Vec<ItemId>,
}

pub struct MirRequirement {
    contract: CallableContract,
    default_implementation: Option<ItemId>,
}

pub struct MirAssociatedType {
    predicates: Vec<Predicate>,
}

pub struct MirEffect {
    operation: CallableContract,
}

pub struct MirConformance {
    generic_parameters: Vec<SchemeParam>,
    self_ty: Ty,
    protocol: crate::types::ty::ProtocolRef,
    context: Vec<Predicate>,
    witnesses: Vec<(ItemId, ItemId)>,
    associated_types: Vec<AssociatedTypeBinding>,
}

pub struct MirExtension {
    generic_parameters: Vec<SchemeParam>,
    extended: Ty,
    context: Vec<Predicate>,
    members: Vec<ItemId>,
    conformances: Vec<ConformanceId>,
}

pub struct MirGlobal {
    scheme: Scheme,
    mutability: Mutability,
    initializer: Option<MirGlobalInitializer>,
    initialization_index: Option<u32>,
}

pub enum MirGlobalInitializer {
    Constant(Constant),
    Function(MirFunctionId),
}

pub struct MirExport {
    name: String,
    item: ItemId,
}
```

Callable `MirExport::name` comes only from
`TypedProgram::callable_suppliers`; global export names come from the same
canonical program export map. MIR does not derive either from display names.
The verifier requires a unique non-empty link name and a locally defined
callable or global supplier for every export. Consumer generation represents an
imported global read only as a call to its exact external reader; the MIR
verifier rejects an external static place that bypasses that reader. Constant
initializers must match
the global type; function initializers must be defined, zero-parameter,
zero-capture, pure, and return that type. Initialization indexes are dense and
unique. Talk IR lowering preserves the same export name and order.

The MIR item records contain the canonical type, effect, witness, field, and
variant relationships needed by lowering. They have no typed AST bodies or
source default expressions. Callable item references resolve to `ItemId`; `MirCallableImplementation`
identifies whether that item has a local `MirFunctionId`, is intrinsic, or links
to an external module. The callable contract lives exactly once on
`MirCallable`. As in `TypedProgram`, ordered
parent vectors are the ownership authority; child item records do not duplicate
an owner reference.

### Functions and locals

```rust
pub struct MirFunction {
    item: ItemId,
    debug_name: String,
    locals: Vec<LocalDecl>,
    drop_flags: Vec<DropFlagDecl>,
    blocks: Vec<BasicBlock>,
    entry: BlockId,
    origin: Origin,
}

pub struct LocalDecl {
    storage: LocalStorage,
    origin: Origin,
}

pub enum LocalStorage {
    Parameter {
        contract_index: u32,
        incoming_loan: Option<LoanId>,
    },
    Capture {
        contract_index: u32,
        incoming_loan: Option<LoanId>,
    },
    Binding {
        binding: BindingId,
        ty: Ty,
        mutability: Mutability,
    },
    Temporary {
        ty: Ty,
        mutability: Mutability,
    },
    Return {
        ty: Ty,
    },
    Resumption {
        ty: Ty,
    },
}

pub struct DropFlagDecl {
    place: Place,
    origin: Origin,
}

pub struct BasicBlock {
    statements: Vec<Statement>,
    terminator: Terminator,
    origin: Origin,
}
```

IDs are dense indexes into their owning vectors. A verifier rejects every
out-of-range or wrong-owner reference; entries do not repeat their own index.
IDs never cross functions except `MirFunctionId`. `debug_name` is printer
metadata and is never used for lookup, linking, or dispatch.

`MirFunction::item` refers to a `MirCallable` whose implementation is
`Defined` with this function's ID. The function does not duplicate its callable
contract.

Parameter and capture locals refer to their `MirCallable::contract` entries
instead of copying type, mode, or mutability. Their local origin describes MIR
storage; the contract origin describes the source parameter or capture. Other local
kinds own their type and mutability. A local's grade is derived from its
canonical type and the MIR item store; it is not stored as a second ownership
judgment.

### Places, operands, and constants

```rust
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Place {
    root: PlaceRoot,
    projections: Vec<Projection>,
}

pub struct PlaceAccess {
    place: Place,
    through_loan: Option<LoanId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PlaceRoot {
    Local(LocalId),
    Static(ItemId),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Projection {
    Field(ItemId),
    VariantPayload { variant: ItemId, index: u32 },
    Dereference,
    Index(LocalId),
}

pub struct Operand {
    kind: OperandKind,
    origin: Origin,
}

pub enum OperandKind {
    Constant { value: Constant, ty: Ty },
    Copy { place: Place, evidence: CopyEvidence },
    Move(Place),
    Borrowed { place: Place, loan: LoanId },
    Function(ItemId),
}

pub enum Constant {
    Unit,
    Bool(bool),
    Int(i64),
    Float(String),
    String(String),
    Character(String),
}
```

Int constants are canonical signed 64-bit values; no downstream phase parses
integer text. Float text remains until its separate canonical constant contract
lands. Constant operands carry the checked type explicitly; all other
operand and place types derive from local contracts, item definitions,
projections, and loan definitions. A Move is an operand because evaluation
consumes its source at that exact ordered position. The verifier applies its
deinitialization effect when visiting the operand. A Copy operand carries its
selected proof; the verifier checks the proof against the place type and never
searches for a conformance.

### Borrow definitions and provenance edges

```rust
pub enum BorrowSource {
    Place(Place),
    Reborrow { parent: LoanId, place: Place },
}

pub struct LoanTransfer {
    loan: LoanId,
    callee_parameter: u32,
    origin: Origin,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BorrowEventId(u32);

pub enum BorrowSubject {
    Loan { function: MirFunctionId, loan: LoanId },
    Parameter { callable: ItemId, parameter: u32 },
    Capture { callable: ItemId, capture: u32 },
}

pub enum BorrowEventLocation {
    ContractParameter { callable: ItemId, parameter: u32 },
    ContractCapture { callable: ItemId, capture: u32 },
    Local { function: MirFunctionId, local: LocalId },
    Statement { function: MirFunctionId, block: BlockId, statement: u32 },
    Terminator { function: MirFunctionId, block: BlockId },
}

pub struct BorrowProvenance {
    events: Vec<BorrowEvent>,
    edges: Vec<BorrowEdge>,
}

pub struct BorrowEvent {
    location: BorrowEventLocation,
    kind: BorrowEventKind,
    origin: Origin,
}

pub enum BorrowEventKind {
    Owner {
        binding: Option<BindingId>,
        name: String,
        ty: Ty,
    },
    Move { place: Place },
    Begin { subject: BorrowSubject, permission: BorrowPermission },
    Reborrow { subject: BorrowSubject, parent: BorrowSubject },
    Projection { subject: BorrowSubject, name: String, item: Option<ItemId> },
    Argument { subject: BorrowSubject, callable: ItemId, parameter: u32 },
    Parameter { subject: BorrowSubject, parameter: u32 },
    Capture { subject: BorrowSubject, capture: u32 },
    Use { subject: BorrowSubject },
    End { subject: BorrowSubject },
    Conflict { subject: BorrowSubject, operation: BorrowConflict },
}

pub struct BorrowEdge {
    from: BorrowEventId,
    to: BorrowEventId,
    relation: BorrowRelation,
}

pub enum BorrowRelation {
    DerivedFrom,
    PassedTo,
    CapturedBy,
    KeptLiveBy,
    EndsAt,
    ConflictsWith,
}

pub enum BorrowConflict {
    Move,
    Write,
    BorrowShared,
    BorrowMut,
    Destroy,
    Escape,
    Suspension,
}

pub struct BorrowProvenanceQuery {
    subject: BorrowSubject,
}

pub struct BorrowProvenanceResult {
    subject: BorrowSubject,
    focus: Vec<BorrowEventId>,
    provenance: BorrowProvenance,
}

pub struct OwnershipDiagnostic {
    kind: OwnershipDiagnosticKind,
    primary: Origin,
    focus: Vec<BorrowEventId>,
    provenance: BorrowProvenance,
}

pub enum OwnershipDiagnosticKind {
    UninitializedRead { place: Place },
    UseAfterMove { place: Place },
    BorrowConflict { subject: BorrowSubject, operation: BorrowConflict },
    BorrowEscapes { subject: BorrowSubject },
    BorrowCrossesSuspension { subject: BorrowSubject },
    IncompleteCleanup { place: Place },
    ImmutableOverwrite { place: Place },
    LinearValueNotConsumed { place: Place },
    ResumptionNotConsumed,
}
```

A `LoanId` is defined exactly once by either a borrowed parameter or capture
`LocalStorage` entry or `StatementKind::BeginBorrow`. Borrowed operands and loan
transfers are use/provenance edges. `EndBorrow` operations are ending edges. No
detached `LoanId -> BorrowFacts` map exists.

For valid MIR, `BorrowProvenance` is derived by traversing the structural events
above; it is not stored in `CheckedMir`. A query uses a globally unambiguous
concrete or abstract `BorrowSubject`. Its result contains the complete connected
graph and the focused events. An LSP source-position index may cache origin to
subject/location mappings but is disposable.

When MIR generation rejects source code and therefore cannot publish
`CheckedMir`, `OwnershipDiagnostic` carries the failed transition as `primary`,
the graph events representing that transition as `focus`, and the relevant
partial `BorrowProvenance`. Related origins and their roles are derived from all
non-focus graph events. Non-borrow ownership diagnostics use `Owner` and `Move`
events for declaration and prior-move causes instead of storing a second list
of related spans. The diagnostic graph is the error result, not a
competing answer beside valid MIR. Non-borrow ownership diagnostics may have an
empty graph; rejected borrow diagnostics may not.

### Statements and rvalues

```rust
pub struct Statement {
    kind: StatementKind,
    origin: Origin,
}

pub enum StatementKind {
    StorageLive(LocalId),
    StorageDead(LocalId),
    Initialize {
        destination: PlaceAccess,
        value: Rvalue,
    },
    BeginBorrow {
        destination: Place,
        loan: LoanId,
        permission: BorrowPermission,
        source: BorrowSource,
    },
    EndBorrow(LoanId),
    Destroy {
        place: PlaceAccess,
        reason: DestroyReason,
    },
    SetDropFlag {
        flag: DropFlagId,
        value: bool,
    },
    DestroyIfLive {
        flag: DropFlagId,
        place: PlaceAccess,
        reason: DestroyReason,
    },
    InstallHandler(HandlerInstallation),
    RemoveHandler {
        handler: HandlerId,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BorrowPermission {
    Shared,
    Mutable,
}

pub enum DestroyReason {
    Discard,
    AssignmentReplacement,
    ScopeExit,
    EarlyExit,
    Discontinue,
    PatternRemainder,
}

pub enum Rvalue {
    Use(Operand),
    SelectedClone {
        source: Operand,
        witness: Option<ItemId>,
    },
    Aggregate {
        item: ItemId,
        variant: Option<ItemId>,
        fields: Vec<Operand>,
    },
    Discriminant(Place),
    Closure {
        function: MirFunctionId,
        captures: Vec<MirCaptureOperand>,
    },
    Intrinsic {
        operation: ScalarIntrinsic,
        operands: Vec<Operand>,
    },
}

pub struct MirCaptureOperand {
    capture: u32,
    value: Operand,
    loan: Option<LoanId>,
    origin: Origin,
}
```

Scalar inline-IR binds lower once in source order into explicit temporaries.
`Bind` and `Parameter` operands become MIR Copy operands carrying the exact
TypedProgram evidence; MIR performs no Copy selection. Constants remain
constant operands. The intrinsic result initializes an explicit scalar
temporary. The verifier derives the one signature from `ScalarIntrinsic`,
checks arity and every operand/result type, and verifies every preserved Copy
proof. Deferred `Unsupported` inline IR rejects before any partial MIR artifact
is published.

`PlaceAccess::through_loan` makes every write or replacement through a mutable
borrow part of that loan's provenance. It is `None` for directly owned storage.

`StorageDead` never destroys a value. All destruction appears as `Destroy` or
`DestroyIfLive`. Assignment has no MIR operation: the builder emits right-hand
side evaluation, destination destruction, and destination initialization in
that order. The verifier tracks whether each local has already been initialized
within its current `StorageLive` lifetime. Immutable storage cannot be
initialized again after Move or Destroy, regardless of the destroy reason.

### Calls, effects, and terminators

```rust
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct HandlerId(u32);

pub struct HandlerInstallation {
    id: HandlerId,
    effect: ItemId,
    instantiation: Vec<(Symbol, Ty)>,
    function: MirFunctionId,
    behavior: HandlerBehavior,
    captures: Vec<MirCaptureOperand>,
    delimiter: BlockId,
}

pub struct Terminator {
    kind: TerminatorKind,
    origin: Origin,
}

pub enum TerminatorKind {
    Goto(BlockId),
    Branch {
        condition: Operand,
        then_block: BlockId,
        else_block: BlockId,
    },
    Switch {
        discriminant: Operand,
        cases: Vec<SwitchCase>,
        fallback: BlockId,
    },
    Call {
        callee: Callee,
        arguments: Vec<MirCallArgument>,
        destination: Option<Place>,
        normal: BlockId,
        discontinue: Option<BlockId>,
    },
    Perform {
        effect: ItemId,
        instantiation: Vec<(Symbol, Ty)>,
        arguments: Vec<Operand>,
        destination: Place,
        normal: BlockId,
        discontinue: BlockId,
    },
    Return(Option<Operand>),
    Resume {
        resumption: Operand,
        value: Operand,
    },
    Discontinue {
        resumption: Operand,
        value: Operand,
    },
    Unreachable,
}

pub struct SwitchCase {
    value: Constant,
    target: BlockId,
}

pub enum Callee {
    Direct {
        callable: ItemId,
        type_arguments: Vec<Ty>,
        witnesses: Vec<WitnessArgument>,
    },
    Witness {
        conformance: ConformanceId,
        requirement: ItemId,
        implementation: ItemId,
        type_arguments: Vec<Ty>,
    },
    Indirect {
        operand: Operand,
        contract: CallableContract,
    },
}

pub struct WitnessArgument {
    conformance: ConformanceId,
    type_arguments: Vec<Ty>,
}

pub struct MirCallArgument {
    parameter: u32,
    value: Operand,
    loan_transfer: Option<LoanTransfer>,
    origin: Origin,
}
```

Call and Perform destinations are directly owned uninitialized storage. A
source assignment through a mutable borrow first receives the call result in a
temporary, then performs the explicit borrowed replacement through
`PlaceAccess`.

Direct and witness-selected callees use canonical callable items. Verification
reads the one contract on `MirCallable`, whether its implementation is defined,
intrinsic, or external. Closure and handler bodies still use `MirFunctionId`
because those operations require an in-module CFG body.

A user-effect-capable call has a `discontinue` successor even when its normal
successor is statically known. Core runtime effects that cannot discontinue do
not require one. The verifier checks this against the callee's checked effect
contract.

A shared loan captured by a handler begins before `InstallHandler`, remains
active for the complete balanced installation extent, and ends after
`RemoveHandler` on every normal or discontinue cleanup path.

`Resume` and `Discontinue` have no successor in the current handler function.
Both consume the one-shot resumption. Their value goes to the suspended normal
successor or handler delimiter respectively.

### MIR verification seam

```rust
#[cfg(test)]
pub(crate) struct MirCandidate {
    items: MirItemStore,
    functions: Vec<MirFunction>,
    entrypoints: Vec<MirFunctionId>,
    exports: Vec<MirExport>,
}

impl MirCandidate {
    pub(crate) fn verify(self) -> Result<CheckedMir, Vec<MirInvariant>>;
}

pub enum MirInvariant {
    InvalidId { function: Option<MirFunctionId>, detail: String },
    InvalidCfg { function: MirFunctionId, detail: String },
    TypeMismatch { origin: Origin, expected: Ty, found: Ty },
    UninitializedRead { place: Place, origin: Origin },
    InvalidMove { place: Place, origin: Origin },
    InvalidCopy { ty: Ty, origin: Origin },
    InvalidCopyEvidence { ty: Ty, origin: Origin },
    InvalidIntrinsic {
        origin: Origin,
        operation: ScalarIntrinsic,
        detail: String,
    },
    MissingClone { origin: Origin },
    InvalidLoan { loan: LoanId, origin: Origin, detail: String },
    BrokenBorrowProvenance { loan: LoanId, origin: Origin },
    BorrowCrossesSuspension { loan: LoanId, origin: Origin },
    IncompleteCleanup { place: Place, origin: Origin },
    LinearValueNotConsumed { place: Place, origin: Origin },
    ResumptionNotConsumed { origin: Origin },
    HandlerContractMismatch { handler: HandlerId, origin: Origin },
    MissingOrigin { detail: String },
}
```

Only the MIR-generation module can name `MirCandidate`. Production lowering can
only receive `CheckedMir`. Tests construct candidates through a fixture builder
that calls `verify` and fails the test with the deterministic MIR printer.

## `TalkIrModule`

Talk IR is monomorphic, closure-converted, target-neutral, and CFG-based. This
draft uses SSA values with block parameters plus explicit memory operations.
That is direct style, not CPS: ordinary calls and effects remain terminators
with explicit successors.

### Identity, types, and module shape

```rust
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct IrTypeId(u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct IrSignatureId(u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct IrEffectId(u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct IrFunctionId(u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct IrImportId(u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct IrGlobalId(u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct IrBlockId(u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ValueId(u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct StackSlotId(u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct IrHandlerId(u32);

pub struct TalkIrModule {
    types: Vec<IrTypeDefinition>,
    signatures: Vec<IrSignature>,
    effects: Vec<IrEffect>,
    functions: Vec<IrFunction>,
    globals: Vec<IrGlobal>,
    imports: Vec<IrImport>,
    exports: Vec<IrExport>,
    initializers: Vec<IrInitializer>,
    entrypoints: Vec<IrFunctionId>,
}

pub enum IrType {
    Unit,
    Never,
    Bool,
    Byte,
    Character,
    Int,
    Float,
    Aggregate(IrTypeId),
    Reference(IrTypeId),
    Address(Box<IrType>),
    Function(IrSignatureId),
    Continuation(IrSignatureId),
}

pub struct IrTypeDefinition {
    name: String,
    kind: IrTypeDefinitionKind,
}

pub enum IrTypeDefinitionKind {
    Struct { fields: Vec<IrField> },
    Enum { variants: Vec<IrVariant> },
    HeapObject { fields: Vec<IrField> },
    Opaque,
}

pub struct IrField {
    name: String,
    ty: IrType,
}

pub struct IrVariant {
    name: String,
    tag: u32,
    fields: Vec<IrField>,
}

pub struct IrSignature {
    parameters: Vec<IrType>,
    result: IrType,
    may_discontinue: bool,
}

pub struct IrEffect {
    link_name: String,
    operation: IrSignatureId,
}
```

Type, signature, effect, function, import, and global IDs are dense indexes into
the corresponding `TalkIrModule` vectors. Blocks, values, stack slots, and
handler installations are dense or unique within one function. Entries do not
repeat their vector index as a stored ID.

`Int`, addresses, and aggregate layout remain target-neutral. A backend chooses
pointer width, ABI, alignment, and concrete enum layout from the target
configuration. An `Address` is an internal storage address, not a source borrow.

### Functions and blocks

```rust
pub struct IrFunction {
    name: String,
    signature: IrSignatureId,
    stack_slots: Vec<StackSlot>,
    blocks: Vec<IrBlock>,
    entry: IrBlockId,
    origin: Origin,
}

pub struct StackSlot {
    ty: IrType,
    origin: Origin,
}

pub struct IrBlock {
    parameters: Vec<BlockParameter>,
    instructions: Vec<Instruction>,
    terminator: IrTerminator,
    origin: Origin,
}

pub struct BlockParameter {
    value: ValueId,
    ty: IrType,
}

pub struct Instruction {
    result: Option<ValueId>,
    kind: InstructionKind,
    origin: Origin,
}
```

An instruction defines at most one SSA value. Its type derives from the
instruction kind, referenced definitions, and operand types; a separate
`ValueId -> IrType` table is not part of the artifact.

### Instructions

```rust
pub enum InstructionKind {
    Constant(IrConstant),
    Aggregate {
        ty: IrTypeId,
        variant: Option<u32>,
        fields: Vec<ValueId>,
    },
    Project {
        aggregate: ValueId,
        field: u32,
    },
    Discriminant(ValueId),
    AddressOfSlot(StackSlotId),
    AddressOfGlobal(IrGlobalId),
    Load {
        address: ValueId,
    },
    Store {
        address: ValueId,
        value: ValueId,
    },
    Allocate {
        ty: IrTypeId,
    },
    Deallocate {
        address: ValueId,
        ty: IrTypeId,
    },
    MakeClosure {
        function: IrFunctionId,
        environment: ValueId,
    },
    InstallHandler {
        handler: IrHandlerId,
        effect: IrEffectId,
        function: IrFunctionId,
        environment: ValueId,
        delimiter: IrBlockId,
    },
    RemoveHandler {
        handler: IrHandlerId,
    },
    Intrinsic {
        operation: ScalarIntrinsic,
        operands: Vec<ValueId>,
    },
}

pub enum IrConstant {
    Unit,
    Bool(bool),
    Byte(u8),
    Character(u32),
    Int(i64),
    Float(String),
    String { value: String, ty: IrTypeId },
    Function(IrFunctionId),
    Import(IrImportId),
}
```

MIR scalar intrinsics lower to the identical `ScalarIntrinsic` and ordered SSA
operand values. MIR Copy evidence ends after MIR verification and has no Talk
IR field or shadow metadata. The Talk IR verifier derives result and operand
types only from `ScalarIntrinsic::signature()`, rejects wrong arity or value
types, and requires every operand value to be defined before the instruction.

Clone, destroy, and deinit are ordinary calls to generated monomorphic glue
functions. They are therefore explicit in the CFG without requiring each
backend to rediscover type-specific ownership behavior. `Allocate` and
`Deallocate` are common Talk operations implemented by each target adapter.

### Terminators

```rust
pub struct IrTerminator {
    kind: IrTerminatorKind,
    origin: Origin,
}

pub enum IrTerminatorKind {
    Goto {
        target: IrBlockId,
        arguments: Vec<ValueId>,
    },
    Branch {
        condition: ValueId,
        then_target: IrEdge,
        else_target: IrEdge,
    },
    Switch {
        discriminant: ValueId,
        cases: Vec<IrSwitchCase>,
        fallback: IrEdge,
    },
    Call {
        callee: IrCallee,
        arguments: Vec<ValueId>,
        normal: IrEdge,
        discontinue: Option<IrEdge>,
    },
    Perform {
        effect: IrEffectId,
        arguments: Vec<ValueId>,
        normal: IrEdge,
        discontinue: IrEdge,
    },
    Return(Option<ValueId>),
    Resume {
        resumption: ValueId,
        value: ValueId,
    },
    Discontinue {
        resumption: ValueId,
        value: ValueId,
    },
    Unreachable,
}

pub struct IrEdge {
    block: IrBlockId,
    arguments: Vec<IrEdgeArgument>,
}

pub enum IrEdgeArgument {
    Value(ValueId),
    TerminatorResult,
}

pub struct IrSwitchCase {
    value: IrConstant,
    target: IrEdge,
}

pub enum IrCallee {
    Direct(IrFunctionId),
    Import(IrImportId),
    Indirect(ValueId),
}
```

`TerminatorResult` binds the result of Call or Perform to a normal successor's
block parameter without inventing a value that is available before the
terminator executes. It is invalid on branch, switch, discontinue, and ordinary
Goto edges.

Talk IR contains no generic calls, witnesses, source places, source loans,
source drop flags, patterns, or checked ownership modes. All such semantics
have already become monomorphic values, storage operations, calls, and CFG
edges.

### Imports, globals, exports, and verification

```rust
pub struct IrGlobal {
    name: String,
    ty: IrType,
    mutability: Mutability,
    initializer: Option<IrConstant>,
}

pub enum IrInitializer {
    Global(IrGlobalId),
    Function(IrFunctionId),
    GlobalFunction {
        function: IrFunctionId,
        global: IrGlobalId,
    },
}

pub struct IrImport {
    module: crate::compiling::module::StableModuleId,
    export: String,
    signature: IrSignatureId,
}

pub struct IrExport {
    name: String,
    target: IrExportTarget,
}

pub enum IrExportTarget {
    Function(IrFunctionId),
    Global(IrGlobalId),
}

#[cfg(test)]
pub(crate) struct TalkIrCandidate {
    // Same fields as TalkIrModule.
}

impl TalkIrCandidate {
    pub(crate) fn verify(self) -> Result<TalkIrModule, Vec<TalkIrInvariant>>;
}

pub enum TalkIrInvariant {
    InvalidId { detail: String },
    InvalidCfg { function: IrFunctionId, detail: String },
    TypeMismatch { origin: Origin, detail: String },
    InvalidEdgeArguments { origin: Origin },
    InvalidCall { origin: Origin },
    InvalidIntrinsic {
        function: IrFunctionId,
        origin: Origin,
        operation: ScalarIntrinsic,
        detail: String,
    },
    InvalidEffectControl { origin: Origin },
    NonMonomorphicType { origin: Origin },
    MissingDefinition { detail: String },
    MissingOrigin { detail: String },
    InvalidGlobalInitialization {
        function: Option<IrFunctionId>,
        global: Option<IrGlobalId>,
        detail: String,
    },
}
```

`IrImport::module` is the stable module identity from `ExternalCallable`; the
name is its exported link name, and the signature is the monomorphic
compatibility contract. Human-readable module names are not linker keys.

Only the MIR-to-Talk-IR lowerer and the verified Talk IR linker can construct
`TalkIrCandidate`. Constant global actions initialize their matching
`IrGlobal::initializer`; `GlobalFunction` actions call a zero-parameter
non-discontinuing function and store its exact scalar result. Verification
requires unique valid actions, complete scheduling of constant initializers,
valid initializer signatures, initialized reads through the transitive direct
call graph, no recursive initializer calls, and no repeated immutable writes.

The scalar linker consumes `(StableModuleId, TalkIrModule)` inputs plus one root
module ID. It resolves each callable import against exactly one function export
with the same stable module ID, export name, and scalar signature; remaps
function, signature, and global identities; rewrites imported references to
direct references; retains root exports and entrypoints; and re-runs Talk IR
verification. Initializer-reachable imports create supplier-before-consumer
ordering edges. Stable module IDs break unrelated ties, and an exact dependency
cycle rejects. Missing readers or suppliers, duplicate module IDs,
incompatible signatures, direct external-global Talk IR forms, aggregate
types, effects, and non-scalar storage reject. Target adapters receive only the resulting verified
`TalkIrModule` plus target configuration.

## E1 validated bytecode target seam

The first bytecode target profile crosses the runtime seam only as:

```rust
pub struct ValidatedBytecodeModule {
    module: talk_runtime::Module, // private after construction
}

impl ValidatedBytecodeModule {
    pub fn new(module: Module) -> Result<Self, ScalarBytecodeError>;
    pub fn render(&self) -> String;
    pub fn run(&self, io: &mut dyn IO) -> Result<Value, String>;
    pub fn run_counted(
        &self,
        io: &mut dyn IO,
    ) -> Result<(Value, RunBalance), String>;
}
```

Validation admits scalar constants, typed scalar global descriptors, and
`Const`, `Move`, `GlobalGet`, `GlobalSet`, scalar arithmetic, comparison and
conversion, direct `Call`, `Jump`, `Branch`, `Switch`, `Ret`, and `Trap`. It
rejects statics, unwind metadata, every legacy operation family, invalid
entries, calls, registers, globals, constants, pools and control targets, pool
data not claimed by an instruction, and reachable chunk fallthrough. Runtime
global slots start uninitialized; reads before initialization, scalar kind
mismatches, and repeated writes to immutable slots trap with errors. The entry
chunk has arity zero. The raw module remains available only for quarantined
legacy runtime tests; the compiler adapter produces the validated wrapper.
Runtime kind checks remain defense in depth and return an error rather than
panicking.

The adapter seam is:

```rust
bytecode::compile(
    module: &TalkIrModule,
    entry: IrFunctionId,
) -> Result<ValidatedBytecodeModule, BytecodeLoweringError>;
```

The selected entry must be a published entrypoint or function export and have
zero parameters. The adapter preflights the whole module before emission and rejects unlinked
imports, non-scalar globals, effects, aggregate definitions, Character,
indirect or discontinuing calls, and every instruction or terminator outside
the scalar profile. It assigns SSA values and scalar stack slots to disjoint registers, treats slot
`AddressOfSlot`/`Load`/`Store` as target-local moves, lowers global addresses to
dedicated gets and sets, places direct-call arguments in the runtime pool, and
lowers call results through the normal edge. If the module has initializer
actions, the adapter appends a private entry wrapper that executes them in
verified order exactly once before calling the selected entry. Bytecode format
version 3 serializes global descriptors and the two global opcodes; it makes no
compatibility promise for version-2 images.
Block parameters use edge-local parallel copies with a dedicated cycle-breaking
temporary. Branch edges receive adapter labels; arbitrary literal switches
lower to ordered equality branches rather than assuming dense tags. Reachable
`Unreachable` emits a deterministic trap. Unit returns materialize runtime
Void. The resulting raw module must pass `ValidatedBytecodeModule::new`; there
is no unchecked compiler execution path.

The public driver wraps that proof as `ScalarExecutable`. Its `run` method uses
counted runtime execution, rejects any nonzero allocation/object balance, and
returns only optional Talk-syntax result text. Unit maps to no final-result line;
Bool, Byte, Int, and Float never expose runtime enum names. Entry selection is
explicit by exported name or deterministic (one published entrypoint, `main`,
or one unambiguous zero-parameter export); ambiguity and parameterized entries
reject. The CLI and embedding seam use this wrapper rather than raw runtime
modules.

## Phase outcomes

Diagnostics are an envelope around an optional artifact, not part of the next
artifact's semantic input:

```rust
pub struct PhaseOutcome<T, D = crate::diagnostic::AnyDiagnostic> {
    artifact: Option<T>,
    diagnostics: Vec<D>,
}
```

Type checking normally supplies a recovery `TypedProgram` even with errors.
`validate_for_mir` rejects it. MIR generation supplies `CheckedMir` only after typed
`OwnershipDiagnostic`s are absent and verification succeeds. Lowering either
supplies verified `TalkIrModule` or reports an internal compiler error.

## Test-only construction

Each artifact module owns a `#[cfg(test)] fixtures` child module. Fixture
builders:

- require every semantic field rather than filling hidden defaults;
- call the production validator or verifier;
- include the artifact printer in failure output;
- are inaccessible to non-test production code;
- never convert `TypeOutput`, `ResolvedNames`, liveness, or drop side tables
  directly into a downstream fixture.

The first fixture set is deliberately small:

1. one Copy-only `TypedProgram` with a direct `main`;
2. its branch and loop variants;
3. one `CheckedMir` direct-return function;
4. one bodyless external callable preserved through CheckedMir;
5. one rejected invalid Copy-evidence proof;
6. one complete shared-borrow provenance result shape;
7. one target-neutral Talk IR direct-return function.

## Stage 0 acceptance for this draft

Before these types become the shared implementation seam, review must confirm:

- `ItemId` covers every canonical declaration, including conformances and
  extension groups;
- callable effect occurrences have stable identities for control requirements;
- every borrow provenance edge is structural in MIR;
- the handler installation/delimiter representation is sufficient for deep
  dynamic handlers and discontinue cleanup;
- the lowerer can monomorphize using only `CheckedMir`;
- Talk IR uses only its own dense type, signature, effect, function, import,
  global, block, value, slot, and handler identities;
- Talk IR's SSA block-parameter form and `TerminatorResult` edge binding are
  acceptable to bytecode, WebAssembly, C, and future native adapters;
- no field asks a consumer to consult an older artifact;
- no two fields independently answer the same semantic question.

The shared vocabulary and dormant MIR/Talk IR artifact modules are implemented.
The type checker now consumes its temporary `TypeOutput` and `ResolvedNames`
state into the canonical `TypedProgram`, module interfaces and frontend/editor
queries consume canonical items and typed nodes, and clean producer artifacts
pass `validate_for_mir`. MIR and Talk IR remain disconnected from the driver.
