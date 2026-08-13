# Compiler phase primitives

Verified against commit `902c3fc7` on 2026-08-13.

This document describes the compiler that exists in the current tree. ADRs explain
why it has this shape; this document records the concrete primitives each phase
consumes, owns while running, and exports. Historical pipelines such as HIR,
Lambda-G, and the pre-reset backend are intentionally omitted.

Here, **primitive** means any fact or carrier a phase must understand to do its
work:

- artifact types crossing a phase seam;
- identities and references used inside those artifacts;
- semantic evidence produced by one phase for another;
- private worklists, indexes, and side tables used while constructing an artifact;
- diagnostics and trust assumptions attached to a seam.

A primitive is not necessarily a Rust primitive type.

## Pipeline at a glance

```text
source bytes + source identity + module environment
  -> frontend ABI value graph
  -> AST<Parsed>
  -> macro-expanded AST<Parsed>
  -> desugared AST<Parsed>
  -> AST<NameResolved> + ResolvedNames
  -> TypeOutput + transient Elaboration
  -> TypedProgram
  -> reachable ProgramInput set
  -> ownership-explicit, monomorphic source MIR
  -> optimized MIR
  -> register-allocated, frame-shaped talk_mir::Module
       -> talk-bytecode -> talk_vm::Module -> Executable
       -> talk-c        -> C executable/library artifact
       -> talk-llvm     -> LLVM executable/library artifact
```

The important public seams are:

1. the self-hosted frontend ABI, because generated native or bytecode code crosses
   into Rust;
2. module artifacts, because separately compiled source facts are cached and
   imported;
3. `talk_mir::Module`, because three target adapters consume it;
4. encoded bytecode and native library calls, because they cross process or
   language trust seams.

Most intermediate stages are private functions, not independently versioned
artifacts.

## Shared primitive vocabulary

These primitives cross several phases and should have one semantic owner.

| Primitive | Meaning | Current owner |
| --- | --- | --- |
| `FileID` | Identity of a source document within a compilation | parse driver |
| `NodeID(FileID, u32)` | Identity of one source or synthesized occurrence | parser/checker id generators |
| `Span { file_id, start, end }` | Byte range in a source document | source frontend |
| `Name` | Source spelling, then `Name::Resolved(Symbol, spelling)` | parser, mutated by resolver |
| `Symbol` | Canonical declaration identity, including symbol kind and module identity | resolver |
| `ModuleId` | Session-local module identity stamped into source symbols | module registry |
| `StableModuleId` | Content-derived module identity used by module artifacts | module publication |
| `Ty` | Final or in-progress source type vocabulary | type checker |
| `Scheme` | Quantified callable/value type with predicates | type checker/catalog |
| `TypeCatalog` | Declared nominal, protocol, conformance, effect, callable, and relationship facts | shared type-checking session |
| `Origin`/diagnostic `NodeID` | Source blame for frontend errors | phase producing the diagnostic |
| `MirSymbol` | Compact executable identity for structs, enums, effects, and protocols | MIR publication mapping |
| `LayoutId` | Index into finalized MIR's layout table | MIR layout phase |
| `LocalId`, `BlockId`, `FuncId` | Finalized MIR-local identities | MIR builder/finalizer |

`NodeID` is source provenance and an editor join key. It is not a valid way for
backend code to rediscover a type, resolution, ownership decision, or runtime
layout unless that fact is part of the elaborated program.

# Frontend phases

## 0. Source graph assembly and import discovery

**Implementation:** `src/compiling/driver.rs`

### Consumes

- initial `Vec<Source>`;
- `DriverConfig`:
  - `ModuleId`;
  - `ModuleEnvironment`;
  - shared `SharedCatalog`;
  - compilation and parse modes;
  - source/workspace roots;
  - optional parser session and parse cache;
  - precompiled source mappings and dependency library bodies;
- filesystem or in-memory source bytes.

### Private working primitives

- FIFO `(Source, FileID)` parse queue;
- canonical-path-to-`FileID` maps;
- `LocalModulePaths` path resolver;
- canonical `(importer FileID, imported FileID)` dependency edges;
- parse-cache keys `(FileID, path, ParseMode, text hash)`.

### Exports

`Driver<Parsed>` containing:

- `IndexMap<Source, AST<Parsed>>` in discovery order;
- exact source snapshots keyed by `FileID`;
- parser diagnostics;
- procedural macro environment;
- canonical file dependency edges.

### Invariants

- A source gets its `FileID` before entering the queue.
- Local import discovery reaches a fixed point before name resolution.
- Dependency edges are recorded once and later determine deterministic global
  initialization order.
- Strict parsing fails closed. Lenient parsing may replace a failed file with an
  empty AST plus diagnostics.

This stage owns source-set discovery. Name resolution consumes the completed set
and does not discover more source files.

## 1. Self-hosted source frontend invocation and bridge adaptation

**Implementation:** canonical Talk sources in `stdlib/syntax/`; host and bridge
in `src/compiling/frontend.rs`, `native_frontend.rs`, `abi.rs`, and `bridge.rs`.

### Consumes

- UTF-8 source bytes;
- `FileID` assigned by the driver;
- parse category (`file`, expression, pattern, type, declaration, or block
  items);
- strict or lenient parse policy;
- checked-in ABI schema;
- native frontend artifact in production, or the verified bytecode seed for
  bootstrap and wasm32.

### Private working primitives

Inside the Talk frontend:

- canonical tokens and token kinds;
- token ranges and delimiter groups;
- parser cursor and category-specific parse routines;
- source spans, line/column positions, comments, and node metadata;
- structured parser diagnostics and recovery nodes.

At the Rust trust seam:

- `NativeValue` or VM values returned by the generated frontend;
- ABI records, variants, arrays, strings, and symbol rows;
- `ResultValidator`, which checks identity, tag, arity, field count, array
  bounds, UTF-8, spans, and references before adaptation;
- `BridgedParse`, the validated intermediate result.

### Exports

`AST<Parsed>` with:

- `Vec<parsing::Node>` roots;
- `NodeID`s under the supplied `FileID`;
- byte `Span`s;
- `NodeMetaStorage` containing token extents and identifier lists;
- `SyntaxMetadata` for hygienic macro materialization;
- comments and structured parser diagnostics;
- `IDGenerator` positioned above all adapted parser ids.

### Invariants

- Rust does not parse source text after the frontend returns.
- Production native parsing and bootstrap-bytecode parsing execute the same
  fixed-point Talk program.
- Unknown ABI variants, malformed references, or invalid spans fail closed.
- Token spelling and source shape belong to this phase. Later phases may retain
  them for diagnostics and tooling but may not reinterpret grammar.

### Consumers

- import discovery;
- macro expansion, including category parsing of expanded syntax;
- formatting and highlighting;
- name resolution and type checking.

## 2. Macro expansion

**Implementation:** `talk-front/src/macro_expansion.rs` plus the host adapter in
`talk-front/src/front/macro_host.rs` and `src/procedural_macros.rs`.

### Consumes

- mutable `AST<Parsed>` files;
- exact source snapshots keyed by `FileID`;
- declarative macro declarations and invocation token records;
- procedural macro bindings from package artifacts;
- `MacroHost` operations:
  - canonical token-kind tags;
  - category parsing;
  - procedural invocation and syntax metadata.

### Private working primitives

- macro definitions keyed by `(FileID, name, arity)`;
- canonical macro-token trees and parameter substitutions;
- hygiene `SyntaxContext` and `SyntaxScope`;
- fresh `NodeID` generation;
- an expansion-work limit;
- source provenance joining generated syntax to definition and use sites.

### Exports

The same `AST<Parsed>` carrier, mutated so that:

- macro declarations are removed;
- invocation placeholders are replaced by parsed AST nodes;
- generated identifiers carry hygiene metadata;
- generated nodes have fresh ids and source provenance;
- macro diagnostics are returned separately.

### Invariants

- Macro syntax does not cross the name-resolution seam.
- Expanded Talk syntax is parsed by the same category parser as ordinary source.
- Expansion never flattens syntax and reparses an independently maintained
  grammar.

## 3. Surface desugaring

**Implementation:** `talk-front/src/desugar/`.

### Consumes

A macro-free mutable `AST<Parsed>`.

### Private working primitives

Nine ordered AST transforms:

1. syntax quotations to opaque syntax-runtime calls;
2. trailing blocks to ordinary anonymous-function arguments;
3. default parameter-mode resolution;
4. `unreachable` to the core form;
5. named `func` declarations to value bindings;
6. subscripts to ordinary operations;
7. operators to protocol-static calls, with short-circuiting as control flow;
8. expression `if` to `match`;
9. explicit `self` insertion on methods and requirements.

Each transform uses parser nodes, fresh ids for synthesized nodes, and existing
spans for source-backed nodes.

### Exports

The same `AST<Parsed>` carrier, now restricted to the kernel forms expected by
resolution and typing.

### Invariants

- Transform order is semantic. For example, operator lowering must precede
  expression-`if` lowering because `&&` and `||` create `if` expressions.
- Later phases do not contain parallel rules for surface operators, trailing
  blocks, expression `if`, or implicit method receivers.
- This is one deep module externally (`desugar(asts)`); the individual passes
  are internal implementation modules.

## 4. Name resolution

**Implementation:** `talk-front/src/name_resolution/`.

### Consumes

- desugared `Vec<AST<Parsed>>`;
- module environment and imported export sets;
- source root and precompiled-source mappings;
- built-in symbol inventory;
- hygiene contexts attached during macro expansion.

### Private working primitives

- `Symbols` id generators;
- one root `Scope` per file and nested scopes keyed by owner `NodeID`;
- separate value, type, handler, hygienic, and callable-overload namespaces;
- declaration rounds:
  - top-level nominals and values;
  - effects;
  - type aliases;
  - imports;
  - full nested declaration walk;
- a second full resolution walk;
- visibility and declaration records;
- imported callable-label sets for overload selection.

### Exports

1. `Vec<AST<NameResolved>>`. The tree shape is unchanged, but every resolvable
   `Name::Raw` has become `Name::Resolved(Symbol, spelling)`.
2. `ResolvedNames`:
   - scopes for editor queries;
   - callable labels;
   - symbol display names and definition nodes;
   - nested child-type relations;
   - mutated symbols;
   - per-symbol declaration and visibility records.
3. `Symbols`, positioned after every declared and synthesized symbol.
4. structured name-resolution diagnostics.

### Invariants

- Symbol equality, not source spelling, identifies declarations downstream.
- Top-level forward references are order-independent.
- Local bindings remain sequential.
- Imports cannot silently overwrite declarations or other imports.
- Visibility has one canonical `DeclarationRecord` answer.
- Resolution reports errors but continues, preserving as much editor state as
  possible.

## 5. Type collection, constraint generation, solving, and finalization

**Implementation:** `talk-front/src/types/`.

### Consumes

- `IndexMap<Source, AST<NameResolved>>`;
- `Symbols` for checker-generated identities;
- `ResolvedNames` for declaration, visibility, mutation, and nested-type facts;
- `ModuleEnvironment` schemes and catalog slices;
- compilation `ModuleId`;
- mutable compilation-wide `SharedCatalog`.

### Shared semantic primitives

- `Ty`: nominal types, tuples, records, functions, borrows, unique values,
  existentials, parameters, projections, effects, static values, and inference
  variables;
- `Scheme`: quantified parameters, predicates, and body type;
- `Predicate`: equality, conformance, member, row, effect, and static
  constraints;
- `Constraint` plus `CtOrigin`: a predicate with source blame and reason;
- `TypeCatalog`: declarations, fields, variants, protocols, requirements,
  effects, conformances, dictionaries, callable contracts, ownership grades,
  bounds, visibility, and derived indexes;
- `VarStore`: union-find state, levels, row/effect variables, and normalization;
- `MemberResolution`: direct, committed conformance, or deferred requirement
  dispatch;
- adaptation evidence from `types/adapt.rs`.

### Internal subphases

#### 5.1 Declaration collection

Consumes resolved declarations and extends the shared catalog with nominal
shapes, protocols, effects, aliases, callable placeholders, conformance rows,
and member ownership. It exports a private `Collected` work inventory for body
checking.

After collection, the checker synthesizes derived and reflexive conformances and
commits Deinit, dictionary, callable-owner, and member-visibility indexes needed
by later checking.

#### 5.2 Binding-group construction

Consumes resolved body references and partitions top-level binders and nominal
member bodies into strongly connected components. The private primitives are
monomorphic skeletons, dependency edges, inference levels, and group-owned
variables.

#### 5.3 Bidirectional constraint generation

Consumes one group plus an expected or inferred context. It exports private
wanteds, implication constraints, checked occurrence types, call selections,
pattern facts, effect contracts, inline-IR operations, and synthesized lowering
plans into `TypeArtifacts`.

The generator owns source legality: call argument labels and modes, captures,
patterns, effects, trusted operations, literals, and visibility. It must not use
runtime representation as proof of source legality.

#### 5.4 Constraint solving and generalization

Consumes wanteds, givens, the catalog, and `VarStore`. It mutates the store and
exports solved substitutions, residual predicates, member/conformance evidence,
and generalized schemes. Stuck constraints may float to a later group or the
final solve; only the final solve enables defaulting.

`types/adapt.rs` is the one pure judgment for crossing a found value into an
expected slot. It exports an internal `Adapted` decision such as equality,
donation, borrow downgrade, missing evidence, or deferred resolution. Its tier
queries are deliberately private to that module.

#### 5.5 Semantic audits

After body checking, the session runs:

- recursive-layout legality;
- match exhaustiveness and unreachable-arm analysis;
- unsupported first-class method-reference checks;
- call-label agreement;
- public-interface closure checks.

These consume solved occurrence facts and emit diagnostics; they do not create a
new semantic artifact.

#### 5.6 Finalization

Consumes the solved `VarStore`, `TypeArtifacts`, schemes, and catalog. It zonks
and normalizes every published type, finalizes call-site substitutions, commits
rank-N field specializations and witness layouts, canonicalizes literals and
patterns, and checks late marker/pack rules.

### Exports

`check_types` currently returns three values:

1. `TypeOutput`, containing only symbol- or module-keyed residue:
   - `module_id`;
   - a `TypeCatalog` value;
   - finished `Scheme`s;
   - inferred generic origins;
   - local binder types;
   - display names.
2. transient `Elaboration`, containing per-occurrence construction facts:
   - node types;
   - instantiations and rank-N specializations;
   - witness layouts;
   - member resolutions and selected callables;
   - canonical integer literals;
   - `for` and propagation plans;
   - clone and existential-pack facts;
   - checked inline IR and effect contracts;
   - checked pattern occurrence types and slot tables.
3. ordered type diagnostics.

`Elaboration` is intentionally non-serializable and should have one consumer:
typed-program construction.

### Invariants

- No inference variable may cross successful finalization.
- Every frontend-decidable conformance or callable selection is committed.
- A recovery error may preserve `Ty::Error`, but a backend-eligible file must
  have complete checked fields.
- Runtime layout, retain/release, and register decisions are not type-system
  evidence.

## 6. Typed-program construction

**Implementation:** `src/compiling/typed_program.rs` and
`src/compiling/typed_program/build.rs`; node vocabulary in
`talk-front/src/typed_ast/`.

### Consumes

- resolved ASTs;
- finalized `TypeOutput`;
- transient `Elaboration`;
- files blocked by error diagnostics;
- canonical file dependency edges.

### Private working primitives

- AST-to-typed-tree builder;
- per-file synthesized-id floor;
- graft records for wrappers whose semantic node replaces an erased inner node;
- frame-fact collection for captures, assignment conversion, and nested refs;
- checked `for`, postfix propagation, constructor, projection, and clone
  elaborations.

### Exports

`TypedProgram` containing:

- initialization-ordered `TypedFile`s;
- elaborated `typed_ast::Node` trees;
- retained `ResolvedNames`;
- retained `TypeOutput`;
- editor `NodeFacts` only for blocked files with no typed tree;
- file dependency edges.

Important node-local exported facts include:

- every expression's finalized `Ty`;
- member resolution, selected callable, and instantiation;
- rank-N specialization and witness layout;
- explicit existential pack and clone forms;
- canonical literal values;
- checked inline-IR operations and effect contracts;
- checked pattern identities, types, and physical slots;
- function schemes, receiver roles, and `bound_as` identities;
- frame capture/cell/nested-reference facts.

### Invariants

- Successful per-occurrence facts live on typed nodes, not in published
  `NodeID` maps.
- `NodeFacts` for successful files is a disposable editor index rebuilt from
  the tree.
- Blocked files have no typed tree; their limited editor facts remain in
  `blocked_facts`, so a fact still has one home per file.
- Files are published dependency-first for deterministic global initialization.

### Current seam leak

The backend still has production access to `TypedProgram::types()` at nine call
sites: eight catalog access sites and one scheme access site. Full
`ResolvedNames` access is test-only, but symbol names remain available as
metadata.

## 7. Module interface publication and cache slices

**Implementation:** `src/compiling/interface.rs`, `module.rs`, and `cache.rs`.

### Consumes

- a completed `TypedProgram`;
- module ownership predicate over `Symbol`;
- exports derived from `ResolvedNames`;
- module identity and dependency list;
- optional procedural macro artifact.

### Private working primitives

- own-symbol filtering;
- foreign-protocol amendment stubs;
- retroactive conformance selection by declaring module;
- scheme sanitization;
- derived-index removal before serialization;
- stable module hash over exports and callable contracts.

### Exports

`Module` with:

- `StableModuleId`;
- export-name-to-symbol-overload sets;
- symbol display names;
- `ModuleTypes { schemes, catalog slice }`;
- dependency module ids;
- optional procedural macro artifact.

### Invariants

- Module export is selection, not semantic rewriting.
- Solver variables and session-only derived indexes do not cross the artifact
  seam.
- Privacy is checked at use sites; hiding catalog facts is not the privacy
  mechanism.
- Cached module slices carry amendments to foreign entities when this module
  owns the amendment.

# Backend phases

## 8. Reachable backend-input assembly

**Implementation:** `Driver<Typed>::with_backend_inputs` in
`src/compiling/driver.rs`.

### Consumes

- root `TypedProgram`;
- core typed program;
- activated stdlib modules and their transitive dependency edges;
- dependency-library typed programs;
- selected entry mode:
  - script;
  - named nullary function;
  - named service exports plus allowed effects.

### Private working primitives

- transitive stdlib body closure;
- module-to-program association;
- deterministic `Vec<ProgramInput>` with root first.

### Exports

A borrowed slice of:

```text
ProgramInput {
  program: &TypedProgram,
  module: ModuleId
}
```

plus the private backend `Entry` selection.

### Invariants

- Backend compilation sees every body reachable through imported library and
  stdlib dependencies.
- Source symbols already carry absolute module identity; the backend does not
  repair aliases.
- The root program is index zero and is the entry/export owner.

## 9. Program indexing, specialization, and source-MIR construction

**Implementation:** `src/compiling/mir/build/`, primarily `build/mod.rs` and
`entries.rs`.

### Consumes

- `ProgramInput` set;
- entry selection;
- typed trees and program-level schemes/catalog facts;
- optional `check_all` and debug-provenance modes.

### Private program-wide primitives

`ProgramBuilder` owns:

- assembled `TypeCatalog` and struct/enum/variant indexes;
- callable and global inventories;
- monomorphic `Instance = (Symbol, substitution)` identities;
- specialization worklist and `FuncId` map;
- witness, writeback, drop/retain, derived-equality, derived-show, and derived-
  identity glue caches;
- global slots and export wrappers;
- memoized type-shape/drop/buffer/object queries;
- `Layouts` oracle and interned layouts;
- debug file, source, and line indexes.

### Private function primitives

`FunctionBuilder` owns:

- source-symbol-to-`LocalId` bindings;
- concrete type substitution for the instance;
- basic blocks, instructions, and terminators;
- lexical loop and scope state;
- temporaries, initialization state, writeback state, and global loads;
- capture environments, cells, witness parameters, and requirement
  dictionaries;
- borrow roots and view locals;
- ownership sites and event order;
- return/layout facts and generated-debug origins.

### Work performed

- discover callables and globals from typed roots;
- demand and monomorphize reachable generic callables;
- materialize committed protocol witnesses and genuinely deferred requirement
  evidence;
- compile expressions and statements into CFG blocks;
- compile patterns to tests, projections, and branches;
- closure-convert functions and handlers;
- emit explicit aggregates, calls, effects, memory operations, and glue;
- compute and intern target-neutral aggregate layouts;
- record ownership and loan sites for the post-build ownership pass.

### Internal output before ownership completion

The builder directly uses the `talk_mir` vocabulary:

- `Function`, `BlockData`, `Inst`, `Term`, `Operand`;
- source-level locals and blocks;
- layout ids and representation annotations;
- incomplete unwind links and no finalized frame/register facts yet.

This value is private despite sharing its Rust type with the eventual public
artifact. Publication happens only after all later backend stages complete.

## 10. Ownership elaboration

**Implementation:** `src/compiling/mir/build/ownership.rs`.

### Consumes

- finished per-function CFG;
- ordered `OwnershipSites`:
  - consume, displacement, and writeback sites;
  - owned reads;
  - loan creation and invalidation;
  - event sequence numbers;
- builder facts needed to classify types and synthesize retain/drop glue;
- borrow-root/view relations.

### Private working primitives

- backward liveness over real CFG successors;
- view-to-owner alias edges;
- forward per-local ownership and loan states;
- insertion records `(block, instruction index, instructions)`;
- source ownership diagnostics.

### Exports back into the function builder

- inserted retain, witness-call, move, displacement, and drop instructions;
- remapped instruction indexes;
- canonical `FlowRecord`s with events:
  - `Def`, `Use`, `Move`, `Drop`;
  - `Anchor`, `EscapeSink`;
  - `GlobalMove`, `GlobalRestore`, `GlobalUse`.

### Invariants

- Lowering records an ownership site; it does not choose retain versus move from
  syntactic last use.
- Liveness is computed over loops, joins, and unwind edges rather than threaded
  through syntax construction.
- A use-after-move, invalid loan, or illegal duplicate linear consume is a source
  diagnostic before public MIR publication.

## 11. Computed flow checks

**Implementation:** `src/compiling/mir/build/flow.rs`.

### Consumes

- ownership-explicit CFG;
- `FlowRecord` stream.

### Private working primitives

Two forward fixpoints:

- anchored-closure taint over copies, environments, block arguments, calls, and
  storage sinks;
- moved-linear-global sets over branches and loop back edges.

### Exports

Ordered `BackendError`s for:

- frame-anchored values escaping their frame;
- use or repeated consume of moved linear globals.

This phase emits diagnostics only; it does not export a semantic side table.

## 12. Release planning and ownership verification

**Implementation:** `src/compiling/mir/build/release.rs` and `verify.rs`.

### Consumes

- CFG after ownership elaboration;
- the same `FlowRecord` stream.

### Private working primitives

The ownership verifier computes one per-block-entry state vector with states:

```text
ABSENT | OWNED | DEAD | CONFLICT
```

The release planner replays those states to compute:

- reverse-definition-order releases at frame exits;
- edge releases that equalize disagreeing predecessor states;
- owned sets live at suspension-capable calls for unwind cleanup.

### Exports

Private `release::Plan`:

```text
end_of_block: Vec<Vec<LocalId>>
edges: Vec<(from block, successor position, locals)>
unwind_live: Vec<((block, instruction), locals)>
```

The function builder immediately realizes the plan as ordinary MIR:

- explicit drop/glue instructions;
- split cleanup edges;
- shared unwind cleanup chains;
- patched call unwind targets.

The plan itself does not cross the function-building seam.

### Verification

In debug builds, `verify::check` replays the final combined event log and rejects:

- use before initialization or after move;
- double move/drop;
- ownership disagreement at joins;
- live owned values at finite frame exits.

The verifier audits construction; it does not replay source type checking.

## 13. MIR optimization

**Implementation:** `src/compiling/mir/optimize/`.

### Consumes

Ownership-complete private MIR using the eventual public instruction vocabulary.

### Private working primitives

- bounded local simplification rounds;
- per-pass change and application counts;
- local def/use and CFG analyses owned by individual passes.

### Pass order

Per-function simplification repeats up to eight rounds:

1. constant folding;
2. branch folding;
3. match-switch formation;
4. unreachable-block removal;
5. block-parameter simplification;
6. dead-code elimination.

Then the program runs:

1. forward-call rewriting;
2. small-function inlining;
3. another local simplification fixed point;
4. dead-function elimination;
5. proof-gated dead-handler elimination;
6. final simplification and dead-function elimination if handlers changed.

### Exports

- mutated MIR;
- `OptimizationStats`, one `(name, applied count)` entry per pass.

### Invariants

- Debug origins remain aligned with instructions.
- Passes preserve the ownership-explicit executable meaning; they do not consult
  source AST or checker artifacts.

## 14. Escape summaries, register allocation, and frame shaping

**Implementation:** `src/compiling/mir/build/escape.rs` and
`src/compiling/mir/regalloc.rs`.

### 14.1 Parameter escape summaries

Consumes pre-allocation MIR and computes a program-wide fixed point describing
whether each function parameter may outlive its call. It must run before local
reuse because parameters still have unique local identities.

### 14.2 Register allocation

Consumes each function plus the complete layout table and return layouts.
Privately it:

- orders blocks in reverse postorder;
- fuses producer/copy pairs and removes dead copies;
- computes backward liveness;
- derives one layout class per local;
- assigns non-overlapping live ranges to reusable registers;
- rewrites every local occurrence and debug name.

Parameters stay pinned at `0..arity`.

### 14.3 Frame shaping

Consumes register-allocated MIR plus pre-allocation escape summaries. It computes:

- construction sites safe for reusable frame storage;
- locals whose values originate only from frame-safe sites;
- final `LocalInfo.frame_local` and `Function.frame_sites` facts.

### Exports

The finalized numbering and frame facts embedded directly in each public
`talk_mir::Function`:

- final locals table;
- `LocalInfo { layout, frame_local }`;
- parameter and return representations;
- frame-local construction sites.

Backends read these facts and do not rerun compiler escape analysis.

## 15. Finalized public MIR publication

**Implementation:** producer in `src/compiling/mir/mod.rs`; vocabulary in
`talk-mir`.

### Consumes

Optimized, ownership-complete, register-allocated, frame-shaped MIR.

### Verification

In debug builds, structural verification checks:

- entry and export function ids;
- local, block, function, layout, and global bounds;
- terminator presence;
- block-parameter and edge-argument agreement;
- instruction structural invariants.

### Exports

`talk_mir::Module`:

- `functions: Vec<Function>`;
- selected `entry`;
- global slot count;
- named host exports;
- interned layout table;
- display metadata;
- well-known String and Storage identities;
- optional debug file/source tables.

Each `Function` exports:

- name and arity;
- final local/frame facts;
- basic blocks with block parameters;
- explicit instructions and one terminator per block;
- parameter and return representations;
- frame-local construction sites;
- optional local names and instruction origins.

The instruction vocabulary includes these families:

- scalar copies, arithmetic, comparisons, and conversions;
- direct and indirect calls;
- aggregate construction, field access, array indexing, and tags;
- raw allocation, retain/free, loads/stores, pointer arithmetic, and memcpy;
- globals;
- closures, environments, cells, and continuations;
- handler installation, lookup, resume/discontinue support, and unwind edges;
- heap objects, regions, and finalizers;
- existential payloads and witness tables;
- host IO.

The terminator vocabulary is:

```text
Goto(args) | Branch | Switch | Return | Trap | UnwindRet
```

### Seam invariants

- No target consumes `TypedProgram`, `Ty`, parser nodes, or source-level
  resolution tables.
- Layout and frame facts are producer-owned and explicit.
- The module is trusted in-process data, not a versioned serialization format.
- Three real adapters justify this seam; adding a MIR variant breaks each
  exhaustive adapter match at compile time.

# Target phases

## 16. Bytecode adaptation

**Implementation:** `talk-bytecode`.

### Consumes

Only `&talk_mir::Module`.

### Private working primitives

- MIR-to-VM register and control-flow mapping;
- target constant, argument, static, layout, and symbol pools;
- block linearization and edge-copy handling;
- VM instruction sequences;
- checked indexed-load fusion;
- runtime display-name adaptation.

### Exports

`talk_bytecode::Executable` containing a private `talk_vm::Module`, display
metadata, adapter statistics, and String identity. It supports:

- execution;
- named export calls with host values and budgets;
- bytecode rendering;
- bytecode encoding;
- VM and adapter statistics.

### Trust distinction

- In-memory modules produced by this adapter rely on compiler construction
  invariants.
- `run_image(bytes)` treats bytes as untrusted and calls the VM decoder and
  validator before execution.

## 17. C adaptation

**Implementation:** `talk-c` plus shared runtime source from
`talk-native-runtime`.

### Consumes

Only `&talk_mir::Module`, and a symbol prefix in library mode.

### Private working primitives

- exhaustive MIR instruction emission;
- native/tagged value representation selection from published layouts;
- interned statics, effects, symbols, and type/layout tables;
- C labels and gotos for MIR blocks;
- native function signatures from `ParamRepr` and return layout;
- frame-local storage from published frame facts;
- shared native runtime and library-call convention.

### Exports

- executable `Artifact { source }`; or
- `LibraryArtifact { source, header, manifest }` with namespaced lifecycle and
  one wrapper per MIR export.

The adapter chooses C representation and syntax. It does not choose source
ownership, conformance, field identity, or layout.

## 18. LLVM adaptation

**Implementation:** `talk-llvm` plus `talk-native-runtime`.

### Consumes

Only `&talk_mir::Module`, and a symbol prefix in library mode.

### Private working primitives

- exhaustive MIR-to-LLVM instruction emission;
- LLVM blocks, values, globals, and calls;
- the same published layouts, exports, and frame facts as C;
- namespaced native-runtime bridge symbols.

### Exports

- `Artifact { ir, runtime_c }`; or
- `LibraryArtifact { ir, runtime_c, header, manifest }`.

C and LLVM share the native runtime and host call convention but remain separate
adapters because their target representations genuinely differ.

# Semantic authority ledger

The following table is the shortest way to detect an invalid re-derivation.

| Question | Sole authority | Downstream realization |
| --- | --- | --- |
| What tokens and syntax did the user write? | source frontend | formatter, tooling, macro expander |
| Which declaration does a name mean? | resolver `Symbol` | checker and typed tree carry the symbol |
| Is a declaration accessible? | resolver declaration record | checker queries it |
| What type does an occurrence have? | type checker | typed node `ty` |
| Which callable/member/witness was selected? | type checker | typed-node evidence; specialization dereferences only deferred requirements |
| How does a found value adapt to an expected slot? | `types/adapt.rs` | checker records clone/evidence; MIR realizes it |
| Is a source use legal as copy/borrow/consume? | type checker plus CFG-sensitive ownership analysis | explicit MIR operations |
| Is a local live, moved, borrowed, or owned at a CFG point? | MIR ownership dataflow | diagnostics and release planning |
| Where must cleanup execute? | MIR release planner | explicit MIR instructions and edges |
| How is a source type represented at runtime? | MIR layout oracle | published `LayoutId`, `LocalInfo`, `ParamRepr` |
| Which locals share target registers? | register allocator | rewritten final ids |
| Which aggregate sites may use frame storage? | MIR escape/frame shaping | published frame facts |
| How is finalized MIR encoded for a target? | target adapter | bytecode, C, or LLVM artifact |
| Is a serialized bytecode image safe to execute? | VM decoder/validator | VM interpreter |

# Consolidation pressure visible in the primitive map

These are evidence-backed deepening opportunities, not proposed interfaces.
They should be explored separately so a deletion in one semantic authority does
not become an accidental rewrite of another.

## 1. Finish the one-catalog transition

**Files**

- `talk-front/src/types/generate/mod.rs`
- `talk-front/src/types/output.rs`
- `src/compiling/typed_program.rs`
- `src/compiling/mir/build/mod.rs`
- `src/compiling/mir/build/layout.rs`
- `src/compiling/interface.rs`

**Problem**

The declared architecture says one catalog per compilation, but the current
implementation still has several whole-table carriers:

1. `check_types` moves the shared catalog into the session;
2. finalization places it in `TypeOutput`;
3. `check_types` clones it back into `SharedCatalog`;
4. every `TypedProgram` retains a `TypeOutput` catalog;
5. `ProgramBuilder::new` clones the root catalog, inserts dependency slices,
   synthesizes, and recommits;
6. `Layouts` receives another catalog clone.

The MIR builder also maintains `struct_index`, `enum_index`, and `variant_index`
beside the catalog. These are derived indexes, but their lifetime and ownership
are mixed with the duplicated table.

This partially contradicts ADR 0053's implemented status. The code comments
still explicitly describe the copies as transitional.

**Deepening direction**

Make one module own the compilation catalog's lifetime through frontend checking,
module-slice publication, and backend compilation. Keep module slices only at
the real cache/artifact seam; keep disposable indexes as borrows over that one
answer.

**Benefits**

- **Locality:** synthesis, commitment, and derived-index construction happen in
  one place.
- **Leverage:** every checker and backend query sees the same facts without merge
  or reconciliation code.
- **Tests:** package/module tests exercise one table rather than testing several
  paths that happen to agree.
- **Deletion test:** removing a copied catalog currently triggers merge/clone
  work elsewhere, which identifies the remaining real owner; removing derived
  indexes should affect performance only, not answers.

## 2. Close the frontend artifact seam completely

**Files**

- `talk-front/src/types/generate/finalize.rs`
- `talk-front/src/types/output.rs`
- `src/compiling/typed_program.rs`
- `src/compiling/typed_program/build.rs`
- `src/compiling/mir/build/mod.rs`
- `src/compiling/mir/build/entries.rs`

**Problem**

`talk-front` owns parsing through type checking and the typed-node vocabulary,
but the root crate owns typed-program construction. The actual type-checker
interface is still the triple `(TypeOutput, Elaboration, diagnostics)`, and the
root builder must know how every elaboration table maps onto typed nodes.
`TypedProgram` then exposes `types()` to production backend code. Nine backend
reads still cross that escape hatch.

The module is therefore shallower than the intended frontend seam: callers must
know about `TypeOutput`, `Elaboration`, typed-tree construction, and the residue
that did not make it onto nodes.

**Deepening direction**

Have the frontend module publish the completed elaborated program itself and
hide the transient elaboration tables and construction sequence inside its
implementation. Expose only deliberate program-level catalog/scheme/name views
needed by module publication and MIR.

**Benefits**

- **Locality:** adding one checked occurrence fact changes checker finalization
  and typed-node construction in one module.
- **Leverage:** backend and editor consumers receive a complete program instead
  of coordinating a tree with residue.
- **Tests:** the elaborated program becomes the interface and test surface;
  temporary table completeness no longer needs cross-crate tests.
- **Deletion test:** deleting `Elaboration` as a cross-module concept should not
  force semantic reconstruction into MIR; if it does, the typed tree is missing
  a fact.

## 3. Consolidate CFG topology and fixpoint plumbing

**Files**

- `src/compiling/mir/build/ownership.rs`
- `src/compiling/mir/build/flow.rs`
- `src/compiling/mir/build/release.rs`
- `src/compiling/mir/build/verify.rs`
- `src/compiling/mir/regalloc.rs`

**Problem**

Several correct, distinct analyses independently rebuild the same mechanical
substrate:

- successor discovery, including unwind edges;
- predecessor lists;
- event buckets by block and instruction;
- worklists and entry-state joins;
- reachable-block handling.

The lattices are genuinely different: ownership, liveness, anchored taint,
linear globals, and escape summaries should not be merged into one meaning.
But the repeated topology and iteration machinery is shallow implementation
code around each analysis and makes edge semantics easy to skew.

**Deepening direction**

Concentrate CFG indexing and traversal mechanics in one private MIR-analysis
module while leaving each semantic transfer/join rule with its current owner.
Do not introduce a public analysis framework; there is only one backend
consumer.

**Benefits**

- **Locality:** adding a new edge kind or unwind form changes successor semantics
  once.
- **Leverage:** all current and future dataflows reuse one proven CFG model.
- **Tests:** topology tests pin edge construction; each analysis test can focus
  on its lattice and diagnostics.
- **Deletion test:** deleting repeated worklist/successor code should remove
  complexity rather than move semantic rules between analyses.

## 4. Finish removing hand-threaded ownership state from `FunctionBuilder`

**Files**

- `src/compiling/mir/build/mod.rs`
- `src/compiling/mir/build/ownership.rs`
- `src/compiling/mir/build/flow.rs`
- `src/compiling/mir/build/release.rs`

**Problem**

The computed ownership pass now decides retain versus move and handles CFG joins,
but `FunctionBuilder` still carries overlapping state and event mechanisms:

- `moved` and `uninitialized` sets;
- lexical `scopes` and statement temporary lists;
- borrow roots and view locals;
- ownership sites plus flow events;
- frame ownership metadata;
- global-load and capture classifications.

Some of these are necessary construction facts; others are remnants or eager
answers duplicated by the later CFG analysis. Their coexistence makes the
`FunctionBuilder` interface nearly as complex as its implementation and keeps
source lowering coupled to ownership analysis details.

**Deepening direction**

Audit every builder field by authority: construction identity, event recording,
or semantic answer. Retain construction identity and events; move every answer
that can be computed from the finished CFG into the ownership module. Keep
statement-local temporary ownership only where evaluation order makes it
intrinsically a construction fact.

**Benefits**

- **Locality:** ownership transitions and diagnostics live in the ownership
  implementation rather than every expression lowering path.
- **Leverage:** a new source construct records standard sites and automatically
  participates in loops, joins, loans, and cleanup.
- **Tests:** ownership tests exercise the computed model through MIR building;
  construct-specific tests need only prove the correct sites were emitted.
- **Deletion test:** a removable builder field should disappear without growing
  branch-specific save/restore logic elsewhere.

## 5. Separate runtime type facts from source catalog access inside MIR

**Files**

- `src/compiling/mir/build/mod.rs`
- `src/compiling/mir/build/layout.rs`
- `src/compiling/mir/build/glue.rs`

**Problem**

MIR legitimately needs source type structure to specialize bodies and generate
layout/drop/retain/equality/show glue. Today those reads are spread across
`ProgramBuilder`, `Layouts`, and glue emission through catalog queries plus
parallel caches such as `needs_drop`, `contains_buffer`, and `contains_object`.
The source-to-runtime classification interface is therefore broad, and it is
hard to tell whether a new catalog query is specialization, runtime
representation, or a forbidden source-semantic re-derivation.

**Deepening direction**

Concentrate specialization-normalized runtime type queries behind one private
MIR module. Its implementation may read the catalog and cache structural walks;
callers should ask runtime questions rather than coordinate catalog rows,
nominal indexes, projection reduction, and layout caches themselves.

**Benefits**

- **Locality:** one implementation owns projection reduction and structural
  traversal for runtime representation.
- **Leverage:** layout and generated glue share normalized member/payload facts.
- **Tests:** test runtime classification against concrete specialized types,
  while frontend tests continue to own source legality.
- **Deletion test:** removing a direct catalog read from an emitter should not
  make the emitter reimplement the query.

## 6. Keep target duplication only where the adapters are genuinely different

**Files**

- `talk-bytecode/src/lower.rs`
- `talk-c/src/lib.rs`
- `talk-llvm/src/emit.rs`
- `talk-native-runtime`

**Problem**

All three adapters exhaustively match the MIR vocabulary, which is intentional
and valuable. C and LLVM also need matching library exports, lifecycle, symbol
mangling, native runtime tables, and trap containment. Those shared concerns
already partly live in `talk-native-runtime`; representation-specific emission
correctly remains separate.

**Deepening direction**

Apply the deletion test narrowly: continue moving only identical native ABI,
runtime-data, and symbol-policy implementation behind the existing shared
module. Do not hide MIR instruction matching behind a target trait or generic
emitter; exhaustive independent adapters are the reason the public MIR seam is
real.

**Benefits**

- **Locality:** native host contracts change once.
- **Leverage:** C and LLVM receive the same lifecycle and ABI behavior.
- **Tests:** shared C-harness tests pin the host seam, while adapter-specific
  tests pin instruction selection.

# Size context

Approximate nonblank Rust lines in the current major semantic areas:

| Area | Lines |
| --- | ---: |
| `talk-front/src/types` | 29,199 |
| `src/compiling/mir` | 20,551 |
| `talk-front/src/parsing` Rust vocabulary/tooling | 6,946 |
| `talk-front/src/name_resolution` | 4,630 |
| `talk-c/src` | 2,492 |
| `talk-llvm/src` | 1,948 |
| `talk-bytecode/src` | 1,881 |
| `talk-mir/src` | 1,226 |
| `talk-front/src/desugar` | 1,008 |
| `talk-front/src/typed_ast` | 793 |

These numbers do not prove that a module is shallow. They identify where a
small reduction in duplicated interface knowledge has the largest potential
payoff. The strongest consolidation candidates above come from duplicated
semantic authority or repeated phase mechanics, not line count alone.
