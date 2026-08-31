# Mincodex critical-path feasibility evidence

Step: B1

Revision inspected: `628ab568` (source inventory remains
`85cf295d46f160efaf4453e05f01e8f61531a455`). No production or generated
file changed during this inspection.

## Decision

The critical path is feasible without VM, formatting, highlighting, artifact,
or LSP-semantic work. All required current facts exist before MIR. P1-P3 own a
checked matrix input model in `types/patterns.rs`; they do not fabricate Core
matches or retain syntax for constructs that have not been elaborated yet.
P1's current-checker adapter exercises the report recursion. P4 adapts each
actual checked Core match occurrence, including synthesized matches, and
stores that invocation's one product.

The current pattern diagnostic gate was run as the existing corpus oracle:

```text
cargo test -p talk-front --test front_suite types_tests:: --no-fail-fast
    546 passed; 0 failed; 206 filtered out
cargo test -p talk-front --test front_suite core_tests:: --no-fail-fast
    14 passed; 0 failed; 738 filtered out
```

## 1. Pattern diagnostic input and output

### Current owner and shape

`crates/talk-front/src/types/generate/mod.rs::TypecheckSession::check_matches`
walks every name-resolved AST after body checking and before `finalize`. For
each `ExprKind::Match` it records the scrutinee `NodeID` and cloned source-order
arm patterns, reads the solved scrutinee from
`Generator::artifacts.node_types`, zonks it, removes one root borrow, and calls:

```rust
exhaustiveness::check_match(
    catalog: &TypeCatalog,
    scrutinee: &Ty,
    arms: &[&parsing::Pattern],
) -> exhaustiveness::MatchReport
```

`types/exhaustiveness.rs` lowers patterns to private `Pat::{Wild,Ctor,Or}` and
runs `Coverage::useful` over a matrix. `MatchReport` is:

```text
missing: Vec<String>             // source-preserving witness order, cap 3
unreachable_arms: Vec<NodeID>    // source arm pattern ids
```

`check_matches` converts missing witnesses to `TypeError::NonExhaustiveMatch`
and unreachable IDs to `UnreachableMatchArm`; a synthesized conditional arm is
mapped to `IrrefutableConditionalPattern` at the preceding written pattern.
`all_missing_patterns` is the uncapped code-action helper and is the other
consumer of the old recursion.

### Replacement owner

`types/patterns.rs` owns `MatchReport`, a checked matrix input, and the one
matrix recursion. P1 adapts current source matches to that input only to run the
report differential. P4 adapts actual checked Core matches after all semantic
elaboration, so source and synthesized matches follow the same path. The old
checker remains the production diagnostic through P5. P6 switches diagnostic
conversion and the `all_missing_patterns` consumer to reports stored on Core.

### Oracle and renderer

`render_match_report` emits matches in `(file id, match node local id)` order,
then `missing[index]=<written pattern>` and
`unreachable[index]=<file>:<local>` in stored order. No hash iteration reaches
the renderer. The existing oracle is:

```text
cargo test -p talk-front --test front_suite types_tests:: --no-fail-fast
```

It covers enums, booleans, integers, tuples, records, structs, nested payloads,
or-patterns, source ordering, synthesized conditional arms, and GADT-impossible
constructors.

## 2. Runtime pattern-control output

### Current owner and shape

`src/compiling/mir/build/mod.rs::FunctionBuilder::compile_match` creates one
result local and join block, then one `matched` and `next_test` block per source
arm. `compile_pattern_test`/`compile_pattern_test_scoped` recursively emit:

- `Goto` for wildcard and binder success;
- `Copy` into one stable binder local;
- scalar comparisons and `Branch` for bool/int/float;
- `GetTag`, tag comparison, `GetField`, and sequential payload tests for enum
  variants;
- declaration-order tuple, closed-row record, and struct projections;
- `ObjectGet` for heap structs;
- source-order alternative continuations for or-patterns;
- length and byte-loop comparisons for string/character literals.

The output is ordinary pre-final `Vec<BlockData>` topology plus binder locals,
not a named pattern product. Failed tests chain to the next source arm; final
fallthrough traps as `unmatched value`. Arm values flow through `merge_arms`
to the result join.

### Replacement owner

`DecisionTree` in `types/patterns.rs` owns tests, source-order alternatives,
projections, bind operations, leaves, and guard continuations. `Core<Nested>`
retains it, `Nested -> Flat` realizes it as explicit Core control flow, and MIR
only lowers flat nodes.

### Oracle and renderer

`render_decision_tree` numbers places and decision nodes by first preorder
visit, renders source IDs as `file:local`, types with canonical `Ty` rendering,
and substitutions sorted by parameter symbol. Tests and alternatives retain
vector order. Runtime realization is compared with the existing
`talk_mir::Program::render`, after replacing local/block/function numeric IDs
with first-definition IDs and omitting debug spans. Existing corpus command:

```text
cargo test --test mir_goldens --no-fail-fast
```

The focused runtime command is `cargo test --test talk_tests match
--no-fail-fast`.

## 3. Leaf binding and settlement output

### Current owner and shape

`compile_pattern_test_scoped` allocates/reuses `LocalId`s in
`FunctionBuilder::locals`, emits `Copy` for binders, and expands record cells so
`label: pattern` can bind both the label and interior pattern.
`Pattern::collect_binders` and private `pattern_bind_symbols` preserve
source traversal while deduplicating shared or-pattern symbols.

For an owning match, `settle_owned_match` recursively emits the leaf ownership
behavior. Its inputs are `(Pattern, Operand, Ty, through_borrow)`. It:

- marks droppable binder locals with `produce_temp`;
- retains a binder reached through a borrowed layer;
- drops whole/unbound droppable values unless reached through borrow;
- projects tuples, variants, records, and value structs by checked occurrence
  type;
- treats heap projections as borrowed from the object and drops the object once;
- gives a record label binder ownership before settling an interior duplicate
  binder through borrow;
- retests an or-pattern alternative only when alternatives differ in unbound
  owned payload settlement.

The concrete output is emitted retain/drop/projection MIR, updates to
`stmt_temps` and tracked ownership, and `FlowEvent` evidence. There is no
separate leaf product.

### Replacement owner

Decision-tree leaves own ordered binders, whole/destructured/unbound place
classification, projection provenance, transfer relative to the root
scrutinee mode, duplicate-binder order, and continuation. Flat Core consumes
these facts. `OwnershipPlacement` later places the explicit transfers and
drops; MIR never reclassifies a syntax pattern.

### Oracle and renderer

`render_pattern_leaf` uses source binder order and renders each place as
`root[/projection...]`, followed by occurrence type, provenance, root mode,
transfer, and disposition. The normalized ownership-event renderer orders
functions by canonical instance key, blocks by CFG reverse postorder with old
block index as tie-break, and records
`block:index:stream-order:event(local-first-definition-id)`. Existing oracle:

```text
cargo test --test talk_tests run_projections_of_a_borrowed_scrutinee_keep_its_owner_alive -- --exact
cargo test --test talk_tests run_clone_of_an_element_settles_before_its_array_releases -- --exact
```

## 4. Checked occurrence types and GADT refinements

### Current owner and shape

`BodyChecker::check_pattern` records the pre-view type of every pattern node in
`Artifacts::pattern_tys`. Binders therefore retain a `Ty::Borrow`; constructor
and literal inspection views through each occurrence's borrow independently.
Record label binders also receive entries. `check_struct_pattern` records one
`(Ty, Option<NodeID>)` per stored field in declaration order.

`TypecheckSession::finalize` applies `final_ty` to `pattern_tys` and struct
slots. It derives closed-record slots from the finalized row, preserving row
layout order and written field IDs. `Elaboration` publishes these exact shapes
once to `core/build.rs`, which bakes them as:

```text
core::Pattern.ty: Option<ValueTy>
core::PatternKind::Struct.slots: Vec<(ValueTy, Option<field index>)>
core::PatternKind::Record.slots: Option<Vec<(ValueTy, Option<field index>)>>
core::RecordFieldPattern.ty: Option<ValueTy>
```

GADT checking currently owns a transient `PatternRefinement`:

```text
givens: Vec<Predicate>
gadt.params: Vec<Symbol>                       // arm-local skolems
gadt.determined: Vec<(Symbol, Ty)>             // skolem -> enclosing type
```

`check_match_arms_against_known_scrutinee` puts this in an OutsideIn
`Implication`; it is solver input and is not published. The finalized facts
needed downstream nevertheless exist: each payload pattern carries its exact
skolem occurrence type, each variant has its constructor scheme/result in the
catalog, and the scrutinee has its final occurrence type. Current MIR
`arm_refinement_subst` reconstructs `skolem -> concrete outer Ty` from exactly
those facts. `variant_case` already uses field occurrence types rather than
catalog payload declarations.

### Replacement owner

The checked matrix model carries occurrence types, struct/record slots, the
scrutinee type, and constructor identity. P3's focused tests pin these fields;
P4's Core adapter fills them from the finalized checked occurrence. The
pattern compiler performs the existing `collect_case_skolems` plus
result-matching operation once and stores the substitution on the arm leaf.
MIR's reconstruction is deleted at P6. Associated projections use the Core
occurrence type; catalog declarations only identify constructor shape and
relate declared case parameters.

### Oracle and renderer

Types use `Ty::render_mono`; maps sort by `Symbol`; givens and binders keep
source order. `render_pattern_leaf` is the renderer. Existing corpus command:

```text
cargo test -p talk-front --test front_suite gadt --no-fail-fast
```

The full `types_tests::` command remains the differential gate because the
filter above is only a focused convenience.

## 5. Published `Elaboration` and `TypeOutput`

### `Elaboration`

`generate::finalize` is the producer. `CoreProgram::from_checked_asts` is the
only handoff. Clean files consume every relevant entry through
`core::build::TypedTreeBuilder`; blocked files retain the editor slice through
`NodeFacts::from_blocked_elaboration`. No MIR code receives `Elaboration`.

| Field | Shape | Current consumer |
| --- | --- | --- |
| `node_types` | `NodeID -> Ty` | `core/build` expression/parameter types, grafts, synthesized calls; `NodeFacts` for blocked files |
| `instantiations` | `NodeID -> Vec<(Symbol, Ty)>` | expression and synthesized-call fields; blocked `NodeFacts` |
| `field_specializations` | `NodeID -> Vec<(Symbol, Ty)>` | expression/function specialization fields |
| `witness_layouts` | `NodeID -> Vec<(Symbol, Ty)>` | expression witness-layout field |
| `member_resolutions` | `NodeID -> MemberResolution` | member/variant/projection classification and expression fields; blocked `NodeFacts` |
| `selected_callables` | `NodeID -> Symbol` | expression/synthesized-call fields; blocked `NodeFacts` |
| `integer_literals` | `NodeID -> CheckedIntegerLiteral` | canonical Core integer literals and integer patterns |
| `for_plans` | `NodeID -> ForPlan` | `TypedTreeBuilder::elaborate_for` |
| `propagation_plans` | `NodeID -> PropagationPlan` | postfix grafting in `expr_unconverted` |
| `synthetic_floors` | `FileID -> u32` | typed-tree synthesized-ID mint |
| `coerce_clones` | `Set<NodeID>` | `ExprOwnership::auto_clone` and graft overlay |
| `existential_packs` | `NodeID -> ExistentialPack` | expression pack field and graft overlay |
| `into_coercions` | `NodeID -> IntoCoercion` | synthesized ordinary `.into()` Core call |
| `checked_ir` | `NodeID -> CheckedIrKind` | `Core::InlineIRInstruction.kind` |
| `effect_contracts` | `NodeID -> EffectContract` | Core perform and handler nodes |
| `pattern_tys` | `NodeID -> Ty` | Core pattern/record-field occurrence types |
| `struct_pattern_slots` | `NodeID -> Vec<(Ty, Option<NodeID>)>` | Core declaration-order struct slots |
| `record_pattern_slots` | `NodeID -> Vec<(Ty, Option<NodeID>)>` | Core finalized row-layout slots |

P1-P3 do not change `Elaboration`. P4 invokes the compiler once for each
checked Core match and stores `PatternResult` directly on that occurrence.

### `TypeOutput`

`CoreProgram` stores the complete value. `CoreProgram::types()` serves MIR,
ABI, REPL, and compiler drivers; `into_semantic_parts` moves it to the editor
`Workspace`. `interface::module_slice` destructures the exported catalog and
schemes.

| Field | Shape | Production consumers |
| --- | --- | --- |
| `module_id` | `ModuleId` | completion accessibility viewer |
| `catalog` | `TypeCatalog` | Core construction; MIR layout/conformance/effect/glue facts; ABI; interface slicing/import; driver/core/repl; completion, hover, rename, occurrence, requirements, code actions; module/name-resolution import views |
| `schemes` | `Symbol -> Scheme` | Core binder/function construction; MIR entry schemes; interface export; REPL; driver/core; completion, hover, requirements |
| `inferred_param_origins` | `Symbol -> NodeID` | hover provenance |
| `local_tys` | `Symbol -> Ty` | `TypeOutput::binder_ty`, used by Core pattern fallback and completion; hover fallback |
| `display_names` | `Symbol -> String` | REPL and analysis completion/hover/requirements/code-actions rendering |

Replacement ownership is split deliberately: occurrence entries become
mandatory Core fields in C2; program-level catalog/scheme/name facts remain in
the phase-owned program and planner inputs; blocked editor facts remain
`NodeFacts`. No field requires a deferred workstream.

The deterministic Core renderer visits files in `IndexMap` order and nodes in
source/tree order, renders all IDs as `file:local`, sorts map/set-valued semantic
fields, and includes every optional occurrence field explicitly as `missing`
or its value. Existing oracle:

```text
cargo test -p talk-front --test front_suite core_tests:: --no-fail-fast
```

## 6. Source callable index, demand, worklist, and retry

### Current owner and shape

`ProgramBuilder::index_callables` walks every `CoreProgram::files()` and builds:

```text
callables: Symbol -> Callable { CallableBody::{Func,Init}, program, receiver }
globals: Symbol -> (&Expr, program index)
value_instantiations: Symbol -> Vec<Vec<(Symbol, Ty)>>
```

It recursively indexes nested functions and uses `Func::bound_as` for lowered
top-level function bindings. The demand key is:

```text
type Instance = (Symbol, Vec<(Symbol, Ty)>)
```

`ProgramBuilder::demand` looks up the source body, prunes evidence to callable
and protocol-member parameters, grounds free variables, enforces depth 64,
sorts substitution entries by symbol, interns `func_ids: Instance -> FuncId`,
records witness parameters, and pushes `(Instance, FuncId)` onto the LIFO
`worklist`. `drain_worklist` compiles bodies and checks writeback widths.
`entries.rs`, normal call lowering, witness/conformance dispatch, and `glue.rs`
can call `demand` while MIR is emitted.

The retry loop is `mir::build::build`: it reruns the entire `build_pass` until
`effect_specializations: EffectInstance -> MirSymbol` stops growing, bounded by
`INSTANTIATION_DEPTH_LIMIT`. Derived bodies are separately memoized in
`glue`, `equality_glue`, `show_glue`, and `identity_glue` maps and allocate MIR
IDs directly.

### Replacement owner

`MonoPlanner` owns source indexing, canonical keys, roots/worklist, all call,
witness, conformance, handler, static-effect, derived-body, and closure edges,
and deterministic lowering order. `Core<Mono>` stores the closed arena. It has
no `FuncId`, instruction, block, retry, or source-body fallback operation.

### Oracle and renderer

The planner renderer has fixed sections in this order: roots, keys, calls,
witnesses, conformances, handlers, static effects, derived bodies, closure
environments, lowering order. Keys render source symbol plus symbol-sorted
canonical substitution; edges sort by `(source key, source occurrence,
target key, edge kind)`; source-order vectors remain ordered. Existing corpus:

```text
cargo test --test mir_goldens --no-fail-fast
```

Ownership regressions add closure, writeback, cancellation, and derived-drop
reachability not visible in one golden family.

## 7. Ownership sites, events, sequence, release plan, and verifier evidence

### Current owner and shape

`ownership.rs` defines pre-placement inputs:

```text
OwnershipSite { block, seq, index, local, ty, kind, span }
SiteKind = Consume { forced } | Displace | Writeback
ReadSite { block, seq, index, local, name, span }
LoanSite { block, seq, index, root, view, view_name, exclusive }
ProjectionSite { block, seq, index, owner, projection, ty, span }
OwnershipSites {
  sites, reads, loans, projections,
  loan_kills: Vec<(seq, root)>,
  event_seqs: Vec<seq>, next_seq
}
```

`FunctionBuilder::next_ownership_seq` gives sites and events one global walk
order. `record_flow` appends `event_seqs` and:

```text
FlowRecord { block, index, event }
FlowEvent = Def | Use | Move | Drop |
            Anchor | EscapeSink | GlobalMove | GlobalRestore | GlobalUse
```

`elaborate_ownership` computes backward `Liveness`, then runs a separate
forward replay over an index/sequence-sorted agenda. It realizes retains,
moves, displacements, writeback copies, first-dead source-deinit drops, user
diagnostics, and additional `FlowRecord`s. Its join is any-path owned/conflict,
intentionally relying on later release equalization.

`release::plan` calls `verify::entry_states`, replays events, and returns:

```text
Plan {
  end_of_block: Vec<Vec<LocalId>>,
  edges: Vec<(from block, successor position, Vec<LocalId>)>,
  unwind_live: Vec<((block, instruction index), Vec<LocalId>)>
}
```

`emit_plan` builds unwind cleanup tries, inserts exit drops, and splits
normal equalization edges. Finally debug `verify::check` replays the finalized
`FlowRecord` stream with the four-state `ABSENT/OWNED/DEAD/CONFLICT` lattice.
`flow::check` independently consumes non-ownership event variants for anchored
closure escape and linear-global diagnostics.

### Replacement owner

O1 separates explicit pre-placement markers from post-placement
`VerifierEvidence`. O2's one liveness consumes only markers/provenance. O3's
`OwnershipPlacement` owns the complete entry lattice. O4 moves decisions in
the contract's fixed order. O6 leaves one debug balance verifier; flow-analysis
seeds remain flow inputs rather than ownership evidence.

### Oracles and renderers

- Marker renderer: function key, CFG block/index, marker kind, canonical local,
  type/provenance, and source order. Corpus: ownership unit tests.
- Liveness renderer: per block/index canonical local sets for source-use,
  any-use, view birth/root, and settlement. Corpus: ownership unit tests plus
  the two projection/clone regressions.
- Entry renderer: block reverse-postorder, then every lattice component with
  locals sorted. Corpus: `cargo test --lib compiling::mir::build::
  --no-fail-fast`.
- Decision renderer: fixed contract category order, then CFG point and local;
  diagnostics retain source order. Corpus: the ownership gate.
- Evidence renderer: final `Def/Use/Move/Drop` only, at finalized instruction
  positions, canonicalized as described in section 3. Corpus: MIR goldens and
  the ownership gate.

No renderer uses hash iteration or allocated MIR IDs as semantic identity.

## 8. Internal pre-final MIR seam

### Current owner and shape

The exact seam is `FunctionBuilder::elaborate_and_verify`, called by `finish`
after `emit_return` and before `flow::check` and publication. At entry:

- `self.blocks: Vec<BlockData>` has complete normal topology and call/suspend
  instructions, but ownership insertions and unwind targets are not finalized;
- `self.ownership_sites`, `borrow_roots`, `view_locals`, frame declared/owned
  types, init shadows, and `flow_events` still exist;
- `elaborate_ownership`, `release::plan`, and `emit_plan` mutate this into the
  target-final blocks;
- debug `verify::check` runs only after that mutation.

This is the internal place for O1 ownership markers. They can be fields of a
private pre-final function body or explicit internal marker instructions; in
either representation target-final `talk_mir::Function` and MIR goldens stay
unchanged through O4.

### Replacement owner and oracle

A private pre-final MIR body owns blocks plus explicit markers until
`OwnershipPlacement::place` returns finalized blocks and verifier evidence.
`FunctionBuilder::finish` publishes only the latter. Structural marker
verification plus:

```text
cargo test --lib compiling::mir::build:: --no-fail-fast
cargo test --test mir_goldens --no-fail-fast
```

is the existing corpus oracle.

## Differential registry

| Differential | Deterministic renderer | Existing corpus command |
| --- | --- | --- |
| report | `render_match_report` | frontend `types_tests::` |
| decision tree and leaves | preorder tree/leaf renderers | frontend `types_tests::` and `core_tests::` |
| runtime realization | canonicalized `Program::render` | `cargo test --test mir_goldens --no-fail-fast` |
| pattern ownership events | canonical final evidence | two pattern ownership regressions |
| old/new Nested Core | canonical Core renderer | Core gate |
| planner discovery | fixed-section planner renderer | MIR goldens plus ownership regressions |
| family MIR lowering | existing `Program::render` | MIR goldens and focused runtime family |
| ownership markers | marker renderer | ownership unit gate |
| liveness | point/set renderer | ownership gate |
| placement entries | complete lattice renderer | ownership gate |
| ownership decisions | fixed category renderer | ownership gate |
| finalized evidence | canonical final evidence | ownership gate and MIR goldens |

## Path closure

Every input comes from type checking/finalization, checked Core, pre-final MIR,
or the shared CFG. No deferred workstream supplies a type, identity, formatter,
artifact, VM, or editor prerequisite.
