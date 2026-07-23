 Outlining unified target architecture

 Defining comprehensive design target

 MIR semantic-authority cleanup: current problems and desired end state

 Current problems

 ### 1. TypedProgram is not a complete semantic interface

 The typed tree publishes expression types and selected resolution facts, but important constructs remain source-shaped:

 - call arguments retain ArgMode;
 - captures retain CaptureMode;
 - patterns have no checked component types or canonical field resolution;
 - inline IR retains parser instructions and source annotations;
 - callable roles are inferred from tree shape;
 - literals retain source text;
 - MIR still accesses TypeOutput and ResolvedNames.

 This forces MIR to recover information that typing already knew or should have decided.

 ### 2. MIR normalizes frontend identities and types again

 MIR contains:

 - canonical;
 - canonical_ty;
 - canon_rigid;
 - module alias scopes;
 - resolved() and scratch type normalization.

 Specialization legitimately requires rigid substitution and projection reduction. Repairing symbol identity and repeatedly finalizing ordinary node types does not.

 ### 3. Use modes and Copy legality have two authorities

 MIR interprets source argument and capture modes, checks borrow-shaped parameter types, reconstructs writeback, and uses representation properties as semantic evidence.

 In particular, these are incorrectly conflated:

 - no cleanup with Copy;
 - buffer ownership with capture legality;
 - Deinit behavior with source grade;
 - liveness implementation choices with semantic use selection.

 An affine value that needs no runtime cleanup can incorrectly pass checks intended to require Copy evidence.

 ### 4. Pattern semantics are reconstructed repeatedly

 Typing, exhaustiveness checking, and MIR each independently determine:

 - constructor identity;
 - field order;
 - payload types;
 - struct field substitution;
 - record slots;
 - binder types;
 - literal values.

 This already creates concrete divergence:

 - MIR variant payload reconstruction does not preserve all GADT result refinements.
 - MIR struct-field reconstruction does not match the checker's effect-row substitution.
 - Synthesized patterns can fall back to source-name lookup.

 ### 5. Conformance and witness selection is distributed

 MIR performs witness selection for:

 - existential packs;
 - inherited requirements;
 - derived Showable and Equatable implementations;
 - Deinit;
 - protocol defaults;
 - construction;
 - string concatenation;
 - some member calls.

 Only evidence that remains abstract until generic specialization should require late selection. Concrete source decisions are currently being made more than once.

 ### 6. Effects and unsafe operations are checked again

 MIR reloads effect signatures, reconstructs substitutions, validates handler contracts, and identifies some effects through display names.

 unsafe_gate.rs duplicates the type checker's unsafe-effect and lexical masking rules with another whole-tree traversal.

 ### 7. MIR parses and interprets source syntax

 MIR currently:

 - parses or reparses literal text;
 - unescapes strings and characters;
 - lowers source type annotations;
 - compares source type names;
 - interprets parser-shaped inline IR;
 - validates inline IR operands and types.

 This is frontend semantic work rather than CFG or representation lowering.

 ### 8. Callable contracts are inferred from syntax and catalog scans

 MIR discovers callable identity and behavior by:

 - scanning source roots;
 - recognizing let-bound function shapes;
 - searching catalogs for member ownership;
 - recognizing generated initializers using synthesized spans and body shape;
 - independently deriving caller and callee writeback conventions.

 Callable role and contract should not depend on source encoding after typing.

 ### 9. Runtime representation queries are used as source type judgments

 Queries such as:

 - needs_drop;
 - contains_buffer;
 - contains_object;
 - is_linear;
 - donation classification;

 are legitimate when selecting runtime operations. They are not valid replacements for checked Copy, Linear, Borrowed, capture, or conformance judgments.

 ────────────────────────────────────────────────────────────────────────────────

 Desired end state

 Semantic ownership

 ┌────────────────────────┬───────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
 │ Module                 │ Sole responsibility                                                                                                           │
 ├────────────────────────┼───────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┤
 │ Parser                 │ Syntax, source spelling, and spans                                                                                            │
 ├────────────────────────┼───────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┤
 │ Resolver               │ Canonical symbol identity and lexical resolution                                                                              │
 ├────────────────────────┼───────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┤
 │ Type checker           │ Final types, source legality, semantic use modes, patterns, effects, captures, conformances, literals, and trusted operations │
 ├────────────────────────┼───────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┤
 │ TypedProgram           │ Immutable publication of all finalized frontend decisions                                                                     │
 ├────────────────────────┼───────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┤
 │ Backend specialization │ Rigid substitution, projection reduction enabled by substitution, and genuinely deferred requirement evidence                 │
 ├────────────────────────┼───────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┤
 │ MIR generation         │ CFG, places, evaluation order, ownership dataflow, runtime representation, cleanup, and glue                                  │
 ├────────────────────────┼───────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┤
 │ MIR verifier           │ MIR structural and ownership invariants                                                                                       │
 └────────────────────────┴───────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘

 No semantic question has more than one owner.

 TypedProgram is the complete frontend seam

 TypedProgram remains a typed tree with compact declaration indexes and attached semantic facts. It is not a second program representation or a giant checked MIR.

 Its interface guarantees:

 - all symbols have canonical identities;
 - all inference variables have been resolved;
 - node types are finalized;
 - generic nodes may contain declared rigid parameters;
 - every synthesized node has the same fact completeness as a source node;
 - no successful typed node requires backend syntax interpretation;
 - missing semantic facts indicate a compiler invariant failure.

 Node-local facts live on the relevant typed node. Declaration-level facts live in the typed catalog or callable index. MIR has no access to raw checker artifact maps as a fallback.

 Canonical type contract

 Frontend finalization and backend specialization are distinct concepts.

 Frontend types:

 - contain no inference variables;
 - use canonical symbols;
 - contain only declared generic parameters;
 - have all frontend-decidable projections normalized.

 Backend specialization:

 - substitutes declared rigid type and effect parameters;
 - reduces projections made concrete by that substitution;
 - never repairs module aliases or symbol spellings;
 - never reinfers a source expression's type.

 There is no general MIR resolved() operation scattered throughout lowering.

 Checked value uses

 Every value-use edge carries its checked semantic operation:

 - shared borrow;
 - exclusive borrow;
 - consume;
 - proven copy;
 - selected auto-clone;
 - writeback.

 Copy and clone operations include the evidence that made them legal, including conditional generic conformance evidence where applicable.

 MIR does not interpret ArgMode, ReceiverMode, or CaptureMode as semantic instructions. Those source markers exist only for diagnostics and source tooling.

 MIR retains responsibility for how a checked operation is realized:

 - move at last use;
 - retain when another owned use remains;
 - create a borrow;
 - establish and end a loan;
 - materialize a temporary;
 - schedule writeback;
 - report CFG-sensitive ownership violations.

 Runtime liveness chooses an implementation of an already-checked semantic use. It does not choose the semantic use itself.

 Checked captures

 Each closure and effect handler carries:

 - the canonical captured symbol;
 - finalized capture type;
 - checked capture mode;
 - required Copy or clone evidence;
 - whether mutable cell representation is required.

 MIR owns environment layout, cell construction, and runtime ownership. It does not rediscover free variables or determine whether a requested capture is legal.

 Checked patterns

 Every pattern occurrence carries a complete semantic description:

 - occurrence type;
 - borrow-viewed matching type;
 - canonical constructor or variant identity;
 - canonical struct fields and declaration-order slots;
 - instantiated payload or field types;
 - record slots;
 - binder symbols and types;
 - GADT refinements;
 - canonical literal values;
 - source subpattern-to-component mapping.

 Typing, exhaustiveness checking, and MIR consume the same checked pattern semantics.

 MIR owns:

 - decision-tree control flow;
 - discriminant tests;
 - runtime projections;
 - place construction;
 - ownership settlement across alternatives.

 MIR does not resolve pattern names, search catalogs for fields, instantiate payload types, or parse pattern literals.

 Committed conformance evidence

 All evidence decidable during typing is committed in TypedProgram, including:

 - direct member witnesses;
 - substitutions;
 - associated-type bindings;
 - existential dictionary entries;
 - inherited requirement closure;
 - Deinit witnesses;
 - derived-conformance field evidence;
 - protocol-default selections;
 - compiler-generated operation evidence.

 Existential packing contains the exact ordered dictionary contents to emit.

 Derived implementations contain a checked derivation recipe. MIR may generate the body, but it does not prove field conformances again.

 The only late conformance selection is a requirement that remains abstract because its receiver is a rigid generic parameter. That selection occurs once the parameter becomes concrete during specialization. General conformance search is not available to ordinary MIR
 lowering.

 Checked effects

 Each effect call carries:

 - canonical effect identity;
 - selected declaration;
 - finalized type and effect substitution;
 - checked argument uses;
 - result type.

 Each handler carries:

 - canonical handled effect;
 - instantiated parameter types;
 - handled result type;
 - continuation/resume contract;
 - checked captures.

 MIR installs runtime handlers and continuations from these facts. It does not reload signatures, structurally solve generic parameters, or identify effects by display name.

 Unsafe access is fully represented by checked frontend semantics. There is no backend source-level unsafe gate.

 Canonical literals and inline IR

 Typed literals carry canonical values used by MIR:

 - integer value;
 - floating-point value;
 - character value;
 - string bytes or value.

 Source spelling remains available for diagnostics and formatting but is never reparsed by MIR.

 Inline IR reaches MIR as checked, target-neutral semantic operations containing:

 - canonical operation identity;
 - canonical scalar types;
 - validated operands;
 - validated result bindings;
 - checked safety requirements.

 MIR only emits the corresponding MIR operation. It does not lower annotations, compare type names, or validate parser instructions.

 Canonical callable inventory

 TypedProgram directly enumerates every callable with:

 - canonical symbol;
 - owner;
 - semantic role;
 - finalized scheme;
 - receiver contract;
 - parameter use and writeback contracts;
 - body location;
 - specialization parameters.

 Callable roles include:

 - free function;
 - method;
 - protocol requirement;
 - protocol default;
 - constructor;
 - memberwise initializer;
 - derived implementation;
 - compiler-generated entry point.

 MIR does not infer these roles through AST shape, source scans, synthesized spans, or catalog searches.

 Clear separation of source grades and runtime representation

 The type system is the sole authority for:

 - Copy;
 - CheapClone;
 - Linear;
 - Borrowed;
 - capture legality;
 - source-level ownership permissions;
 - protocol conformance.

 MIR representation logic is the sole authority for:

 - whether a value contains managed buffers;
 - whether runtime retain/release is required;
 - memory layout;
 - object and aggregate representation;
 - generated drop and clone glue;
 - whether ownership can be transferred without a runtime retain.

 A runtime representation property never serves as proof of a source type-system property.

 Error ownership

 Frontend diagnostics cover:

 - type mismatch;
 - invalid source use mode;
 - missing Copy or clone evidence;
 - invalid capture;
 - unknown pattern field or variant;
 - invalid effect operation;
 - unsafe access;
 - invalid inline IR;
 - missing conformance;
 - invalid initializer use.

 MIR errors cover:

 - use after move;
 - conflicting live loans;
 - impossible writeback;
 - invalid CFG ownership state;
 - malformed internal typed facts;
 - unsupported runtime representation.

 MIR never emits a second version of a source type error.

 Dependencies absent from MIR

 The clean MIR module has no semantic dependency on:

 - parser instruction types;
 - annotation lowering;
 - raw TypeOutput;
 - raw ResolvedNames;
 - source Name values for selection;
 - source argument or capture modes;
 - literal source parsing;
 - general conformance solving;
 - pattern field or variant lookup by text;
 - source-level unsafe traversal.

 Display names may be supplied separately for diagnostics and debugging, but they are never semantic identities.

 Completion criteria

 The desired result is present when:

 - a successful TypedProgram is sufficient to lower without consulting raw frontend side tables;
 - each source-semantic decision is represented explicitly and has one owner;
 - synthesized and source nodes obey the same completeness invariant;
 - concrete conformance selection never occurs during ordinary MIR generation;
 - specialization is the only backend type-resolution operation;
 - MIR contains no parser or annotation interpretation;
 - pattern semantics are shared by typing, exhaustiveness, and lowering;
 - runtime representation predicates are used only for runtime representation;
 - unsafe_gate.rs and equivalent duplicate validators do not exist;
 - MIR's remaining complexity consists of CFG, ownership, representation, and code generation rather than a partial second type checker.

 MIR deletion inventory

 This is the code that should disappear from the current MIR implementation once the desired semantic interface exists. Functions that still have legitimate lowering responsibilities are listed separately under “delete only the semantic portions.”

 Line numbers refer to the current working tree.

 Delete entire files

 - src/backend/mir/unsafe_gate.rs
     - UnsafeVisitor
     - mentions_raw_ptr
     - all RawPtr and inline-IR unsafe validation
 - Remove mod unsafe_gate and unsafe_gate::check(programs) from src/backend/mir/mod.rs.

 Delete identity repair and repeated frontend finalization

 From src/backend/mir/mod.rs:

 - canonical_ty — line 1437
 - MODULE_ALIASES
 - module_alias_scope — line 1476
 - ModuleAliasGuard
 - impl Drop for ModuleAliasGuard
 - canonical — line 1499
 - FunctionBuilder::canon_rigid — line 4874
 - FunctionBuilder::resolved — line 5053
 - ty_has_var — line 1391
 - ty_has_projection — line 1248
 - ty_mentions_param in its current alias-aware form — line 1409
 - all per-call symbol retagging and dual-spelling dictionary lookups

 The legitimate rigid substitution and projection reduction should exist only in backend specialization, not in these MIR helpers.

 Delete direct frontend side-table access

 From src/backend/mir/mod.rs:

 - FunctionBuilder::types — line 4977
 - Reads of TypeOutput::integer_literals
 - Reads of TypeOutput::member_resolutions
 - Reads of raw program.types() for source-semantic decisions
 - Reads of program.resolved_names() for semantic identity
 - Name-based protocol, requirement, effect, field, or variant discovery

 Current helper implementations to delete:

 - ProgramBuilder::display_name as a ResolvedNames scan — line 2452
 - ProgramBuilder::protocol_named — line 2470
 - ProgramBuilder::variant_names as a raw catalog scan — line 2487
 - ProgramBuilder::field_names as a raw catalog scan — line 2500
 - ProgramBuilder::requirement_symbol as a label lookup — line 2572
 - ProgramBuilder::is_io_effect as a display-name lookup — line 2589

 Display metadata can still exist, but it must not determine semantic identity.

 Delete source type and grade checking

 From src/backend/mir/mod.rs:

 - conforms_to — line 741
 - is_linear — line 832
 - FunctionBuilder::check_copy — line 4984
 - FunctionBuilder::check_captures — line 5286
 - FunctionBuilder::check_capture_list — line 5341

 Delete the stored-borrow source checks from build:

 - struct-field borrow rejection around line 1529
 - enum-payload borrow rejection around line 1546

 Delete all uses of these runtime properties as proof of source legality:

 - needs_drop as a Copy test
 - contains_buffer as a capture or clone-legality test
 - contains_object as a capture-legality test
 - Deinit presence as a grade test

 Retain needs_drop, contains_buffer, and contains_object only where they drive runtime layout, retain/release, or glue.

 Delete source-mode interpretation

 Remove MIR imports and matches involving:

 - ArgMode
 - CaptureMode
 - ReceiverMode when used to infer a checked call contract

 Delete from compile_call_args:

 - ArgMode::Mut validation
 - ArgMode::Copy validation
 - Copy/CheapClone source diagnostics
 - reconstruction of use semantics from parameter types

 Delete from compile_call and compile_indirect_call:

 - checks that mut markers correspond to exclusive borrows
 - checks that borrow markers correspond to borrowing parameters
 - source receiver-mode interpretation
 - “cannot call a mut func through a shared borrow” source validation
 - any inference of consuming versus borrowing behavior from raw function types

 Delete or replace the current:

 - FunctionBuilder::writeback_targets semantic reconstruction — line 4706
 - FunctionBuilder::requirement_is_mut — line 4817
 - caller/callee writeback expectation checks
 - ProgramBuilder::writeback_expectations
 - writeback-convention mismatch diagnostics in drain_worklist

 The runtime code that applies already-checked writebacks remains.

 Delete capture rediscovery

 From src/backend/mir/mod.rs:

 - free_locals — line 907
 - cell_scan — line 964
 - cell_celled_params in its current source-analysis form — line 5315
 - check_captures — line 5286
 - check_capture_list — line 5341
 - source capture-list completeness diagnostics
 - Copy/move/borrow capture legality checks
 - implicit-capture rejection in MIR
 - capture-mode matching in capture_env and compile_closure

 capture_env and compile_closure remain as runtime lowering, but consume checked capture facts directly.

 Delete pattern semantic reconstruction

 From src/backend/mir/mod.rs:

 - pattern_bindings_with_tys — line 1121
 - pattern_bind_symbols — line 1171
 - tuple_element_tys — line 1224
 - FunctionBuilder::record_cells — line 7278
 - FunctionBuilder::struct_cells — line 7360
 - FunctionBuilder::variant_case — line 7467
 - pattern_leaves_owned_unbound in its current type-reconstruction form — line 7225

 Delete pattern uses of:

 - ProgramBuilder::field_types
 - ProgramBuilder::variant_payloads
 - ProgramBuilder::field_index_by_name
 - raw member_resolutions
 - raw integer-literal side tables
 - source field names
 - source variant names
 - source pattern arity checks
 - catalog-based pattern type substitution
 - pattern string/character unescaping
 - pattern integer parsing

 field_types and variant_payloads may remain for runtime layout and glue. Their use for source pattern semantics should disappear.

 Retain:

 - pattern-test CFG generation;
 - discriminant reads;
 - runtime projections;
 - ownership settlement;
 - string comparison;
 - alternative control flow.

 Delete general conformance selection from MIR

 From src/backend/mir/mod.rs:

 - ProgramBuilder::conformance_witness — line 2129
 - ProgramBuilder::conformance_assoc — line 2177
 - ProgramBuilder::deinit_witness — line 2335
 - ProgramBuilder::is_deinit_witness — line 2348
 - ProgramBuilder::deinit_witnesses field
 - concrete calls to satisfied_conformances
 - concrete calls to ty_conforms for source decisions

 From src/backend/mir/glue.rs:

 - the current FunctionBuilder::requirement_closure implementation
 - its conformance-row search
 - its protocol-default fallback search
 - derived-conformance detection by "show" or "equals"
 - associated-type reconstruction
 - requirement lookup by string
 - writeback-width reconstruction from checker schemes

 Delete conformance selection from:

 - heap_teardown
 - drop_value
 - emit_string_concat
 - emit_sub_show
 - emit_equality
 - compile_call
 - compile_existential_pack
 - compile_construction

 Those functions may remain as emitters, but they must consume committed witnesses or checked derivation recipes.

 The only conformance selector retained anywhere in the backend should be the narrow selector for a ViaRequirement made concrete by specialization. The current general-purpose helpers should not survive.

 Delete name-driven derived-glue semantics

 From src/backend/mir/mod.rs and glue.rs, delete:

 - "Add" protocol lookup
 - "add" requirement lookup
 - "show" requirement lookup
 - "equals" requirement lookup
 - protocol-default discovery by requirement label
 - field and variant discovery from raw catalogs
 - recursive leaf-conformance searches

 The following emitters can remain, but their current evidence-selection portions should be deleted:

 - derived_show
 - derived_equality
 - emit_show
 - emit_sub_show
 - emit_equality
 - emit_enum_equality
 - emit_field_equality
 - emit_string_concat

 They should operate from checked derivation recipes and canonical callable identities.

 Delete effect signature reconstruction

 From src/backend/mir/mod.rs:

 - solve_param — line 1369
 - ProgramBuilder::effect_sig — line 2405
 - FunctionBuilder::closure_effects — line 8990
 - the current name-based is_io_effect — line 2589

 Delete from effect-call lowering:

 - effect signature lookup
 - generic parameter structural matching
 - fallback effect instantiation
 - argument-mode validation
 - result-type reconstruction
 - “backend cannot resolve generic effect instantiation” diagnostics

 Delete from handler lowering:

 - handler signature lookup
 - clause parameter type reconstruction
 - handler arity revalidation
 - resume type reconstruction
 - source diagnostics for resume outside a handler

 Keep:

 - capability lookup;
 - IO runtime dispatch;
 - handler installation;
 - continuation construction;
 - resume/discontinue CFG lowering.

 Delete source literal parsing

 From FunctionBuilder::compile_literal and pattern tests:

 - integer parsing fallback
 - float parsing
 - string unescaping
 - character unescaping
 - invalid-literal source diagnostics
 - access to CheckedIntegerLiteral

 compile_literal remains only as canonical-value-to-MIR-constant emission.

 Delete source annotation and inline-IR interpretation

 From src/backend/mir/mod.rs:

 - FunctionBuilder::annotation_value_ty — line 5103
 - FunctionBuilder::annotation_mem_ty — line 5130
 - SimpleName trait — line 9824
 - impl SimpleName — line 9828
 - current string-based arith_op — line 9724
 - current string-based bit_op — line 9744

 Delete from compile_inline_ir:

 - parser-instruction semantic dispatch
 - source type-annotation lowering
 - "RawPtr" type-name checks
 - scalar operation selection from strings
 - comparison-operator validation
 - register-range source diagnostics
 - result-binding type validation
 - inline-IR safety validation

 compile_inline_ir may remain as a small checked-operation-to-MIR emitter. ir_value may remain only as an internal operand lookup without source validation.

 Delete callable discovery and contract reconstruction

 From src/backend/mir/mod.rs:

 - let_bound_func — line 624
 - current ProgramBuilder::index_callables — line 1800
 - index_decl
 - index_func
 - index_nested_funcs
 - index_nested_stmt
 - index_nested_expr
 - index_method
 - index_bound_func
 - ProgramBuilder::method_owner_params — line 2627
 - ProgramBuilder::default_owner_protocol — line 2678
 - callable ownership scans across struct, enum, extend, and protocol catalogs
 - initializer-role recognition through Span::SYNTHESIZED
 - source-tree recognition of let name = func
 - caller/callee contract reconstruction

 ProgramBuilder may still copy a published callable inventory into backend storage, but it should not discover callables by traversing source syntax.

 Also delete files_in_initialization_order if initialization order is published by program assembly rather than reconstructed from typed imports.

 Delete source validation from retained lowering functions

 These functions remain, but the listed branches should disappear.

 ### compile_stmt

 Delete source diagnostics for:

 - break outside a loop
 - continue outside a loop
 - resume outside an effect handler
 - invalid assignment targets
 - statically invalid assignment shapes

 ### compile_expr

 Delete source diagnostics and recovery for:

 - invalid tuple indexes already rejected by typing
 - invalid member targets already rejected by typing
 - malformed source borrow/copy modes
 - clone legality
 - generic effect inference
 - source-level raw-storage restrictions
 - semantic constructor errors

 CFG-sensitive use-after-move, loan, and invalidated-view checks remain.

 ### compile_match and compile_pattern_test

 Delete:

 - pattern arity validation
 - unknown fields and variants
 - pattern type reconstruction
 - pattern literal parsing
 - unsupported source-pattern diagnostics

 Runtime branch construction remains.

 ### compile_call_args, compile_call, compile_indirect_call

 Delete:

 - source mode checking
 - parameter-mode inference
 - requirement mutability lookup
 - concrete witness selection
 - associated-type reconstruction
 - source receiver legality checks

 Call emission, specialization demand, argument evaluation, and checked writeback execution remain.

 ### compile_existential_pack

 Delete:

 - requirement closure discovery
 - dictionary slot reconstruction
 - conformance selection
 - associated-type reconstruction
 - source-level existential escape diagnostics
 - missing-evidence recovery

 Payload storage and emission of the already-described witness table remain.

 ### install_handler

 Delete:

 - effect signature lookup
 - parameter type reconstruction
 - arity revalidation
 - source handler diagnostics

 Runtime handler and continuation construction remain.

 ### compile_construction

 Delete:

 - initializer-role discovery
 - owner parameter reconstruction
 - initializer conformance selection
 - field-count semantic validation
 - synthesized-span checks
 - source constructor legality diagnostics

 Allocation and checked field initialization remain.

 Delete obsolete imports and fields

 Expected removals include:

 - crate::node_kinds::call_arg::ArgMode
 - crate::node_kinds::func::CaptureMode
 - source ReceiverMode in callable contracts
 - source type-annotation imports used only by inline IR
 - parser inline-IR operation imports
 - CheckedIntegerLiteral
 - raw checker artifact accessors
 - deinit_witnesses
 - writeback_expectations
 - alias-map state
 - any MIR field whose only purpose is semantic fallback or source diagnostic recovery

 Code that should explicitly remain

 To avoid deleting legitimate MIR responsibilities:

 - contains_buffer, contains_object, needs_drop for runtime representation only
 - field_types and variant_payloads for runtime layout and glue only
 - rigid specialization substitution
 - late ViaRequirement resolution after specialization
 - consume_operand, move/retain selection, and liveness
 - loan and invalidated-view tracking
 - release planning
 - CFG construction
 - pattern decision control flow
 - runtime field and payload projection
 - existential storage and dictionary emission
 - retain/drop/heap teardown generation
 - MIR ownership verification

 The intended result is not the deletion of type-driven MIR generation. It is the deletion of every MIR path that decides, validates, or rediscovers source semantics.

────────────────────────────────────────────────────────────────────────────────

Implementation status (2026-07-22)

Eight stage-1 slices are implemented, full suite green after each. Line numbers in the deletion inventory above predate these changes.

### Completed

1. **unsafe_gate.rs deleted** (whole file plus `mod`/`check` wiring). The checker already owns the rule through the intrinsic `'unsafe` effect: `require_unsafe` in `types/generate/expr.rs` demands it for inline IR and RawPtr-mentioning types, and `@unsafe { ... }` masks it via `enter_effect_mask`. Two checker pinning tests added: a RawPtr escaping as an `@unsafe` block's result, and a nested function escaping the block (its `'unsafe` stays in its scheme, so outside call sites still fail). Note: calling an `'unsafe`-schemed function *inside* `@unsafe { }` is legal in both the old gate and the effect system — the invariant is that the effect stays in the nested function's scheme, not that nested bodies are checked lexically.

2. **`break`/`continue` outside a loop → checker-owned** via `Ctx.in_loop` (reset by `enter_function`, set by `enter_loop()` at `Loop`/`For` bodies in `types/generate/stmt.rs`), reported through `unsupported()`. `'continue` outside a handler was already checker-owned (`ctx.handler_ret`). The three MIR source diagnostics are downgraded to invariant assertions — errored files never reach lowering (`error_diagnostic_files` blocks them from the TypedProgram).

3. **`copy` marker legality → checker-owned evidence.** All call-arg loops in `types/generate/call.rs` record marked args; finalize validates Copy-or-CheapClone via `coerce_kind_application`/`bounds_coerce_kind` (borrow-peeled, tuple-componentwise), reporting `NotConforming { protocol: "Copy or CheapClone" }`. MIR's `needs_release && !CheapClone` check in `compile_call_args` is deleted — that check was this ADR's §3 conflation (an affine value needing no cleanup passed a check meant to require Copy evidence). The reference corpus matches `.error` fragments case-insensitively, so `copy_marker_on_non_cloneable_errors` now rejects at typing with no pin change.

4. **Canonical literals.** `typed_ast::Literal` is now `Int(i64)`, `Float(FloatValue)` (a bit-equality newtype), `String`/`Character` (unescaped); `PatternKind::LiteralInt(i64)`/`LiteralFloat(FloatValue)` likewise. The typed-program build canonicalizes: integers from the checker's LIT-01 side table (an `Invalid` entry is unreachable because errored files are blocked); float parsing and unescaping are infallible because the lexer validates escapes at scan time and only produces parseable float spellings. MIR's `compile_literal` is pure value→constant emission; all backend parsing, unescaping, and `CheckedIntegerLiteral`/`integer_literals` access is deleted.

5. **`Symbol::Io` and `Symbol::Add` pinned as well-known core symbols** at resolver mint time (`well_known_core_effect` added for effects; `Add` joined `well_known_core_protocol`; ids: `Io` = Effect `u32::MAX - 1` (`Unsafe` holds `u32::MAX`), `Add` = `WELL_KNOWN_CORE_ADD_ID = u32::MAX - 21`). MIR's `is_io_effect` display-name scan and `protocol_named` catalog scan are deleted. Core is compiled in-process (OnceLock, no disk cache), so symbol-id changes need no cache flush.

6. **Frame facts published (checked captures, structural half).** `typed_ast::Block.frame: Option<FrameFacts>` carries `captured` (free frame-local variables in first-use order — the environment layout), `celled` (assigned ∩ nested-referenced, assignment conversion), and `nested_refs` (letrec decision). Computed once by `frame_facts()` in the typed-program build and set at the three frame roots: `func()`, `DeclKind::Init`, `StmtKind::Handling` (clause parameters live on `block.args`). Interior and synthesized blocks carry `None`. MIR's `free_locals` and `cell_scan` are deleted; the surviving `frame_uses()` walker is depth-0 use counting only — a liveness input, which this ADR retains in MIR. Two correctness points: (a) consumers filter published `captured` by creation-site locals (`FunctionBuilder::live_captures`) because `capture_env` filters by locals while `bind_env` indexes the list raw — both sides must consume the same filtered vec; (b) the static free-variable computation must filter bound symbols at the END of the walk, not incrementally — a hoisted func-valued `let` is referenced before its binding pattern is visited.

7. **`mut`/`borrow` marker agreement → checker-owned.** The marker recording generalizes through `MarkedSlot`: `Param(ty)` where the parameter type is in hand (checking-mode paths), `CalleeIndexed { callee, index, arg_count, arg_ty }` through unresolved callees (member calls, in-flight constructions), resolved at finalize by right-aligned indexing of the callee's solved function type (member types may exclude the receiver). New `TypeError::ArgMarkerMismatch`. MIR's marker-agreement block in `compile_call` is deleted. Design gotcha that cost a debug cycle: validating the *argument's own inferred type* for `mut` markers is wrong — an owned `Int` argument never unifies into a `&mut Int` slot because application auto-borrow is a solver rule, not unification, so member-call `v.bump_by(mut step)` false-errors under that scheme.

8. **Variant-pattern resolution baked on the typed tree.** `typed_ast::PatternKind::Variant` gains `resolved: Option<Symbol>` (typing's `Direct` member resolution, baked at build; `None` only on for-elaboration synthesized patterns, which resolve from the scrutinee type as before). `variant_case` consumes it, removing the last raw `TypeOutput` read inside function lowering; the `FunctionBuilder::types` accessor is deleted. (`glue.rs`'s `program.types()` read remains — it belongs to the conformance-evidence slice.)

9. **Effect-call instantiation and clause binder types → published facts.** The perform-site structural fallback (`solve_param` over declared-vs-payload types) and its "backend cannot resolve generic effect instantiation" diagnostic are deleted: typing instantiates every generic effect perform and records it (`instantiations[expr.id]`), so the recorded substitution is authoritative and a miss is an invariant failure. `solve_param` itself is deleted. On the handler side, the checker now publishes each clause binder's checked type on its parameter node (`node_types[arg.id]` in the `Handling` arm), so the typed tree's `Parameter.ty` is always `Some` for clause binders; `install_handler`'s `declared_params` reconstruction from `effect_sig` is deleted (the signature is consulted only for its generics, which drive witness-block layout). Side effect worth noting: the published binder types are more precise than the old reconstruction, and `move_inside_handler_body_is_may_moved_after` — a reference-adjudicated accept we previously rejected fail-closed — now compiles and runs, so it moved off `KNOWN_STRICTER` and its pin is enforced (that list may only shrink, by design). `effect_sig` itself remains for generics/witness layout until effect calls carry a full published contract.

10. **Checked inline IR.** Typing now validates every inline-IR instruction and publishes a checked, target-neutral operation (`TypeOutput::checked_ir`, baked onto the typed tree): a closed `IrScalarOp` set with checker-validated scalar/operation combinations (including `Bool` comparisons limited to equality and `add RawPtr` as pointer arithmetic), validated `IrCmp` operators, and index-checked `IrOperand`s. Type-carrying operations (`alloc`/`load`/`store`/`swap`/`take`/`retain`/`gep`) carry a checked frontend `Ty` rather than a static memory kind — a generic annotation substitutes per instance during backend specialization, and memory-kind selection (`mem_ty_of`) from the substituted type is lowering's representation work, both retained by design. `compile_inline_ir` is now a checked-op emitter; deleted from MIR: `SimpleName`, string-based `arith_op`/`bit_op` and their `Arith`/`Bit` enums, `annotation_value_ty`/`annotation_mem_ty`, `TokenKind` comparison interpretation, `"RawPtr"`-by-name checks, operand/register validation, and the parser inline-IR imports. The checked types live in `types::output` (the `ExistentialPack` precedent) so both `typed_ast` and the backend consume one definition.

11. **Effect contracts published; `effect_sig` deleted.** Both effect sites now carry a checked `EffectContract` (declared parameter types with rigid generics as `Ty::Param`, plus the type-generic list that fixes the hidden witness-block layout): the checker records it at every perform (`CallEffect` arm) and every handler (`Handling` arm, empty when the signature is unknown — the arity error blocks real programs), published through `TypeOutput::effect_contracts` and baked onto `ExprKind::CallEffect` and `StmtKind::Handling`. `ProgramBuilder::effect_sig` (the per-program catalog scan with `canonical` stamping) and `type_param_symbols` are deleted, along with the perform site's dual-spelling instantiation lookup — the contract's generics and the recorded instantiation keys are both checker-minted, so their spellings agree by construction. `closure_effects` remains: it reads the closure's checked function-type effect row (a published fact); its `canonical()` stamp belongs to the identity-repair slice.

12. **Checked pattern occurrence types (checked patterns, part 1).** Every pattern occurrence checked by `check_pattern` publishes its type (`TypeOutput::pattern_tys`, pre-view so binders keep their borrows; record-field slots keyed by the field node; match-arm roots recorded at the `check_pattern_viewed` call site). Baked onto the typed tree as `Pattern.ty` and `RecordFieldPattern.ty`. Plain `let` binders never pass through `check_pattern` — locals bind via the monomorphic environment and top-level binders via schemes — so the typed-tree build falls back to the symbol's published type (`binder_ty`, then `schemes`); this is a build-time read of published tables, not a MIR fallback. Consumers converted: `pattern_bindings_with_tys` no longer walks the initializer type or looks up row fields by source name — it reads baked types (this had been the "synthesized patterns fall back to source-name lookup" divergence); the three pattern-site `tuple_element_tys` calls now read baked element types with per-instance substitution. `tuple_element_tys` survives only for the tuple-*expression* site, which decomposes a checked expression type (not pattern reconstruction). Found the hard way: registering globals from baked types leaks if top-level binders lack them — the fallback chain is load-bearing, pinned by `run_initializes_globals_for_named_entries`.

13. **Struct-pattern slots (checked patterns, part 2a).** `check_struct_pattern` publishes one slot per stored field in declaration order — the instantiated field type (the same substitution the sub-patterns check against, effect-row splice included, fixing the "MIR struct-field reconstruction does not match the checker's effect-row substitution" divergence) and the covering written sub-pattern (`TypeOutput::struct_pattern_slots`, baked onto `PatternKind::Struct` as `slots: Vec<(Ty, Option<usize>)>` with node ids translated to field indices at build). `struct_cells` now builds its cells from published slots with per-instance substitution; its catalog field-type instantiation (`field_types`), declaration-order reconstruction, and source-name matching are deleted. Only the heap flag — object versus value representation — still reads the layout catalog, which the ADR retains.

14. **Variant payload types from checked occurrence types (part 2b).** `variant_case` no longer calls `variant_payloads` — payload types are the payload sub-patterns' baked occurrence types with per-instance substitution, i.e. the checker's actual per-occurrence instantiation, GADT refinements included (the "MIR variant payload reconstruction does not preserve all GADT result refinements" divergence). `field_types`/`variant_payloads` now serve only drop/equality glue, teardown, construction, and IO-request layout — the "runtime layout and glue only" line the ADR draws. Remaining in part 2c: `record_cells` (row decomposition of a checked type plus label matching — the mildest reconstruction) and the string-pattern `field_index_by_name` reads of core String layout.

15. **Record-pattern slots (checked patterns, part 2c — patterns complete).** Row layout order is only fixed after solving, so record slots assemble at finalize: the checker records each record pattern's written labels and field nodes at generation; finalize reads the pattern's finalized occurrence row (closed, all-named — open or unresolved rows publish nothing) and produces the slot table (`TypeOutput::record_pattern_slots`), baked onto `PatternKind::Record` as `slots: Option<Vec<(Ty, Option<usize>)>>`. `record_cells` now consumes the table — the pun/`label: _` folding stays (it interprets written field *kinds*, not names), but the row decomposition and label matching are gone; a missing table is the open-row unsupported case. With this, the ADR's checked-pattern publication is done: occurrence types, binder types, constructor identity, struct slots, variant payload types, and record slots all come off the typed tree. What remains in MIR for patterns is exactly the retained list — decision-tree control flow, discriminant tests, runtime projections, place construction, ownership settlement — plus the string-pattern `field_index_by_name` reads of core String's well-known layout (a runtime-layout query, retained under the layout line, though it could someday become well-known slot constants).

16. **Conformance evidence stage A: the committed Deinit index.** Approved design: dictionaries belong to conformance rows, not use sites — complete each row once at typing, publish row references, and keep one narrow post-specialization dereference (the GHC/Swift shape: dictionaries at instances, witness tables per conformance descriptor). Stage A lands the channel: `TypeCatalog::deinit_rows` (head → committed row ids, a derived index rebuilt after merge — row ids shift across merge's value-dedup, so id-keyed indexes must rebuild, not merge) plus `committed_conformance(id, head, args)`, the narrow dereference: match one row, no search, no overlap arbitration, with the row's context verified per application. `deinit_witness` and the drop-sharing probe now dereference instead of calling `satisfied_conformances`; typing rejects protocol-head `Deinit` rows (they cannot commit per family; fail-closed, previously unexercised).

    **Design correction learned here, binding on stages B–F:** conditional conformances are an adjudicated ADR 0036 feature — `extend<T> Box<T>: Deinit where T: Marker` is evidence exactly where its context holds, pinned by `conditional_deinit_row_requires_its_context`. The original "no context re-proof" phrasing was wrong: a where-clause over a rigid parameter is abstract until specialization, so context verification at the dereference IS the sanctioned late selection, not a re-proof. Row completion in stage B must therefore keep completed dictionaries per row and verify context at dereference — never assume presence-in-index equals applicability.

17. **Conformance evidence stages B–F: committed dictionaries end-to-end.** Typing completes every conformance row with an ordered dictionary at collection (`TypeCatalog::commit_dictionaries`, run after collection and re-run after merge): one `DictionaryEntry` per protocol requirement in declaration order — `Implementation { symbol, writeback_width }` for a declared witness or the protocol's default body, `Derived(recipe)` for a derivable protocol's bodyless requirement. The writeback width is computed once at requirement collection (`Requirement::writeback_width`, exclusive-borrow parameter count of the declared signature, receiver included). Derived conformances have no row; their dictionaries come from `derived_dictionary`, the recipe registry keyed by well-known protocol identity — `Showable`/`Equatable` joined the well-known core symbol pins, the name-based `derivable` registration and the `derivable` catalog field are deleted, and the solver/member/completion consumers read `derived_recipe`/`derivable_protocols`. Registration is not applicability: whether a type actually derives stays the solver's structural judgment (`try_derive`), and conditional rows still verify context at dereference (the slice-16 lesson).

    Lowering now reaches every late selection through two functions that read committed entries: `conformance_dictionary` (whole table: the selected row's entries + evidence substitution, or the derived-recipe entries; fails closed if a row's entry count does not match the protocol's requirement count — the witness-table slot contract) and `forced_witness` (one entry at a requirement label's slot). Converted sites: existential packs, effect re-perform dictionaries, the `compile_call` ViaRequirement dereference, protocol-init construction, string-concat glue, and the show/equality glue recursion. Deleted from MIR: `conformance_witness`, `conformance_assoc`, the name-based `"show"`/`"equals"` derived detection in both `requirement_closure` and `compile_call` (typing publishes the recipe; lowering never guesses from a label string), the protocol-default guessing fallback, and `requirement_closure`'s declared-writeback schemes scan (entries carry the width). Exactly one conformance search remains in the backend — the `satisfied_conformances` call inside `conformance_dictionary` — and coherence makes its answer forced. Runtime pins added: derived show and default `notEquals` dispatched through a generic (`generic_dispatch_reaches_derived_and_default_entries`).

    **Stage C deviation, flagged for review:** the approved plan's "extend ExistentialPack with a row reference" is intentionally not implemented. Per-node `ConformanceId`s do not survive the backend's catalog merge — merge dedups rows by value precisely because the same row carries different ids through different import paths, which is also why MIR ignores the `row` field `MemberResolution::ViaConformance` already publishes. Publishing entries-plus-substitution on the pack fact instead would add a second pack path without deleting the late one (late-concrete packs still need it). C's substance landed elsewhere: pack tables are built from committed entries in the published per-protocol requirement order, and C's open question resolved — witness tables contain only the protocol's own requirements (no super-closure), so the published order is exactly `ProtocolInfo::requirements` order. If a typed pack commitment is still wanted, it needs the ViaConformance shape (facts, not ids) and should be its own slice.

18. **Canonical callable inventory (design session 2026-07-23; five decisions, all landed).** The systemic root was the backend reconstructing the *callable contract* from syntax; each decision moved to a frontend publication, and the backend's remaining walk is a role-free body binder.

    - **Owner-binding index** (`TypeCatalog::callable_owners`, committed after collection and rebuilt after merge like the other derived indexes): member symbol → `OwnerBinding::Nominal { params }` (struct/enum members; inherent extend members carry the row's own binders) or `OwnerBinding::Protocol(symbol)` (requirement defaults). `check_all`'s rigid compilation reads it; `method_owner_params` and `default_owner_protocol` — per-query scans over every catalog — are deleted.
    - **`Requirement::mut_receiver` published** at requirement collection (first parameter exclusive-borrow, signatures being self-prepended). MIR's `requirement_is_mut` is now a catalog read; the per-program schemes scan is deleted, and `requirement_symbol` (its last dependency) with it.
    - **Callable contract facts baked on the typed `Func` node** — the annotated-tree shape rather than a parallel symbol-keyed map, since every fact is per-node: `Func::receiver` (the declared receiver mode, stamped by the typed-program build from the enclosing `Method`) and `Func::bound_as` (the binding symbol of the top-level `let name = <func>` desugar — the callable's identity for calls and entry selection, stamped at root construction). MIR's `index_*` family survives only as a structural body binder reading baked facts: `let_bound_func` recognition is deleted (readers gate on the stamp via `bound_func`), `index_method`/`index_bound_func` collapse into one `index_func`, and the memberwise-init role comes from symbol identity (`Symbol::Synthesized` — only the resolver's memberwise synthesis mints one that reaches `StructInfo::inits`) instead of the `Span::SYNTHESIZED` sentinel + arity coincidence.
    - **Initialization order published by program assembly**: `TypedProgram::from_checked_asts` orders `files()` dependency-first (imports hoist ahead of the importer, discovery order otherwise, cycles break at the back edge) — the published order every consumer iterates. MIR's `files_in_initialization_order` (path-stem re-derivation of the import graph) is deleted; the entry builders iterate `files()`.
    - **Writeback-width single-sourcing investigated and rejected for now**: the callee derives its writeback params from *instance-resolved* types (`fx.resolved(ty)`), so a scheme-level published width is only sound if substitution can never introduce an exclusive borrow into a parameter slot — unproven. The caller/callee cross-check therefore stays (both sides derive from instance-level types today and the drain-time check is the guard); dictionary entries' declared widths (slice 17) are unaffected, since a requirement's convention is fixed by its declaration.

    Not done, deliberately: hoisting declaration bodies out of the tree into an owned inventory (the rustc bodies-map shape). Expression-position functions must stay inline regardless (they are values with capture environments), so the hoist cannot be uniform; the binder walk survives until that restructure is worth it on its own.

### Deferred, with reasons

- **`check_captures` / `check_capture_list`**: these are representation-based v1 gates (`contains_buffer`/`needs_release`), not duplicate source validation. Replacing them with checker-side Copy evidence would change language semantics in both directions: it would reject plain non-Copy structs whose captures pass today, and admit CheapClone captures (e.g. String) that need closure drop glue that does not exist yet. Their deletion belongs to the capture-evidence feature wave; until then they are legitimate "unsupported runtime representation" errors under this ADR's error ownership.

- **"cannot call a `mut func` through a shared borrow"** (`compile_call`): implemented as a place-chain judgment (`chain.base`'s type) and pinned by `rejects_mut_receiver_call_through_field_of_shared_borrow`. Moving it to the checker means enforcing receiver permissions in typing — receiver checking is currently perm-lenient, and making it strict without false positives across owned/borrowed/celled receivers is real borrow-typing design. Needs a dedicated session, not a side effect of cleanup.

- **`writeback_expectations` cross-check**: caller and callee both derive the convention from instance-level types (the callee from `resolved` parameter types, callers from the resolved call-site type), and the drain-time check guards their agreement. A single published width would have to be scheme-level, which is only sound if substitution can never introduce an exclusive borrow into a parameter slot — unproven (slice 18's finding). Keep until that proof or a per-instance publication exists. (`requirement_is_mut`'s schemes scan, formerly listed here, was deleted in slice 18 — it reads `Requirement::mut_receiver` now.)

- **Invalid assignment targets**: no MIR change needed. The parser owns rejection of non-place targets (`(x+1) = 2` and `f() = 2` do not parse — "expected lhs"/`CannotAssign`), consistent with this ADR's ownership table. MIR's remaining assignment arms are ADR-0037 "not supported yet" markers, not duplicate validation.

- **`check_copy`** (the misleadingly named wave-2 gate): a representation-support gate ("values of type X are not supported yet"), legitimate under MIR's "unsupported runtime representation" error category until the representation waves land. Not a Copy-semantics check despite its name; do not delete as part of grade-checking cleanup.

### Suggested next slices

The approved conformance-evidence design (2026-07-23) is fully landed: stage A (slice 16), stages B–F (slice 17, with E folded into B's entry shape and the stage-C row-reference deviation recorded above). What remains of conformance in MIR is the retained list — the single forced dereference, witness-table emission, derived-glue synthesis (`emit_show`/`emit_equality`, runtime representation work), and the deferred `writeback_expectations` cross-check + `requirement_is_mut` pair, which dissolve only with the published callable inventory.

Stage 1, the checked-patterns publication, committed conformance evidence, and the callable-inventory publications are complete (18 slices). What remains is the identity-repair deletion (`canonical`, `canonical_ty`, `MODULE_ALIASES`, `resolved`, `canon_rigid`, `ty_has_var`/`ty_has_projection`/`ty_mentions_param`, `closure_effects`' stamping) — deliberately last, since every earlier slice reduced the number of places identity repair is load-bearing. It needs its own design pass; the deferred list above records the semantic traps already identified.
