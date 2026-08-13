//! Bidirectional constraint generation and the per-binding-group driver.
//!
//! Structure follows OutsideIn(X) (JFP 2011): one walk per binder body
//! *generates* constraints (it never solves), then `solve` runs exactly once
//! per SCC binding group, then the group generalizes and its constraint state
//! is dropped. Binding groups and their monomorphic-recursion treatment
//! follow THIH (Mark P. Jones, *Typing Haskell in Haskell*, Haskell Workshop
//! 1999, §11.6.3) — recursion types against the group's monomorphic skeleton,
//! and a nominal type's methods/initializers check as members of the
//! nominal's own group.
//!
//! The infer/check mode split is bidirectional typing in the sense of Pierce
//! & Turner (*Local Type Inference*, TOPLAS 2000; survey: Dunfield &
//! Krishnaswami, ACM CSUR 2021): `check_expr` pushes expected types inward
//! where the syntax allows, everything else infers and emits an equality.
//! `Never` acts as bottom at joins only (Pierce & Turner joins).
//!
//! Local lets are NOT generalized (OutsideIn(X) §4.2, "let should not be
//! generalized" — GHC's MonoLocalBinds); generalization happens only at
//! top-level binding groups, value-restricted per Wright (*Simple Imperative
//! Polymorphism*, 1995) via `is_syntactic_value` + `mutated_symbols`.
//!
//! Each function body carries an ambient effect row; calls unify the callee's
//! latent row with it (Koka's application rule, Leijen MSR-TR-2013-79).
//! Deviation from Koka's row-typed algebraic-effects work: closed effect
//! annotations are checked as bounds at declaration sites, so arrow rows under
//! inference stay open.
//!
//! Member access on a known head resolves directly against the catalog;
//! methods are self-prepended functions, so `recv.m(args)` checks the full
//! signature against `(recv, args...)` (the dictionary-free reading of
//! Wadler & Blott's method lookup for the nominal case). Member access on a
//! head that is still a variable becomes a scheme-carried `HasMember`
//! predicate (Gaster & Jones 1996), retried at each instantiation.

use std::ops::ControlFlow;

use indexmap::IndexMap;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::ast::{AST, NameResolved};
use crate::front::source::Source;
use crate::front::module::ModuleId;
use crate::diagnostic::{AnyDiagnostic, Diagnostic, Severity};
use crate::label::Label;
use crate::name::Name;
use crate::name_resolution::name_resolver::ResolvedNames;
use crate::name_resolution::symbol::{Symbol, Symbols};
use crate::node::Node;
use crate::node_id::NodeID;
use crate::node_kinds::func_signature::FuncSignature;
use crate::node_kinds::generic_decl::GenericDecl;
use crate::node_kinds::{
    block::Block,
    body::Body,
    call_arg::CallArg,
    decl::{Decl, DeclKind},
    expr::{Expr, ExprKind},
    func::{EffectSet, Func},
    generic_arg::{GenericArg, StaticExpr, StaticExprKind, StaticOpKind},
    match_arm::MatchArm,
    parameter::{ParamMode, Parameter},
    pattern::{Pattern, PatternKind, RecordFieldPatternKind},
    stmt::{Stmt, StmtKind},
    type_annotation::{AnyAssocBinding, TypeAnnotation, TypeAnnotationKind},
    where_clause::{WhereClause, WherePredicateKind},
};
use crate::types::Level;
use crate::types::catalog::{
    Conformance, ConformanceId, Enum, MemberOwner, ProtocolApplication, ProtocolInfo, Requirement,
    StructInfo, TypeAliasInfo, TypeCatalog, Variant,
};
use crate::types::constraint::{Constraint, CtOrigin, CtReason, Implication};
use crate::types::error::TypeError;
use crate::types::output::{
    CheckedIntegerLiteral, ExistentialPack, ForPlan, MemberResolution, PropagationPlan, TypeOutput,
};
use crate::types::solve::{Generalizer, Solver, TyNode, VarStore, normalize_ty};
use crate::types::ty::{
    EffTail, EffectEntry, EffectRow, Perm, Predicate, ProtocolRef, Row, RowTail, Scheme,
    SchemeParam, StaticInt, StaticValue, Ty, TyFold,
};
use crate::types::variant::VariantInstantiation;

/// The level at which top-level binding groups solve; their skeletons and
/// body variables live above it so generalization (base = OUTER_LEVEL)
/// catches exactly them (Rémy 1992 levels).
const OUTER_LEVEL: Level = Level(0);
const GROUP_LEVEL: Level = Level(1);

pub fn check_types(
    asts: &IndexMap<Source, AST<NameResolved>>,
    symbols: &mut Symbols,
    resolved: &ResolvedNames,
    modules: &crate::front::module::ModuleEnvironment,
    module_id: ModuleId,
    shared: &mut crate::front::source::SharedCatalog,
) -> (
    TypeOutput,
    crate::types::output::Elaboration,
    Vec<AnyDiagnostic>,
) {
    // The compilation's ONE fact table (ADR 0053): seed any imported
    // slices it hasn't seen (import order — deterministic), then hand the
    // whole table to this module's session. The session's output carries
    // the evolved table back (and a copy outward on `TypeOutput`, until
    // the backend and the cache stop wanting per-program catalogs).
    for module in modules.all_modules() {
        shared.seed(module);
    }
    let catalog = std::mem::take(&mut shared.types);
    let mut schemes: FxHashMap<Symbol, Scheme> = FxHashMap::default();
    for module in modules.all_modules() {
        schemes.extend(module.types.schemes.clone());
    }

    let (output, elaboration, diagnostics) = TypecheckSession {
        resolved,
        modules,
        symbols,
        module_id,
        store: VarStore::default(),
        catalog,
        diagnostics: DiagnosticSink::default(),
        schemes,
        mono: FxHashMap::default(),
        artifacts: TypeArtifacts::default(),
        wanteds: vec![],
        self_types: vec![],
        deferred: vec![],
        pending_force_unwraps: vec![],
        type_aliases: FxHashMap::default(),
        alias_stack: vec![],
        level: GROUP_LEVEL,
    }
    .run(asts);
    shared.types = output.catalog.clone();
    (output, elaboration, diagnostics)
}

/// An `extend` block whose member bodies are checked after all binding
/// groups (witness signatures come from the protocol requirement, so users
/// never depend on this ordering).
struct ExtendWork<'a> {
    self_ty: Ty,
    context: Vec<Predicate>,
    decl: &'a Decl,
    protocols: Vec<ProtocolRef>,
    rows: Vec<(ProtocolRef, ConformanceId)>,
}

#[derive(Clone)]
struct TypeAliasDef {
    rhs: TypeAnnotation,
    owner: Option<Symbol>,
    exportable: bool,
}

#[derive(Clone, Default)]
struct DeclaredSchemeContext {
    params: Vec<SchemeParam>,
    param_nodes: Vec<(Symbol, NodeID)>,
    predicates: Vec<Predicate>,
}

/// Record inference-minted parameters' origin nodes and suggest display
/// names from the source binding each parameter was minted for (a param
/// inferred from `value` renders as `Value`). Shared by the group
/// generalization and the per-field (rank-N) generalization.
fn publish_inferred_param_names(
    generalizer: &Generalizer<'_>,
    resolved: &ResolvedNames,
    artifacts: &mut TypeArtifacts,
) {
    for (&param, &origin) in generalizer.inferred_param_origins() {
        artifacts.inferred_param_origins.insert(param, origin);
        if let Some(source_name) = resolved.symbols_to_node.iter().find_map(|(symbol, node)| {
            (*node == origin
                && matches!(symbol, Symbol::ParamLocal(_) | Symbol::PatternBindLocal(_)))
            .then(|| resolved.symbol_names.get(symbol))
            .flatten()
        }) {
            let mut chars = source_name.chars();
            if let Some(first) = chars.next() {
                let suggested = first.to_uppercase().collect::<String>() + chars.as_str();
                artifacts.display_names.insert(param, suggested);
            }
        }
    }
}

/// Attach a binder's declared context to its freshly generalized scheme
/// and publish the result: declared predicates lead the inferred
/// qualified context, quantified parameters' conformances land in
/// `catalog.param_bounds` (typing publishes, lowering reads them to
/// thread a rigid compilation's dictionaries — an inference-minted param
/// carries its constraints only in the scheme's predicates), and a
/// declared predicate that names no quantified parameter is diagnosed.
/// Shared by the group generalization and the per-field (rank-N) one.
fn finish_scheme(
    scheme: &mut Scheme,
    declared: &DeclaredSchemeContext,
    catalog: &mut TypeCatalog,
    diagnostics: &mut DiagnosticSink,
) {
    let mut predicates = declared.predicates.clone();
    predicates.extend(std::mem::take(&mut scheme.predicates));
    scheme.predicates = predicates;
    for predicate in &scheme.predicates {
        if let Predicate::Conforms {
            ty: Ty::Param(param),
            protocol,
        } = predicate
            && scheme.params.iter().any(|p| p.symbol == *param)
        {
            let bounds = catalog.param_bounds.entry(*param).or_default();
            if !bounds.contains(protocol) {
                bounds.push(protocol.clone());
            }
        }
    }
    diagnostics
        .errors
        .extend(BindingGroupChecker::ambiguous_declared_predicate_errors(
            scheme, declared,
        ));
}

/// A top-level binder's declaration site, indexed by symbol.
enum TopEntry<'a> {
    Let {
        decl: &'a Decl,
        annotation: Option<&'a TypeAnnotation>,
        rhs: Option<&'a Expr>,
    },
    Struct {
        decl: &'a Decl,
    },
    Enum {
        decl: &'a Decl,
    },
}

/// A nominal member body waiting to be checked with its group.
enum MemberWork<'a> {
    Method(&'a Func),
    Init {
        params: &'a [Parameter],
        body: &'a Block,
        node: NodeID,
    },
}

/// The typed hand-off from declaration collection (`collect`) to body
/// checking (`check`): everything declaration collection produces that body
/// checking consumes.
struct Collected<'a> {
    decls: IndexMap<Symbol, TopEntry<'a>>,
    stmts: Vec<&'a Stmt>,
    destructuring_lets: Vec<&'a Decl>,
    extends: Vec<ExtendWork<'a>>,
    protocol_defaults: Vec<(Symbol, Symbol, &'a Func)>,
    /// Declaration-level static formation obligations, solved before the
    /// first binding group.
    obligations: Vec<Constraint>,
}

struct TypecheckSession<'a> {
    resolved: &'a ResolvedNames,
    modules: &'a crate::front::module::ModuleEnvironment,
    symbols: &'a mut Symbols,
    module_id: ModuleId,
    store: VarStore,
    catalog: TypeCatalog,
    diagnostics: DiagnosticSink,
    schemes: FxHashMap<Symbol, Scheme>,
    mono: FxHashMap<Symbol, Ty>,
    artifacts: TypeArtifacts,
    wanteds: Vec<Constraint>,
    self_types: Vec<Ty>,
    deferred: Vec<Constraint>,
    pending_force_unwraps: Vec<PendingForceUnwrap>,
    type_aliases: FxHashMap<Symbol, TypeAliasDef>,
    alias_stack: Vec<Symbol>,
    level: Level,
}

struct CatalogBuilder<'s, 'a> {
    resolved: &'a ResolvedNames,
    symbols: &'s mut Symbols,
    module_id: ModuleId,
    store: &'s mut VarStore,
    catalog: &'s mut TypeCatalog,
    schemes: &'s mut FxHashMap<Symbol, Scheme>,
    diagnostics: &'s mut DiagnosticSink,
    type_aliases: &'s mut FxHashMap<Symbol, TypeAliasDef>,
    alias_stack: &'s mut Vec<Symbol>,
    explicit_conformances: FxHashSet<(Symbol, ProtocolRef)>,
    /// Explicit claims on the substructural marker protocols (Copy,
    /// CheapClone, Deinit) with their blame nodes, validated once the whole
    /// catalog is collected.
    /// Marker-protocol conformance claims awaiting validation: the head,
    /// marker, EXACT row claimed (ADR 0036: disjoint rows validate
    /// independently), and the claiming declaration's node.
    marker_claims: Vec<(Symbol, Symbol, crate::types::catalog::ConformanceId, NodeID)>,
    self_types: Vec<Ty>,
    level: Level,
    /// Static formation obligations from declaration annotations
    /// (ADR 0035 §2): collection has no solver, so they queue here —
    /// wrapped under their declaration's givens — and the first checking
    /// solve discharges them. See `CatalogBuilder::absorb_obligations`.
    obligations: Vec<Constraint>,
}

struct BodyChecker<'s, 'a> {
    resolved: &'a ResolvedNames,
    symbols: &'s mut Symbols,
    module_id: ModuleId,
    store: &'s mut VarStore,
    catalog: &'s mut TypeCatalog,
    diagnostics: &'s mut DiagnosticSink,
    schemes: &'s mut FxHashMap<Symbol, Scheme>,
    mono: &'s mut FxHashMap<Symbol, Ty>,
    artifacts: &'s mut TypeArtifacts,
    wanteds: &'s mut Vec<Constraint>,
    self_types: &'s mut Vec<Ty>,
    deferred: &'s mut Vec<Constraint>,
    pending_force_unwraps: &'s mut Vec<PendingForceUnwrap>,
    type_aliases: &'s FxHashMap<Symbol, TypeAliasDef>,
    alias_stack: &'s mut Vec<Symbol>,
    level: Level,
}

struct BindingGroupChecker<'s, 'a> {
    resolved: &'a ResolvedNames,
    symbols: &'s mut Symbols,
    module_id: ModuleId,
    store: &'s mut VarStore,
    catalog: &'s mut TypeCatalog,
    diagnostics: &'s mut DiagnosticSink,
    schemes: &'s mut FxHashMap<Symbol, Scheme>,
    mono: &'s mut FxHashMap<Symbol, Ty>,
    artifacts: &'s mut TypeArtifacts,
    wanteds: &'s mut Vec<Constraint>,
    self_types: &'s mut Vec<Ty>,
    deferred: &'s mut Vec<Constraint>,
    pending_force_unwraps: &'s mut Vec<PendingForceUnwrap>,
    type_aliases: &'s FxHashMap<Symbol, TypeAliasDef>,
    alias_stack: &'s mut Vec<Symbol>,
    level: Level,
    /// The effects a top-level computation may always perform: the row
    /// core's `_with_host` entry wrapper discharges around the program
    /// (ADR 0039), read off its scheme. Top-level ambient rows close
    /// over this set plus the top-level `#handle`s installed BEFORE the
    /// computation (`handler_positions`), so a user effect with no
    /// handler on the way up — or only a later one — is a type error at
    /// the node where it tries to flow in.
    ambient_effects: std::collections::BTreeSet<Symbol>,
    /// Top-level `#handle`s in source order: (statement id, effect).
    handler_positions: Vec<(NodeID, Symbol)>,
}

/// What a statement contributes to its block's value (block value = last
/// expression; Return/Break/Continue diverge, so they are `Never` at joins).
struct PendingForceUnwrap {
    expr: Expr,
    source: Expr,
    failure: Expr,
    source_ty: Ty,
    result: Ty,
    ctx: Ctx,
    level: Level,
}

enum StmtValue {
    Value(Ty),
    Divergent { report_unreachable: bool },
    Unit,
}

impl StmtValue {
    fn divergent() -> Self {
        StmtValue::Divergent {
            report_unreachable: false,
        }
    }

    fn divergent_loop() -> Self {
        StmtValue::Divergent {
            report_unreachable: true,
        }
    }

    fn is_divergent(&self) -> bool {
        matches!(self, StmtValue::Divergent { .. })
    }

    fn reports_unreachable(&self) -> bool {
        matches!(
            self,
            StmtValue::Divergent {
                report_unreachable: true
            }
        )
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct PatternRefinement {
    givens: Vec<Predicate>,
    local_params: Vec<Symbol>,
}

/// The bidirectional checking context Γ (Dunfield & Krishnaswami, *Bidirectional
/// Typing*, ACM CSUR 2021): the ambient scope a body is checked under. Threaded
/// immutably by `&` and *extended* on scope entry, so the call stack is the
/// scope stack — there are no mutable push/pop stacks to keep balanced.
#[derive(Clone)]
struct Ctx {
    ret: Ty,
    eff: EffectRow,
    handler_ret: Option<Ty>,
    binder: Option<Symbol>,
    has_return_boundary: bool,
    in_loop: bool,
}

impl Ctx {
    fn root() -> Self {
        Ctx {
            ret: Ty::Error,
            eff: EffectRow::pure(),
            handler_ret: None,
            binder: None,
            has_return_boundary: false,
            in_loop: false,
        }
    }

    fn with_ret_eff(&self, ret: Ty, eff: EffectRow) -> Self {
        Ctx {
            ret,
            eff,
            ..self.clone()
        }
    }

    fn enter_function(&self, ret: Ty, eff: EffectRow) -> Self {
        Ctx {
            ret,
            eff,
            handler_ret: None,
            binder: self.binder,
            has_return_boundary: true,
            in_loop: false,
        }
    }

    fn enter_loop(&self) -> Self {
        Ctx {
            in_loop: true,
            ..self.clone()
        }
    }

    fn with_binder(&self, binder: Symbol) -> Self {
        Ctx {
            binder: Some(binder),
            ..self.clone()
        }
    }

    fn with_handler_ret(&self, handler_ret: Ty) -> Self {
        Ctx {
            handler_ret: Some(handler_ret),
            ..self.clone()
        }
    }
}

impl<'a> TypecheckSession<'a> {
    fn run(
        mut self,
        asts: &'a IndexMap<Source, AST<NameResolved>>,
    ) -> (
        TypeOutput,
        crate::types::output::Elaboration,
        Vec<AnyDiagnostic>,
    ) {
        let mut display_names = self.modules.imported_symbol_names();
        display_names.extend(self.resolved.symbol_names.clone());
        self.artifacts.display_names = display_names.clone();
        let _names = crate::name_resolution::symbol::set_symbol_names(display_names);

        let collected = {
            let mut builder = CatalogBuilder {
                resolved: self.resolved,
                symbols: &mut *self.symbols,
                module_id: self.module_id,
                store: &mut self.store,
                catalog: &mut self.catalog,
                schemes: &mut self.schemes,
                diagnostics: &mut self.diagnostics,
                type_aliases: &mut self.type_aliases,
                alias_stack: &mut self.alias_stack,
                explicit_conformances: FxHashSet::default(),
                marker_claims: vec![],
                self_types: vec![],
                level: OUTER_LEVEL,
                obligations: vec![],
            };
            builder.collect(asts)
        };
        // Every conformance row exists now: materialize derived
        // conformances as ordinary rows, then commit the Deinit index and
        // each row's dictionary (ADR 0038) so lowering dereferences
        // committed entries instead of searching and guessing.
        self.catalog.synthesize_derived_conformances(self.module_id);
        self.catalog.synthesize_reflexive_into_conformances(self.module_id);
        self.catalog.commit_deinit_rows();
        self.catalog.commit_dictionaries();
        self.catalog.commit_callable_owners();
        self.catalog.commit_member_visibility(self.resolved);

        {
            let mut groups = BindingGroupChecker {
                resolved: self.resolved,
                symbols: &mut *self.symbols,
                module_id: self.module_id,
                store: &mut self.store,
                catalog: &mut self.catalog,
                diagnostics: &mut self.diagnostics,
                schemes: &mut self.schemes,
                mono: &mut self.mono,
                artifacts: &mut self.artifacts,
                wanteds: &mut self.wanteds,
                self_types: &mut self.self_types,
                deferred: &mut self.deferred,
                pending_force_unwraps: &mut self.pending_force_unwraps,
                type_aliases: &self.type_aliases,
                alias_stack: &mut self.alias_stack,
                level: self.level,
                ambient_effects: Default::default(),
                handler_positions: Default::default(),
            };
            groups.check(collected);
            self.level = groups.level;
        }

        self.check_recursive_declarations(asts);
        self.check_matches(asts);
        self.check_member_references(asts);
        self.check_call_labels(asts);
        visibility::check_public_api_closure(
            self.resolved,
            &self.schemes,
            &self.catalog,
            &mut self.diagnostics.errors,
        );
        self.finalize()
    }

    /// A method used as a VALUE (`x.method` with no call) has no lowering
    /// yet: reject it here with a real diagnostic so it can never reach
    /// the lowerer's internal fallthrough. Scoped to value receivers —
    /// type-name receivers (`Optional.none`, statics) resolve through the
    /// variant/static machinery.
    fn check_member_references(&mut self, asts: &IndexMap<Source, AST<NameResolved>>) {
        use crate::parsing::label::Label;
        use derive_visitor::Drive;
        let mut callees: rustc_hash::FxHashSet<NodeID> = Default::default();
        let mut sites: Vec<(NodeID, String)> = vec![];
        {
            let mut collector = derive_visitor::visitor_enter_fn(|expr: &Expr| match &expr.kind {
                ExprKind::Call { callee, .. } => {
                    callees.insert(callee.id);
                }
                ExprKind::Member(Some(receiver), Label::Named(label), _) => {
                    let type_receiver = matches!(&receiver.kind, ExprKind::Constructor(..))
                        || matches!(
                            &receiver.kind,
                            ExprKind::Variable(name) if matches!(
                                name.symbol(),
                                Ok(Symbol::Struct(_)
                                    | Symbol::Enum(_)
                                    | Symbol::Protocol(_)
                                    | Symbol::TypeAlias(_)
                                    | Symbol::TypeParameter(_))
                            )
                        );
                    if !type_receiver {
                        sites.push((expr.id, label.clone()));
                    }
                }
                _ => {}
            });
            for ast in asts.values() {
                for root in &ast.roots {
                    root.drive(&mut collector);
                }
            }
        }
        for (node, label) in sites {
            if callees.contains(&node) {
                continue;
            }
            // The solver's published resolution is the authority for
            // field-vs-method (the same judgment the typed-tree build uses
            // for projections). No resolution means the member never
            // resolved — the solver already diagnosed it.
            let resolution = self.artifacts.member_resolutions.get(&node);
            if resolution.is_none()
                || crate::types::output::stored_field_symbol(
                    &self.catalog,
                    &self.schemes,
                    resolution,
                )
                .is_some()
            {
                continue;
            }
            self.diagnostics
                .errors
                .push((TypeError::MethodReference { label }, node));
        }
    }

    /// ADR 0045 rule 2: a declaration whose layout contains itself must
    /// live behind a reference, and `'heap` is how a declaration says
    /// so — recursion is the case where indirection is not optional.
    /// Runs after collection, when the whole catalog can answer the
    /// cycle walk; only this module's own declarations are judged
    /// (imports were judged when their module compiled). One direction
    /// only: `'heap` on a non-recursive type stays an ordinary choice.
    fn check_recursive_declarations(&mut self, asts: &IndexMap<Source, AST<NameResolved>>) {
        fn walk(decl: &Decl, out: &mut Vec<(NodeID, Symbol, String, bool)>) {
            match &decl.kind {
                DeclKind::Struct {
                    name, body, heap, ..
                }
                | DeclKind::Enum {
                    name, body, heap, ..
                } => {
                    if let Ok(symbol) = name.symbol() {
                        out.push((decl.id, symbol, name.name_str(), *heap));
                    }
                    for member in &body.decls {
                        walk(member, out);
                    }
                }
                DeclKind::Protocol { body, .. } | DeclKind::Extend { body, .. } => {
                    for member in &body.decls {
                        walk(member, out);
                    }
                }
                _ => {}
            }
        }
        let mut declared = vec![];
        for ast in asts.values() {
            for root in &ast.roots {
                if let Node::Decl(decl) = root {
                    walk(decl, &mut declared);
                }
            }
        }
        for (node, symbol, name, heap) in declared {
            if !heap && self.catalog.layout_recursive(symbol) {
                self.diagnostics
                    .errors
                    .push((TypeError::RecursiveTypeNeedsHeap { name }, node));
            }
        }
    }

    fn check_matches(&mut self, asts: &IndexMap<Source, AST<NameResolved>>) {
        use derive_visitor::Drive;
        let mut sites: Vec<(NodeID, Vec<Pattern>)> = vec![];
        {
            let mut collector = derive_visitor::visitor_enter_fn(|expr: &Expr| {
                if let ExprKind::Match(scrutinee, arms) = &expr.kind {
                    sites.push((
                        scrutinee.id,
                        arms.iter().map(|arm| arm.pattern.clone()).collect(),
                    ));
                }
            });
            for ast in asts.values() {
                for root in &ast.roots {
                    root.drive(&mut collector);
                }
            }
        }
        for (scrutinee, patterns) in sites {
            let Some(ty) = self.artifacts.node_types.get(&scrutinee) else {
                continue;
            };
            let ty = self.store.zonk_ty(ty);
            if matches!(ty, Ty::Error) || ty.has_unification_vars() {
                continue;
            }
            let ty = match ty {
                Ty::Borrow(_, inner) => *inner,
                other => other,
            };
            let arms: Vec<&Pattern> = patterns.iter().collect();
            let report = crate::types::exhaustiveness::check_match(&self.catalog, &ty, &arms);
            if !report.missing.is_empty() {
                self.diagnostics.errors.push((
                    TypeError::NonExhaustiveMatch {
                        missing: report.missing,
                    },
                    scrutinee,
                ));
            }
            for arm in report.unreachable_arms {
                // A synthesized unreachable arm is a desugared
                // conditional's implicit else: the useful position is
                // the written pattern that swallowed it, and the useful
                // message is that the pattern is irrefutable.
                let index = arms.iter().position(|pattern| pattern.id == arm);
                let synthesized = index.is_some_and(|index| {
                    arms[index].span == crate::parsing::span::Span::SYNTHESIZED
                });
                if synthesized {
                    let written = index
                        .and_then(|index| {
                            arms[..index].iter().rev().find(|pattern| {
                                pattern.span != crate::parsing::span::Span::SYNTHESIZED
                            })
                        })
                        .map(|pattern| pattern.id)
                        .unwrap_or(scrutinee);
                    self.diagnostics
                        .warnings
                        .push((TypeError::IrrefutableConditionalPattern, written));
                } else {
                    self.diagnostics
                        .warnings
                        .push((TypeError::UnreachableMatchArm, arm));
                }
            }
        }
    }
}

impl<'s, 'a> BindingGroupChecker<'s, 'a> {
    fn body(&mut self) -> BodyChecker<'_, 'a> {
        BodyChecker {
            resolved: self.resolved,
            symbols: &mut *self.symbols,
            module_id: self.module_id,
            store: &mut *self.store,
            catalog: &mut *self.catalog,
            diagnostics: &mut *self.diagnostics,
            schemes: &mut *self.schemes,
            mono: &mut *self.mono,
            artifacts: &mut *self.artifacts,
            wanteds: &mut *self.wanteds,
            self_types: &mut *self.self_types,
            deferred: &mut *self.deferred,
            pending_force_unwraps: &mut *self.pending_force_unwraps,
            type_aliases: self.type_aliases,
            alias_stack: &mut *self.alias_stack,
            level: self.level,
        }
    }
}

mod artifacts;
mod bounds;
mod call;
mod collect;
mod diagnostics;
mod elaborate;
mod expr;
mod extend;
mod finalize;
mod func;
mod groups;
mod instantiate;
mod labels;
mod pattern;
mod stmt;
mod support;
mod visibility;

use artifacts::{MarkedSlot, TypeArtifacts};
use diagnostics::DiagnosticSink;
use support::*;
