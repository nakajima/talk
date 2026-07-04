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
use crate::compiling::driver::Source;
use crate::compiling::module::ModuleId;
use crate::diagnostic::{AnyDiagnostic, Diagnostic, Severity};
use crate::label::Label;
use crate::name::Name;
use crate::name_resolution::name_resolver::ResolvedNames;
use crate::name_resolution::scc_graph::Level;
use crate::name_resolution::symbol::{Symbol, Symbols};
use crate::node::Node;
use crate::node_id::NodeID;
use crate::node_kinds::func_signature::FuncSignature;
use crate::node_kinds::generic_decl::GenericDecl;
use crate::node_kinds::{
    block::Block,
    call_arg::CallArg,
    decl::{Decl, DeclKind},
    expr::{Expr, ExprKind},
    func::Func,
    match_arm::MatchArm,
    parameter::Parameter,
    pattern::{Pattern, PatternKind, RecordFieldPatternKind},
    stmt::{Stmt, StmtKind},
    type_annotation::{AnyAssocBinding, TypeAnnotation, TypeAnnotationKind},
    where_clause::{WhereClause, WherePredicateKind},
};
use crate::types::catalog::{
    Conformance, Enum, MemberOwner, ProtocolInfo, Requirement, StructInfo, TypeAliasInfo,
    TypeCatalog, Variant,
};
use crate::types::constraint::{Constraint, CtOrigin, CtReason, Implication};
use crate::types::error::TypeError;
use crate::types::output::{ExistentialPack, MemberResolution, TypeOutput};
use crate::types::solve::{Generalizer, Solver, TyNode, VarStore, normalize_ty};
use crate::types::ty::{
    EffTail, EffectEntry, EffectRow, Perm, Predicate, Row, RowTail, Scheme, SchemeParam, Ty, TyFold,
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
    modules: &crate::compiling::module::ModuleEnvironment,
    module_id: ModuleId,
) -> (TypeOutput, Vec<AnyDiagnostic>) {
    let mut catalog = TypeCatalog::default();
    let mut schemes: FxHashMap<Symbol, Scheme> = FxHashMap::default();
    for module in modules.all_modules() {
        catalog.merge(module.types.catalog.clone());
        schemes.extend(module.types.schemes.clone());
    }

    TypecheckSession {
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
        type_aliases: FxHashMap::default(),
        alias_stack: vec![],
        level: GROUP_LEVEL,
    }
    .run(asts)
}

/// An `extend` block whose member bodies are checked after all binding
/// groups (witness signatures come from the protocol requirement, so users
/// never depend on this ordering).
struct ExtendWork<'a> {
    self_ty: Ty,
    context: Vec<Predicate>,
    decl: &'a Decl,
    protocols: Vec<Symbol>,
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
}

struct TypecheckSession<'a> {
    resolved: &'a ResolvedNames,
    modules: &'a crate::compiling::module::ModuleEnvironment,
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
    diagnostics: &'s mut DiagnosticSink,
    type_aliases: &'s mut FxHashMap<Symbol, TypeAliasDef>,
    alias_stack: &'s mut Vec<Symbol>,
    explicit_conformances: FxHashSet<(Symbol, Symbol)>,
    /// Explicit claims on the substructural marker protocols (Copy,
    /// CheapClone, Deinit) with their blame nodes, validated once the whole
    /// catalog is collected.
    marker_claims: Vec<(Symbol, Symbol, NodeID)>,
    self_types: Vec<Ty>,
    level: Level,
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
    type_aliases: &'s FxHashMap<Symbol, TypeAliasDef>,
    alias_stack: &'s mut Vec<Symbol>,
    level: Level,
    /// The effects a top-level computation may always perform: the core
    /// effects the runtime handles implicitly ('io, 'async, 'alloc).
    /// Top-level ambient rows close over this set plus the top-level
    /// `@handle`s installed BEFORE the computation (`handler_positions`),
    /// so a user effect with no handler on the way up — or only a later
    /// one — is a type error at the node where it tries to flow in.
    ambient_effects: std::collections::BTreeSet<Symbol>,
    /// Top-level `@handle`s in source order: (statement id, effect).
    handler_positions: Vec<(NodeID, Symbol)>,
}

/// What a statement contributes to its block's value (block value = last
/// expression; Return/Break/Continue diverge, so they are `Never` at joins).
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
}

impl Ctx {
    fn root() -> Self {
        Ctx {
            ret: Ty::Error,
            eff: EffectRow::pure(),
            handler_ret: None,
            binder: None,
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
    ) -> (TypeOutput, Vec<AnyDiagnostic>) {
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
                diagnostics: &mut self.diagnostics,
                type_aliases: &mut self.type_aliases,
                alias_stack: &mut self.alias_stack,
                explicit_conformances: FxHashSet::default(),
                marker_claims: vec![],
                self_types: vec![],
                level: OUTER_LEVEL,
            };
            builder.collect(asts)
        };

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
                type_aliases: &self.type_aliases,
                alias_stack: &mut self.alias_stack,
                level: self.level,
                ambient_effects: Default::default(),
                handler_positions: Default::default(),
            };
            groups.check(collected);
            self.level = groups.level;
        }

        self.check_matches(asts);
        self.finalize()
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
            if matches!(ty, Ty::Error) {
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
                self.diagnostics
                    .warnings
                    .push((TypeError::UnreachableMatchArm, arm));
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
mod pattern;
mod stmt;
mod support;

use artifacts::TypeArtifacts;
use diagnostics::DiagnosticSink;
use support::*;
