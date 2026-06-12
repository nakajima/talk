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
//! latent row with it (Koka's application rule, Leijen MSFP 2014). Deviation
//! from Koka: closed effect annotations will be checked as bounds at
//! declaration sites (milestone 5) instead of inserting open-coercions
//! (Leijen POPL 2017 §3) — arrow rows under inference stay open.
//!
//! Member access on a known head resolves directly against the catalog;
//! methods are self-prepended functions, so `recv.m(args)` checks the full
//! signature against `(recv, args...)` (the dictionary-free reading of
//! Wadler & Blott's method lookup for the nominal case). Member access on a
//! head that is still a variable becomes a `HasMember` predicate in
//! milestone 3 (Gaster & Jones 1996); today it errors.

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
use crate::node_kinds::{
    block::Block,
    call_arg::CallArg,
    decl::{Decl, DeclKind},
    expr::{Expr, ExprKind},
    func::Func,
    parameter::Parameter,
    pattern::{Pattern, PatternKind, RecordFieldPatternKind},
    stmt::{Stmt, StmtKind},
    type_annotation::{TypeAnnotation, TypeAnnotationKind},
};
use crate::node_kinds::func_signature::FuncSignature;
use crate::node_kinds::generic_decl::GenericDecl;
use crate::types::catalog::{
    Conformance, EnumInfo, MemberOwner, ProtocolInfo, Requirement, StructInfo, TypeCatalog,
    VariantInfo,
};
use crate::types::constraint::{Constraint, CtOrigin, CtReason};
use crate::types::error::TypeError;
use crate::types::output::{MemberResolution, TypeOutput};
use crate::types::solve::{Generalizer, Solver, VarStore};
use crate::types::ty::{Bound, EffTail, EffectRow, Row, Scheme, SchemeParam, Ty};

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
    // Phase 0 — import: seed the catalog and schemes from every imported
    // module's type payload (the core prelude, plus user imports).
    let mut catalog = TypeCatalog::default();
    let mut schemes: FxHashMap<Symbol, Scheme> = FxHashMap::default();
    for module in modules.all_modules() {
        catalog.merge(module.types.catalog.clone());
        schemes.extend(module.types.schemes.clone());
    }

    let checker = Checker {
        resolved,
        modules,
        symbols,
        module_id,
        store: VarStore::default(),
        catalog,
        errors: vec![],
        schemes,
        mono: FxHashMap::default(),
        node_types: FxHashMap::default(),
        instantiations: FxHashMap::default(),
        member_resolutions: FxHashMap::default(),
        binder_stack: vec![],
        performs_into: FxHashMap::default(),
        binder_refs: FxHashMap::default(),
        handler_payload_tys: FxHashMap::default(),
        handler_ret_stack: vec![],
        wanteds: vec![],
        ret_stack: vec![],
        eff_stack: vec![],
        self_types: vec![],
        extends: vec![],
        protocol_defaults: vec![],
        deferred: vec![],
        level: GROUP_LEVEL,
    };
    checker.run(asts)
}

/// An `extend` block whose member bodies are checked after all binding
/// groups (witness signatures come from the protocol requirement, so users
/// never depend on this ordering).
struct ExtendWork<'a> {
    self_ty: Ty,
    decl: &'a Decl,
    protocols: Vec<Symbol>,
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
    Enum,
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

struct Checker<'a> {
    resolved: &'a ResolvedNames,
    modules: &'a crate::compiling::module::ModuleEnvironment,
    symbols: &'a mut Symbols,
    module_id: ModuleId,
    store: VarStore,
    catalog: TypeCatalog,
    errors: Vec<(TypeError, NodeID)>,
    /// Finished types, one entry per binder; monomorphic entries keep
    /// sharing their unsolved variables until the final zonk.
    schemes: FxHashMap<Symbol, Scheme>,
    /// Monomorphic in-flight types: group skeletons, member skeletons,
    /// params, locals, pattern binds.
    mono: FxHashMap<Symbol, Ty>,
    node_types: FxHashMap<NodeID, Ty>,
    instantiations: FxHashMap<NodeID, Vec<(Symbol, Ty)>>,
    member_resolutions: FxHashMap<NodeID, MemberResolution>,
    /// The named binder whose body is being checked (top-level binder,
    /// method, init, witness, protocol default) — attribution for the
    /// capability tables below. Empty for top-level statements.
    binder_stack: Vec<Symbol>,
    /// Capability flow, recorded as it is discovered and exported for
    /// the lowerer's abort analysis (see `TypeOutput`): binder → lexical
    /// handlers its body performs into; binder → named symbols its body
    /// references.
    performs_into: FxHashMap<Symbol, FxHashSet<Symbol>>,
    binder_refs: FxHashMap<Symbol, FxHashSet<Symbol>>,
    /// `@handle` payload types (zonked at finalize): handler symbol →
    /// the effect's parameter types as this module solved them.
    handler_payload_tys: FxHashMap<Symbol, Vec<Ty>>,
    /// The effect return type of the handler block being checked:
    /// `continue v` resumes the perform, so v checks against it. Cleared
    /// inside nested function literals (they cannot resume).
    handler_ret_stack: Vec<Ty>,
    wanteds: Vec<Constraint>,
    ret_stack: Vec<Ty>,
    eff_stack: Vec<EffectRow>,
    /// `Self` for the nominal whose members are being checked.
    self_types: Vec<Ty>,
    extends: Vec<ExtendWork<'a>>,
    /// Default-bodied protocol requirements awaiting their generic check:
    /// (protocol, requirement symbol, body).
    protocol_defaults: Vec<(Symbol, Symbol, &'a Func)>,
    /// Constraints floated out of their group because their head is an
    /// outer-level variable a later group may solve (OutsideIn's floating);
    /// re-solved once at finalization.
    deferred: Vec<Constraint>,
    level: Level,
}

/// What a statement contributes to its block's value (block value = last
/// expression; Return/Break/Continue diverge, so they are `Never` at joins).
enum StmtValue {
    Value(Ty),
    Divergent,
    Unit,
}

impl<'a> Checker<'a> {
    fn run(
        mut self,
        asts: &'a IndexMap<Source, AST<NameResolved>>,
    ) -> (TypeOutput, Vec<AnyDiagnostic>) {
        // Symbols render with their source names in diagnostics — including
        // names imported from other modules.
        let mut display_names = self.modules.imported_symbol_names();
        display_names.extend(self.resolved.symbol_names.clone());
        let _names = crate::name_resolution::symbol::set_symbol_names(display_names);

        // Phase 1 — declaration collection (signatures only, no bodies).
        // Variables minted while lowering declaration annotations live at the
        // outer level so no group ever quantifies them.
        self.level = OUTER_LEVEL;
        let mut decls: IndexMap<Symbol, TopEntry<'a>> = IndexMap::default();
        let mut stmts: Vec<&'a Stmt> = vec![];

        // Pass A gathers declarations; nominals and protocols register
        // before extends and lets so cross-file references (core files are
        // order-sensitive) always find their targets.
        let mut top_decls: Vec<&'a Decl> = vec![];
        for ast in asts.values() {
            for root in &ast.roots {
                match root {
                    Node::Decl(decl) => top_decls.push(decl),
                    Node::Stmt(stmt) => stmts.push(stmt),
                    _ => {}
                }
            }
        }

        let mut struct_decls: Vec<(Symbol, &'a Decl)> = vec![];
        let mut destructuring_lets: Vec<&'a Decl> = vec![];
        for decl in &top_decls {
            match &decl.kind {
                DeclKind::Struct { name, .. } => {
                    if let Ok(symbol) = name.symbol() {
                        self.register_struct(symbol, decl);
                        struct_decls.push((symbol, decl));
                        decls.insert(symbol, TopEntry::Struct { decl });
                    }
                }
                DeclKind::Enum { name, .. } => {
                    if let Ok(symbol) = name.symbol() {
                        self.register_enum(symbol, decl);
                        decls.insert(symbol, TopEntry::Enum);
                    }
                }
                DeclKind::Protocol { name, .. } => {
                    if let Ok(symbol) = name.symbol() {
                        self.register_protocol(symbol, decl);
                    }
                }
                DeclKind::Effect {
                    name, params, ret, ..
                } => {
                    if let Ok(symbol) = name.symbol() {
                        self.register_effect(symbol, params, ret);
                    }
                }
                _ => {}
            }
        }

        // Pass B: extends (top-level and nested in struct bodies) and lets.
        for decl in &top_decls {
            match &decl.kind {
                DeclKind::Let {
                    lhs:
                        Pattern {
                            kind: PatternKind::Bind(name),
                            ..
                        },
                    type_annotation,
                    rhs,
                } => {
                    if let Ok(symbol) = name.symbol() {
                        // Declared generics (`func f<T: P>`) register their
                        // bounds up front so any group can discharge against
                        // them.
                        if let Some(Expr {
                            kind: ExprKind::Func(func),
                            ..
                        }) = rhs
                        {
                            self.register_generic_bounds(&func.generics);
                        }
                        decls.insert(
                            symbol,
                            TopEntry::Let {
                                decl,
                                annotation: type_annotation.as_ref(),
                                rhs: rhs.as_ref(),
                            },
                        );
                    }
                }
                // A destructuring let binds several symbols monomorphically
                // (no scheme to enter a binding group with); it checks with
                // the top-level statements, in source order.
                DeclKind::Let { .. } => destructuring_lets.push(decl),
                DeclKind::Extend { .. } => {
                    if let Some(work) = self.register_extend(decl, None) {
                        self.extends.push(work);
                    }
                }
                DeclKind::Struct { .. }
                | DeclKind::Enum { .. }
                | DeclKind::Protocol { .. }
                | DeclKind::Effect { .. }
                | DeclKind::Import(_) => {}
                other => self.unsupported(decl.id, decl_kind_name(other)),
            }
        }

        // Nested `extend Self: P` blocks inside struct bodies.
        for (symbol, decl) in &struct_decls {
            let DeclKind::Struct { body, .. } = &decl.kind else {
                continue;
            };
            for member in &body.decls {
                if matches!(member.kind, DeclKind::Extend { .. })
                    && let Some(work) = self.register_extend(member, Some(*symbol))
                {
                    self.extends.push(work);
                }
            }
        }

        // Phase 2 — solve binding groups in dependency order. Groups come
        // from our own free-variable dependency analysis (THIH §11.6.2
        // computes binding groups exactly this way): the resolver's SCC
        // graph omits edges out of method bodies, which would order struct
        // groups before the globals they call. kosaraju_scc returns SCCs in
        // postorder = reverse topological order of the condensation, and
        // edges point binder -> dependency, so dependencies come first
        // (verified by binding_groups_solve_in_dependency_order).
        for binders in binding_groups(&decls) {
            self.check_group(&binders, &decls);
        }

        // Phase 2b — extend bodies. Witness signatures were never needed by
        // earlier groups (member discharge goes through protocol requirement
        // signatures), so extends check last, each as its own mini-group:
        // the witness body must match the requirement (this is where
        // `extend Thing: Foo { func foo() { 123 } }` gets its return type).
        let extends = std::mem::take(&mut self.extends);
        for work in extends {
            self.check_extend(work);
        }

        // Phase 2b' — protocol default bodies, checked once, generically
        // over Self (the class-default treatment of Wadler & Blott's
        // dictionary translation): Self is the rigid `Param(protocol)`,
        // bounded by the protocol itself so requirement dispatch works, and
        // the inferred type must equal the registered requirement signature.
        let defaults = std::mem::take(&mut self.protocol_defaults);
        for (protocol, requirement_symbol, func) in defaults {
            self.check_protocol_default(protocol, requirement_symbol, func);
        }

        // Phase 2c — top-level statements, in source order, against the
        // finished schemes. Their ambient effect row lives at the outer level.
        self.level = GROUP_LEVEL;
        let top_eff = EffectRow::open(self.store.fresh_eff(OUTER_LEVEL, NodeID::SYNTHESIZED));
        let top_ret = Ty::Var(self.store.fresh_ty(OUTER_LEVEL, NodeID::SYNTHESIZED));
        self.eff_stack.push(top_eff);
        self.ret_stack.push(top_ret);
        for decl in destructuring_lets {
            self.check_local_decl(decl);
        }
        for stmt in stmts {
            self.infer_stmt(stmt);
        }
        self.eff_stack.pop();
        self.ret_stack.pop();
        let wanteds = std::mem::take(&mut self.wanteds);
        let residuals = self.run_solver(wanteds);
        self.report_unresolved_residuals(residuals);
        self.solve_deferred();

        self.finalize()
    }

    // ----- Declaration collection ---------------------------------------

    fn register_struct(&mut self, symbol: Symbol, decl: &Decl) {
        let DeclKind::Struct { generics, body, .. } = &decl.kind else {
            return;
        };
        let params = generic_symbols(generics);
        let mut info = StructInfo {
            params,
            ..Default::default()
        };
        for member in &body.decls {
            match &member.kind {
                DeclKind::Property {
                    name,
                    is_static,
                    type_annotation,
                    ..
                } => {
                    if *is_static {
                        self.unsupported(member.id, "static properties");
                        continue;
                    }
                    let Ok(property) = name.symbol() else { continue };
                    let ty = match type_annotation {
                        Some(annotation) => self.lower_annotation(annotation),
                        None => {
                            // Inference for default-valued properties lands
                            // with the core prelude (milestone 4).
                            self.unsupported(member.id, "properties without type annotations");
                            Ty::Error
                        }
                    };
                    info.fields.insert(name.name_str(), (property, ty));
                }
                DeclKind::Method { func, is_static } => {
                    let Ok(method) = func.name.symbol() else {
                        continue;
                    };
                    let table = if *is_static {
                        &mut info.statics
                    } else {
                        &mut info.methods
                    };
                    table.insert(func.name.name_str(), method);
                }
                DeclKind::Init { name, .. } => {
                    if let Ok(init) = name.symbol() {
                        info.inits.push(init);
                    }
                }
                // Nested `extend Self: P` registers in pass B.
                DeclKind::Extend { .. } => {}
                other => self.unsupported(member.id, decl_kind_name(other)),
            }
        }
        for label in info.fields.keys().chain(info.methods.keys()) {
            self.catalog.add_owner(label, MemberOwner::Nominal(symbol));
        }
        self.catalog.structs.insert(symbol, info);
    }

    fn register_enum(&mut self, symbol: Symbol, decl: &Decl) {
        let DeclKind::Enum { generics, body, .. } = &decl.kind else {
            return;
        };
        let params = generic_symbols(generics);
        let result = Ty::Nominal(symbol, params.iter().map(|p| Ty::Param(*p)).collect());
        let mut info = EnumInfo {
            params,
            ..Default::default()
        };
        for member in &body.decls {
            match &member.kind {
                DeclKind::EnumVariant(name, _, payload_annotations) => {
                    let Ok(variant) = name.symbol() else { continue };
                    let payloads = payload_annotations
                        .iter()
                        .map(|a| self.lower_annotation(a))
                        .collect();
                    info.variants.insert(
                        name.name_str(),
                        VariantInfo {
                            symbol: variant,
                            payloads,
                            result: result.clone(),
                        },
                    );
                }
                other => self.unsupported(member.id, decl_kind_name(other)),
            }
        }
        self.catalog.enums.insert(symbol, info);
    }

    /// Register a protocol: associated types, supers, and requirement
    /// signatures over `Self = Ty::Param(protocol)` and the assoc params
    /// (Wadler & Blott 1989 classes; Chakravarty et al. 2005 assoc types).
    fn register_protocol(&mut self, symbol: Symbol, decl: &'a Decl) {
        let DeclKind::Protocol {
            generics,
            body,
            conformances,
            ..
        } = &decl.kind
        else {
            return;
        };
        if !generics.is_empty() {
            self.unsupported(decl.id, "generic protocols");
        }
        let supers: Vec<Symbol> = conformances
            .iter()
            .filter_map(|c| c.symbol().ok())
            .collect();

        let mut info = ProtocolInfo {
            supers,
            ..Default::default()
        };
        self.self_types.push(Ty::Param(symbol));
        for member in &body.decls {
            match &member.kind {
                DeclKind::Associated { generic } => {
                    if let Ok(assoc) = generic.name.symbol() {
                        info.assoc.insert(generic.name.name_str(), assoc);
                        // `associated T: Iterator` — bounds on the assoc
                        // param discharge member access through it.
                        self.register_generic_bounds(std::slice::from_ref(generic));
                    }
                }
                DeclKind::MethodRequirement(signature) | DeclKind::FuncSignature(signature) => {
                    if let Some(requirement) = self.lower_requirement(signature, false) {
                        info.requirements
                            .insert(signature.name.name_str(), requirement);
                    }
                }
                // Default-bodied requirements: register the signature now;
                // the body checks generically over Self after all groups.
                DeclKind::Method { func, .. } => {
                    if let Some(requirement) = self.lower_default_requirement(func) {
                        self.protocol_defaults
                            .push((symbol, requirement.symbol, func));
                        info.requirements.insert(func.name.name_str(), requirement);
                    }
                }
                other => self.unsupported(member.id, decl_kind_name(other)),
            }
        }
        self.self_types.pop();

        for label in info.requirements.keys() {
            self.catalog.add_owner(label, MemberOwner::Protocol(symbol));
        }
        // Showable is auto-derived for structs and enums (the lowerer
        // synthesizes the bodies, as the previous implementation did).
        if let DeclKind::Protocol { name, .. } = &decl.kind
            && name.name_str() == "Showable"
            && !self.catalog.derivable.contains(&symbol)
        {
            self.catalog.derivable.push(symbol);
        }
        self.catalog.protocols.insert(symbol, info);
    }

    fn lower_requirement(
        &mut self,
        signature: &FuncSignature,
        has_default: bool,
    ) -> Option<Requirement> {
        let symbol = signature.name.symbol().ok()?;
        let params: Vec<Ty> = signature
            .params
            .iter()
            .map(|p| match &p.type_annotation {
                Some(annotation) => self.lower_annotation(annotation),
                None => Ty::Var(self.store.fresh_ty(OUTER_LEVEL, p.id)),
            })
            .collect();
        let ret = match &signature.ret {
            Some(annotation) => self.lower_annotation(annotation),
            None => {
                self.unsupported(
                    signature.id,
                    "protocol requirements without a return type annotation",
                );
                Ty::Error
            }
        };
        // The effect tail is a parameter keyed by the requirement symbol so
        // every use substitutes a fresh one (no accidental row sharing).
        let eff = EffectRow {
            effects: Default::default(),
            tail: Some(EffTail::Param(symbol)),
        };
        Some(Requirement {
            symbol,
            sig: Ty::Func(params, Box::new(ret), eff),
            has_default,
        })
    }

    fn lower_default_requirement(&mut self, func: &Func) -> Option<Requirement> {
        let symbol = func.name.symbol().ok()?;
        let params: Vec<Ty> = func
            .params
            .iter()
            .map(|p| match &p.type_annotation {
                Some(annotation) => self.lower_annotation(annotation),
                None => Ty::Var(self.store.fresh_ty(OUTER_LEVEL, p.id)),
            })
            .collect();
        let ret = match &func.ret {
            Some(annotation) => self.lower_annotation(annotation),
            None => Ty::Var(self.store.fresh_ty(OUTER_LEVEL, func.id)),
        };
        let eff = EffectRow {
            effects: Default::default(),
            tail: Some(EffTail::Param(symbol)),
        };
        Some(Requirement {
            symbol,
            sig: Ty::Func(params, Box::new(ret), eff),
            has_default: true,
        })
    }

    fn register_effect(&mut self, symbol: Symbol, params: &[Parameter], ret: &TypeAnnotation) {
        let params = params
            .iter()
            .map(|p| match &p.type_annotation {
                Some(annotation) => self.lower_annotation(annotation),
                // Unannotated effect params are handler-site inferred
                // (milestone 5); a shared outer variable is the permissive
                // placeholder until then.
                None => Ty::Var(self.store.fresh_ty(OUTER_LEVEL, p.id)),
            })
            .collect();
        let ret = self.lower_annotation(ret);
        self.catalog
            .effects
            .insert(symbol, crate::types::catalog::EffectSig { params, ret });
    }

    /// Register an `extend`: conformance rows (witness map + associated-type
    /// bindings inferred by matching witness annotations against requirement
    /// signatures — Chakravarty et al. 2005's instance-determined synonyms),
    /// conditional-conformance contexts (instances with contexts, Hall et
    /// al. TOPLAS 1996), inherent members, and completeness errors. Bodies
    /// check later (`check_extend`). `enclosing` is the struct whose body a
    /// nested `extend Self: P` appears in.
    fn register_extend(&mut self, decl: &'a Decl, enclosing: Option<Symbol>) -> Option<ExtendWork<'a>> {
        let DeclKind::Extend {
            name,
            conformances,
            generics,
            body,
            ..
        } = &decl.kind
        else {
            return None;
        };
        let head = match (name, enclosing) {
            (Name::SelfType(_), Some(parent)) | (_, Some(parent)) => parent,
            _ => name.symbol().ok()?,
        };
        self.register_generic_bounds(generics);

        // The row's own rigid params and the head application they index:
        // a nested extend uses the enclosing struct's generics; a top-level
        // `extend Array<Element>` uses its declared generics; plain heads
        // (`extend Int`) have none.
        let params: Vec<Symbol> = if enclosing.is_some() || generics.is_empty() {
            self.catalog
                .structs
                .get(&head)
                .map(|i| i.params.clone())
                .or_else(|| self.catalog.enums.get(&head).map(|i| i.params.clone()))
                .unwrap_or_default()
        } else {
            generic_symbols(generics)
        };
        let self_args: Vec<Ty> = params.iter().map(|p| Ty::Param(*p)).collect();
        let self_ty = Ty::Nominal(head, self_args.clone());
        let context: Vec<(Symbol, Vec<Symbol>)> = generics
            .iter()
            .filter_map(|g| {
                let symbol = g.name.symbol().ok()?;
                let bounds: Vec<Symbol> =
                    g.conformances.iter().filter_map(|c| c.symbol().ok()).collect();
                (!bounds.is_empty()).then_some((symbol, bounds))
            })
            .collect();

        // Collect declared members (witnesses and inherent methods).
        let mut members: IndexMap<String, (Symbol, &'a Func)> = IndexMap::default();
        for member in &body.decls {
            if let DeclKind::Method { func, .. } = &member.kind
                && let Ok(method) = func.name.symbol()
            {
                members.insert(func.name.name_str(), (method, func));
            }
        }
        let mut witnessed: Vec<String> = vec![];

        let mut protocols = vec![];
        for conformance_annotation in conformances {
            let Ok(protocol) = conformance_annotation.symbol() else {
                continue;
            };
            let Some(info) = self.catalog.protocols.get(&protocol).cloned() else {
                self.unsupported(decl.id, "conforming to an unknown protocol");
                continue;
            };
            protocols.push(protocol);

            let mut conformance = Conformance {
                params: params.clone(),
                self_args: self_args.clone(),
                context: context.clone(),
                ..Default::default()
            };

            // Positional associated-type application: `Iterator<Element>`
            // binds the protocol's assoc params in declaration order.
            if let TypeAnnotationKind::Nominal {
                generics: assoc_args,
                ..
            } = &conformance_annotation.kind
            {
                for (assoc_symbol, arg) in info.assoc.values().zip(assoc_args) {
                    let binding = self.lower_annotation(arg);
                    conformance.assoc.insert(*assoc_symbol, binding);
                }
            }

            self.self_types.push(self_ty.clone());
            for (label, requirement) in &info.requirements {
                match members.get(label) {
                    Some((witness, func)) => {
                        conformance.witnesses.insert(label.clone(), *witness);
                        witnessed.push(label.clone());
                        self.infer_assoc_bindings(requirement, func, &mut conformance);
                    }
                    None => {
                        if !requirement.has_default {
                            self.errors.push((
                                TypeError::MissingWitness {
                                    protocol: protocol.to_string(),
                                    requirement: label.clone(),
                                },
                                decl.id,
                            ));
                        }
                    }
                }
            }
            self.self_types.pop();

            self.catalog
                .conformances
                .insert((head, protocol), conformance);
            let by_head = self.catalog.conformances_by_head.entry(head).or_default();
            if !by_head.contains(&protocol) {
                by_head.push(protocol);
            }
        }

        // Members that witness no requirement are inherent: register their
        // annotation-derived signatures so any group can dispatch on them.
        self.self_types.push(self_ty.clone());
        for (label, (method, func)) in &members {
            if witnessed.contains(label) {
                continue;
            }
            let sig_params: Vec<Ty> = func
                .params
                .iter()
                .map(|p| match &p.type_annotation {
                    Some(annotation) => self.lower_annotation(annotation),
                    None => Ty::Var(self.store.fresh_ty(OUTER_LEVEL, p.id)),
                })
                .collect();
            let ret = match &func.ret {
                Some(annotation) => self.lower_annotation(annotation),
                None => Ty::Var(self.store.fresh_ty(OUTER_LEVEL, func.id)),
            };
            let eff = EffectRow {
                effects: Default::default(),
                tail: Some(EffTail::Param(*method)),
            };
            let member = crate::types::catalog::InherentMember {
                symbol: *method,
                sig: Ty::Func(sig_params, Box::new(ret), eff),
                params: params.clone(),
                self_args: self_args.clone(),
            };
            self.catalog
                .extend_members
                .entry(head)
                .or_default()
                .insert(label.clone(), member);
            self.catalog.add_owner(label, MemberOwner::Nominal(head));
        }
        self.self_types.pop();

        Some(ExtendWork {
            self_ty,
            decl,
            protocols,
        })
    }

    /// One-way match of a requirement signature against a witness's declared
    /// annotations: wherever the requirement says `Param(assoc)` and the
    /// witness annotation gives a concrete type, that's the conformance's
    /// binding for the associated type.
    fn infer_assoc_bindings(
        &mut self,
        requirement: &Requirement,
        func: &Func,
        conformance: &mut Conformance,
    ) {
        let Ty::Func(req_params, req_ret, _) = &requirement.sig else {
            return;
        };
        let witness_params: Vec<Option<Ty>> = func
            .params
            .iter()
            .map(|p| {
                p.type_annotation
                    .as_ref()
                    .map(|annotation| self.lower_annotation(annotation))
            })
            .collect();
        let witness_ret = func
            .ret
            .as_ref()
            .map(|annotation| self.lower_annotation(annotation));

        for (pattern, witness) in req_params.iter().zip(&witness_params) {
            if let Some(witness) = witness {
                collect_assoc_bindings(pattern, witness, &mut conformance.assoc);
            }
        }
        if let Some(witness) = &witness_ret {
            collect_assoc_bindings(req_ret, witness, &mut conformance.assoc);
        }
    }

    fn register_generic_bounds(&mut self, generics: &[GenericDecl]) {
        for generic in generics {
            let Ok(symbol) = generic.name.symbol() else {
                continue;
            };
            let bounds: Vec<Symbol> = generic
                .conformances
                .iter()
                .filter_map(|c| c.symbol().ok())
                .collect();
            self.catalog.param_bounds.insert(symbol, bounds);
        }
    }

    /// Check an extend's member bodies as a mini binding group, equating
    /// each witness against its requirement (this is what infers unannotated
    /// witness return types and rejects mismatched witnesses).
    fn check_extend(&mut self, work: ExtendWork<'a>) {
        let DeclKind::Extend { body, .. } = &work.decl.kind else {
            return;
        };
        self.level = GROUP_LEVEL;
        debug_assert!(self.wanteds.is_empty());

        let group_eff = EffectRow::open(self.store.fresh_eff(OUTER_LEVEL, NodeID::SYNTHESIZED));
        let group_ret = Ty::Var(self.store.fresh_ty(OUTER_LEVEL, NodeID::SYNTHESIZED));
        self.eff_stack.push(group_eff);
        self.ret_stack.push(group_ret);
        self.self_types.push(work.self_ty.clone());

        let mut outputs: Vec<(Symbol, Ty)> = vec![];
        for member in &body.decls {
            let DeclKind::Method { func, .. } = &member.kind else {
                continue;
            };
            let Ok(method) = func.name.symbol() else {
                continue;
            };
            let ty = self.with_binder(method, |this| this.infer_func(func));

            // Witness ~ requirement (substituting Self and the conformance's
            // associated bindings).
            let label = func.name.name_str();
            for protocol in &work.protocols {
                let Some((owner, requirement)) = self.catalog.requirement_in(*protocol, &label)
                else {
                    continue;
                };
                let requirement = requirement.clone();
                let assoc_symbols: Vec<Symbol> = self
                    .catalog
                    .protocols
                    .get(&owner)
                    .map(|i| i.assoc.values().copied().collect())
                    .unwrap_or_default();
                let bindings = self
                    .catalog
                    .conformances
                    .get(&(head_symbol(&work.self_ty), owner))
                    .map(|c| c.assoc.clone())
                    .unwrap_or_default();

                let mut tys: FxHashMap<Symbol, Ty> = FxHashMap::default();
                tys.insert(owner, work.self_ty.clone());
                for assoc in assoc_symbols {
                    let binding = bindings
                        .get(&assoc)
                        .cloned()
                        .unwrap_or_else(|| Ty::Var(self.store.fresh_ty(self.level, member.id)));
                    tys.insert(assoc, binding);
                }
                let mut effs = FxHashMap::default();
                effs.insert(
                    requirement.symbol,
                    EffTail::Var(self.store.fresh_eff(self.level, member.id)),
                );
                let expected = requirement.sig.substitute(&tys, &effs, &Default::default());
                self.emit_eq(expected, ty.clone(), member.id, CtReason::Annotation);
                break;
            }

            outputs.push((method, ty));
        }

        self.self_types.pop();
        self.ret_stack.pop();
        self.eff_stack.pop();

        let wanteds = std::mem::take(&mut self.wanteds);
        let residuals = self.run_solver(wanteds);
        self.report_unresolved_residuals(residuals);

        for (symbol, ty) in outputs {
            let zonked = self.store.zonk_ty(&ty);
            self.schemes.insert(symbol, Scheme::mono(zonked));
        }
    }

    /// Check one default-bodied requirement generically over Self.
    fn check_protocol_default(
        &mut self,
        protocol: Symbol,
        requirement_symbol: Symbol,
        func: &'a Func,
    ) {
        self.level = GROUP_LEVEL;
        debug_assert!(self.wanteds.is_empty());

        // Self conforms to the protocol by construction; registering the
        // bound lets `self.other_requirement(...)` dispatch (and supers
        // resolve through the bounds closure).
        self.catalog
            .param_bounds
            .entry(protocol)
            .or_insert_with(|| vec![protocol]);

        let group_eff = EffectRow::open(self.store.fresh_eff(OUTER_LEVEL, NodeID::SYNTHESIZED));
        let group_ret = Ty::Var(self.store.fresh_ty(OUTER_LEVEL, NodeID::SYNTHESIZED));
        self.eff_stack.push(group_eff);
        self.ret_stack.push(group_ret);
        self.self_types.push(Ty::Param(protocol));

        let inferred = self.with_binder(requirement_symbol, |this| this.infer_func(func));
        let expected = self
            .catalog
            .protocols
            .get(&protocol)
            .and_then(|info| info.requirements.get(&func.name.name_str()))
            .map(|requirement| requirement.sig.clone());
        if let Some(expected) = expected {
            let mut effs = FxHashMap::default();
            effs.insert(
                requirement_symbol,
                EffTail::Var(self.store.fresh_eff(self.level, func.id)),
            );
            let expected = expected.substitute(&Default::default(), &effs, &Default::default());
            self.emit_eq(expected, inferred, func.id, CtReason::Annotation);
        }

        self.self_types.pop();
        self.ret_stack.pop();
        self.eff_stack.pop();

        let wanteds = std::mem::take(&mut self.wanteds);
        let residuals = self.run_solver(wanteds);
        self.report_unresolved_residuals(residuals);
    }

    fn run_solver(&mut self, wanteds: Vec<Constraint>) -> Vec<Constraint> {
        let mut solver = Solver {
            store: &mut self.store,
            errors: &mut self.errors,
            catalog: &self.catalog,
            schemes: &self.schemes,
            mono: &self.mono,
            instantiations: &mut self.instantiations,
            member_resolutions: &mut self.member_resolutions,
            level: self.level,
            derived_seen: Default::default(),
        };
        solver.solve(wanteds)
    }

    /// Residuals in a context that cannot generalize float out to the final
    /// solve (their heads may be solved by a later group).
    fn report_unresolved_residuals(&mut self, residuals: Vec<Constraint>) {
        self.deferred.extend(residuals);
    }

    /// The final solve over everything that floated out of its group. After
    /// this, a variable-headed predicate really is unsolvable: improvement
    /// applies one last time (the solver owns every level now), then errors.
    fn solve_deferred(&mut self) {
        let deferred = std::mem::take(&mut self.deferred);
        if deferred.is_empty() {
            return;
        }
        self.level = OUTER_LEVEL;
        let leftover = self.run_solver(deferred);
        self.level = GROUP_LEVEL;
        for constraint in leftover {
            match constraint {
                Constraint::Conforms {
                    ty,
                    protocol,
                    origin,
                    ..
                } => {
                    let rendered = self.store.render(&ty);
                    self.errors.push((
                        TypeError::NotConforming {
                            ty: rendered,
                            protocol: protocol.to_string(),
                        },
                        origin.node,
                    ));
                }
                Constraint::HasMember {
                    receiver,
                    label,
                    origin,
                    ..
                } => {
                    let receiver = self.store.render(&receiver);
                    self.errors.push((
                        TypeError::UnknownMember {
                            receiver,
                            label: label.to_string(),
                        },
                        origin.node,
                    ));
                }
                Constraint::Eq(a, b, origin) => {
                    // A projection equality that never reduced: unprovable.
                    let expected = self.store.render(&a);
                    let found = self.store.render(&b);
                    self.errors
                        .push((TypeError::Mismatch { expected, found }, origin.node));
                }
                _ => {}
            }
        }
    }

    // ----- Binding groups -------------------------------------------------

    /// Check one binding group: skeletons at the group's level, generate
    /// every binder's constraints, solve once, then generalize (THIH-style
    /// per-group quantification, value-restricted).
    fn check_group(&mut self, binders: &[Symbol], decls: &IndexMap<Symbol, TopEntry<'a>>) {
        self.level = GROUP_LEVEL;
        debug_assert!(self.wanteds.is_empty());

        // (symbol, type, passes value restriction, was annotated, declared generics)
        let mut outputs: Vec<(Symbol, Ty, bool, bool, Vec<SchemeParam>)> = vec![];
        // Binders with a closed effect annotation (`func f() 'a -> ()`),
        // checked as an exact upper bound after the solve.
        let mut closed_annotations: Vec<(Symbol, &'a Func)> = vec![];
        // Nominal member bodies queued behind skeleton creation so members
        // can reference each other (and Lets in the same group) freely.
        let mut member_queue: Vec<(Ty, Vec<(Symbol, MemberWork<'a>)>)> = vec![];

        // Skeletons first: annotated binders use their annotation; the rest
        // get fresh variables at the group level so they generalize. A
        // variable may already exist if an earlier group referenced this
        // binder out of dependency order — reuse it (it sits at the outer
        // level, so this group conservatively won't generalize what it
        // touches).
        for binder in binders {
            match &decls[binder] {
                TopEntry::Let {
                    decl, annotation, ..
                } => {
                    if !self.mono.contains_key(binder) {
                        let skeleton = match annotation {
                            Some(annotation) => self.lower_annotation(annotation),
                            None => Ty::Var(self.store.fresh_ty(self.level, decl.id)),
                        };
                        self.mono.insert(*binder, skeleton);
                    }
                }
                TopEntry::Struct { decl } => {
                    let work = self.prepare_struct_members(*binder, decl);
                    member_queue.push(work);
                }
                TopEntry::Enum => {}
            }
        }

        // The ambient effect row for top-level right-hand-side computation
        // is not part of any binder's type: it lives at the outer level so
        // it can never be quantified.
        let group_eff = EffectRow::open(self.store.fresh_eff(OUTER_LEVEL, NodeID::SYNTHESIZED));
        let group_ret = Ty::Var(self.store.fresh_ty(OUTER_LEVEL, NodeID::SYNTHESIZED));
        self.eff_stack.push(group_eff);
        self.ret_stack.push(group_ret);

        for binder in binders {
            if let TopEntry::Let {
                decl: _,
                annotation,
                rhs,
            } = &decls[binder]
            {
                if let Some(rhs) = rhs {
                    let expected = self.mono[binder].clone();
                    self.with_binder(*binder, |this| {
                        this.check_expr(rhs, &expected, CtReason::Recursion)
                    });
                }
                // Value restriction (Wright 1995): only syntactic values of
                // unmutated binders generalize.
                let is_value = rhs
                    .map(|rhs| rhs.kind.is_syntactic_value())
                    .unwrap_or(true);
                let passes = is_value && !self.resolved.mutated_symbols.contains(binder);
                let declared = match rhs {
                    Some(Expr {
                        kind: ExprKind::Func(func),
                        ..
                    }) => self.declared_scheme_params(&func.generics),
                    _ => vec![],
                };
                if let Some(Expr {
                    kind: ExprKind::Func(func),
                    ..
                }) = rhs
                    && !func.effects.is_open
                {
                    closed_annotations.push((*binder, func));
                }
                outputs.push((
                    *binder,
                    self.mono[binder].clone(),
                    passes,
                    annotation.is_some(),
                    declared,
                ));
            }
        }

        for (self_ty, members) in member_queue {
            self.self_types.push(self_ty);
            for (symbol, work) in members {
                let ty = self.with_binder(symbol, |this| match work {
                    MemberWork::Method(func) => this.infer_func(func),
                    MemberWork::Init { params, body, node } => {
                        this.infer_callable(params, None, body, node)
                    }
                });
                let skeleton = self.mono[&symbol].clone();
                self.emit_eq(skeleton.clone(), ty, NodeID::SYNTHESIZED, CtReason::Recursion);
                // Member bodies are function literals: always values.
                outputs.push((symbol, skeleton, true, false, vec![]));
            }
            self.self_types.pop();
        }

        self.eff_stack.pop();
        self.ret_stack.pop();

        let wanteds = std::mem::take(&mut self.wanteds);
        let residuals = self.run_solver(wanteds);

        // Closed effect annotations are exact upper bounds on the inferred
        // row, checked at the declaration site so arrow rows stay open
        // (deviation from Koka's open-coercion elaboration, POPL 2017 §3).
        for (binder, func) in closed_annotations {
            let declared: Vec<Symbol> = func
                .effects
                .names
                .iter()
                .filter_map(|n| n.symbol().ok())
                .collect();
            let ty = self.mono[&binder].clone();
            if let Ty::Func(_, _, eff) = self.store.zonk_ty(&ty) {
                for effect in &eff.effects {
                    if !declared.contains(effect) {
                        self.errors.push((
                            TypeError::UndeclaredEffect {
                                effect: effect.to_string(),
                            },
                            func.id,
                        ));
                    }
                }
            }
        }

        // THIH's restricted-group rule: one restricted binder makes the
        // whole group monomorphic.
        let generalizable = outputs.iter().all(|(_, _, passes, ..)| *passes);

        // Residual variable-headed Conforms become bounds on the parameters
        // about to be quantified (THIH §11.6.2 context splitting); in a
        // monomorphic group they are inference failures.
        let mut var_bounds: FxHashMap<u32, Vec<Bound>> = FxHashMap::default();
        for residual in residuals {
            match &residual {
                Constraint::Conforms {
                    ty,
                    protocol,
                    assoc,
                    ..
                } => {
                    let Ty::Var(v) = self.store.shallow(ty) else {
                        continue;
                    };
                    let root = self.store.find(v.0);
                    if self.store.level(root) <= OUTER_LEVEL || !generalizable {
                        // A later group may still solve this variable:
                        // float the obligation out to the final solve.
                        self.deferred.push(residual);
                        continue;
                    }
                    let assoc: Vec<(Symbol, Ty)> = assoc
                        .iter()
                        .map(|(s, t)| (*s, self.store.zonk_ty(t)))
                        .collect();
                    let bound = Bound {
                        protocol: *protocol,
                        assoc,
                    };
                    let bounds = var_bounds.entry(root).or_default();
                    if !bounds.contains(&bound) {
                        bounds.push(bound);
                    }
                }
                Constraint::HasMember { .. } | Constraint::Eq(..) => {
                    self.deferred.push(residual)
                }
                _ => {}
            }
        }

        if generalizable {
            let mut generalizer = Generalizer::new(
                &mut self.store,
                self.symbols,
                self.module_id,
                OUTER_LEVEL,
                var_bounds,
            );
            for (symbol, ty, _, annotated, declared) in &outputs {
                let scheme = if *annotated {
                    Scheme::mono(generalizer.store.zonk_ty(ty))
                } else {
                    generalizer.generalize(ty, declared)
                };
                self.schemes.insert(*symbol, scheme);
            }
        } else {
            for (symbol, ty, ..) in &outputs {
                let zonked = self.store.zonk_ty(ty);
                self.schemes.insert(*symbol, Scheme::mono(zonked));
            }
        }

        for (symbol, ..) in &outputs {
            self.mono.remove(symbol);
        }
    }

    fn declared_scheme_params(&mut self, generics: &[GenericDecl]) -> Vec<SchemeParam> {
        generics
            .iter()
            .filter_map(|generic| {
                let symbol = generic.name.symbol().ok()?;
                let bounds = generic
                    .conformances
                    .iter()
                    .filter_map(|c| c.symbol().ok())
                    .map(|protocol| Bound {
                        protocol,
                        assoc: vec![],
                    })
                    .collect();
                Some(SchemeParam { symbol, bounds })
            })
            .collect()
    }

    /// Create member skeletons for a struct's methods and initializers and
    /// queue their bodies. Returns (Self type, member work list).
    fn prepare_struct_members(
        &mut self,
        symbol: Symbol,
        decl: &'a Decl,
    ) -> (Ty, Vec<(Symbol, MemberWork<'a>)>) {
        let params = self
            .catalog
            .structs
            .get(&symbol)
            .map(|info| info.params.clone())
            .unwrap_or_default();
        let self_ty = Ty::Nominal(symbol, params.iter().map(|p| Ty::Param(*p)).collect());

        let mut work = vec![];
        let DeclKind::Struct { body, .. } = &decl.kind else {
            return (self_ty, work);
        };
        for member in &body.decls {
            match &member.kind {
                DeclKind::Method { func, .. } => {
                    if let Ok(method) = func.name.symbol() {
                        work.push((method, MemberWork::Method(func)));
                    }
                }
                DeclKind::Init { name, params, body } => {
                    if let Ok(init) = name.symbol() {
                        work.push((
                            init,
                            MemberWork::Init {
                                params,
                                body,
                                node: member.id,
                            },
                        ));
                    }
                }
                _ => {}
            }
        }
        for (member_symbol, _) in &work {
            if !self.mono.contains_key(member_symbol) {
                let var = Ty::Var(self.store.fresh_ty(self.level, decl.id));
                self.mono.insert(*member_symbol, var);
            }
        }
        (self_ty, work)
    }

    fn finalize(mut self) -> (TypeOutput, Vec<AnyDiagnostic>) {
        // Re-zonk everything: schemes stored mid-run may share variables that
        // a later group solved.
        let mut schemes = FxHashMap::default();
        for (symbol, scheme) in std::mem::take(&mut self.schemes) {
            let ty = self.store.zonk_ty(&scheme.ty);
            schemes.insert(symbol, Scheme { ty, ..scheme });
        }
        let mut node_types = FxHashMap::default();
        for (node, ty) in std::mem::take(&mut self.node_types) {
            node_types.insert(node, self.store.zonk_ty(&ty));
        }
        let mut instantiations = FxHashMap::default();
        for (node, subst) in std::mem::take(&mut self.instantiations) {
            let subst = subst
                .into_iter()
                .map(|(sym, ty)| (sym, self.store.zonk_ty(&ty)))
                .collect();
            instantiations.insert(node, subst);
        }
        // Handler payload types pick up everything the perform sites
        // taught their (possibly unannotated) effect parameters.
        let mut handler_payload_tys = FxHashMap::default();
        for (handler, tys) in std::mem::take(&mut self.handler_payload_tys) {
            let tys = tys.iter().map(|ty| self.store.zonk_ty(ty)).collect();
            handler_payload_tys.insert(handler, tys);
        }

        let diagnostics = self
            .errors
            .into_iter()
            .map(|(kind, id)| {
                AnyDiagnostic::Types(Diagnostic {
                    id,
                    severity: Severity::Error,
                    kind,
                })
            })
            .collect();

        (
            TypeOutput {
                catalog: self.catalog,
                node_types,
                schemes,
                instantiations,
                member_resolutions: self.member_resolutions,
                performs_into: self.performs_into,
                binder_refs: self.binder_refs,
                handler_payload_tys,
            },
            diagnostics,
        )
    }

    // ----- Expressions -------------------------------------------------

    fn infer_expr(&mut self, expr: &Expr) -> Ty {
        let ty = self.infer_expr_kind(expr);
        self.node_types.insert(expr.id, ty.clone());
        ty
    }

    /// Checking mode: push the expected type inward where syntax allows
    /// (Pierce & Turner; DK 2021's mode recipe), otherwise infer and emit an
    /// equality oriented expected-then-found for blame.
    fn check_expr(&mut self, expr: &Expr, expected: &Ty, reason: CtReason) {
        match &expr.kind {
            // Leading-dot variant construction (`.sleep(ms)`, `.none`)
            // resolves through the expected enum — checking mode is what
            // makes the head known (bidirectional payoff).
            ExprKind::Member(None, label, _) => {
                if self.check_leading_dot(expr, label, None, expected) {
                    return;
                }
                let ty = self.infer_expr(expr);
                self.emit_eq(expected.clone(), ty, expr.id, reason);
            }
            ExprKind::Call { callee, args, .. }
                if matches!(callee.kind, ExprKind::Member(None, _, _)) =>
            {
                if let ExprKind::Member(None, label, _) = &callee.kind
                    && self.check_leading_dot(expr, label, Some(args), expected)
                {
                    return;
                }
                let ty = self.infer_expr(expr);
                self.emit_eq(expected.clone(), ty, expr.id, reason);
            }
            ExprKind::Func(func) => {
                if let Ty::Func(params, ret, eff) = self.store.shallow(expected)
                    && params.len() == func.params.len()
                {
                    let ty = self.infer_func_against(func, &params, &ret, &eff);
                    self.node_types.insert(expr.id, ty);
                    return;
                }
                let ty = self.infer_expr(expr);
                self.emit_eq(expected.clone(), ty, expr.id, reason);
            }
            _ => {
                let ty = self.infer_expr(expr);
                self.emit_eq(expected.clone(), ty, expr.id, reason);
            }
        }
    }

    /// Try to resolve `.variant`/`.variant(args)` against an expected enum
    /// type. Returns false when the expected head is not (yet) a known enum.
    fn check_leading_dot(
        &mut self,
        expr: &Expr,
        label: &Label,
        args: Option<&[CallArg]>,
        expected: &Ty,
    ) -> bool {
        let Ty::Nominal(symbol, enum_args) = self.store.shallow(expected) else {
            return false;
        };
        let Some(info) = self.catalog.enums.get(&symbol).cloned() else {
            return false;
        };
        let Some(variant) = info.variants.get(&label.to_string()).cloned() else {
            self.errors.push((
                TypeError::UnknownMember {
                    receiver: self.store.render(expected),
                    label: label.to_string(),
                },
                expr.id,
            ));
            self.node_types.insert(expr.id, Ty::Error);
            return true;
        };
        self.member_resolutions
            .insert(expr.id, MemberResolution::Direct(variant.symbol));
        if !info.params.is_empty() {
            self.record_instantiation(expr.id, &info.params, &enum_args);
        }
        let substitution = param_subst(&info.params, &enum_args);
        let args = args.unwrap_or(&[]);
        if args.len() != variant.payloads.len() {
            self.errors.push((
                TypeError::ArityMismatch {
                    expected: variant.payloads.len(),
                    found: args.len(),
                },
                expr.id,
            ));
        } else {
            for (arg, payload) in args.iter().zip(&variant.payloads) {
                let payload =
                    payload.substitute(&substitution, &Default::default(), &Default::default());
                self.check_expr(&arg.value, &payload, CtReason::Apply);
            }
        }
        self.node_types.insert(expr.id, expected.clone());
        true
    }

    fn infer_expr_kind(&mut self, expr: &Expr) -> Ty {
        match &expr.kind {
            ExprKind::LiteralInt(_) => Ty::Nominal(Symbol::Int, vec![]),
            ExprKind::LiteralFloat(_) => Ty::Nominal(Symbol::Float, vec![]),
            ExprKind::LiteralTrue | ExprKind::LiteralFalse => Ty::Nominal(Symbol::Bool, vec![]),
            ExprKind::LiteralString(_) => Ty::Nominal(Symbol::String, vec![]),

            ExprKind::LiteralArray(items) => {
                let element = Ty::Var(self.store.fresh_ty(self.level, expr.id));
                for item in items {
                    self.check_expr(item, &element, CtReason::ArrayElement);
                }
                Ty::Nominal(Symbol::Array, vec![element])
            }

            ExprKind::Tuple(items) => match items.as_slice() {
                // `()` is the unit value, `(e)` is grouping.
                [] => Ty::unit(),
                [single] => self.infer_expr(single),
                _ => Ty::Tuple(items.iter().map(|item| self.infer_expr(item)).collect()),
            },

            ExprKind::RecordLiteral { fields, spread } => {
                if spread.is_some() {
                    self.unsupported(expr.id, "record spread");
                    return Ty::Error;
                }
                let fields = fields
                    .iter()
                    .map(|field| {
                        let ty = self.infer_expr(&field.value);
                        (Label::Named(field.label.name_str()), ty)
                    })
                    .collect();
                Ty::Record(Row::closed(fields))
            }

            ExprKind::Variable(name) => self.lookup(name, expr.id),

            ExprKind::Block(block) => self.infer_block_value(block),

            ExprKind::If(condition, then_block, else_block) => {
                let cond_ty = self.infer_expr(condition);
                self.emit_eq(
                    Ty::Nominal(Symbol::Bool, vec![]),
                    cond_ty,
                    condition.id,
                    CtReason::Condition,
                );
                let then_ty = self.infer_block_value(then_block);
                let else_ty = self.infer_block_value(else_block);
                self.join(then_ty, else_ty, expr.id)
            }

            ExprKind::Match(scrutinee, arms) => {
                let scrutinee_ty = self.infer_expr(scrutinee);
                let mut result: Option<Ty> = None;
                for arm in arms {
                    self.check_pattern(&arm.pattern, &scrutinee_ty);
                    let arm_ty = self.infer_block_value(&arm.body);
                    result = Some(match result {
                        None => arm_ty,
                        Some(acc) => self.join(acc, arm_ty, arm.id),
                    });
                }
                result.unwrap_or(Ty::Nominal(Symbol::Never, vec![]))
            }

            ExprKind::Call {
                callee,
                type_args,
                args,
                trailing_block,
            } => {
                if let ExprKind::Constructor(name) = &callee.kind {
                    return self.infer_construction(
                        expr,
                        callee,
                        name,
                        type_args,
                        args,
                        trailing_block,
                    );
                }
                if let ExprKind::Member(Some(receiver), label, _) = &callee.kind
                    && !matches!(receiver.kind, ExprKind::Constructor(_))
                {
                    if !type_args.is_empty() {
                        self.unsupported(expr.id, "type arguments on method calls");
                    }
                    return self.infer_member_call(
                        expr,
                        callee,
                        receiver,
                        label,
                        args,
                        trailing_block,
                    );
                }
                let callee_ty = self.infer_expr(callee);
                if !type_args.is_empty() {
                    self.apply_type_args(callee.id, type_args);
                }
                self.finish_call(expr.id, callee_ty, args, trailing_block)
            }

            ExprKind::Func(func) => self.infer_func(func),

            ExprKind::As(inner, annotation) => {
                let ty = self.lower_annotation(annotation);
                self.check_expr(inner, &ty, CtReason::Annotation);
                ty
            }

            ExprKind::Member(Some(receiver), label, _) => {
                if let ExprKind::Constructor(name) = &receiver.kind {
                    let Ok(symbol) = name.symbol() else {
                        return Ty::Error;
                    };
                    return match self.resolve_type_member(symbol, label, expr.id) {
                        Some(ty) => ty,
                        None => {
                            self.errors.push((
                                TypeError::UnknownMember {
                                    receiver: name.name_str(),
                                    label: label.to_string(),
                                },
                                expr.id,
                            ));
                            Ty::Error
                        }
                    };
                }
                // A HasMember predicate (Gaster & Jones 1996); the solver
                // discharges it as soon as the receiver's head is known.
                let receiver_ty = self.infer_expr(receiver);
                let member = Ty::Var(self.store.fresh_ty(self.level, expr.id));
                self.wanteds.push(Constraint::HasMember {
                    receiver: receiver_ty,
                    label: label.clone(),
                    member: member.clone(),
                    origin: CtOrigin::new(expr.id, CtReason::Apply),
                });
                member
            }
            ExprKind::Member(None, _, _) => {
                self.unsupported(expr.id, "leading-dot member access");
                Ty::Error
            }

            ExprKind::Constructor(_) => {
                self.unsupported(expr.id, "type names as values");
                Ty::Error
            }
            ExprKind::CallEffect {
                effect_name, args, ..
            } => {
                // Performing an operation: arguments check against the
                // declared signature, the effect joins the ambient row
                // (Plotkin & Pretnar 2009 operations; row growth per Koka).
                // Row subtraction at handlers and closed-annotation checks
                // land in milestone 5.
                let Ok(symbol) = effect_name.symbol() else {
                    return Ty::Error;
                };
                let Some(sig) = self.catalog.effects.get(&symbol).cloned() else {
                    self.unsupported(expr.id, "calling an undeclared effect");
                    return Ty::Error;
                };
                if args.len() == sig.params.len() {
                    for (arg, param) in args.iter().zip(&sig.params) {
                        self.check_expr(&arg.value, param, CtReason::Apply);
                    }
                } else {
                    self.errors.push((
                        TypeError::ArityMismatch {
                            expected: sig.params.len(),
                            found: args.len(),
                        },
                        expr.id,
                    ));
                }
                // A perform the resolver routed to a lexical handler is
                // discharged right there — it never escapes into the
                // function's latent row (handler discharge in the row
                // reading, Leijen POPL 2017 §3). The discharge is still
                // recorded in the capability tables: the lowerer needs to
                // know which functions can abort, and the row no longer
                // says (effects as capabilities — Brachthäuser et al.,
                // OOPSLA 2020).
                match self.resolved.effect_handlers.get(&expr.id) {
                    Some(&handler) => {
                        if let Some(&binder) = self.binder_stack.last() {
                            self.performs_into.entry(binder).or_default().insert(handler);
                        }
                    }
                    None => {
                        let tail = self.store.fresh_eff(self.level, expr.id);
                        let performed = EffectRow {
                            effects: [symbol].into(),
                            tail: Some(EffTail::Var(tail)),
                        };
                        self.emit_eff_eq(performed, self.ambient_eff(), expr.id);
                    }
                }
                sig.ret
            }
            ExprKind::InlineIR(_) => {
                // Inline IR is trusted: it takes whatever type its context
                // demands (a fresh variable solved by the surrounding
                // annotation or return type).
                Ty::Var(self.store.fresh_ty(self.level, expr.id))
            }
            ExprKind::Unary(..) | ExprKind::Binary(..) => {
                // Operators are desugared to method calls during name
                // resolution; reaching one here is a transform bug.
                self.unsupported(expr.id, "raw operator expression");
                Ty::Error
            }
            ExprKind::RowVariable(_) => {
                self.unsupported(expr.id, "row variables in expressions");
                Ty::Error
            }
            ExprKind::Incomplete(_) => Ty::Error,
        }
    }

    // ----- Calls ---------------------------------------------------------

    /// The shared tail of every call: callee type against arguments, the
    /// callee's latent effects unified into the ambient row (Koka's
    /// application rule).
    fn finish_call(
        &mut self,
        node: NodeID,
        callee_ty: Ty,
        args: &[CallArg],
        trailing_block: &Option<Block>,
    ) -> Ty {
        let arg_count = args.len() + usize::from(trailing_block.is_some());

        match self.store.shallow(&callee_ty) {
            Ty::Func(params, ret, eff) => {
                if params.len() != arg_count {
                    self.errors.push((
                        TypeError::ArityMismatch {
                            expected: params.len(),
                            found: arg_count,
                        },
                        node,
                    ));
                    return Ty::Error;
                }
                for (arg, param) in args.iter().zip(&params) {
                    self.check_expr(&arg.value, param, CtReason::Apply);
                }
                if let Some(block) = trailing_block {
                    let block_ty = self.infer_closure_block(block);
                    self.emit_eq(
                        params[args.len()].clone(),
                        block_ty,
                        block.id,
                        CtReason::Apply,
                    );
                }
                self.emit_eff_eq(eff, self.ambient_eff(), node);
                *ret
            }
            Ty::Var(_) => {
                let mut arg_tys: Vec<Ty> =
                    args.iter().map(|arg| self.infer_expr(&arg.value)).collect();
                if let Some(block) = trailing_block {
                    arg_tys.push(self.infer_closure_block(block));
                }
                let ret = Ty::Var(self.store.fresh_ty(self.level, node));
                let expected = Ty::Func(arg_tys, Box::new(ret.clone()), self.ambient_eff());
                self.emit_eq(expected, callee_ty, node, CtReason::Apply);
                ret
            }
            Ty::Error => Ty::Error,
            other => {
                let found = self.store.render(&other);
                self.errors.push((TypeError::NotAFunction { found }, node));
                Ty::Error
            }
        }
    }

    /// `recv.label(args)`: a HasMember predicate plus the ordinary call
    /// tail. The member variable carries the call's arity, so an in-flight
    /// method of the same group resolves once its signature variable does.
    fn infer_member_call(
        &mut self,
        expr: &Expr,
        callee: &Expr,
        receiver: &Expr,
        label: &Label,
        args: &[CallArg],
        trailing_block: &Option<Block>,
    ) -> Ty {
        let receiver_ty = self.infer_expr(receiver);
        let member = Ty::Var(self.store.fresh_ty(self.level, callee.id));
        self.wanteds.push(Constraint::HasMember {
            receiver: receiver_ty,
            label: label.clone(),
            member: member.clone(),
            origin: CtOrigin::new(callee.id, CtReason::Apply),
        });
        self.node_types.insert(callee.id, member.clone());
        self.finish_call(expr.id, member, args, trailing_block)
    }

    /// `Person(args)`: pick an initializer by arity, equate its
    /// self-prepended signature against a fresh instantiation of the struct.
    fn infer_construction(
        &mut self,
        expr: &Expr,
        callee: &Expr,
        name: &Name,
        type_args: &[TypeAnnotation],
        args: &[CallArg],
        trailing_block: &Option<Block>,
    ) -> Ty {
        let Ok(symbol) = name.symbol() else {
            return Ty::Error;
        };
        let Some(info) = self.catalog.structs.get(&symbol).cloned() else {
            if self.catalog.enums.contains_key(&symbol) {
                self.unsupported(expr.id, "constructing an enum directly (use a case)");
            } else {
                self.unsupported(expr.id, "constructing this type");
            }
            return Ty::Error;
        };

        let theta: Vec<Ty> = info
            .params
            .iter()
            .map(|_| Ty::Var(self.store.fresh_ty(self.level, expr.id)))
            .collect();
        if !info.params.is_empty() {
            self.record_instantiation(expr.id, &info.params, &theta);
        }
        // `ArrayIterator<Element>(array: self)`: explicit type arguments pin
        // the instantiation positionally.
        for (annotation, target) in type_args.iter().zip(&theta) {
            let ty = self.lower_annotation(annotation);
            self.emit_eq(target.clone(), ty, annotation.id, CtReason::Annotation);
        }
        let self_ty = Ty::Nominal(symbol, theta.clone());

        let arg_count = args.len() + usize::from(trailing_block.is_some());
        let init = info
            .inits
            .iter()
            .copied()
            .find(|init| self.callable_arity(*init) == Some(arg_count + 1))
            .or_else(|| info.inits.first().copied());
        let Some(init) = init else {
            self.unsupported(expr.id, "constructing a type with no initializer");
            return Ty::Error;
        };
        self.member_resolutions
            .insert(callee.id, MemberResolution::Direct(init));

        let substitution = param_subst(&info.params, &theta);
        let signature = self
            .lookup_symbol_ty(init, expr.id)
            .substitute(&substitution, &Default::default(), &Default::default());

        match self.store.shallow(&signature) {
            Ty::Func(params, _ret, eff) => {
                if params.len() != arg_count + 1 {
                    self.errors.push((
                        TypeError::ArityMismatch {
                            expected: params.len().saturating_sub(1),
                            found: arg_count,
                        },
                        expr.id,
                    ));
                    return Ty::Error;
                }
                self.emit_eq(params[0].clone(), self_ty.clone(), expr.id, CtReason::Apply);
                for (arg, param) in args.iter().zip(&params[1..]) {
                    self.check_expr(&arg.value, param, CtReason::Apply);
                }
                if let Some(block) = trailing_block {
                    let block_ty = self.infer_closure_block(block);
                    self.emit_eq(
                        params[args.len() + 1].clone(),
                        block_ty,
                        block.id,
                        CtReason::Apply,
                    );
                }
                self.emit_eff_eq(eff, self.ambient_eff(), expr.id);
                self.node_types.insert(
                    callee.id,
                    Ty::Func(
                        params[1..].to_vec(),
                        Box::new(self_ty.clone()),
                        EffectRow::pure(),
                    ),
                );
                self_ty
            }
            Ty::Var(_) => {
                // In-flight initializer: the struct is being constructed
                // within its own binding group.
                if !info.params.is_empty() {
                    self.unsupported(
                        expr.id,
                        "constructing a generic type within its own binding group",
                    );
                    return Ty::Error;
                }
                let mut arg_tys: Vec<Ty> = vec![self_ty.clone()];
                arg_tys.extend(args.iter().map(|arg| self.infer_expr(&arg.value)));
                if let Some(block) = trailing_block {
                    arg_tys.push(self.infer_closure_block(block));
                }
                let expected = Ty::Func(
                    arg_tys,
                    Box::new(self_ty.clone()),
                    self.ambient_eff(),
                );
                self.emit_eq(signature, expected, expr.id, CtReason::Apply);
                self_ty
            }
            Ty::Error => Ty::Error,
            other => {
                let found = self.store.render(&other);
                self.errors
                    .push((TypeError::NotAFunction { found }, expr.id));
                Ty::Error
            }
        }
    }

    // ----- Member resolution ----------------------------------------------
    // Value-receiver member access is a HasMember predicate solved in
    // solve.rs. Only TYPE members (Constructor receivers) resolve here.

    /// Resolve `Type.label`: enum variants (constructors, or bare values for
    /// payload-less cases), protocol requirements (the protocol-static form
    /// operators desugar to: `Add.add(lhs, rhs)`), and static methods.
    fn resolve_type_member(&mut self, symbol: Symbol, label: &Label, node: NodeID) -> Option<Ty> {
        let label_str = label.to_string();

        if let Some(info) = self.catalog.enums.get(&symbol).cloned() {
            let variant = info.variants.get(&label_str)?;
            let theta: Vec<Ty> = info
                .params
                .iter()
                .map(|_| Ty::Var(self.store.fresh_ty(self.level, node)))
                .collect();
            if !info.params.is_empty() {
                self.record_instantiation(node, &info.params, &theta);
            }
            self.member_resolutions
                .insert(node, MemberResolution::Direct(variant.symbol));
            let substitution = param_subst(&info.params, &theta);
            let result =
                variant
                    .result
                    .substitute(&substitution, &Default::default(), &Default::default());
            if variant.payloads.is_empty() {
                return Some(result);
            }
            let payloads = variant
                .payloads
                .iter()
                .map(|p| p.substitute(&substitution, &Default::default(), &Default::default()))
                .collect();
            let eff = EffectRow::open(self.store.fresh_eff(self.level, node));
            return Some(Ty::Func(payloads, Box::new(result), eff));
        }

        // Protocol-static dispatch: `P.requirement(self, args...)`. The full
        // self-prepended signature is returned; Self is a fresh variable
        // constrained to conform, pinned by the first argument.
        if self.catalog.protocols.contains_key(&symbol) {
            let (owner, requirement) = self.catalog.requirement_in(symbol, &label_str)?;
            let requirement = requirement.clone();
            let assoc_symbols: Vec<Symbol> = self
                .catalog
                .protocols
                .get(&owner)
                .map(|i| i.assoc.values().copied().collect())
                .unwrap_or_default();

            let self_var = Ty::Var(self.store.fresh_ty(self.level, node));
            let assoc: Vec<(Symbol, Ty)> = assoc_symbols
                .iter()
                .map(|a| (*a, Ty::Var(self.store.fresh_ty(self.level, node))))
                .collect();
            let mut tys: FxHashMap<Symbol, Ty> = assoc.iter().cloned().collect();
            tys.insert(owner, self_var.clone());
            let mut effs = FxHashMap::default();
            effs.insert(
                requirement.symbol,
                EffTail::Var(self.store.fresh_eff(self.level, node)),
            );
            let signature = requirement.sig.substitute(&tys, &effs, &Default::default());

            self.wanteds.push(Constraint::Conforms {
                ty: self_var,
                protocol: owner,
                assoc,
                origin: CtOrigin::new(node, CtReason::Apply),
            });
            self.member_resolutions.insert(
                node,
                MemberResolution::ViaConformance {
                    protocol: owner,
                    witness: requirement.symbol,
                },
            );
            return Some(signature);
        }

        if let Some(info) = self.catalog.structs.get(&symbol).cloned()
            && let Some(&method) = info.statics.get(&label_str)
        {
            let theta: Vec<Ty> = info
                .params
                .iter()
                .map(|_| Ty::Var(self.store.fresh_ty(self.level, node)))
                .collect();
            if !info.params.is_empty() {
                self.record_instantiation(node, &info.params, &theta);
            }
            let substitution = param_subst(&info.params, &theta);
            let signature = self
                .lookup_symbol_ty(method, node)
                .substitute(&substitution, &Default::default(), &Default::default());
            self.member_resolutions
                .insert(node, MemberResolution::Direct(method));
            return Some(signature);
        }
        None
    }

    // ----- Functions ------------------------------------------------------

    /// Infer a function literal: parameters from annotations or fresh vars,
    /// a fresh open ambient effect row (Koka-style), body joined into the
    /// return type.
    fn infer_func(&mut self, func: &Func) -> Ty {
        self.infer_callable(&func.params, func.ret.as_ref(), &func.body, func.id)
    }

    fn infer_callable(
        &mut self,
        params: &[Parameter],
        ret_annotation: Option<&TypeAnnotation>,
        body: &Block,
        node: NodeID,
    ) -> Ty {
        let params: Vec<Ty> = params
            .iter()
            .map(|param| {
                let ty = match &param.type_annotation {
                    Some(annotation) => self.lower_annotation(annotation),
                    None => Ty::Var(self.store.fresh_ty(self.level, param.id)),
                };
                if let Ok(symbol) = param.name.symbol() {
                    self.mono.insert(symbol, ty.clone());
                }
                ty
            })
            .collect();

        let ret = match ret_annotation {
            Some(annotation) => self.lower_annotation(annotation),
            None => Ty::Var(self.store.fresh_ty(self.level, node)),
        };
        let eff = EffectRow::open(self.store.fresh_eff(self.level, node));

        self.ret_stack.push(ret.clone());
        self.eff_stack.push(eff.clone());
        // A nested function cannot resume an enclosing handler.
        let outer_handlers = std::mem::take(&mut self.handler_ret_stack);
        let body_ty = self.infer_block_value(body);
        self.handler_ret_stack = outer_handlers;
        self.eff_stack.pop();
        self.ret_stack.pop();

        if !body_ty.is_never() {
            self.emit_eq(ret.clone(), body_ty, body.id, CtReason::Body);
        }

        Ty::Func(params, Box::new(ret), eff)
    }

    /// Checking-mode function literal: expected parameter and return types
    /// are pushed into the body (the bidirectional payoff: unannotated
    /// closure params get their types from context).
    fn infer_func_against(
        &mut self,
        func: &Func,
        expected_params: &[Ty],
        expected_ret: &Ty,
        expected_eff: &EffectRow,
    ) -> Ty {
        let params: Vec<Ty> = func
            .params
            .iter()
            .zip(expected_params)
            .map(|(param, expected)| {
                let ty = match &param.type_annotation {
                    Some(annotation) => {
                        let annotated = self.lower_annotation(annotation);
                        self.emit_eq(
                            expected.clone(),
                            annotated.clone(),
                            param.id,
                            CtReason::Annotation,
                        );
                        annotated
                    }
                    None => expected.clone(),
                };
                if let Ok(symbol) = param.name.symbol() {
                    self.mono.insert(symbol, ty.clone());
                }
                ty
            })
            .collect();

        let ret = match &func.ret {
            Some(annotation) => {
                let annotated = self.lower_annotation(annotation);
                self.emit_eq(
                    expected_ret.clone(),
                    annotated.clone(),
                    func.id,
                    CtReason::Annotation,
                );
                annotated
            }
            None => expected_ret.clone(),
        };

        self.ret_stack.push(ret.clone());
        self.eff_stack.push(expected_eff.clone());
        // A nested function cannot resume an enclosing handler.
        let outer_handlers = std::mem::take(&mut self.handler_ret_stack);
        let body_ty = self.infer_block_value(&func.body);
        self.handler_ret_stack = outer_handlers;
        self.eff_stack.pop();
        self.ret_stack.pop();

        if !body_ty.is_never() {
            self.emit_eq(ret.clone(), body_ty, func.body.id, CtReason::Body);
        }

        Ty::Func(params, Box::new(ret), expected_eff.clone())
    }

    /// A trailing block treated as a closure: its labeled args are its
    /// parameters, its own return type and effect row.
    fn infer_closure_block(&mut self, block: &Block) -> Ty {
        let params: Vec<Ty> = block
            .args
            .iter()
            .map(|param| {
                let ty = match &param.type_annotation {
                    Some(annotation) => self.lower_annotation(annotation),
                    None => Ty::Var(self.store.fresh_ty(self.level, param.id)),
                };
                if let Ok(symbol) = param.name.symbol() {
                    self.mono.insert(symbol, ty.clone());
                }
                ty
            })
            .collect();

        let ret = Ty::Var(self.store.fresh_ty(self.level, block.id));
        let eff = EffectRow::open(self.store.fresh_eff(self.level, block.id));

        self.ret_stack.push(ret.clone());
        self.eff_stack.push(eff.clone());
        let body_ty = self.infer_block_value(block);
        self.eff_stack.pop();
        self.ret_stack.pop();

        if !body_ty.is_never() {
            self.emit_eq(ret.clone(), body_ty, block.id, CtReason::Body);
        }

        Ty::Func(params, Box::new(ret), eff)
    }

    // ----- Blocks, statements, declarations -----------------------------

    /// A block's value is its final expression statement; a block ending in
    /// a divergent statement is `Never`; anything else is unit.
    fn infer_block_value(&mut self, block: &Block) -> Ty {
        let mut last = StmtValue::Unit;
        let mut is_empty = true;
        let final_index = block.body.len().saturating_sub(1);
        for (index, node) in block.body.iter().enumerate() {
            is_empty = false;
            last = match node {
                Node::Decl(decl) => {
                    self.check_local_decl(decl);
                    StmtValue::Unit
                }
                // A block-final `if/else` statement is the block's value
                // (joined like the expression form).
                Node::Stmt(Stmt {
                    kind: StmtKind::If(condition, then_block, Some(else_block)),
                    ..
                }) if index == final_index => {
                    let cond_ty = self.infer_expr(condition);
                    self.emit_eq(
                        Ty::Nominal(Symbol::Bool, vec![]),
                        cond_ty,
                        condition.id,
                        CtReason::Condition,
                    );
                    let then_ty = self.infer_block_value(then_block);
                    let else_ty = self.infer_block_value(else_block);
                    StmtValue::Value(self.join(then_ty, else_ty, node.node_id()))
                }
                Node::Stmt(stmt) => self.infer_stmt(stmt),
                // Desugared `||`/`&&` blocks hold bare expressions.
                Node::Expr(expr) => StmtValue::Value(self.infer_expr(expr)),
                _ => StmtValue::Unit,
            };
        }
        if is_empty {
            return Ty::unit();
        }
        match last {
            StmtValue::Value(ty) => ty,
            StmtValue::Divergent => Ty::Nominal(Symbol::Never, vec![]),
            StmtValue::Unit => Ty::unit(),
        }
    }

    fn infer_stmt(&mut self, stmt: &Stmt) -> StmtValue {
        match &stmt.kind {
            StmtKind::Expr(expr) => StmtValue::Value(self.infer_expr(expr)),

            StmtKind::Return(value) => {
                let ty = match value {
                    Some(expr) => self.infer_expr(expr),
                    None => Ty::unit(),
                };
                let expected = self.ret_stack.last().cloned().unwrap_or(Ty::Error);
                self.emit_eq(expected, ty, stmt.id, CtReason::Return);
                StmtValue::Divergent
            }

            StmtKind::If(condition, then_block, else_block) => {
                let cond_ty = self.infer_expr(condition);
                self.emit_eq(
                    Ty::Nominal(Symbol::Bool, vec![]),
                    cond_ty,
                    condition.id,
                    CtReason::Condition,
                );
                self.infer_block_value(then_block);
                if let Some(else_block) = else_block {
                    self.infer_block_value(else_block);
                }
                StmtValue::Unit
            }

            StmtKind::Assignment(lhs, rhs) => {
                let lhs_ty = self.infer_expr(lhs);
                let rhs_ty = self.infer_expr(rhs);
                self.emit_eq(lhs_ty, rhs_ty, stmt.id, CtReason::Assignment);
                StmtValue::Unit
            }

            StmtKind::Loop(condition, body) => {
                if let Some(condition) = condition {
                    let cond_ty = self.infer_expr(condition);
                    self.emit_eq(
                        Ty::Nominal(Symbol::Bool, vec![]),
                        cond_ty,
                        condition.id,
                        CtReason::Condition,
                    );
                }
                self.infer_block_value(body);
                StmtValue::Unit
            }

            StmtKind::Break => StmtValue::Divergent,
            StmtKind::Continue(payload) => {
                // A bare `continue` re-enters the enclosing loop; with a
                // payload it resumes the enclosing handler's perform.
                if let Some(expr) = payload {
                    match self.handler_ret_stack.last().cloned() {
                        Some(expected) => {
                            self.check_expr(expr, &expected, CtReason::Apply);
                        }
                        None => self.unsupported(
                            stmt.id,
                            "continue with a value outside an effect handler",
                        ),
                    }
                }
                StmtValue::Divergent
            }

            StmtKind::For { .. } => {
                // for-loops are desugared by the name resolver; reaching one
                // is a transform bug.
                self.unsupported(stmt.id, "raw for loop");
                StmtValue::Unit
            }

            StmtKind::Handling {
                effect_name, body, ..
            } => {
                // Handler block parameters take the effect's declared
                // parameter types (handler-site inference for unannotated
                // effects refines this in milestone 5; row subtraction too).
                let sig = effect_name
                    .symbol()
                    .ok()
                    .and_then(|symbol| self.catalog.effects.get(&symbol))
                    .cloned();
                let params = sig.as_ref().map(|sig| sig.params.clone()).unwrap_or_default();
                for (arg, param) in body.args.iter().zip(&params) {
                    if let Ok(symbol) = arg.name.symbol() {
                        self.mono.insert(symbol, param.clone());
                    }
                }
                // The payload types this handler receives — zonked at
                // finalize, once the perform sites have taught the
                // unannotated parameters their types — for the lowerer's
                // capability closure.
                if let Some(&handler) = self.resolved.effect_handler_definitions.get(&stmt.id) {
                    self.handler_payload_tys.insert(handler, params.clone());
                }
                // `continue v` inside this block resumes the perform: v
                // checks against the effect's return type.
                let resume_ty = sig.map(|sig| sig.ret).unwrap_or(Ty::Error);
                self.handler_ret_stack.push(resume_ty);
                self.infer_block_value(body);
                self.handler_ret_stack.pop();
                StmtValue::Unit
            }
        }
    }

    /// Local lets: monomorphic, never generalized (OutsideIn(X) §4.2 /
    /// MonoLocalBinds).
    fn check_local_decl(&mut self, decl: &Decl) {
        match &decl.kind {
            DeclKind::Let {
                lhs,
                type_annotation,
                rhs,
            } => {
                let ty = match type_annotation {
                    Some(annotation) => self.lower_annotation(annotation),
                    None => Ty::Var(self.store.fresh_ty(self.level, decl.id)),
                };
                if let Some(rhs) = rhs {
                    self.check_expr(rhs, &ty, CtReason::Annotation);
                }
                match &lhs.kind {
                    PatternKind::Bind(name) => {
                        if let Ok(symbol) = name.symbol() {
                            self.mono.insert(symbol, ty);
                        }
                    }
                    // Destructuring let: the lhs is a pattern checked
                    // against the rhs type; its binders enter the
                    // monomorphic environment exactly like plain lets.
                    _ => self.check_pattern(lhs, &ty),
                }
            }
            DeclKind::Import(_) => {}
            other => self.unsupported(decl.id, decl_kind_name(other)),
        }
    }

    // ----- Patterns -----------------------------------------------------

    fn check_pattern(&mut self, pattern: &Pattern, expected: &Ty) {
        match &pattern.kind {
            PatternKind::Wildcard => {}
            PatternKind::Bind(name) => {
                if let Ok(symbol) = name.symbol() {
                    self.mono.insert(symbol, expected.clone());
                }
            }
            PatternKind::LiteralInt(_) => {
                self.emit_eq(
                    expected.clone(),
                    Ty::Nominal(Symbol::Int, vec![]),
                    pattern.id,
                    CtReason::Pattern,
                );
            }
            PatternKind::LiteralFloat(_) => {
                self.emit_eq(
                    expected.clone(),
                    Ty::Nominal(Symbol::Float, vec![]),
                    pattern.id,
                    CtReason::Pattern,
                );
            }
            PatternKind::LiteralTrue | PatternKind::LiteralFalse => {
                self.emit_eq(
                    expected.clone(),
                    Ty::Nominal(Symbol::Bool, vec![]),
                    pattern.id,
                    CtReason::Pattern,
                );
            }
            PatternKind::Tuple(patterns) => {
                let items: Vec<Ty> = patterns
                    .iter()
                    .map(|p| Ty::Var(self.store.fresh_ty(self.level, p.id)))
                    .collect();
                self.emit_eq(
                    expected.clone(),
                    Ty::Tuple(items.clone()),
                    pattern.id,
                    CtReason::Pattern,
                );
                for (sub, ty) in patterns.iter().zip(&items) {
                    self.check_pattern(sub, ty);
                }
            }
            PatternKind::Or(patterns) => {
                for sub in patterns {
                    self.check_pattern(sub, expected);
                }
            }
            PatternKind::Variant {
                enum_name,
                variant_name,
                variant_name_span: _,
                fields,
            } => {
                self.check_variant_pattern(pattern, enum_name, variant_name, fields, expected);
            }
            PatternKind::Record { fields } => {
                let mut row_fields: Vec<(Label, Ty)> = vec![];
                let mut open = false;
                for field in fields {
                    match &field.kind {
                        RecordFieldPatternKind::Bind(name) => {
                            let ty = Ty::Var(self.store.fresh_ty(self.level, field.id));
                            row_fields.push((Label::Named(name.name_str()), ty.clone()));
                            if let Ok(symbol) = name.symbol() {
                                self.mono.insert(symbol, ty);
                            }
                        }
                        RecordFieldPatternKind::Equals { name, value, .. } => {
                            let ty = Ty::Var(self.store.fresh_ty(self.level, field.id));
                            row_fields.push((Label::Named(name.name_str()), ty.clone()));
                            if let Ok(symbol) = name.symbol() {
                                self.mono.insert(symbol, ty.clone());
                            }
                            self.check_pattern(value, &ty);
                        }
                        RecordFieldPatternKind::Rest => open = true,
                    }
                }
                let tail = if open {
                    Some(crate::types::ty::RowTail::Var(
                        self.store.fresh_row(self.level, pattern.id),
                    ))
                } else {
                    None
                };
                let mut row = Row::closed(row_fields);
                row.tail = tail;
                self.emit_eq(
                    expected.clone(),
                    Ty::Record(row),
                    pattern.id,
                    CtReason::Pattern,
                );
            }
            PatternKind::Struct { .. } => {
                self.unsupported(pattern.id, "struct destructuring patterns");
            }
        }
    }

    /// Variant patterns (`.definitely(x)` / `Maybe.definitely(x)`): the enum
    /// comes from the explicit name or the scrutinee's head — the
    /// checking-mode requirement of *Simple Unification-Based Type Inference
    /// for GADTs* (ICFP 2006) in its non-refining form.
    fn check_variant_pattern(
        &mut self,
        pattern: &Pattern,
        enum_name: &Option<Name>,
        variant_name: &str,
        fields: &[Pattern],
        expected: &Ty,
    ) {
        let shallow = self.store.shallow(expected);
        let enum_symbol = match enum_name {
            Some(name) => name.symbol().ok(),
            None => match &shallow {
                Ty::Nominal(symbol, _) if self.catalog.enums.contains_key(symbol) => Some(*symbol),
                _ => None,
            },
        };
        let Some(enum_symbol) = enum_symbol else {
            self.unsupported(
                pattern.id,
                "variant patterns on a scrutinee whose enum is not yet known (annotate the scrutinee)",
            );
            return;
        };
        let Some(info) = self.catalog.enums.get(&enum_symbol).cloned() else {
            self.unsupported(pattern.id, "variant patterns on non-enum types");
            return;
        };
        let Some(variant) = info.variants.get(variant_name) else {
            self.errors.push((
                TypeError::UnknownMember {
                    receiver: self.store.render(expected),
                    label: variant_name.to_string(),
                },
                pattern.id,
            ));
            return;
        };

        // Bind the scrutinee to this enum, reusing its arguments when the
        // head is already concrete.
        let theta: Vec<Ty> = match &shallow {
            Ty::Nominal(symbol, args) if *symbol == enum_symbol => args.clone(),
            _ => {
                let theta: Vec<Ty> = info
                    .params
                    .iter()
                    .map(|_| Ty::Var(self.store.fresh_ty(self.level, pattern.id)))
                    .collect();
                self.emit_eq(
                    expected.clone(),
                    Ty::Nominal(enum_symbol, theta.clone()),
                    pattern.id,
                    CtReason::Pattern,
                );
                theta
            }
        };

        self.member_resolutions
            .insert(pattern.id, MemberResolution::Direct(variant.symbol));

        if fields.len() != variant.payloads.len() {
            self.errors.push((
                TypeError::ArityMismatch {
                    expected: variant.payloads.len(),
                    found: fields.len(),
                },
                pattern.id,
            ));
            return;
        }
        let substitution = param_subst(&info.params, &theta);
        for (sub, payload) in fields.iter().zip(&variant.payloads) {
            let payload =
                payload.substitute(&substitution, &Default::default(), &Default::default());
            self.check_pattern(sub, &payload);
        }
    }

    // ----- Names, annotations, helpers ----------------------------------

    fn lookup(&mut self, name: &Name, node: NodeID) -> Ty {
        let Ok(symbol) = name.symbol() else {
            // The name resolver already diagnosed this; poison quietly.
            return Ty::Error;
        };
        self.lookup_symbol_ty(symbol, node)
    }

    /// Check a body attributed to `binder` for the capability tables.
    fn with_binder<R>(&mut self, binder: Symbol, check: impl FnOnce(&mut Self) -> R) -> R {
        self.binder_stack.push(binder);
        let result = check(self);
        self.binder_stack.pop();
        result
    }

    fn lookup_symbol_ty(&mut self, symbol: Symbol, node: NodeID) -> Ty {
        // A reference edge for the capability tables. Locals land here
        // too; they are harmless noise (the consumer only chases
        // abort-capable targets, and symbols are never reused).
        if let Some(&binder) = self.binder_stack.last()
            && binder != symbol
        {
            self.binder_refs.entry(binder).or_default().insert(symbol);
        }
        if let Some(ty) = self.mono.get(&symbol) {
            return ty.clone();
        }
        if let Some(scheme) = self.schemes.get(&symbol).cloned() {
            return self.instantiate(&scheme, node);
        }
        // Referenced before its (later) group runs: park a conservative
        // outer-level variable; that group will reuse and solve it, and will
        // skip generalization for whatever it touched.
        let ty = Ty::Var(self.store.fresh_ty(OUTER_LEVEL, node));
        self.mono.insert(symbol, ty.clone());
        ty
    }

    /// Instantiate a scheme with fresh variables (Damas-Milner) and record
    /// the substitution for the future lowerer (the "call sites and
    /// substitutions" surface).
    fn instantiate(&mut self, scheme: &Scheme, node: NodeID) -> Ty {
        if scheme.params.is_empty() && scheme.eff_params.is_empty() && scheme.row_params.is_empty()
        {
            return scheme.ty.clone();
        }

        let mut tys = FxHashMap::default();
        let mut recorded = vec![];
        for param in &scheme.params {
            let var = Ty::Var(self.store.fresh_ty(self.level, node));
            recorded.push((param.symbol, var.clone()));
            tys.insert(param.symbol, var);
        }
        let mut effs = FxHashMap::default();
        for param in &scheme.eff_params {
            effs.insert(
                *param,
                crate::types::ty::EffTail::Var(self.store.fresh_eff(self.level, node)),
            );
        }
        let mut rows = FxHashMap::default();
        for param in &scheme.row_params {
            rows.insert(
                *param,
                crate::types::ty::RowTail::Var(self.store.fresh_row(self.level, node)),
            );
        }

        // Each bound becomes a wanted Conforms on the fresh variable, with
        // the bound's associated bindings substituted (qualified-type
        // instantiation: Jones, ESOP 1992).
        for param in &scheme.params {
            let fresh = tys[&param.symbol].clone();
            for bound in &param.bounds {
                let assoc = bound
                    .assoc
                    .iter()
                    .map(|(s, t)| (*s, t.substitute(&tys, &effs, &rows)))
                    .collect();
                self.wanteds.push(Constraint::Conforms {
                    ty: fresh.clone(),
                    protocol: bound.protocol,
                    assoc,
                    origin: CtOrigin::new(node, CtReason::Apply),
                });
            }
        }
        self.instantiations
            .entry(node)
            .or_default()
            .extend(recorded);
        scheme.ty.substitute(&tys, &effs, &rows)
    }

    fn record_instantiation(&mut self, node: NodeID, params: &[Symbol], theta: &[Ty]) {
        self.instantiations
            .entry(node)
            .or_default()
            .extend(params.iter().copied().zip(theta.iter().cloned()));
    }

    /// Explicit call-site type arguments (`_alloc<Element>(capacity)`)
    /// equate positionally with the instantiation recorded at the callee
    /// (scheme params list declared generics first, in order).
    fn apply_type_args(&mut self, callee_node: NodeID, type_args: &[TypeAnnotation]) {
        let recorded: Vec<Ty> = self
            .instantiations
            .get(&callee_node)
            .map(|subst| subst.iter().map(|(_, ty)| ty.clone()).collect())
            .unwrap_or_default();
        for (annotation, target) in type_args.iter().zip(recorded) {
            let ty = self.lower_annotation(annotation);
            self.emit_eq(target, ty, annotation.id, CtReason::Annotation);
        }
    }

    fn callable_arity(&mut self, symbol: Symbol) -> Option<usize> {
        if let Some(scheme) = self.schemes.get(&symbol)
            && let Ty::Func(params, ..) = &scheme.ty
        {
            return Some(params.len());
        }
        if let Some(ty) = self.mono.get(&symbol).cloned()
            && let Ty::Func(params, ..) = self.store.shallow(&ty)
        {
            return Some(params.len());
        }
        None
    }

    fn lower_annotation(&mut self, annotation: &TypeAnnotation) -> Ty {
        match &annotation.kind {
            TypeAnnotationKind::Nominal { name, generics, .. } => {
                let Ok(symbol) = name.symbol() else {
                    return Ty::Error;
                };
                let args: Vec<Ty> = generics.iter().map(|g| self.lower_annotation(g)).collect();
                match symbol {
                    Symbol::TypeParameter(_) | Symbol::AssociatedType(_) => Ty::Param(symbol),
                    _ => Ty::Nominal(symbol, args),
                }
            }
            TypeAnnotationKind::Func { params, returns } => {
                let params = params.iter().map(|p| self.lower_annotation(p)).collect();
                let ret = self.lower_annotation(returns);
                // Function-type annotations carry no effect syntax yet; an
                // open tail keeps them usable in any context.
                let eff = EffectRow::open(self.store.fresh_eff(self.level, annotation.id));
                Ty::Func(params, Box::new(ret), eff)
            }
            TypeAnnotationKind::Tuple(items) => match items.as_slice() {
                // `()` is unit, `(T)` is grouping.
                [] => Ty::unit(),
                [single] => self.lower_annotation(single),
                _ => Ty::Tuple(items.iter().map(|i| self.lower_annotation(i)).collect()),
            },
            TypeAnnotationKind::Record { fields } => {
                let fields = fields
                    .iter()
                    .map(|field| {
                        (
                            Label::Named(field.label.name_str()),
                            self.lower_annotation(&field.value),
                        )
                    })
                    .collect();
                Ty::Record(Row::closed(fields))
            }
            TypeAnnotationKind::SelfType(_) => match self.self_types.last() {
                Some(self_ty) => self_ty.clone(),
                None => {
                    self.unsupported(annotation.id, "Self outside a nominal declaration");
                    Ty::Error
                }
            },
            TypeAnnotationKind::NominalPath { .. } => {
                self.unsupported(annotation.id, "nominal path type annotations");
                Ty::Error
            }
        }
    }

    /// Branch join: `Never` is bottom here and only here (Pierce & Turner
    /// joins; divergence-as-bottom as in Koka).
    fn join(&mut self, a: Ty, b: Ty, node: NodeID) -> Ty {
        if a.is_never() {
            return b;
        }
        if b.is_never() {
            return a;
        }
        self.emit_eq(a.clone(), b, node, CtReason::Branch);
        a
    }

    fn ambient_eff(&self) -> EffectRow {
        self.eff_stack
            .last()
            .cloned()
            .unwrap_or_else(EffectRow::pure)
    }

    fn emit_eq(&mut self, expected: Ty, found: Ty, node: NodeID, reason: CtReason) {
        self.wanteds
            .push(Constraint::Eq(expected, found, CtOrigin::new(node, reason)));
    }

    fn emit_eff_eq(&mut self, a: EffectRow, b: EffectRow, node: NodeID) {
        self.wanteds.push(Constraint::EffEq(
            a,
            b,
            CtOrigin::new(node, CtReason::Effect),
        ));
    }

    fn unsupported(&mut self, node: NodeID, what: &str) {
        self.errors
            .push((TypeError::Unsupported(what.to_string()), node));
    }
}

fn generic_symbols(generics: &[crate::node_kinds::generic_decl::GenericDecl]) -> Vec<Symbol> {
    generics
        .iter()
        .filter_map(|g| g.name.symbol().ok())
        .collect()
}

fn param_subst(params: &[Symbol], args: &[Ty]) -> FxHashMap<Symbol, Ty> {
    params.iter().copied().zip(args.iter().cloned()).collect()
}

/// Dependency analysis for binding groups (THIH §11.6.2): collect each
/// binder's references to other top-level binders (including from struct
/// member bodies), condense with kosaraju SCC, and return groups in
/// dependencies-first order.
fn binding_groups(decls: &IndexMap<Symbol, TopEntry<'_>>) -> Vec<Vec<Symbol>> {
    use derive_visitor::{Drive, Visitor};
    use petgraph::algo::kosaraju_scc;
    use petgraph::graph::DiGraph;

    #[derive(Visitor)]
    #[visitor(Expr(enter))]
    struct RefCollector {
        refs: rustc_hash::FxHashSet<Symbol>,
    }
    impl RefCollector {
        fn enter_expr(&mut self, expr: &Expr) {
            match &expr.kind {
                ExprKind::Variable(name) | ExprKind::Constructor(name) => {
                    if let Ok(symbol) = name.symbol() {
                        self.refs.insert(symbol);
                    }
                }
                _ => {}
            }
        }
    }

    let mut graph = DiGraph::<Symbol, ()>::new();
    let mut index = FxHashMap::default();
    for symbol in decls.keys() {
        index.insert(*symbol, graph.add_node(*symbol));
    }
    for (symbol, entry) in decls {
        let mut collector = RefCollector {
            refs: Default::default(),
        };
        match entry {
            TopEntry::Let { rhs: Some(rhs), .. } => rhs.drive(&mut collector),
            TopEntry::Struct { decl } => {
                if let DeclKind::Struct { body, .. } = &decl.kind {
                    for member in &body.decls {
                        match &member.kind {
                            DeclKind::Method { func, .. } => func.drive(&mut collector),
                            DeclKind::Init { body, .. } => body.drive(&mut collector),
                            _ => {}
                        }
                    }
                }
            }
            _ => {}
        }
        for reference in collector.refs {
            if reference != *symbol
                && let Some(&target) = index.get(&reference)
            {
                graph.add_edge(index[symbol], target, ());
            }
        }
    }

    kosaraju_scc(&graph)
        .iter()
        .map(|scc| scc.iter().map(|i| graph[*i]).collect())
        .collect()
}

fn head_symbol(ty: &Ty) -> Symbol {
    match ty {
        Ty::Nominal(symbol, _) => *symbol,
        _ => Symbol::Main,
    }
}

/// One-way structural match: wherever `pattern` mentions an associated-type
/// parameter and `witness` is concrete, record the binding (Chakravarty,
/// Keller & Peyton Jones, ICFP 2005 — instances determine their synonyms).
fn collect_assoc_bindings(pattern: &Ty, witness: &Ty, bindings: &mut FxHashMap<Symbol, Ty>) {
    match (pattern, witness) {
        (Ty::Param(symbol), concrete) => {
            if matches!(symbol, Symbol::AssociatedType(_)) {
                bindings.entry(*symbol).or_insert_with(|| concrete.clone());
            }
        }
        (Ty::Nominal(_, pattern_args), Ty::Nominal(_, witness_args)) => {
            for (p, w) in pattern_args.iter().zip(witness_args) {
                collect_assoc_bindings(p, w, bindings);
            }
        }
        (Ty::Func(p1, r1, _), Ty::Func(p2, r2, _)) => {
            for (p, w) in p1.iter().zip(p2) {
                collect_assoc_bindings(p, w, bindings);
            }
            collect_assoc_bindings(r1, r2, bindings);
        }
        (Ty::Tuple(p1), Ty::Tuple(p2)) => {
            for (p, w) in p1.iter().zip(p2) {
                collect_assoc_bindings(p, w, bindings);
            }
        }
        _ => {}
    }
}

fn decl_kind_name(kind: &DeclKind) -> &'static str {
    match kind {
        DeclKind::Import(_) => "imports",
        DeclKind::Effect { .. } => "effect declarations",
        DeclKind::Struct { .. } => "struct declarations",
        DeclKind::Let { .. } => "destructuring let bindings",
        DeclKind::Protocol { .. } => "protocol declarations",
        DeclKind::Init { .. } => "initializers",
        DeclKind::Property { .. } => "properties",
        DeclKind::Method { .. } => "methods",
        DeclKind::Extend { .. } => "extend declarations",
        DeclKind::Enum { .. } => "enum declarations",
        DeclKind::EnumVariant(..) => "enum variants",
        DeclKind::Associated { .. } => "associated type declarations",
        DeclKind::Func(_) => "function declarations",
        DeclKind::FuncSignature(_) => "function signatures",
        DeclKind::MethodRequirement(_) => "method requirements",
        DeclKind::TypeAlias(..) => "type aliases",
    }
}
