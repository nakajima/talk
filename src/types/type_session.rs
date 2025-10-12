use std::rc::Rc;

use indexmap::IndexMap;
use rustc_hash::{FxHashMap, FxHashSet};
use tracing::instrument;

use crate::{
    ast::AST,
    compiling::module::{ModuleEnvironment, ModuleId},
    label::Label,
    name::Name,
    name_resolution::{
        name_resolver::NameResolved,
        symbol::{ProtocolId, Symbol, TypeId},
    },
    node_id::NodeID,
    node_kinds::{generic_decl::GenericDecl, type_annotation::TypeAnnotation},
    span::Span,
    types::{
        builtins::builtin_scope,
        constraints::constraint::Constraint,
        fields::{Associated, Initializer, Method, MethodRequirement, Property, Variant},
        infer_row::InferRow,
        infer_ty::{InferTy, Level, SkolemId, TypeParamId},
        kind::Kind,
        passes::{
            dependencies_pass::{Conformance, DependenciesPass, SCCResolved},
            inference_pass::{InferencePass, Meta, collect_meta},
            type_headers_pass::TypeHeaderPass,
            type_resolve_pass::TypeResolvePass,
        },
        scheme::{ForAll, Scheme},
        term_environment::{EnvEntry, TermEnv},
        ty::{SomeType, Ty},
        type_catalog::{ConformanceKey, ConformanceStub, Nominal, Protocol, TypeCatalog},
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, apply, apply_row, substitute},
        vars::Vars,
    },
};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ASTTyRepr {
    Annotated(TypeAnnotation), // already resolved names
    Generic(GenericDecl),
    Hole(NodeID, Span),           // no annotation; to be inferred later
    SelfType(Name, NodeID, Span), // For synthesized `self` param
}

impl ASTTyRepr {
    pub fn span(&self) -> Span {
        match self {
            Self::Annotated(ta) => ta.span,
            Self::Generic(gd) => gd.span,
            Self::Hole(_, span) => *span,
            Self::SelfType(_, _, span) => *span,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum TypeDefKind {
    Struct,
    Enum,
    Protocol,
    Extension,
}

#[derive(Debug, PartialEq, Default, Clone)]
pub struct Raw {
    pub type_constructors: FxHashMap<Symbol, TypeDef>,
    pub protocols: FxHashMap<ProtocolId, TypeDef>,
    pub extensions: FxHashMap<Symbol, Vec<TypeExtension>>,
    pub annotations: FxHashMap<NodeID, ASTTyRepr>,
    pub typealiases: FxHashMap<NodeID, (Name, TypeAnnotation)>,
    pub instance_methods: FxHashMap<Symbol, FxHashMap<Label, Method>>,
    pub static_methods: FxHashMap<Symbol, FxHashMap<Label, Method>>,
    pub initializers: FxHashMap<Symbol, FxHashMap<Label, Initializer>>,
    pub properties: FxHashMap<Symbol, IndexMap<Label, Property>>,
    pub variants: FxHashMap<Symbol, IndexMap<Label, Variant>>,
    pub associated_types: FxHashMap<Symbol, IndexMap<Name, Associated>>,
    pub method_requirements: FxHashMap<Symbol, IndexMap<Label, MethodRequirement>>,

    pub generics: FxHashMap<Symbol, IndexMap<Name, ASTTyRepr>>,
    pub conformances: FxHashMap<Symbol, Vec<ConformanceStub>>,
    pub child_types: FxHashMap<Symbol, FxHashMap<String, Symbol>>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeExtension {
    pub node_id: NodeID,
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeDef {
    pub name: Name,
    pub node_id: NodeID,
    pub kind: Kind,
    pub def: TypeDefKind,
}

// new helper
#[derive(Debug, Clone)]
pub struct ProtocolBound {
    pub protocol_id: ProtocolId,
    pub args: Vec<InferTy>, // concrete types the protocol is instantiated with, e.g. [Ty::Float]
}

#[derive(Debug)]
pub struct TypeSession {
    pub types_by_node: FxHashMap<NodeID, InferTy>,
    pub(super) vars: Vars,
    term_env: TermEnv,
    pub(super) meta_levels: FxHashMap<Meta, Level>,
    pub(super) skolem_map: FxHashMap<InferTy, InferTy>,
    pub skolem_bounds: FxHashMap<SkolemId, Vec<TypeId>>,
    pub(super) type_param_bounds: FxHashMap<TypeParamId, Vec<ProtocolBound>>,
    pub typealiases: FxHashMap<Symbol, Scheme<InferTy>>,
    pub(super) type_catalog: TypeCatalog,
    pub(super) modules: Rc<ModuleEnvironment>,
    pub aliases: FxHashMap<Symbol, Scheme<InferTy>>,
}

pub struct Typed {}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeEntry {
    Mono(Ty),
    Poly(Scheme<Ty>),
}

#[derive(Debug, Default)]
pub struct Types {
    types_by_node: FxHashMap<NodeID, TypeEntry>,
    types_by_symbol: FxHashMap<Symbol, TypeEntry>,
    pub catalog: TypeCatalog,
}

impl Types {
    pub fn define(&mut self, id: NodeID, ty: TypeEntry) {
        self.types_by_node.insert(id, ty);
    }

    pub fn get(&self, id: &NodeID) -> Option<&TypeEntry> {
        self.types_by_node.get(id)
    }

    pub fn get_symbol(&self, sym: &Symbol) -> Option<&TypeEntry> {
        self.types_by_symbol.get(sym)
    }
}

impl TypeSession {
    pub fn new(modules: Rc<ModuleEnvironment>) -> Self {
        let mut term_env = TermEnv {
            symbols: FxHashMap::default(),
        };

        for (sym, entry) in builtin_scope() {
            term_env.insert(sym, entry);
        }

        TypeSession {
            vars: Default::default(),
            skolem_map: Default::default(),
            meta_levels: Default::default(),
            term_env,
            type_param_bounds: Default::default(),
            skolem_bounds: Default::default(),
            types_by_node: Default::default(),
            typealiases: Default::default(),
            type_catalog: Default::default(),
            modules,
            aliases: Default::default(),
        }
    }

    pub fn finalize(mut self) -> Result<Types, TypeError> {
        let types_by_node = std::mem::take(&mut self.types_by_node);
        let entries = types_by_node
            .into_iter()
            .map(|(id, ty)| {
                let ty = self.finalize_ty(ty);

                (id, ty)
            })
            .collect();

        let term_env = std::mem::take(&mut self.term_env);
        let types_by_symbol = term_env
            .symbols
            .into_iter()
            .map(|(sym, entry)| {
                let entry = match entry {
                    EnvEntry::Mono(ty) => self.finalize_ty(ty),
                    EnvEntry::Scheme(scheme) => {
                        if scheme.ty.contains_var() {
                            // Merge with existing scheme's foralls/predicates
                            let EnvEntry::Scheme(generalized) =
                                self.generalize(Level(0), scheme.ty, &[])
                            else {
                                unreachable!(
                                    "generalize returned Mono when scheme.ty.contains_var()"
                                );
                            };

                            TypeEntry::Poly(Scheme {
                                foralls: [scheme.foralls, generalized.foralls].concat(),
                                predicates: [
                                    scheme
                                        .predicates
                                        .into_iter()
                                        .map(|p| p.into())
                                        .collect::<Vec<_>>(),
                                    generalized
                                        .predicates
                                        .into_iter()
                                        .map(|p| p.into())
                                        .collect::<Vec<_>>(),
                                ]
                                .concat(),
                                ty: generalized.ty.into(),
                            })
                        } else {
                            TypeEntry::Poly(Scheme {
                                foralls: scheme.foralls,
                                predicates: scheme
                                    .predicates
                                    .into_iter()
                                    .map(|p| p.into())
                                    .collect(),
                                ty: scheme.ty.into(),
                            })
                        }
                    }
                };
                (sym, entry)
            })
            .collect();

        let types = Types {
            catalog: self.type_catalog,
            types_by_node: entries,
            types_by_symbol,
        };

        Ok(types)
    }

    fn finalize_ty(&mut self, ty: InferTy) -> TypeEntry {
        let ty = substitute(ty.clone(), &self.skolem_map);

        if ty.contains_var() {
            self.generalize(Level(0), ty.clone(), &[]).into()
        } else {
            TypeEntry::Mono(ty.clone().into())
        }
    }

    pub fn apply(&mut self, substitutions: &mut UnificationSubstitutions) {
        for ty in self.types_by_node.values_mut() {
            if matches!(ty, InferTy::Primitive(_)) {
                continue;
            }

            *ty = apply(ty.clone(), substitutions);
        }
    }

    pub fn get_term_env(&self) -> &TermEnv {
        &self.term_env
    }

    pub fn drive(ast: &mut AST<NameResolved>) -> TypeSession {
        let modules = ModuleEnvironment::default();
        let mut session = TypeSession::new(Rc::new(modules));
        let raw = TypeHeaderPass::drive(ast);
        let _headers = TypeResolvePass::drive(ast, &mut session, raw);
        let mut scc = SCCResolved::default();
        DependenciesPass::drive(&mut session, ast, &mut scc);
        InferencePass::perform(&mut session, &scc, ast);
        session
    }

    #[instrument(skip(self))]
    pub fn generalize(&mut self, inner: Level, ty: InferTy, unsolved: &[Constraint]) -> EnvEntry {
        // collect metas in ty
        let mut metas = FxHashSet::default();
        collect_meta(&ty, &mut metas);

        // Also collect metas that appear only in constraints
        for constraint in unsolved {
            collect_metas_in_constraint(constraint, &mut metas);
        }

        // keep only metas born at or above inner
        let mut foralls = vec![];
        let mut substitutions = UnificationSubstitutions::new(self.meta_levels.clone());
        for m in &metas {
            match m {
                InferTy::Param(p) => {
                    if !foralls
                        .iter()
                        .any(|fa| matches!(fa, ForAll::Ty(q) if *q == *p))
                    {
                        foralls.push(ForAll::Ty(*p));
                    }
                }

                InferTy::UnificationVar { level, id } => {
                    if *level <= inner {
                        tracing::warn!("discarding {m:?} due to level ({level:?} < {inner:?})");
                        continue;
                    }

                    let param_id = self.vars.type_params.next_id();
                    tracing::trace!("generalizing {m:?} to {param_id:?}");
                    foralls.push(ForAll::Ty(param_id));
                    substitutions.ty.insert(*id, InferTy::Param(param_id));
                }
                InferTy::Record(box InferRow::Var(id))
                | InferTy::Nominal {
                    row: box InferRow::Var(id),
                    ..
                } => {
                    let level = self
                        .meta_levels
                        .get(&Meta::Row(*id))
                        .expect("didn't get level for row meta");
                    if *level <= inner {
                        tracing::trace!("discarding {m:?} due to level ({level:?} < {inner:?})");
                        continue;
                    }

                    let param_id = self.vars.row_params.next_id();
                    tracing::trace!("generalizing {m:?} to {param_id:?}");
                    foralls.push(ForAll::Row(param_id));
                    substitutions.row.insert(*id, InferRow::Param(param_id));
                }
                _ => {
                    tracing::warn!("got {m:?} for var while generalizing")
                }
            }
        }

        for c in unsolved {
            if let Constraint::HasField(h) = c {
                tracing::info!("got unsolved hasfield: {c:?}");
                let r = apply_row(h.row.clone(), &mut substitutions);
                if let InferRow::Var(row_meta) = r {
                    // quantify if its level is above the binder's level
                    let lvl = *self
                        .meta_levels
                        .get(&Meta::Row(row_meta))
                        .unwrap_or(&Level(0));
                    if lvl >= inner {
                        let param_id = self.vars.row_params.next_id();
                        foralls.push(ForAll::Row(param_id));
                        substitutions
                            .row
                            .insert(row_meta, InferRow::Param(param_id));
                    }
                }
            }
        }

        // De-skolemize
        let ty = substitute(ty, &self.skolem_map);
        let ty = apply(ty, &mut substitutions);

        if foralls.is_empty() {
            return EnvEntry::Mono(ty);
        }

        let predicates = unsolved
            .iter()
            .map(|c| {
                let c = c.substitute(&self.skolem_map);

                c.into_predicate(&mut substitutions)
            })
            .collect();

        EnvEntry::Scheme(Scheme::<InferTy>::new(foralls, predicates, ty))
    }

    #[instrument(skip(self))]
    pub fn generalize_with_substitutions(
        &mut self,
        inner: Level,
        ty: InferTy,
        unsolved: &[Constraint],
        substitutions: &mut UnificationSubstitutions,
    ) -> EnvEntry {
        let ty = apply(ty, substitutions);

        // collect metas in ty
        let mut metas = FxHashSet::default();
        collect_meta(&ty, &mut metas);

        // keep only metas born at or above inner
        let mut foralls = vec![];
        for m in &metas {
            match m {
                InferTy::Param(p) => {
                    // No substitution needed (the ty already contains Ty::Param(p)),
                    // but we must record it in `foralls`, so instantiate() knows what to replace.
                    if !foralls
                        .iter()
                        .any(|fa| matches!(fa, ForAll::Ty(q) if *q == *p))
                    {
                        foralls.push(ForAll::Ty(*p));
                    }
                }

                InferTy::UnificationVar { level, id } => {
                    if *level <= inner {
                        tracing::warn!("discarding {m:?} due to level ({level:?} < {inner:?})");
                        continue;
                    }

                    let param_id = self.vars.type_params.next_id();
                    tracing::trace!("generalizing {m:?} to {param_id:?}");
                    foralls.push(ForAll::Ty(param_id));
                    substitutions.ty.insert(*id, InferTy::Param(param_id));
                }
                InferTy::Record(box InferRow::Var(id)) => {
                    let level = self
                        .meta_levels
                        .get(&Meta::Row(*id))
                        .expect("didn't get level for row meta");
                    if *level <= inner {
                        tracing::trace!("discarding {m:?} due to level ({level:?} < {inner:?})");
                        continue;
                    }

                    let param_id = self.vars.row_params.next_id();
                    tracing::trace!("generalizing {m:?} to {param_id:?}");
                    foralls.push(ForAll::Row(param_id));
                    substitutions.row.insert(*id, InferRow::Param(param_id));
                }
                _ => {
                    tracing::warn!("got {m:?} for var while generalizing")
                }
            }
        }

        // 3) de-skolemize+apply again
        let ty = substitute(ty, &self.skolem_map);
        let ty = apply(ty, substitutions);

        // 4) build predicates from unsolved using *current substitutions*
        if foralls.is_empty() {
            return EnvEntry::Mono(ty);
        }
        let predicates = unsolved
            .iter()
            .map(|c| c.substitute(&self.skolem_map))
            .map(|c| c.into_predicate(substitutions))
            .collect();

        EnvEntry::Scheme(Scheme::<InferTy>::new(foralls, predicates, ty))
    }

    // Handle converting Ty::TypeConstructor/Ty::TypeApplication to Ty::Nominal
    pub(super) fn normalize_nominals(&mut self, ty: &InferTy, level: Level) -> InferTy {
        let normalized = match ty.clone() {
            InferTy::Nominal { .. } => ty.clone(),
            InferTy::Constructor {
                symbol,
                params,
                ret,
            } => InferTy::Constructor {
                symbol,
                params: params
                    .into_iter()
                    .map(|p| self.normalize_nominals(&p, level))
                    .collect(),
                ret: self.normalize_nominals(&ret, level).into(),
            },
            InferTy::Func(box ty, box ty1) => InferTy::Func(
                self.normalize_nominals(&ty, level).into(),
                self.normalize_nominals(&ty1, level).into(),
            ),
            InferTy::Tuple(items) => InferTy::Tuple(
                items
                    .into_iter()
                    .map(|i| self.normalize_nominals(&i, level))
                    .collect(),
            ),
            InferTy::Record(row) => {
                InferTy::Record(self.normalize_nominals_row(&row, level).into())
            }
            ty @ (InferTy::Hole(..)
            | InferTy::Primitive(..)
            | InferTy::Param(..)
            | InferTy::Rigid(..)
            | InferTy::UnificationVar { .. }) => ty,
        };

        #[cfg(debug_assertions)]
        if normalized != *ty {
            tracing::trace!("normalize_nominal: {ty:?} -> {normalized:?}");
        }

        normalized
    }

    #[instrument(skip(self))]
    pub(super) fn lookup(&mut self, sym: &Symbol) -> Option<EnvEntry> {
        if let Some(entry) = self.term_env.lookup(sym).cloned() {
            return Some(entry);
        }

        if let Some(module_id) = sym.module_id()
            && let Some(module) = self.modules.modules.get(&module_id)
        {
            // Try looking up with the symbol's current module_id first (for Core/Prelude),
            // then fall back to Current (for External modules)
            let entry = module
                .types
                .get_symbol(sym)
                .or_else(|| module.types.get_symbol(&sym.current()))
                .cloned()
                .expect("did not get external symbol");
            let entry: EnvEntry = match entry.clone() {
                TypeEntry::Mono(t) => EnvEntry::Mono(t.into()),
                TypeEntry::Poly(..) => entry.into(),
            };

            let entry = entry.import(module_id);
            self.term_env.insert(*sym, entry.clone());
            return Some(entry);
        }

        if let Some(entry) = builtin_scope().get(sym).cloned() {
            return Some(entry);
        }

        None
    }

    pub(super) fn insert_term(&mut self, sym: Symbol, entry: EnvEntry) {
        self.term_env.insert(sym, entry);
    }

    pub(super) fn insert_mono(&mut self, sym: Symbol, ty: InferTy) {
        self.term_env.insert(sym, EnvEntry::Mono(ty));
    }

    pub(super) fn lookup_nominal(&mut self, symbol: &Symbol) -> Option<Nominal> {
        if let Some(entry) = self.type_catalog.nominals.get(symbol).cloned() {
            return Some(entry);
        }

        if let Symbol::Type(TypeId {
            module_id: module_id @ (ModuleId::External(..) | ModuleId::Core | ModuleId::Prelude),
            local_id,
        }) = *symbol
            && let Some(module) = self.modules.modules.get(&module_id)
        {
            let nominal = module
                .types
                .catalog
                .nominals
                .get(&Symbol::Type(TypeId {
                    module_id: ModuleId::Current,
                    local_id,
                }))
                .cloned()
                .expect("did not get external symbol");

            let nominal = nominal.import(module_id);
            self.type_catalog.nominals.insert(*symbol, nominal.clone());
            return Some(nominal);
        }

        None
    }

    pub(super) fn lookup_member(&mut self, receiver: &Symbol, label: &Label) -> Option<Symbol> {
        if let Some(sym) = self.type_catalog.lookup_member(receiver, label) {
            return Some(sym);
        }

        for module in self.modules.modules.values() {
            if let Some(sym) = module.types.catalog.lookup_member(receiver, label) {
                return Some(sym);
            }
        }

        None
    }

    pub(super) fn lookup_variants(&self, receiver: &Symbol) -> Option<FxHashMap<Label, Symbol>> {
        if let Some(variants) = self.type_catalog.variants.get(receiver).cloned() {
            return Some(variants);
        }

        for module in self.modules.modules.values() {
            if let Some(variants) = module.types.catalog.variants.get(receiver).cloned() {
                return Some(variants);
            }
        }

        None
    }

    pub(super) fn clone_conformances(&self) -> FxHashMap<ConformanceKey, Conformance> {
        self.type_catalog.conformances.clone()
    }

    pub(super) fn lookup_conformance(&self, key: &ConformanceKey) -> Option<&Conformance> {
        self.type_catalog.conformances.get(key)
    }

    pub(super) fn lookup_protocol(&mut self, protocol_id: ProtocolId) -> Option<Protocol> {
        if let Some(entry) = self.type_catalog.protocols.get(&protocol_id).cloned() {
            return Some(entry);
        }

        if let ProtocolId {
            module_id: module_id @ (ModuleId::External(..) | ModuleId::Core | ModuleId::Prelude),
            local_id,
        } = protocol_id
            && let Some(module) = self.modules.modules.get(&module_id)
        {
            let module_key = if matches!(module_id, ModuleId::External(..)) {
                ModuleId::Current
            } else {
                module_id
            };
            let protocol = module
                .types
                .catalog
                .protocols
                .get(&ProtocolId {
                    module_id: module_key,
                    local_id,
                })
                .cloned()
                .expect("did not get external symbol");

            let protocol = protocol.import(module_id);
            self.type_catalog
                .protocols
                .insert(protocol_id, protocol.clone());
            return Some(protocol);
        }

        None
    }

    pub(super) fn lookup_initializers(
        &mut self,
        symbol: &Symbol,
    ) -> Option<FxHashMap<Label, Symbol>> {
        if let Some(initializers) = self.type_catalog.initializers.get(symbol).cloned() {
            return Some(initializers);
        }

        if let Symbol::Type(TypeId {
            module_id: module_id @ (ModuleId::External(..) | ModuleId::Core | ModuleId::Prelude),
            local_id,
        }) = *symbol
            && let Some(module) = self.modules.modules.get(&module_id)
        {
            let module_key = if matches!(module_id, ModuleId::External(..)) {
                ModuleId::Current
            } else {
                module_id
            };
            let initializers = module
                .types
                .catalog
                .initializers
                .get(&Symbol::Type(TypeId {
                    module_id: module_key,
                    local_id,
                }))
                .cloned()?;

            let imported: FxHashMap<Label, Symbol> = initializers
                .into_iter()
                .map(|(label, sym)| (label, sym.import(module_id)))
                .collect();

            self.type_catalog
                .initializers
                .insert(*symbol, imported.clone());
            return Some(imported);
        }

        None
    }

    pub(super) fn lookup_properties(&mut self, symbol: &Symbol) -> Option<IndexMap<Label, Symbol>> {
        if let Some(properties) = self.type_catalog.properties.get(symbol).cloned() {
            return Some(properties);
        }

        if let Symbol::Type(TypeId {
            module_id: module_id @ (ModuleId::External(..) | ModuleId::Core | ModuleId::Prelude),
            local_id,
        }) = *symbol
            && let Some(module) = self.modules.modules.get(&module_id)
        {
            let module_key = if matches!(module_id, ModuleId::External(..)) {
                ModuleId::Current
            } else {
                module_id
            };
            let properties = module
                .types
                .catalog
                .properties
                .get(&Symbol::Type(TypeId {
                    module_id: module_key,
                    local_id,
                }))
                .cloned()?;

            let imported: IndexMap<Label, Symbol> = properties
                .into_iter()
                .map(|(label, sym)| (label, sym.import(module_id)))
                .collect();

            self.type_catalog
                .properties
                .insert(*symbol, imported.clone());
            return Some(imported);
        }

        None
    }

    pub(super) fn normalize_nominals_row(&mut self, row: &InferRow, level: Level) -> InferRow {
        if let InferRow::Extend { box row, label, ty } = row.clone() {
            return InferRow::Extend {
                row: self.normalize_nominals_row(&row, level).into(),
                label,
                ty: self.normalize_nominals(&ty, level),
            };
        }

        row.clone()
    }

    pub(crate) fn new_type_param(&mut self) -> InferTy {
        let id = self.vars.type_params.next_id();
        tracing::trace!("Fresh type param {id:?}");
        InferTy::Param(id)
    }

    pub(crate) fn new_skolem(&mut self) -> InferTy {
        let id = self.vars.skolems.next_id();
        tracing::trace!("Fresh skolem {id:?}");
        InferTy::Rigid(id)
    }

    pub(crate) fn new_ty_meta_var(&mut self, level: Level) -> InferTy {
        let id = self.vars.ty_metas.next_id();
        self.meta_levels.insert(Meta::Ty(id), level);
        tracing::trace!("Fresh {id:?}");
        InferTy::UnificationVar { id, level }
    }

    pub(crate) fn new_row_meta_var(&mut self, level: Level) -> InferRow {
        let id = self.vars.row_metas.next_id();
        self.meta_levels.insert(Meta::Row(id), level);
        tracing::trace!("Fresh {id:?}");
        InferRow::Var(id)
    }
}

fn collect_metas_in_constraint(constraint: &Constraint, out: &mut FxHashSet<InferTy>) {
    match constraint {
        Constraint::Equals(equals) => {
            collect_meta(&equals.lhs, out);
            collect_meta(&equals.rhs, out);
        }
        Constraint::Member(member) => {
            collect_meta(&member.receiver, out);
            collect_meta(&member.ty, out);
        }
        Constraint::Call(call) => {
            collect_meta(&call.callee, out);
            for argument in &call.args {
                collect_meta(argument, out);
            }
            if let Some(receiver) = &call.receiver {
                collect_meta(receiver, out);
            }
            collect_meta(&call.returns, out);
        }
        Constraint::Construction(construction) => {
            collect_meta(&construction.callee, out);
            for argument in &construction.args {
                collect_meta(argument, out);
            }
            collect_meta(&construction.returns, out);
        }
        Constraint::HasField(has_field) => {
            // The row meta is handled in your existing HasField block later.
            collect_meta(&has_field.ty, out);
        }
        Constraint::Conforms(_) => {
            // No direct metas to generalize here.
        }
        Constraint::AssociatedEquals(associated_equals) => {
            collect_meta(&associated_equals.output, out);
            collect_meta(&associated_equals.subject, out);
        }
        Constraint::TypeMember(c) => {
            collect_meta(&c.base, out);
            collect_meta(&c.result, out);
            for ty in &c.generics {
                collect_meta(ty, out);
            }
        }
    }
}
