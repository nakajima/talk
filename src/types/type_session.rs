use std::{cell::RefCell, rc::Rc};

use indexmap::{IndexMap, IndexSet};
use rustc_hash::{FxHashMap, FxHashSet};
use tracing::instrument;

use crate::{
    compiling::module::{ModuleEnvironment, ModuleId},
    label::Label,
    name::Name,
    name_resolution::symbol::{ProtocolId, StructId, Symbol},
    node_id::NodeID,
    node_kinds::{generic_decl::GenericDecl, type_annotation::TypeAnnotation},
    span::Span,
    types::{
        builtins::builtin_scope,
        constraints::constraint::Constraint,
        fields::{Associated, Initializer, Method, MethodRequirement, Property, Variant},
        infer_row::{InferRow, RowMetaId, RowParamId},
        infer_ty::{InferTy, Level, MetaVarId, SkolemId, TypeParamId},
        kind::Kind,
        passes::{
            dependencies_pass::Conformance,
            old_inference_pass::{Meta, collect_meta},
        },
        row::Row,
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
    pub nominals: FxHashMap<Symbol, TypeDef>,
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
    pub current_module_id: ModuleId,
    pub types_by_node: FxHashMap<NodeID, InferTy>,
    vars: Vars,
    term_env: TermEnv,
    pub(super) meta_levels: Rc<RefCell<FxHashMap<Meta, Level>>>,
    pub(super) skolem_map: FxHashMap<InferTy, InferTy>,
    pub skolem_bounds: FxHashMap<SkolemId, Vec<StructId>>,
    // pub(super) type_param_bounds: FxHashMap<TypeParamId, Vec<ProtocolBound>>,
    pub typealiases: FxHashMap<Symbol, Scheme<InferTy>>,
    pub(super) type_catalog: TypeCatalog<InferTy>,
    pub(super) modules: Rc<ModuleEnvironment>,
    pub aliases: FxHashMap<Symbol, Scheme<InferTy>>,
    pub(super) reverse_instantiations: ReverseInstantiations,
}

pub struct Typed {}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeEntry {
    Mono(Ty),
    Poly(Scheme<Ty>),
}

impl TypeEntry {
    pub fn as_mono_ty(&self) -> &Ty {
        if let Self::Mono(ty) = self {
            return ty;
        }

        panic!("Cannot get mono ty: {self:?}");
    }
}

#[derive(Clone, Debug, Default)]
pub struct Types {
    pub types_by_node: FxHashMap<NodeID, TypeEntry>,
    types_by_symbol: FxHashMap<Symbol, TypeEntry>,
    pub catalog: TypeCatalog<Ty>,
}

#[derive(Debug, Default)]
pub struct ReverseInstantiations {
    pub ty: FxHashMap<MetaVarId, TypeParamId>,
    pub row: FxHashMap<RowMetaId, RowParamId>,
}

impl Types {
    pub fn define(&mut self, symbol: Symbol, ty: TypeEntry) {
        self.types_by_symbol.insert(symbol, ty);
    }

    pub fn get(&self, id: &NodeID) -> Option<&TypeEntry> {
        self.types_by_node.get(id)
    }

    pub fn get_symbol(&self, sym: &Symbol) -> Option<&TypeEntry> {
        self.types_by_symbol.get(sym)
    }
}

impl TypeSession {
    pub fn new(current_module_id: ModuleId, modules: Rc<ModuleEnvironment>) -> Self {
        let mut term_env = TermEnv {
            symbols: FxHashMap::default(),
        };

        for (sym, entry) in builtin_scope() {
            term_env.insert(sym, entry);
        }

        TypeSession {
            current_module_id,
            vars: Default::default(),
            skolem_map: Default::default(),
            meta_levels: Default::default(),
            term_env,
            // type_param_bounds: Default::default(),
            skolem_bounds: Default::default(),
            reverse_instantiations: Default::default(),
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
                                foralls: [scheme.foralls, generalized.foralls]
                                    .iter()
                                    .flat_map(|f| f.clone())
                                    .collect(),
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

        let catalog = std::mem::take(&mut self.type_catalog);
        let catalog = catalog.finalize(&mut self);
        let types = Types {
            catalog,
            types_by_node: entries,
            types_by_symbol,
        };

        Ok(types)
    }

    fn shallow_generalize_row(&mut self, row: InferRow) -> InferRow {
        match row {
            InferRow::Empty(..) => row,
            InferRow::Extend { box row, label, ty } => InferRow::Extend {
                row: self.shallow_generalize_row(row).into(),
                label,
                ty: self.shallow_generalize(ty),
            },
            InferRow::Param(..) => row,
            InferRow::Var(meta) => {
                let id = self
                    .reverse_instantiations
                    .row
                    .get(&meta)
                    .cloned()
                    .unwrap_or_else(|| {
                        let InferRow::Param(id) = self.new_row_type_param(Some(meta)) else {
                            unreachable!()
                        };

                        self.reverse_instantiations.row.insert(meta, id);

                        id
                    });

                InferRow::Param(id)
            }
        }
    }

    #[instrument(skip(self))]
    fn shallow_generalize(&mut self, ty: InferTy) -> InferTy {
        match ty {
            InferTy::Var { id: meta, .. } => {
                let id = self
                    .reverse_instantiations
                    .ty
                    .get(&meta)
                    .cloned()
                    .unwrap_or_else(|| {
                        let InferTy::Param(id) = self.new_type_param(Some(meta)) else {
                            unreachable!()
                        };

                        self.reverse_instantiations.ty.insert(meta, id);

                        id
                    });

                InferTy::Param(id)
            }
            InferTy::Constructor {
                name,
                params,
                box ret,
            } => InferTy::Constructor {
                name,
                params: params
                    .into_iter()
                    .map(|p| self.shallow_generalize(p))
                    .collect(),
                ret: self.shallow_generalize(ret).into(),
            },
            InferTy::Func(box param, box ret) => InferTy::Func(
                self.shallow_generalize(param).into(),
                self.shallow_generalize(ret).into(),
            ),
            InferTy::Tuple(items) => InferTy::Tuple(
                items
                    .into_iter()
                    .map(|p| self.shallow_generalize(p))
                    .collect(),
            ),
            InferTy::Record(box row) => InferTy::Record(self.shallow_generalize_row(row).into()),
            InferTy::Nominal { symbol, box row } => InferTy::Nominal {
                symbol,
                row: self.shallow_generalize_row(row).into(),
            },
            ty => ty,
        }
    }

    pub(super) fn finalize_ty(&mut self, ty: InferTy) -> TypeEntry {
        let ty = substitute(ty.clone(), &self.skolem_map);
        let ty = self.shallow_generalize(ty);

        if ty.contains_var() {
            self.generalize(Level(0), ty.clone(), &[]).into()
        } else {
            TypeEntry::Mono(ty.clone().into())
        }
    }

    pub(super) fn finalize_row(&mut self, row: InferRow) -> Row {
        let row = self.shallow_generalize_row(row);

        match row {
            InferRow::Empty(..) => row.into(),
            InferRow::Param(..) => row.into(),
            InferRow::Var(var) => Row::Param(*self.reverse_instantiations.row.get(&var).unwrap()),
            InferRow::Extend { box row, label, ty } => Row::Extend {
                row: self.finalize_row(row).into(),
                label,
                ty: match self.finalize_ty(ty) {
                    TypeEntry::Mono(ty) => ty.clone(),
                    TypeEntry::Poly(scheme) => scheme.ty,
                },
            },
        }
    }

    pub fn apply(&mut self, substitutions: &mut UnificationSubstitutions) {
        for ty in self.types_by_node.values_mut() {
            if matches!(ty, InferTy::Primitive(_)) {
                continue;
            }

            *ty = apply(ty.clone(), substitutions);
        }

        for ty in self.type_catalog.instantiations.ty.values_mut() {
            if matches!(ty, InferTy::Primitive(_)) {
                continue;
            }

            *ty = apply(ty.clone(), substitutions);
        }

        for row in self.type_catalog.instantiations.row.values_mut() {
            *row = apply_row(row.clone(), substitutions);
        }
    }

    pub fn get_term_env(&self) -> &TermEnv {
        &self.term_env
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub fn generalize(&mut self, inner: Level, ty: InferTy, unsolved: &[Constraint]) -> EnvEntry {
        // collect metas in ty
        let mut metas = FxHashSet::default();
        collect_meta(&ty, &mut metas);

        // Also collect metas that appear only in constraints
        for constraint in unsolved {
            collect_metas_in_constraint(constraint, &mut metas);
        }

        // keep only metas born at or above inner
        let mut foralls = IndexSet::default();
        let mut substitutions = UnificationSubstitutions::new(self.meta_levels.clone());
        for m in &metas {
            match m {
                InferTy::Param(p) => {
                    if !foralls
                        .iter()
                        .any(|fa| matches!(fa, ForAll::Ty(q) if *q == *p))
                    {
                        foralls.insert(ForAll::Ty(*p));
                    }
                }

                InferTy::Var { level, id } => {
                    if *level <= inner {
                        tracing::warn!("discarding {m:?} due to level ({level:?} < {inner:?})");
                        continue;
                    }

                    let param_id = self.vars.type_params.next_id();
                    self.reverse_instantiations.ty.insert(*id, param_id);
                    tracing::trace!("generalizing {m:?} to {param_id:?}");
                    foralls.insert(ForAll::Ty(param_id));
                    substitutions.ty.insert(*id, InferTy::Param(param_id));
                }
                InferTy::Record(box InferRow::Var(id))
                | InferTy::Nominal {
                    row: box InferRow::Var(id),
                    ..
                } => {
                    let levels = self.meta_levels.borrow();
                    let level = levels
                        .get(&Meta::Row(*id))
                        .expect("didn't get level for row meta");
                    if *level <= inner {
                        tracing::trace!("discarding {m:?} due to level ({level:?} < {inner:?})");
                        continue;
                    }

                    let param_id = self.vars.row_params.next_id();
                    tracing::trace!("generalizing {m:?} to {param_id:?}");
                    foralls.insert(ForAll::Row(param_id));
                    substitutions.row.insert(*id, InferRow::Param(param_id));
                    self.reverse_instantiations.row.insert(*id, param_id);
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
                    let levels = self.meta_levels.borrow();
                    let lvl = levels.get(&Meta::Row(row_meta)).unwrap_or(&Level(0));
                    if *lvl >= inner {
                        let param_id = self.vars.row_params.next_id();
                        foralls.insert(ForAll::Row(param_id));
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

    #[instrument(level = tracing::Level::TRACE, skip(self))]
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
        let mut foralls = IndexSet::default();
        for m in &metas {
            match m {
                InferTy::Param(p) => {
                    // No substitution needed (the ty already contains Ty::Param(p)),
                    // but we must record it in `foralls`, so instantiate() knows what to replace.
                    if !foralls
                        .iter()
                        .any(|fa| matches!(fa, ForAll::Ty(q) if *q == *p))
                    {
                        foralls.insert(ForAll::Ty(*p));
                    }
                }

                InferTy::Var { level, id } => {
                    if *level <= inner {
                        tracing::warn!("discarding {m:?} due to level ({level:?} < {inner:?})");
                        continue;
                    }

                    let param_id = self.vars.type_params.next_id();
                    self.reverse_instantiations.ty.insert(*id, param_id);
                    tracing::trace!("generalizing {m:?} to {param_id:?}");
                    foralls.insert(ForAll::Ty(param_id));
                    substitutions.ty.insert(*id, InferTy::Param(param_id));
                }
                InferTy::Record(box InferRow::Var(id)) => {
                    let levels = self.meta_levels.borrow();
                    let level = levels
                        .get(&Meta::Row(*id))
                        .expect("didn't get level for row meta");
                    if *level <= inner {
                        tracing::trace!("discarding {m:?} due to level ({level:?} < {inner:?})");
                        continue;
                    }

                    let param_id = self.vars.row_params.next_id();
                    tracing::trace!("generalizing {m:?} to {param_id:?}");
                    self.reverse_instantiations.row.insert(*id, param_id);
                    foralls.insert(ForAll::Row(param_id));
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

    #[instrument(level = tracing::Level::TRACE, skip(self))]
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
                .unwrap_or_else(|| panic!("did not get external symbol: {sym:?}"));
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

    pub(super) fn promote(&mut self, sym: Symbol, entry: EnvEntry) {
        self.term_env.promote(sym, entry);
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
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

        if let Symbol::Struct(StructId {
            module_id: module_id @ (ModuleId::External(..) | ModuleId::Core),
            local_id,
        }) = *symbol
            && let Some(module) = self.modules.modules.get(&module_id)
        {
            let nominal = module
                .types
                .catalog
                .nominals
                .get(&Symbol::Struct(StructId {
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
                match sym {
                    Symbol::InstanceMethod(..) => {
                        self.type_catalog
                            .instance_methods
                            .entry(*receiver)
                            .or_default()
                            .insert(label.clone(), sym);
                    }
                    Symbol::Property(..) => {
                        self.type_catalog
                            .properties
                            .entry(*receiver)
                            .or_default()
                            .insert(label.clone(), sym);
                    }
                    Symbol::StaticMethod(..) => {
                        self.type_catalog
                            .static_methods
                            .entry(*receiver)
                            .or_default()
                            .insert(label.clone(), sym);
                    }
                    _ => (),
                }

                return Some(sym);
            }
        }

        None
    }

    pub(super) fn lookup_variants(&self, receiver: &Symbol) -> Option<IndexMap<Label, Symbol>> {
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

    pub(super) fn lookup_conformance_mut(
        &mut self,
        key: &ConformanceKey,
    ) -> Option<&mut Conformance> {
        self.type_catalog.conformances.get_mut(key)
    }

    pub(super) fn lookup_protocol(&mut self, protocol_id: ProtocolId) -> Option<Protocol> {
        if let Some(entry) = self.type_catalog.protocols.get(&protocol_id).cloned() {
            return Some(entry);
        }

        if let ProtocolId {
            module_id: module_id @ (ModuleId::External(..) | ModuleId::Core | ModuleId::Builtin),
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
                .unwrap_or_else(|| {
                    panic!(
                        "did not get external symbol: {:?}",
                        ProtocolId {
                            module_id: module_key,
                            local_id,
                        }
                    )
                });

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

        if let Symbol::Struct(StructId {
            module_id: module_id @ (ModuleId::External(..) | ModuleId::Core),
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
                .get(&Symbol::Struct(StructId {
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

        if let Symbol::Struct(StructId {
            module_id: module_id @ (ModuleId::External(..) | ModuleId::Core),
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
                .get(&Symbol::Struct(StructId {
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

    pub(crate) fn new_type_param(&mut self, meta: Option<MetaVarId>) -> InferTy {
        let id = self.vars.type_params.next_id();
        if let Some(meta) = meta {
            self.reverse_instantiations.ty.insert(meta, id);
        }

        tracing::trace!("Fresh type param {id:?}");
        InferTy::Param(id)
    }

    pub(crate) fn new_type_param_id(&mut self, meta: Option<MetaVarId>) -> TypeParamId {
        let id = self.vars.type_params.next_id();
        if let Some(meta) = meta {
            self.reverse_instantiations.ty.insert(meta, id);
        }

        tracing::trace!("Fresh type param {id:?}");
        id
    }

    pub(crate) fn new_row_type_param(&mut self, meta: Option<RowMetaId>) -> InferRow {
        let id = self.vars.row_params.next_id();

        if let Some(meta) = meta {
            self.reverse_instantiations.row.insert(meta, id);
        }

        tracing::trace!("Fresh type param {id:?}");
        InferRow::Param(id)
    }

    pub(crate) fn new_skolem(&mut self) -> InferTy {
        let id = self.vars.skolems.next_id();
        tracing::trace!("Fresh skolem {id:?}");
        InferTy::Rigid(id)
    }

    pub(crate) fn new_ty_meta_var(&mut self, level: Level) -> InferTy {
        let id = self.vars.ty_metas.next_id();
        self.meta_levels.borrow_mut().insert(Meta::Ty(id), level);
        tracing::trace!("Fresh {id:?}");
        InferTy::Var { id, level }
    }

    pub(crate) fn new_row_meta_var(&mut self, level: Level) -> InferRow {
        let id = self.vars.row_metas.next_id();
        self.meta_levels.borrow_mut().insert(Meta::Row(id), level);
        tracing::trace!("Fresh {id:?}");
        InferRow::Var(id)
    }

    pub(crate) fn new_row_meta_var_id(&mut self, level: Level) -> RowMetaId {
        let id = self.vars.row_metas.next_id();
        self.meta_levels.borrow_mut().insert(Meta::Row(id), level);
        tracing::trace!("Fresh {id:?}");
        id
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
