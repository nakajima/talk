use std::{cell::RefCell, rc::Rc};

use ena::unify::{InPlaceUnificationTable, UnifyKey};
use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use tracing::instrument;

use crate::{
    compiling::module::{ModuleEnvironment, ModuleId},
    label::Label,
    name_resolution::symbol::{ProtocolId, StructId, Symbol},
    node_id::NodeID,
    types::{
        builtins::builtin_scope,
        constraints::{constraint::Constraint, store::ConstraintStore},
        infer_row::{InferRow, RowMetaId, RowParamId},
        infer_ty::{InferTy, Level, Meta, MetaVarId, SkolemId, TypeParamId},
        predicate::Predicate,
        row::Row,
        scheme::{ForAll, Scheme},
        solve_context::{Solve, SolveContext, SolveContextKind},
        term_environment::{EnvEntry, TermEnv},
        ty::{SomeType, Ty},
        type_catalog::{MemberWitness, TypeCatalog},
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, substitute},
        vars::Vars,
    },
};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum TypeDefKind {
    Struct,
    Enum,
    Protocol,
    Extension,
}

#[derive(Debug)]
pub struct TypeSession {
    pub current_module_id: ModuleId,
    pub types_by_node: FxHashMap<NodeID, InferTy>,
    vars: Vars,
    term_env: TermEnv,
    pub(super) meta_levels: Rc<RefCell<FxHashMap<Meta, Level>>>,
    pub(super) skolem_map: FxHashMap<InferTy, InferTy>,

    pub(super) type_param_bounds: FxHashMap<TypeParamId, IndexSet<Predicate<InferTy>>>,

    pub typealiases: FxHashMap<Symbol, Scheme<InferTy>>,
    pub(super) type_catalog: TypeCatalog<InferTy>,
    pub(super) modules: Rc<ModuleEnvironment>,
    pub aliases: FxHashMap<Symbol, Scheme<InferTy>>,
    pub(super) reverse_instantiations: ReverseInstantiations,

    meta_vars: InPlaceUnificationTable<MetaVarId>,
    row_vars: InPlaceUnificationTable<RowMetaId>,
}

pub struct Typed {}

#[derive(Debug, Clone, PartialEq)]
pub enum MemberSource {
    SelfMember,
    Protocol(ProtocolId),
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeEntry {
    Mono(Ty),
    Poly(Scheme<Ty>),
}

impl TypeEntry {
    pub fn as_mono_ty(&self) -> &Ty {
        match self {
            Self::Mono(ty) => ty,
            Self::Poly(scheme) => &scheme.ty,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Types {
    pub types_by_node: FxHashMap<NodeID, TypeEntry>,
    pub types_by_symbol: FxHashMap<Symbol, TypeEntry>,
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

#[allow(clippy::expect_used)]
impl TypeSession {
    pub fn new(current_module_id: ModuleId, modules: Rc<ModuleEnvironment>) -> Self {
        let mut term_env = TermEnv {
            symbols: FxHashMap::default(),
        };

        for (sym, entry) in builtin_scope() {
            term_env.insert(sym, entry);
        }

        let mut catalog = TypeCatalog::<InferTy>::default();

        // Import reqs
        for module in &modules.modules {
            for (sym, reqs) in module.1.types.catalog.method_requirements.iter() {
                catalog
                    .method_requirements
                    .entry(*sym)
                    .or_default()
                    .extend(reqs.clone());
            }

            for (sym, reqs) in module.1.types.catalog.instance_methods.iter() {
                catalog
                    .instance_methods
                    .entry(*sym)
                    .or_default()
                    .extend(reqs.clone());
            }

            catalog.conformances.extend(
                module
                    .1
                    .types
                    .catalog
                    .conformances
                    .clone()
                    .into_iter()
                    .map(|(k, v)| (k, v.into())),
            );

            catalog.member_witnesses.extend(
                module
                    .1
                    .types
                    .catalog
                    .member_witnesses
                    .clone()
                    .into_iter()
                    .map(|(k, v)| {
                        (
                            k,
                            match v {
                                MemberWitness::Concrete(sym) => MemberWitness::Concrete(sym),
                                MemberWitness::Requirement(sym) => MemberWitness::Requirement(sym),
                                MemberWitness::Meta { receiver, label } => MemberWitness::Meta {
                                    receiver: receiver.into(),
                                    label,
                                },
                            },
                        )
                    }),
            );
        }

        TypeSession {
            current_module_id,
            vars: Default::default(),
            skolem_map: Default::default(),
            meta_levels: Default::default(),
            type_param_bounds: Default::default(),
            term_env,
            reverse_instantiations: Default::default(),
            types_by_node: Default::default(),
            typealiases: Default::default(),
            type_catalog: catalog,
            modules,
            aliases: Default::default(),

            meta_vars: Default::default(),
            row_vars: Default::default(),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, constraints))]
    pub fn insert(&mut self, symbol: Symbol, ty: InferTy, constraints: &mut ConstraintStore) {
        let foralls: IndexSet<_> = ty.collect_foralls().into_iter().collect();
        if foralls.is_empty() {
            self.term_env.insert(symbol, EnvEntry::Mono(ty));
        } else {
            self.term_env.insert(
                symbol,
                EnvEntry::Scheme(Scheme {
                    foralls,
                    predicates: Default::default(),
                    ty,
                }),
            );
        }

        constraints.wake_symbols(&[symbol]);
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

        let mut context = SolveContext::new(
            UnificationSubstitutions::new(self.meta_levels.clone()),
            Default::default(),
            Default::default(),
            SolveContextKind::Normal,
        );
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
                            let generalized = self.generalize(scheme.ty, &mut context, &Default::default(), &mut Default::default());
                            let EnvEntry::Scheme(generalized) = generalized
                            else {
                                unreachable!(
                                    "generalize returned Mono when scheme.ty.contains_var() {generalized:?}"
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
                                ty: self.finalize_infer_ty(generalized.ty).into(),
                            })
                        } else {
                            TypeEntry::Poly(Scheme {
                                foralls: scheme.foralls,
                                predicates: scheme
                                    .predicates
                                    .into_iter()
                                    .map(|p| p.into())
                                    .collect(),
                                ty: self.finalize_infer_ty(scheme.ty).into(),
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
                        tracing::warn!("did not solve {meta:?}");
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

    pub(super) fn finalize_infer_ty(&mut self, ty: InferTy) -> InferTy {
        let ty = substitute(ty.clone(), &self.skolem_map);
        self.shallow_generalize(ty)
    }

    pub(super) fn finalize_ty(&mut self, ty: InferTy) -> TypeEntry {
        let ty = self.finalize_infer_ty(ty);
        let mut context = SolveContext::new(
            UnificationSubstitutions::new(self.meta_levels.clone()),
            Default::default(),
            Default::default(),
            SolveContextKind::Normal,
        );

        if ty.contains_var() {
            self.generalize(
                ty.clone(),
                &mut context,
                &Default::default(),
                &mut Default::default(),
            )
            .into()
        } else {
            TypeEntry::Mono(ty.clone().into())
        }
    }

    pub(super) fn finalize_row(&mut self, row: InferRow) -> Row {
        let row = self.shallow_generalize_row(row);

        match row {
            InferRow::Empty(..) => row.into(),
            InferRow::Param(..) => row.into(),
            InferRow::Var(var) => Row::Param(
                *self
                    .reverse_instantiations
                    .row
                    .get(&var)
                    .expect("did not get reverse instantiation"),
            ),
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

    pub(super) fn apply_row(
        &mut self,
        row: InferRow,
        substitutions: &mut UnificationSubstitutions,
    ) -> InferRow {
        match row {
            InferRow::Empty(kind) => InferRow::Empty(kind),
            InferRow::Var(id) => {
                let rep = self.canon_row(id);
                if let Some(bound) = substitutions.row.get(&rep).cloned() {
                    self.apply_row(bound, substitutions)
                } else {
                    InferRow::Var(rep)
                }
            }
            InferRow::Param(_) => row,
            InferRow::Extend { row, label, ty } => InferRow::Extend {
                row: Box::new(self.apply_row(*row, substitutions)),
                label,
                ty: self.apply(ty, substitutions),
            },
        }
    }

    pub(super) fn apply(
        &mut self,
        ty: InferTy,
        substitutions: &mut UnificationSubstitutions,
    ) -> InferTy {
        match ty {
            InferTy::Error(..) => ty,
            InferTy::Param(..) => ty,
            InferTy::Rigid(..) => ty,
            InferTy::Projection {
                box base,
                associated,
                protocol_id,
            } => InferTy::Projection {
                base: self.apply(base, substitutions).into(),
                associated,
                protocol_id,
            },
            InferTy::Var { id, .. } => {
                let rep = self.canon_meta(id);
                if let Some(bound) = substitutions.ty.get(&rep).cloned()
                    && !matches!(bound, InferTy::Var { id, .. } if rep == id)
                {
                    self.apply(bound, substitutions) // keep collapsing
                } else {
                    InferTy::Var {
                        id: rep,
                        level: substitutions
                            .meta_levels
                            .borrow()
                            .get(&Meta::Ty(rep))
                            .copied()
                            .unwrap_or_default(),
                    }
                }
            }
            InferTy::Constructor { name, params, ret } => InferTy::Constructor {
                name,
                params: params
                    .into_iter()
                    .map(|p| self.apply(p, substitutions))
                    .collect(),
                ret: Box::new(self.apply(*ret, substitutions)),
            },
            InferTy::Primitive(..) => ty,
            InferTy::Func(params, ret) => InferTy::Func(
                Box::new(self.apply(*params, substitutions)),
                Box::new(self.apply(*ret, substitutions)),
            ),
            InferTy::Tuple(items) => InferTy::Tuple(
                items
                    .into_iter()
                    .map(|t| self.apply(t, substitutions))
                    .collect(),
            ),
            InferTy::Record(row) => InferTy::Record(Box::new(self.apply_row(*row, substitutions))),
            InferTy::Nominal { symbol, box row } => InferTy::Nominal {
                symbol,
                row: Box::new(self.apply_row(row, substitutions)),
            },
        }
    }

    pub fn apply_mult(
        &mut self,
        tys: Vec<InferTy>,
        substitutions: &mut UnificationSubstitutions,
    ) -> Vec<InferTy> {
        tys.into_iter()
            .map(|ty| self.apply(ty, substitutions))
            .collect()
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, substitutions))]
    pub fn apply_all(&mut self, substitutions: &mut UnificationSubstitutions) {
        for key in self.types_by_node.keys().copied().collect_vec() {
            let ty = self
                .types_by_node
                .remove(&key)
                .unwrap_or_else(|| unreachable!());
            let ty = self.apply(ty.clone(), substitutions);
            self.types_by_node.insert(key, ty);
        }

        for key in self.term_env.symbols.keys().copied().collect_vec() {
            let entry = self
                .term_env
                .symbols
                .remove(&key)
                .unwrap_or_else(|| unreachable!());
            let entry = entry.apply(substitutions, self);
            self.term_env.insert(key, entry);
        }

        #[allow(clippy::unwrap_used)]
        for key in self
            .type_catalog
            .instantiations
            .ty
            .keys()
            .copied()
            .collect_vec()
        {
            let ty = self.type_catalog.instantiations.ty.remove(&key).unwrap();
            let ty = self.apply(ty.clone(), substitutions);
            self.type_catalog.instantiations.ty.insert(key, ty);
        }

        #[allow(clippy::unwrap_used)]
        for key in self
            .type_catalog
            .instantiations
            .row
            .keys()
            .copied()
            .collect_vec()
        {
            let row = self.type_catalog.instantiations.row.remove(&key).unwrap();
            let row = self.apply_row(row, substitutions);
            self.type_catalog.instantiations.row.insert(key, row);
        }
    }

    pub fn get_term_env(&self) -> &TermEnv {
        &self.term_env
    }

    pub fn skolemize(&mut self, entry: &EnvEntry<InferTy>) -> InferTy {
        let mut skolems = FxHashMap::default();
        for forall in entry.foralls() {
            let ForAll::Ty(id) = forall else {
                continue;
            };

            let new_id = self.new_skolem(id);
            skolems.insert(InferTy::Param(id), new_id);
        }

        substitute(entry._as_ty().clone(), &skolems)
    }

    pub fn canon_row(&mut self, id: RowMetaId) -> RowMetaId {
        self.row_vars.find(id)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub fn link_row(&mut self, a: RowMetaId, b: RowMetaId) {
        self.row_vars
            .unify_var_var(a, b)
            .unwrap_or_else(|_| unreachable!());
    }

    pub fn canon_meta(&mut self, id: MetaVarId) -> MetaVarId {
        self.meta_vars.find(id)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub fn link_meta(&mut self, a: MetaVarId, b: MetaVarId) {
        self.meta_vars
            .unify_var_var(a, b)
            .unwrap_or_else(|_| unreachable!());
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, unsolved, context, constraints))]
    pub fn generalize(
        &mut self,
        ty: InferTy,
        context: &mut impl Solve,
        unsolved: &IndexSet<Constraint>,
        constraints: &mut ConstraintStore,
    ) -> EnvEntry<InferTy> {
        // Make sure we're up to date
        let ty = self.apply(ty, context.substitutions_mut());

        // collect metas in ty
        let mut metas = FxHashSet::default();
        metas.extend(ty.collect_metas());

        // Also collect metas that appear only in constraints
        for constraint in unsolved {
            let constraint = constraint.clone().apply(context.substitutions_mut(), self);
            metas.extend(constraint.collect_metas());
        }

        let mut foralls: IndexSet<_> = ty.collect_foralls().into_iter().collect();
        let mut predicates: IndexSet<Predicate<InferTy>> = Default::default();
        let mut substitutions = UnificationSubstitutions::new(self.meta_levels.clone());
        for m in &metas {
            match m {
                InferTy::Param(p) => {
                    predicates.extend(self.type_param_bounds.get(p).cloned().unwrap_or_default());
                    foralls.insert(ForAll::Ty(*p));
                }

                InferTy::Var { level, id } => {
                    if *level < context.level() {
                        tracing::warn!(
                            "discarding {m:?} due to level ({level:?} < {:?})",
                            context.level()
                        );
                        continue;
                    }

                    let param_id = self
                        .reverse_instantiations
                        .ty
                        .get(id)
                        .copied()
                        .unwrap_or_else(|| {
                            let param_id = self.vars.type_params.next_id();
                            self.reverse_instantiations.ty.insert(*id, param_id);
                            tracing::trace!("generalizing {m:?} to {param_id:?}");
                            foralls.insert(ForAll::Ty(param_id));
                            param_id
                        });
                    foralls.insert(ForAll::Ty(param_id));
                    substitutions.ty.insert(*id, InferTy::Param(param_id));
                }
                InferTy::Record(box InferRow::Var(id))
                | InferTy::Nominal {
                    row: box InferRow::Var(id),
                    ..
                } => {
                    let levels = self.meta_levels.borrow();
                    let level = levels.get(&Meta::Row(*id)).copied().unwrap_or_default();
                    if level < context.level() {
                        tracing::trace!(
                            "discarding {m:?} due to level ({level:?} < {:?})",
                            context.level()
                        );
                        continue;
                    }

                    let param_id = self
                        .reverse_instantiations
                        .row
                        .get(id)
                        .copied()
                        .unwrap_or_else(|| {
                            let param_id = self.vars.row_params.next_id();
                            self.reverse_instantiations.row.insert(*id, param_id);
                            tracing::trace!("generalizing {m:?} to {param_id:?}");
                            foralls.insert(ForAll::Row(param_id));
                            param_id
                        });

                    foralls.insert(ForAll::Row(param_id));
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
                let r = self.apply_row(h.row.clone(), &mut substitutions);
                if let InferRow::Var(row_meta) = r {
                    // quantify if its level is above the binder's level
                    let levels = self.meta_levels.borrow();
                    let lvl = levels.get(&Meta::Row(row_meta)).unwrap_or(&Level(0));
                    if *lvl >= context.level() {
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
        let ty = self.apply(ty, &mut substitutions);

        predicates.extend(unsolved.iter().filter_map(|c| {
            let metas = c.collect_metas();

            if metas.is_empty() {
                return None;
            }

            // Check that all metas are at or above the current generalization level
            // Predicates should only reference quantified variables (foralls), not
            // ungeneralized metas from outer scopes
            for meta in &metas {
                if let InferTy::Var { level, .. } = meta && *level < context.level() {
                        tracing::debug!(
                            "skipping constraint {c:?} with outer-scope meta {meta:?} (level {level:?} < {:?})", context.level()
                        );
                        return None;
                }
            }

            c.substitute(&self.skolem_map)
                .into_predicate(&mut substitutions, self)
        }));

        if foralls.is_empty() && predicates.is_empty() {
            return EnvEntry::Mono(ty);
        }

        EnvEntry::Scheme(Scheme::<InferTy>::new(
            foralls,
            predicates.into_iter().collect(),
            ty,
        ))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(super) fn lookup(&mut self, sym: &Symbol) -> Option<EnvEntry<InferTy>> {
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
                .cloned()?;
            let entry: EnvEntry<InferTy> = match entry.clone() {
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

    #[instrument(level = tracing::Level::TRACE, skip(self, constraints))]
    pub(super) fn promote(
        &mut self,
        sym: Symbol,
        entry: EnvEntry<InferTy>,
        constraints: &mut ConstraintStore,
    ) {
        if matches!(sym, Symbol::Builtin(..)) {
            tracing::error!("can't override builtin");
            return;
        }

        constraints.wake_symbols(&[sym]);

        self.term_env.promote(sym, entry);
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, constraints))]
    pub(super) fn insert_term(
        &mut self,
        sym: Symbol,
        entry: EnvEntry<InferTy>,
        constraints: &mut ConstraintStore,
    ) {
        if matches!(sym, Symbol::Builtin(..)) {
            tracing::error!("can't override builtin");
            return;
        }

        constraints.wake_symbols(&[sym]);

        self.term_env.insert(sym, entry);
    }

    pub(super) fn insert_mono(
        &mut self,
        sym: Symbol,
        ty: InferTy,
        constraints: &mut ConstraintStore,
    ) {
        if matches!(sym, Symbol::Builtin(..)) {
            tracing::error!("can't override builtin");
            return;
        }

        constraints.wake_symbols(&[sym]);

        self.term_env.insert(sym, EnvEntry::Mono(ty));
    }

    #[instrument(skip(self))]
    pub(super) fn lookup_member(
        &mut self,
        receiver: &Symbol,
        label: &Label,
    ) -> Option<(Symbol, MemberSource)> {
        if let Some(sym) = self.type_catalog.lookup_member(receiver, label) {
            return Some(sym);
        }

        for module in self.modules.modules.values() {
            if let Some((sym, source)) = module
                .types
                .catalog
                .lookup_member(&receiver.current(), label)
            {
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
                    Symbol::MethodRequirement(..) => {
                        self.type_catalog
                            .method_requirements
                            .entry(*receiver)
                            .or_default()
                            .insert(label.clone(), sym);
                    }
                    Symbol::Variant(..) => {
                        self.type_catalog
                            .variants
                            .entry(*receiver)
                            .or_default()
                            .insert(label.clone(), sym);
                    }
                    _ => {
                        tracing::warn!("found unhandled nominal member: {sym:?}");
                    }
                }

                return Some((sym, source));
            }
        }

        None
    }

    pub(super) fn lookup_static_member(
        &mut self,
        receiver: &Symbol,
        label: &Label,
    ) -> Option<Symbol> {
        if let Some(sym) = self.type_catalog.lookup_static_member(receiver, label) {
            return Some(sym);
        }

        for module in self.modules.modules.values() {
            if let Some(sym) = module
                .types
                .catalog
                .lookup_static_member(&receiver.current(), label)
            {
                match sym {
                    Symbol::StaticMethod(..) => {
                        self.type_catalog
                            .static_methods
                            .entry(*receiver)
                            .or_default()
                            .insert(label.clone(), sym);
                    }
                    Symbol::Variant(..) => {
                        self.type_catalog
                            .variants
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

    pub(super) fn _lookup_variants(&self, receiver: &Symbol) -> Option<IndexMap<Label, Symbol>> {
        if let Some(variants) = self.type_catalog.variants.get(receiver).cloned() {
            return Some(variants);
        }

        for module in self.modules.modules.values() {
            if let Some(variants) = module
                .types
                .catalog
                .variants
                .get(&receiver.current())
                .cloned()
            {
                return Some(variants);
            }
        }

        None
    }

    pub(super) fn lookup_method_requirements(
        &mut self,
        protocol_id: &ProtocolId,
    ) -> Option<IndexMap<Label, Symbol>> {
        if let Some(reqs) = self
            .type_catalog
            .method_requirements
            .get(&protocol_id.into())
            .cloned()
        {
            return Some(reqs);
        }

        if let ProtocolId {
            module_id: module_id @ (ModuleId::External(..) | ModuleId::Core),
            local_id,
        } = *protocol_id
            && let Some(module) = self.modules.modules.get(&module_id)
        {
            let module_key = if matches!(module_id, ModuleId::External(..)) {
                ModuleId::Current
            } else {
                module_id
            };
            let requirements = module
                .types
                .catalog
                .method_requirements
                .get(&Symbol::Protocol(ProtocolId {
                    module_id: module_key,
                    local_id,
                }))
                .cloned()?;

            let imported: IndexMap<Label, Symbol> = requirements
                .into_iter()
                .map(|(label, sym)| (label, sym.import(module_id)))
                .collect();

            self.type_catalog
                .method_requirements
                .insert((*protocol_id).into(), imported.clone());
            return Some(imported);
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

    pub(super) fn _lookup_properties(
        &mut self,
        symbol: &Symbol,
    ) -> Option<IndexMap<Label, Symbol>> {
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

    pub(crate) fn new_skolem(&mut self, param: TypeParamId) -> InferTy {
        let id = self.new_skolem_id(param);
        InferTy::Rigid(id)
    }

    pub(crate) fn new_skolem_id(&mut self, param: TypeParamId) -> SkolemId {
        let id = self.vars.skolems.next_id();
        self.skolem_map
            .insert(InferTy::Rigid(id), InferTy::Param(param));
        tracing::trace!("Fresh skolem {id:?}");
        id
    }

    pub(crate) fn new_ty_meta_var(&mut self, level: Level) -> InferTy {
        let id = self.meta_vars.new_key(level);
        self.meta_levels.borrow_mut().insert(Meta::Ty(id), level);
        tracing::trace!("Fresh {id:?}");
        InferTy::Var { id, level }
    }

    pub(crate) fn new_ty_meta_var_id(&mut self, level: Level) -> MetaVarId {
        let id = self.meta_vars.new_key(level);
        self.meta_levels.borrow_mut().insert(Meta::Ty(id), level);
        tracing::trace!("Fresh {id:?}");
        id
    }

    pub(crate) fn new_row_meta_var(&mut self, level: Level) -> InferRow {
        let id = self.row_vars.new_key(level);
        self.meta_levels.borrow_mut().insert(Meta::Row(id), level);
        tracing::trace!("Fresh {id:?}");
        InferRow::Var(id)
    }

    pub(crate) fn new_row_meta_var_id(&mut self, level: Level) -> RowMetaId {
        let id = self.row_vars.new_key(level);
        self.meta_levels.borrow_mut().insert(Meta::Row(id), level);
        tracing::trace!("Fresh {id:?}");
        id
    }
}
