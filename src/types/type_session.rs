use std::{cell::RefCell, rc::Rc};

use ena::unify::InPlaceUnificationTable;
use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use tracing::instrument;

use crate::{
    compiling::module::{ModuleEnvironment, ModuleId},
    label::Label,
    name_resolution::{
        name_resolver::ResolvedNames,
        symbol::{ProtocolId, Symbol, Symbols},
    },
    node_id::NodeID,
    types::{
        builtins::builtin_scope,
        conformance::{Conformance, ConformanceKey},
        constraints::{call::CallId, constraint::Constraint, store::ConstraintStore},
        infer_row::{InferRow, RowMetaId, RowParamId},
        infer_ty::{InferTy, Level, Meta, MetaVarId, SkolemId, TypeParamId},
        matcher::MatchPlan,
        predicate::Predicate,
        row::Row,
        scheme::{ForAll, Scheme},
        solve_context::{Solve, SolveContext, SolveContextKind},
        term_environment::{EnvEntry, TermEnv},
        ty::{SomeType, Ty},
        type_catalog::{Nominal, TypeCatalog},
        type_error::TypeError,
        type_operations::{InstantiationSubstitutions, UnificationSubstitutions, substitute},
        typed_ast::TyMappable,
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

    pub protocol_member_witnesses: FxHashMap<NodeID, Symbol>,
    pub(crate) symbols: Symbols,
    pub(crate) resolved_names: ResolvedNames,
    pub(crate) instantiations_by_call: FxHashMap<CallId, InstantiationSubstitutions<InferTy>>,

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

    pub fn import(self, module_id: ModuleId) -> Self {
        match self {
            Self::Mono(ty) => Self::Mono(ty.import(module_id)),
            Self::Poly(scheme) => Self::Poly(scheme.import(module_id)),
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Types {
    pub types_by_node: FxHashMap<NodeID, TypeEntry>,
    pub types_by_symbol: FxHashMap<Symbol, TypeEntry>,
    pub catalog: TypeCatalog<Ty>,
    pub(crate) match_plans: FxHashMap<NodeID, MatchPlan>,
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

    pub fn import_as(self, module_id: ModuleId) -> Types {
        Types {
            types_by_node: self
                .types_by_node
                .into_iter()
                .map(|(k, v)| (k, v.import(module_id)))
                .collect(),
            types_by_symbol: self
                .types_by_symbol
                .into_iter()
                .map(|(k, v)| (k.import(module_id), v.import(module_id)))
                .collect(),
            catalog: self.catalog.import_as(module_id),
            match_plans: self.match_plans,
        }
    }
}

#[allow(clippy::expect_used)]
impl TypeSession {
    pub fn new(
        current_module_id: ModuleId,
        modules: Rc<ModuleEnvironment>,
        symbols: Symbols,
        resolved_names: ResolvedNames,
    ) -> Self {
        let mut term_env = TermEnv {
            symbols: FxHashMap::default(),
        };

        for (sym, entry) in builtin_scope() {
            term_env.insert(sym, entry);
        }

        let mut catalog = TypeCatalog::<InferTy>::default();

        // Import builtin nominals
        catalog.nominals.insert(
            Symbol::Bool,
            Nominal {
                properties: Default::default(),
                variants: Default::default(),
                type_params: Default::default(),
            },
        );
        catalog.nominals.insert(
            Symbol::Int,
            Nominal {
                properties: Default::default(),
                variants: Default::default(),
                type_params: Default::default(),
            },
        );
        catalog.nominals.insert(
            Symbol::Float,
            Nominal {
                properties: Default::default(),
                variants: Default::default(),
                type_params: Default::default(),
            },
        );
        catalog.nominals.insert(
            Symbol::RawPtr,
            Nominal {
                properties: Default::default(),
                variants: Default::default(),
                type_params: Default::default(),
            },
        );
        catalog.nominals.insert(
            Symbol::Byte,
            Nominal {
                properties: Default::default(),
                variants: Default::default(),
                type_params: Default::default(),
            },
        );

        // Import conformances from all modules
        for (key, conformance) in modules.all_conformances() {
            catalog
                .conformances
                .entry(key)
                .or_insert_with(|| conformance.into());
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
            protocol_member_witnesses: Default::default(),
            instantiations_by_call: Default::default(),

            meta_vars: Default::default(),
            row_vars: Default::default(),

            symbols,
            resolved_names,
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

        // let instantiations = std::mem::take(&mut self.instantiations_by_call)
        //     .into_iter()
        //     .map(|(k, v)| {
        //         (
        //             k,
        //             InstantiationSubstitutions {
        //                 ty: v
        //                     .ty
        //                     .into_iter()
        //                     .map(|(k, v)| (k, self.finalize_ty(v).as_mono_ty().clone()))
        //                     .collect(),
        //                 row: v
        //                     .row
        //                     .into_iter()
        //                     .map(|(k, v)| (k, self.finalize_row(v)))
        //                     .collect(),
        //             },
        //         )
        //     });

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
            match_plans: Default::default(),
        };

        Ok(types)
    }

    fn shallow_generalize_row(&mut self, row: InferRow) -> InferRow {
        match row {
            InferRow::Empty => row,
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
                        tracing::warn!("did not solve {meta:?}, generating a type param even tho that's probably not what we want.");
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
            InferTy::Func(box param, box ret, box effects) => InferTy::Func(
                self.shallow_generalize(param).into(),
                self.shallow_generalize(ret).into(),
                self.shallow_generalize_row(effects).into(),
            ),
            InferTy::Tuple(items) => InferTy::Tuple(
                items
                    .into_iter()
                    .map(|p| self.shallow_generalize(p))
                    .collect(),
            ),
            InferTy::Record(box row) => InferTy::Record(self.shallow_generalize_row(row).into()),
            InferTy::Nominal { symbol, type_args } => InferTy::Nominal {
                symbol,
                type_args: type_args
                    .into_iter()
                    .map(|a| self.shallow_generalize(a))
                    .collect(),
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
            InferRow::Empty => row.into(),
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
            InferRow::Empty => InferRow::Empty,
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
                params: self.apply_mult(params, substitutions),
                ret: Box::new(self.apply(*ret, substitutions)),
            },
            InferTy::Primitive(..) => ty,
            InferTy::Func(params, ret, effects) => InferTy::Func(
                Box::new(self.apply(*params, substitutions)),
                Box::new(self.apply(*ret, substitutions)),
                Box::new(self.apply_row(*effects, substitutions)),
            ),
            InferTy::Tuple(items) => InferTy::Tuple(self.apply_mult(items, substitutions)),
            InferTy::Record(row) => InferTy::Record(Box::new(self.apply_row(*row, substitutions))),
            InferTy::Nominal { symbol, type_args } => InferTy::Nominal {
                symbol,
                type_args: self.apply_mult(type_args, substitutions),
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

        let instantiations_by_call = std::mem::take(&mut self.instantiations_by_call);
        self.instantiations_by_call = instantiations_by_call
            .into_iter()
            .map(|(k, v)| (k, v.map_ty(&mut |t| self.apply(t.clone(), substitutions))))
            .collect();

        for key in self.term_env.symbols.keys().copied().collect_vec() {
            let entry = self
                .term_env
                .symbols
                .remove(&key)
                .unwrap_or_else(|| unreachable!());
            let entry = entry.apply(substitutions, self);
            self.term_env.insert(key, entry);
        }

        let mut conformances = std::mem::take(&mut self.type_catalog.conformances);
        for conformance in conformances.values_mut() {
            for ty in conformance.witnesses.associated_types.values_mut() {
                *ty = self.apply(ty.clone(), substitutions);
            }
        }
        _ = std::mem::replace(&mut self.type_catalog.conformances, conformances);
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

    #[instrument(level = tracing::Level::TRACE, skip(self, unsolved, context))]
    pub fn generalize(
        &mut self,
        ty: InferTy,
        context: &mut impl Solve,
        unsolved: &IndexSet<Constraint>,
        constraints: &mut ConstraintStore,
    ) -> EnvEntry<InferTy> {
        // Make sure we're up to date
        let ty = self.apply(ty, context.substitutions_mut());
        let mut foralls = ty.collect_foralls();
        let mut predicates: IndexSet<Predicate<InferTy>> = Default::default();

        // collect metas in ty
        let mut metas = FxHashSet::default();
        metas.extend(ty.collect_metas());

        // Also collect metas/foralls that appear only in constraints
        for constraint in unsolved {
            let constraint = constraint.clone().apply(context.substitutions_mut(), self);
            metas.extend(constraint.collect_metas());
            foralls.extend(constraint.collect_foralls());
        }

        for forall in &foralls {
            if let ForAll::Ty(id) = forall {
                predicates.extend(self.type_param_bounds.get(id).cloned().unwrap_or_default());
            }
        }

        let mut substitutions = UnificationSubstitutions::new(self.meta_levels.clone());
        for m in &metas {
            match m {
                Meta::Ty(id) => {
                    let levels = self.meta_levels.borrow();
                    let level = levels.get(m).copied().unwrap_or_default();
                    if level < context.level() {
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
                Meta::Row(id) => {
                    let levels = self.meta_levels.borrow();
                    let level = levels.get(m).copied().unwrap_or_default();
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
                let level = self.meta_levels.borrow().get(meta).copied().unwrap_or_default();
                if level < context.level() {
                        tracing::debug!(
                            "skipping constraint {c:?} with outer-scope meta {meta:?} (level {level:?} < {:?})", context.level()
                        );
                        return None;
                }
            }

            constraints.solve(c.id());

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

    pub(super) fn resolve_name(&self, sym: &Symbol) -> Option<&str> {
        if let Some(name) = self.resolved_names.symbol_names.get(sym) {
            return Some(name);
        }

        self.modules.resolve_name(sym).map(|x| x.as_str())
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(super) fn lookup(&mut self, sym: &Symbol) -> Option<EnvEntry<InferTy>> {
        if let Some(entry) = builtin_scope().get(sym).cloned() {
            return Some(entry);
        }

        if let Some(entry) = self.term_env.lookup(sym).cloned() {
            return Some(entry);
        }

        if let Some(entry) = self.modules.lookup(sym) {
            let entry: EnvEntry<InferTy> = match entry.clone() {
                TypeEntry::Mono(t) => EnvEntry::Mono(t.into()),
                TypeEntry::Poly(..) => entry.into(),
            };

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

    pub fn lookup_conformance(&mut self, key: &ConformanceKey) -> Option<Conformance<InferTy>> {
        if let Some(conformance) = self.type_catalog.conformances.get(key) {
            return Some(conformance.clone());
        }

        if let Some(conformance) = self.modules.lookup_conformance(key) {
            self.type_catalog
                .conformances
                .insert(*key, conformance.clone().into());
            return Some(conformance.clone().into());
        }

        None
    }

    pub fn lookup_associated_types(
        &mut self,
        protocol_id: Symbol,
    ) -> Option<IndexMap<Label, Symbol>> {
        if let Some(associated_types) = self
            .type_catalog
            .associated_types
            .get(&protocol_id)
            .cloned()
        {
            return Some(associated_types);
        }

        if let Some(associated_types) = self.modules.lookup_associated_types(&protocol_id) {
            self.type_catalog
                .associated_types
                .insert(protocol_id, associated_types.clone());
            return Some(associated_types);
        }

        None
    }

    pub fn lookup_effect(&self, id: &Symbol) -> Option<InferTy> {
        if let Some(effect) = self.type_catalog.lookup_effect(id) {
            return Some(effect.clone());
        }

        self.modules.lookup_effect(id).map(|t| t.into())
    }

    pub fn lookup_method_requirements(
        &mut self,
        protocol_id: Symbol,
    ) -> Option<IndexMap<Label, Symbol>> {
        if let Some(method_requirements) = self
            .type_catalog
            .method_requirements
            .get(&protocol_id)
            .cloned()
        {
            return Some(method_requirements);
        }

        if let Some(method_requirements) = self.modules.lookup_method_requirements(&protocol_id) {
            self.type_catalog
                .method_requirements
                .insert(protocol_id, method_requirements.clone());
            return Some(method_requirements);
        }

        None
    }

    pub fn lookup_instance_methods(&mut self, symbol: &Symbol) -> IndexMap<Label, Symbol> {
        let mut instance_methods = IndexMap::<Label, Symbol>::default();

        if let Some(methods) = self.modules.lookup_instance_methods(symbol) {
            self.type_catalog
                .instance_methods
                .entry(*symbol)
                .or_default()
                .extend(methods.clone());
            instance_methods.extend(methods);
        }

        if let Some(methods) = self.type_catalog.instance_methods.get(symbol).cloned() {
            instance_methods.extend(methods);
        }

        instance_methods
    }

    pub fn lookup_protocol_conformances(
        &mut self,
        protocol_id: &ProtocolId,
    ) -> Vec<ConformanceKey> {
        let mut result = vec![];

        for key in self.type_catalog.conformances.keys() {
            if key.protocol_id == *protocol_id {
                result.push(*key);
            }
        }

        result.extend(self.modules.lookup_protocol_conformances(protocol_id));
        result
    }

    pub fn lookup_nominal(&mut self, symbol: &Symbol) -> Option<Nominal<InferTy>> {
        if let Some(nominal) = self.type_catalog.nominals.get(symbol).cloned() {
            return Some(nominal);
        }

        if let Some(nominal) = self.modules.lookup_nominal(symbol).cloned() {
            self.type_catalog
                .nominals
                .insert(*symbol, nominal.clone().into());
            return Some(nominal.into());
        }

        None
    }

    #[instrument(skip(self))]
    pub(super) fn lookup_concrete_member(
        &mut self,
        receiver: &Symbol,
        label: &Label,
    ) -> Option<Symbol> {
        if let Some((sym, _)) = self.type_catalog.lookup_concrete_member(receiver, label) {
            if matches!(sym, Symbol::InstanceMethod(..))
                && !self
                    .type_catalog
                    .instance_methods
                    .entry(*receiver)
                    .or_default()
                    .contains_key(label)
            {
                self.type_catalog
                    .instance_methods
                    .entry(*receiver)
                    .or_default()
                    .insert(label.clone(), sym);
            }

            return Some(sym);
        }

        if let Some(sym) = self.modules.lookup_concrete_member(receiver, label) {
            self.cache_member(sym, receiver, label);
            return Some(sym);
        }

        None
    }

    #[instrument(skip(self))]
    pub(super) fn lookup_member(
        &mut self,
        receiver: &Symbol,
        label: &Label,
    ) -> Option<(Symbol, MemberSource)> {
        if let Some(sym) = self.type_catalog.lookup_member(receiver, label) {
            if matches!(sym.0, Symbol::InstanceMethod(..))
                && !self
                    .type_catalog
                    .instance_methods
                    .entry(*receiver)
                    .or_default()
                    .contains_key(label)
            {
                self.type_catalog
                    .instance_methods
                    .entry(*receiver)
                    .or_default()
                    .insert(label.clone(), sym.0);
            }

            return Some(sym);
        }

        if let Some(sym) = self.modules.lookup_member(receiver, label) {
            self.cache_member(sym, receiver, label);
            return Some((sym, MemberSource::SelfMember));
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

        if let Some(sym) = self.modules.lookup_static_member(receiver, label) {
            self.cache_member(sym, receiver, label);
            return Some(sym);
        }

        None
    }

    pub(super) fn lookup_initializers(
        &mut self,
        symbol: &Symbol,
    ) -> Option<IndexMap<Label, Symbol>> {
        if let Some(initializers) = self.type_catalog.initializers.get(symbol).cloned() {
            return Some(initializers);
        }

        if let Some(initializers) = self.modules.lookup_initializers(symbol) {
            self.type_catalog
                .initializers
                .entry(*symbol)
                .and_modify(|e| e.extend(initializers.clone()));
            return Some(initializers);
        }

        None
    }

    fn cache_member(&mut self, sym: Symbol, receiver: &Symbol, label: &Label) {
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
        InferTy::Var { id, level }
    }

    pub(crate) fn new_ty_meta_var_id(&mut self, level: Level) -> MetaVarId {
        let id = self.meta_vars.new_key(level);
        self.meta_levels.borrow_mut().insert(Meta::Ty(id), level);
        id
    }

    pub(crate) fn new_row_meta_var(&mut self, level: Level) -> InferRow {
        let id = self.row_vars.new_key(level);
        self.meta_levels.borrow_mut().insert(Meta::Row(id), level);
        InferRow::Var(id)
    }
}
