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
        call_tree::CallTree,
        conformance::{Conformance, ConformanceKey},
        constraints::{constraint::Constraint, store::ConstraintStore},
        infer_row::{InferRow, RowMetaId, RowParamId},
        infer_ty::{InferTy, Level, Meta, MetaVarId, SkolemId, TypeParamId},
        predicate::Predicate,
        row::Row,
        scheme::{ForAll, Scheme},
        solve_context::{Solve, SolveContext, SolveContextKind},
        term_environment::{EnvEntry, TermEnv},
        ty::SomeType,
        type_catalog::{Nominal, TypeCatalog},
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, substitute},
        types::{TypeEntry, Types},
        variational::{resolve_overloads, ChoiceStore, ErrorConstraintStore},
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

    pub typealiases: FxHashMap<Symbol, Scheme<InferTy>>,
    pub(super) type_catalog: TypeCatalog<InferTy>,
    pub(super) modules: Rc<ModuleEnvironment>,
    pub aliases: FxHashMap<Symbol, Scheme<InferTy>>,
    pub(super) reverse_instantiations: ReverseInstantiations,

    /// Variational choices for protocol method calls.
    /// Each call site (NodeID) that involves a protocol method on a type parameter
    /// gets choices registered here, allowing resolution at specialization time.
    pub choices: ChoiceStore,

    /// Error constraints recorded during variational type checking.
    /// When a constraint fails in a non-universal configuration, the error is
    /// recorded here instead of immediately failing. This allows resolution
    /// to determine which alternatives are valid.
    pub error_constraints: ErrorConstraintStore,

    /// Call tree mapping each function to the callees in its body.
    /// Built during inference and used by specialization pass.
    pub call_tree: CallTree,

    pub(crate) symbols: Symbols,
    pub(crate) resolved_names: ResolvedNames,

    meta_vars: InPlaceUnificationTable<MetaVarId>,
    row_vars: InPlaceUnificationTable<RowMetaId>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum MemberSource {
    SelfMember,
    Protocol(ProtocolId),
}

#[derive(Debug, Default)]
pub struct ReverseInstantiations {
    /// Maps meta vars back to the type param they were instantiated from.
    /// Stores the full InferTy::Param with bounds so we don't need a separate lookup.
    pub ty: FxHashMap<MetaVarId, InferTy>,
    pub row: FxHashMap<RowMetaId, RowParamId>,
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
            term_env,
            reverse_instantiations: Default::default(),
            types_by_node: Default::default(),
            typealiases: Default::default(),
            type_catalog: catalog,
            modules,
            aliases: Default::default(),
            choices: ChoiceStore::new(),
            error_constraints: ErrorConstraintStore::new(),
            call_tree: Default::default(),

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
            // Collect predicates from InferTy::Param bounds embedded in the type
            let predicates = ty.collect_param_predicates();

            self.term_env.insert(
                symbol,
                EnvEntry::Scheme(Scheme {
                    foralls,
                    predicates,
                    ty,
                }),
            );
        }

        constraints.wake_symbols(&[symbol]);
    }

    pub fn finalize(mut self) -> Result<(Types, ResolvedNames), TypeError> {
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
                    EnvEntry::Scheme(scheme) => TypeEntry::Poly(Scheme {
                        foralls: scheme.foralls,
                        predicates: scheme.predicates.into_iter().map(|p| p.into()).collect(),
                        ty: self.finalize_infer_ty(scheme.ty).into(),
                    }),
                };
                (sym, entry)
            })
            .collect();

        let catalog = std::mem::take(&mut self.type_catalog);
        let catalog = catalog.finalize(&mut self);

        // Resolve overloads using the variational type checking results
        let choices = std::mem::take(&mut self.choices);
        let error_constraints = std::mem::take(&mut self.error_constraints);
        let resolution = resolve_overloads(&choices, &error_constraints).unwrap_or_else(|errors| {
            // Log resolution errors - these indicate no valid overload was found
            for error in &errors {
                tracing::warn!("Resolution error: {:?}", error);
            }
            // Return empty resolution on error - SpecializationPass will use fallback logic
            Default::default()
        });

        let call_tree = std::mem::take(&mut self.call_tree);

        let types = Types {
            catalog,
            types_by_node: entries,
            types_by_symbol,
            match_plans: Default::default(),
            choices,
            resolution,
            call_tree,
        };

        let resolved_names = std::mem::take(&mut self.resolved_names);
        Ok((types, resolved_names))
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
                // Use lookup_reverse_instantiation to find the type param through union-find.
                // This handles the case where the meta was unified with another that has the mapping.
                // The returned InferTy::Param already includes the bounds.
                self.lookup_reverse_instantiation(meta).unwrap_or_else(|| {
                    let param = self.new_type_param(Some(meta));
                    tracing::warn!("did not solve {meta:?}, generating a type param even tho that's probably not what we want.");
                    param
                })
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

        for key in self.term_env.symbols.keys().copied().collect_vec() {
            let entry = self
                .term_env
                .symbols
                .remove(&key)
                .unwrap_or_else(|| unreachable!());
            let entry = entry.apply(substitutions, self);
            self.term_env.insert(key, entry);
        }

        let instantiations = std::mem::take(&mut self.type_catalog.instantiations);
        self.type_catalog.instantiations = instantiations.apply(self, substitutions);

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
            skolems.insert(InferTy::Param(id, vec![]), new_id);
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

    /// Look up the type param for a meta, checking through the union-find equivalence class.
    /// This is needed because reverse_instantiations is keyed by the original meta id,
    /// but after unification we might be looking up with a different meta id.
    /// Returns the full InferTy::Param with bounds.
    pub fn lookup_reverse_instantiation(&mut self, id: MetaVarId) -> Option<InferTy> {
        // First try direct lookup
        if let Some(param) = self.reverse_instantiations.ty.get(&id).cloned() {
            return Some(param);
        }

        // Find canonical representative
        let canon = self.canon_meta(id);

        // Check if canonical representative has a mapping
        if canon != id {
            if let Some(param) = self.reverse_instantiations.ty.get(&canon).cloned() {
                return Some(param);
            }
        }

        // Search all entries for one with the same canonical representative
        // This handles the case where another meta in the equivalence class has the mapping
        for (&meta_id, param) in &self.reverse_instantiations.ty.clone() {
            if self.canon_meta(meta_id) == canon {
                return Some(param.clone());
            }
        }

        None
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub fn link_meta(&mut self, a: MetaVarId, b: MetaVarId) {
        // Before unifying, check if either has a reverse_instantiation entry
        // and propagate it to both so lookup works after unification.
        // Prefer entries with non-empty bounds over empty bounds.
        let entry_a = self.reverse_instantiations.ty.get(&a).cloned();
        let entry_b = self.reverse_instantiations.ty.get(&b).cloned();

        self.meta_vars
            .unify_var_var(a, b)
            .unwrap_or_else(|_| unreachable!());

        // Choose the entry with bounds if available
        let chosen = match (&entry_a, &entry_b) {
            (Some(InferTy::Param(_, bounds_a)), Some(InferTy::Param(_, bounds_b))) => {
                // Prefer the one with non-empty bounds
                if !bounds_a.is_empty() {
                    entry_a
                } else if !bounds_b.is_empty() {
                    entry_b
                } else {
                    entry_a // Both empty, doesn't matter
                }
            }
            (Some(_), None) => entry_a,
            (None, Some(_)) => entry_b,
            (None, None) => None,
            // For non-Param entries (shouldn't happen but be safe)
            _ => entry_a.or(entry_b),
        };

        // Propagate reverse_instantiation entry to both meta vars
        // so that lookup from either will find it
        if let Some(param) = chosen {
            self.reverse_instantiations.ty.insert(a, param.clone());
            self.reverse_instantiations.ty.insert(b, param);
        }
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
                InferTy::Param(p, bounds) => {
                    // Use bounds embedded in the Param to create Conforms predicates
                    for protocol_id in bounds {
                        predicates.insert(Predicate::Conforms {
                            param: *p,
                            protocol_id: *protocol_id,
                        });
                    }
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

                    // Use lookup_reverse_instantiation to find the param through union-find.
                    // This handles the case where this meta var was unified with another
                    // that has the mapping (e.g., return type of a call unified with scheme's param).
                    let param = self
                        .lookup_reverse_instantiation(*id)
                        .unwrap_or_else(|| {
                            let param_id: TypeParamId = self.vars.type_params.next_id();
                            let param = InferTy::Param(param_id, vec![]);
                            self.reverse_instantiations.ty.insert(*id, param.clone());
                            tracing::trace!("generalizing {m:?} to {param_id:?}");
                            foralls.insert(ForAll::Ty(param_id));
                            param
                        });
                    if let InferTy::Param(param_id, bounds) = &param {
                        foralls.insert(ForAll::Ty(*param_id));
                        // Add predicates for bounds embedded in the param
                        for protocol_id in bounds {
                            predicates.insert(Predicate::Conforms {
                                param: *param_id,
                                protocol_id: *protocol_id,
                            });
                        }
                    }
                    substitutions.ty.insert(*id, param);
                }
                InferTy::Record(box InferRow::Var(id)) => {
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
        let id: TypeParamId = self.vars.type_params.next_id();
        let param = InferTy::Param(id, vec![]);
        if let Some(meta) = meta {
            self.reverse_instantiations.ty.insert(meta, param.clone());
        }

        tracing::trace!("Fresh type param {id:?}");
        param
    }

    pub(crate) fn new_type_param_id(&mut self, meta: Option<MetaVarId>) -> TypeParamId {
        let id: TypeParamId = self.vars.type_params.next_id();
        if let Some(meta) = meta {
            self.reverse_instantiations
                .ty
                .insert(meta, InferTy::Param(id, vec![]));
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
            .insert(InferTy::Rigid(id), InferTy::Param(param, vec![]));
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
