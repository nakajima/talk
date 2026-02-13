use std::{cell::RefCell, rc::Rc};

use ena::unify::{InPlaceUnificationTable, UnifyKey};
use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use tracing::instrument;

use crate::{
    compiling::module::{ModuleEnvironment, ModuleId},
    label::Label,
    name_resolution::{
        name_resolver::ResolvedNames,
        symbol::{ProtocolId, Symbol, Symbols, TypeParameterId},
    },
    node_id::NodeID,
    span::Span,
    types::{
        builtins::builtin_scope,
        call_tree::CallTree,
        conformance::{Conformance, ConformanceKey, Witnesses},
        constraints::{constraint::Constraint, store::ConstraintStore},
        infer_row::{Row, RowMetaId, RowParamId},
        infer_ty::{Level, Meta, MetaVarId, SkolemId, Ty},
        predicate::Predicate,
        scheme::{ForAll, Scheme},
        solve_context::SolveContext,
        term_environment::{EnvEntry, TermEnv},
        type_catalog::{Nominal, TypeCatalog},
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, substitute},
        types::{TypeEntry, Types},
        variational::{ChoiceStore, ErrorConstraintStore},
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
    pub types_by_node: FxHashMap<NodeID, Ty>,
    vars: Vars,
    term_env: TermEnv,
    pub(super) meta_levels: Rc<RefCell<FxHashMap<Meta, Level>>>,
    pub(super) skolem_map: FxHashMap<Ty, Ty>,

    pub typealiases: FxHashMap<Symbol, Scheme>,
    pub(super) type_catalog: TypeCatalog,
    pub(super) modules: Rc<ModuleEnvironment>,
    pub aliases: FxHashMap<Symbol, Scheme>,
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

    /// Set of protocol IDs that can be auto-derived for structs/enums.
    auto_derivable_protocols: Vec<ProtocolId>,

    /// Records of completed auto-derivations: (nominal, protocol) → [(label, method_sym, self_param_sym)]
    pub(crate) auto_derived: IndexMap<(Symbol, ProtocolId), Vec<(Label, Symbol, Symbol)>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum MemberSource {
    SelfMember,
    Protocol(ProtocolId),
}

#[derive(Debug, Default)]
pub struct ReverseInstantiations {
    /// Maps meta vars back to the type param they were instantiated from.
    /// Stores the full Ty::Param with bounds so we don't need a separate lookup.
    pub ty: FxHashMap<MetaVarId, Ty>,
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

        let mut catalog = TypeCatalog::default();

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
                .or_insert_with(|| conformance.clone());
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

            auto_derivable_protocols: Default::default(),
            auto_derived: Default::default(),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, constraints))]
    pub fn insert(&mut self, symbol: Symbol, ty: Ty, constraints: &mut ConstraintStore) {
        let foralls: IndexSet<_> = ty.collect_foralls().into_iter().collect();
        if foralls.is_empty() {
            self.term_env.insert(symbol, EnvEntry::Mono(ty));
        } else {
            // Collect predicates from Ty::Param bounds embedded in the type
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
        let entries: FxHashMap<NodeID, TypeEntry> = types_by_node
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
                        predicates: scheme.predicates,
                        ty: self.shallow_generalize(scheme.ty),
                    }),
                };
                (sym, entry)
            })
            .collect();

        let catalog = std::mem::take(&mut self.type_catalog);
        let choices = std::mem::take(&mut self.choices);
        let error_constraints = std::mem::take(&mut self.error_constraints);
        let call_tree = std::mem::take(&mut self.call_tree);

        let types = Types {
            catalog,
            types_by_node: entries,
            types_by_symbol,
            match_plans: Default::default(),
            choices,
            error_constraints,
            call_tree,
        };

        let resolved_names = std::mem::take(&mut self.resolved_names);
        Ok((types, resolved_names))
    }

    pub fn shallow_generalize_row(&mut self, row: Row) -> Row {
        match row {
            Row::Empty => row,
            Row::Extend { box row, label, ty } => Row::Extend {
                row: self.shallow_generalize_row(row).into(),
                label,
                ty: self.shallow_generalize(ty),
            },
            Row::Param(..) => row,
            Row::Var(meta) => {
                let id = self
                    .reverse_instantiations
                    .row
                    .get(&meta)
                    .cloned()
                    .unwrap_or_else(|| {
                        let Row::Param(id) = self.new_row_type_param(Some(meta)) else {
                            unreachable!()
                        };

                        self.reverse_instantiations.row.insert(meta, id);

                        id
                    });

                Row::Param(id)
            }
        }
    }

    pub fn shallow_generalize(&mut self, ty: Ty) -> Ty {
        match ty {
            Ty::Var { id: meta, .. } => {
                // Check if this var exists in our unification table
                if self.try_canon_meta(meta).is_none() {
                    // This var is from an imported module - leave it as-is
                    return ty;
                }

                // Use lookup_reverse_instantiation to find the type param through union-find.
                // This handles the case where the meta was unified with another that has the mapping.
                // The returned Ty::Param already includes the bounds.
                self.lookup_reverse_instantiation(meta).unwrap_or_else(|| {
                    let param = self.new_type_param(Some(meta));
                    tracing::warn!("did not solve {meta:?}, generating a type param even tho that's probably not what we want.");
                    param
                })
            }
            Ty::Constructor {
                name,
                params,
                box ret,
            } => Ty::Constructor {
                name,
                params: params
                    .into_iter()
                    .map(|p| self.shallow_generalize(p))
                    .collect(),
                ret: self.shallow_generalize(ret).into(),
            },
            Ty::Func(box param, box ret, box effects) => Ty::Func(
                self.shallow_generalize(param).into(),
                self.shallow_generalize(ret).into(),
                self.shallow_generalize_row(effects).into(),
            ),
            Ty::Tuple(items) => Ty::Tuple(
                items
                    .into_iter()
                    .map(|p| self.shallow_generalize(p))
                    .collect(),
            ),
            Ty::Record(sym, box row) => Ty::Record(sym, self.shallow_generalize_row(row).into()),
            Ty::Nominal { symbol, type_args } => Ty::Nominal {
                symbol,
                type_args: type_args
                    .into_iter()
                    .map(|a| self.shallow_generalize(a))
                    .collect(),
            },
            ty => ty,
        }
    }

    pub(super) fn finalize_infer_ty(&mut self, ty: Ty) -> Ty {
        let ty = substitute(&ty, &self.skolem_map);
        self.shallow_generalize(ty)
    }

    pub(super) fn finalize_ty(&mut self, ty: Ty) -> TypeEntry {
        let ty = self.finalize_infer_ty(ty);
        TypeEntry::Mono(ty)
    }

    pub(super) fn apply_row(
        &mut self,
        row: &Row,
        substitutions: &mut UnificationSubstitutions,
    ) -> Row {
        match row {
            Row::Empty => Row::Empty,
            Row::Var(id) => {
                // First check if we have a direct substitution for this id
                if let Some(bound) = substitutions.row.get(id).cloned() {
                    return self.apply_row(&bound, substitutions);
                }

                // Try to canonicalize the id - if it doesn't exist in our table,
                // this Var is from an imported module and we should leave it as-is
                let Some(rep) = self.try_canon_row(*id) else {
                    return row.clone();
                };

                if let Some(bound) = substitutions.row.get(&rep).cloned() {
                    self.apply_row(&bound, substitutions)
                } else {
                    Row::Var(rep)
                }
            }
            Row::Param(_) => row.clone(),
            Row::Extend {
                row: inner,
                label,
                ty,
            } => Row::Extend {
                row: Box::new(self.apply_row(inner, substitutions)),
                label: label.clone(),
                ty: self.apply(ty, substitutions),
            },
        }
    }

    pub(super) fn apply(&mut self, ty: &Ty, substitutions: &mut UnificationSubstitutions) -> Ty {
        match ty {
            Ty::Error(..) => ty.clone(),
            Ty::Param(..) => ty.clone(),
            Ty::Rigid(..) => ty.clone(),
            Ty::Projection {
                base,
                associated,
                protocol_id,
            } => Ty::Projection {
                base: self.apply(base, substitutions).into(),
                associated: associated.clone(),
                protocol_id: *protocol_id,
            },
            Ty::Var { id, level } => {
                // First check if we have a direct substitution for this id
                if let Some(bound) = substitutions.ty.get(id).cloned()
                    && !matches!(bound, Ty::Var { id: bound_id, .. } if bound_id == *id)
                {
                    return self.apply(&bound, substitutions); // keep collapsing
                }

                // Try to canonicalize the id - if it doesn't exist in our table,
                // this Var is from an imported module and we should leave it as-is
                let Some(rep) = self.try_canon_meta(*id) else {
                    // This Var was created by a different TypeSession (imported from a module)
                    // Return it unchanged
                    return ty.clone();
                };

                if let Some(bound) = substitutions.ty.get(&rep).cloned()
                    && !matches!(bound, Ty::Var { id, .. } if rep == id)
                {
                    self.apply(&bound, substitutions) // keep collapsing
                } else {
                    Ty::Var {
                        id: rep,
                        level: substitutions
                            .meta_levels
                            .borrow()
                            .get(&Meta::Ty(rep))
                            .copied()
                            .unwrap_or(*level),
                    }
                }
            }
            Ty::Constructor { name, params, ret } => Ty::Constructor {
                name: name.clone(),
                params: self.apply_mult(params.as_slice(), substitutions),
                ret: Box::new(self.apply(ret.as_ref(), substitutions)),
            },
            Ty::Primitive(..) => ty.clone(),
            Ty::Func(params, ret, effects) => Ty::Func(
                Box::new(self.apply(params.as_ref(), substitutions)),
                Box::new(self.apply(ret.as_ref(), substitutions)),
                Box::new(self.apply_row(effects.as_ref(), substitutions)),
            ),
            Ty::Tuple(items) => Ty::Tuple(self.apply_mult(items.as_slice(), substitutions)),
            Ty::Record(sym, row) => {
                Ty::Record(*sym, Box::new(self.apply_row(row.as_ref(), substitutions)))
            }
            Ty::Nominal { symbol, type_args } => Ty::Nominal {
                symbol: *symbol,
                type_args: self.apply_mult(type_args.as_slice(), substitutions),
            },
        }
    }

    pub fn apply_mult(
        &mut self,
        tys: &[Ty],
        substitutions: &mut UnificationSubstitutions,
    ) -> Vec<Ty> {
        tys.iter().map(|ty| self.apply(ty, substitutions)).collect()
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, substitutions))]
    pub fn apply_all(&mut self, substitutions: &mut UnificationSubstitutions) {
        for key in self.types_by_node.keys().copied().collect_vec() {
            let ty = self
                .types_by_node
                .remove(&key)
                .unwrap_or_else(|| unreachable!());
            let ty = self.apply(&ty, substitutions);
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
                *ty = self.apply(ty, substitutions);
            }
        }
        _ = std::mem::replace(&mut self.type_catalog.conformances, conformances);
    }

    pub fn get_term_env(&self) -> &TermEnv {
        &self.term_env
    }

    pub fn skolemize(&mut self, entry: &EnvEntry) -> Ty {
        let mut skolems = FxHashMap::default();
        for forall in entry.foralls() {
            let ForAll::Ty(id) = forall else {
                continue;
            };

            let new_id = self.new_skolem(id);
            skolems.insert(Ty::Param(id, vec![]), new_id);
        }

        substitute(&entry._as_ty(), &skolems)
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

    /// Try to canonicalize a meta var id, returning None if the id doesn't exist in the table.
    /// This is useful when processing types that may have been imported from other modules.
    fn try_canon_meta(&mut self, id: MetaVarId) -> Option<MetaVarId> {
        if id.index() < self.meta_vars.len() as u32 {
            Some(self.meta_vars.find(id))
        } else {
            None
        }
    }

    /// Try to canonicalize a row meta var id, returning None if the id doesn't exist in the table.
    fn try_canon_row(&mut self, id: RowMetaId) -> Option<RowMetaId> {
        if id.0 < self.row_vars.len() as u32 {
            Some(self.row_vars.find(id))
        } else {
            None
        }
    }

    pub fn lookup_reverse_instantiation(&mut self, id: MetaVarId) -> Option<Ty> {
        // First try direct lookup
        if let Some(param) = self.reverse_instantiations.ty.get(&id).cloned() {
            return Some(param);
        }

        // Try to find canonical representative - if the id doesn't exist in our table,
        // return None (this var is from an imported module)
        let canon = self.try_canon_meta(id)?;

        // Check if canonical representative has a mapping
        if canon != id
            && let Some(param) = self.reverse_instantiations.ty.get(&canon).cloned()
        {
            return Some(param);
        }

        // Search all entries for one with the same canonical representative
        // This handles the case where another meta in the equivalence class has the mapping
        for (&meta_id, param) in &self.reverse_instantiations.ty.clone() {
            if let Some(meta_canon) = self.try_canon_meta(meta_id)
                && meta_canon == canon
            {
                return Some(param.clone());
            }
        }

        None
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub fn link_meta(&mut self, a: MetaVarId, b: MetaVarId) {
        let entry_a = self.reverse_instantiations.ty.get(&a).cloned();
        let entry_b = self.reverse_instantiations.ty.get(&b).cloned();

        self.meta_vars
            .unify_var_var(a, b)
            .unwrap_or_else(|_| unreachable!());

        // Choose the entry with bounds if available
        let chosen = match (&entry_a, &entry_b) {
            (Some(Ty::Param(_, bounds_a)), Some(Ty::Param(_, bounds_b))) => {
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
        ty: Ty,
        context: &mut SolveContext,
        unsolved: &IndexSet<Constraint>,
        constraints: &mut ConstraintStore,
    ) -> EnvEntry {
        // Make sure we're up to date
        let ty = self.apply(&ty, &mut context.substitutions_mut());

        // collect metas in ty
        let mut metas = FxHashSet::default();
        metas.extend(ty.collect_metas());

        // Also collect metas that appear only in constraints
        for constraint in unsolved {
            let constraint = constraint
                .clone()
                .apply(&mut context.substitutions_mut(), self);
            metas.extend(constraint.collect_metas());
        }

        let mut foralls: IndexSet<_> = ty.collect_foralls().into_iter().collect();
        let mut predicates: IndexSet<Predicate> = Default::default();
        let mut substitutions = UnificationSubstitutions::new(self.meta_levels.clone());
        for m in &metas {
            match m {
                Ty::Var { level, id } => {
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
                    let param = self.lookup_reverse_instantiation(*id).unwrap_or_else(|| {
                        let local_id: u32 = self.vars.type_params.next_id();
                        let sym = Symbol::TypeParameter(TypeParameterId::new(
                            self.current_module_id,
                            local_id,
                        ));
                        let param = Ty::Param(sym, vec![]);
                        self.reverse_instantiations.ty.insert(*id, param.clone());
                        tracing::trace!("generalizing {m:?} to {sym:?}");
                        foralls.insert(ForAll::Ty(sym));
                        param
                    });
                    if let Ty::Param(param_id, bounds) = &param {
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
                Ty::Record(_, box Row::Var(id)) => {
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
                    substitutions.row.insert(*id, Row::Param(param_id));
                }
                _ => {
                    tracing::warn!("got {m:?} for var while generalizing")
                }
            }
        }

        // De-skolemize
        let ty = substitute(&ty, &self.skolem_map);
        let ty = self.apply(&ty, &mut substitutions);

        predicates.extend(unsolved.iter().filter_map(|c| {
            let metas = c.collect_metas();

            if metas.is_empty() {
                return None;
            }

            // Check that all metas are at or above the current generalization level
            // Predicates should only reference quantified variables (foralls), not
            // ungeneralized metas from outer scopes
            for meta in &metas {
                if let Ty::Var { level, .. } = meta && *level < context.level() {
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

        EnvEntry::Scheme(Scheme::new(foralls, predicates.into_iter().collect(), ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(super) fn lookup(&mut self, sym: &Symbol) -> Option<EnvEntry> {
        if let Some(entry) = builtin_scope().get(sym).cloned() {
            return Some(entry);
        }

        if let Some(entry) = self.term_env.lookup(sym).cloned() {
            return Some(entry);
        }

        if let Some(entry) = self.modules.lookup(sym) {
            let entry: EnvEntry = match entry.clone() {
                TypeEntry::Mono(t) => EnvEntry::Mono(t),
                TypeEntry::Poly(..) => entry.into(),
            };

            self.term_env.insert(*sym, entry.clone());
            return Some(entry);
        }

        None
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, constraints))]
    pub(super) fn promote(
        &mut self,
        sym: Symbol,
        entry: EnvEntry,
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
        entry: EnvEntry,
        constraints: &mut ConstraintStore,
    ) {
        if matches!(sym, Symbol::Builtin(..)) {
            tracing::error!("can't override builtin");
            return;
        }

        constraints.wake_symbols(&[sym]);

        self.term_env.insert(sym, entry);
    }

    pub(super) fn insert_mono(&mut self, sym: Symbol, ty: Ty, constraints: &mut ConstraintStore) {
        if matches!(sym, Symbol::Builtin(..)) {
            tracing::error!("can't override builtin");
            return;
        }

        constraints.wake_symbols(&[sym]);

        self.term_env.insert(sym, EnvEntry::Mono(ty));
    }

    pub fn lookup_conformance(&mut self, key: &ConformanceKey) -> Option<Conformance> {
        if let Some(conformance) = self.type_catalog.conformances.get(key) {
            return Some(conformance.clone());
        }

        if let Some(conformance) = self.modules.lookup_conformance(key) {
            self.type_catalog
                .conformances
                .insert(*key, conformance.clone());
            return Some(conformance.clone());
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

    pub fn lookup_effect(&self, id: &Symbol) -> Option<Ty> {
        if let Some(effect) = self.type_catalog.lookup_effect(id) {
            return Some(effect.clone());
        }

        self.modules.lookup_effect(id)
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

    pub fn lookup_nominal(&mut self, symbol: &Symbol) -> Option<Nominal> {
        if let Some(nominal) = self.type_catalog.nominals.get(symbol).cloned() {
            return Some(nominal);
        }

        if let Some(nominal) = self.modules.lookup_nominal(symbol).cloned() {
            self.type_catalog.nominals.insert(*symbol, nominal.clone());
            return Some(nominal);
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

    pub(crate) fn new_type_param(&mut self, meta: Option<MetaVarId>) -> Ty {
        let local_id: u32 = self.vars.type_params.next_id();
        let sym = Symbol::TypeParameter(TypeParameterId::new(self.current_module_id, local_id));
        let param = Ty::Param(sym, vec![]);
        if let Some(meta) = meta {
            self.reverse_instantiations.ty.insert(meta, param.clone());
        }

        tracing::trace!("Fresh type param {sym:?}");
        param
    }

    pub(crate) fn new_type_param_id(&mut self, meta: Option<MetaVarId>) -> Symbol {
        let local_id: u32 = self.vars.type_params.next_id();
        let sym = Symbol::TypeParameter(TypeParameterId::new(self.current_module_id, local_id));
        if let Some(meta) = meta {
            self.reverse_instantiations
                .ty
                .insert(meta, Ty::Param(sym, vec![]));
        }

        tracing::trace!("Fresh type param {sym:?}");
        sym
    }

    pub(crate) fn new_row_type_param(&mut self, meta: Option<RowMetaId>) -> Row {
        let id = self.vars.row_params.next_id();

        if let Some(meta) = meta {
            self.reverse_instantiations.row.insert(meta, id);
        }

        tracing::trace!("Fresh type param {id:?}");
        Row::Param(id)
    }

    pub(crate) fn new_skolem(&mut self, param: Symbol) -> Ty {
        let id = self.new_skolem_id(param);
        Ty::Rigid(id)
    }

    pub(crate) fn new_skolem_id(&mut self, param: Symbol) -> SkolemId {
        let id = self.vars.skolems.next_id();
        self.skolem_map
            .insert(Ty::Rigid(id), Ty::Param(param, vec![]));
        tracing::trace!("Fresh skolem {id:?}");
        id
    }

    pub(crate) fn new_ty_meta_var(&mut self, level: Level) -> Ty {
        let id = self.meta_vars.new_key(level);
        self.meta_levels.borrow_mut().insert(Meta::Ty(id), level);
        Ty::Var { id, level }
    }

    pub(crate) fn new_ty_meta_var_id(&mut self, level: Level) -> MetaVarId {
        let id = self.meta_vars.new_key(level);
        self.meta_levels.borrow_mut().insert(Meta::Ty(id), level);
        id
    }

    pub(crate) fn new_row_meta_var(&mut self, level: Level) -> Row {
        let id = self.row_vars.new_key(level);
        self.meta_levels.borrow_mut().insert(Meta::Row(id), level);
        Row::Var(id)
    }

    /// Find a protocol's ProtocolId by name.
    pub(crate) fn find_protocol_id(&self, protocol_name: &str) -> Option<ProtocolId> {
        for (sym, name) in &self.resolved_names.symbol_names {
            if name == protocol_name {
                if let Symbol::Protocol(id) = sym {
                    return Some(*id);
                }
            }
        }
        // Also check imported modules
        for (sym, name) in self.modules.imported_symbol_names() {
            if name == protocol_name {
                if let Symbol::Protocol(id) = sym {
                    return Some(id);
                }
            }
        }
        None
    }

    /// Lazily initialize the set of auto-derivable protocols.
    fn init_auto_derivable_protocols(&mut self) {
        if !self.auto_derivable_protocols.is_empty() {
            return;
        }
        if let Some(id) = self.find_protocol_id("Showable") {
            self.auto_derivable_protocols.push(id);
        }
    }

    /// Check whether a protocol can be auto-derived.
    pub(crate) fn is_auto_derivable(&mut self, protocol_id: ProtocolId) -> bool {
        self.init_auto_derivable_protocols();
        self.auto_derivable_protocols.contains(&protocol_id)
    }

    /// Given a method label, return which auto-derivable protocol it belongs to (if any).
    pub(crate) fn auto_derivable_method_protocol(&mut self, label: &Label) -> Option<ProtocolId> {
        self.init_auto_derivable_protocols();
        // Index-based iteration to avoid cloning the Vec (lookup_method_requirements takes &mut self).
        for i in 0..self.auto_derivable_protocols.len() {
            let protocol_id = self.auto_derivable_protocols[i];
            if let Some(reqs) = self.lookup_method_requirements(protocol_id.into()) {
                if reqs.contains_key(label) {
                    return Some(protocol_id);
                }
            }
        }
        None
    }

    /// Look up a protocol method witness for a conforming type.
    pub(crate) fn find_witness(
        &mut self,
        conforming_sym: Symbol,
        protocol_id: ProtocolId,
        method_label: &Label,
    ) -> Option<Symbol> {
        let key = ConformanceKey {
            protocol_id,
            conforming_id: conforming_sym,
        };
        let conformance = self.lookup_conformance(&key)?;
        conformance.witnesses.methods.get(method_label).copied()
    }

    /// Register a symbol with a monomorphic type in the term environment.
    pub(crate) fn register_mono(&mut self, sym: Symbol, ty: Ty) {
        self.term_env.insert(sym, EnvEntry::Mono(ty));
    }

    /// Auto-derive a protocol for a nominal type on demand.
    /// Returns the first method symbol if successful, None if the type can't be auto-derived.
    pub(crate) fn auto_derive_protocol(
        &mut self,
        nominal_sym: Symbol,
        protocol_id: ProtocolId,
        constraints: &mut ConstraintStore,
    ) -> Option<Symbol> {
        let derive_key = (nominal_sym, protocol_id);

        // Already derived?
        if let Some(methods) = self.auto_derived.get(&derive_key) {
            return methods.first().map(|(_, method_sym, _)| *method_sym);
        }

        // Must be a struct or enum
        if !matches!(nominal_sym, Symbol::Struct(..) | Symbol::Enum(..)) {
            return None;
        }

        // Must not already have an explicit conformance
        let key = ConformanceKey {
            protocol_id,
            conforming_id: nominal_sym,
        };
        if self.lookup_conformance(&key).is_some() {
            return None;
        }

        // Look up protocol Self param
        let protocol_symbol: Symbol = protocol_id.into();
        let Some(EnvEntry::Scheme(Scheme {
            ty: Ty::Param(self_id, _),
            ..
        })) = self.lookup(&protocol_symbol)
        else {
            return None;
        };

        let nominal = self.lookup_nominal(&nominal_sym)?;
        let nominal_ty = Ty::Nominal {
            symbol: nominal_sym,
            type_args: nominal.type_params.clone(),
        };

        // Build substitution: Self → nominal_ty
        let mut subs = FxHashMap::default();
        subs.insert(Ty::Param(self_id, vec![]), nominal_ty.clone());

        // Look up method requirements
        let Some(requirements) = self.lookup_method_requirements(protocol_symbol) else {
            return None;
        };

        let mut witnesses = Witnesses::default();
        let mut derived_methods = Vec::new();
        let mut first_method_sym = None;

        let type_name = self
            .resolved_names
            .symbol_names
            .get(&nominal_sym)
            .cloned()
            .or_else(|| {
                self.modules
                    .imported_symbol_names()
                    .get(&nominal_sym)
                    .cloned()
            })
            .unwrap_or_default();

        for (label, req_sym) in &requirements {
            let Some(entry) = self.lookup(req_sym) else {
                continue;
            };

            // Get the requirement type and substitute Self → nominal_ty
            let req_ty = substitute(&entry._as_ty(), &subs);

            // Allocate symbols for this method
            let method_sym =
                Symbol::InstanceMethod(self.symbols.next_instance_method(self.current_module_id));
            let self_param_sym = Symbol::ParamLocal(self.symbols.next_param());

            if first_method_sym.is_none() {
                first_method_sym = Some(method_sym);
            }

            // Register in term_env
            self.insert(method_sym, req_ty, constraints);
            self.term_env
                .insert(self_param_sym, EnvEntry::Mono(nominal_ty.clone()));

            // Register as instance method
            self.type_catalog
                .instance_methods
                .entry(nominal_sym)
                .or_default()
                .insert(label.clone(), method_sym);

            witnesses.methods.insert(label.clone(), method_sym);
            witnesses.requirements.insert(*req_sym, method_sym);

            derived_methods.push((label.clone(), method_sym, self_param_sym));

            // Register symbol names for debugging
            self.resolved_names
                .symbol_names
                .insert(method_sym, format!("{type_name}.{label}"));
            self.resolved_names
                .symbol_names
                .insert(self_param_sym, "self".into());
        }

        self.type_catalog.conformances.insert(
            key,
            Conformance {
                node_id: NodeID::SYNTHESIZED,
                conforming_id: nominal_sym,
                protocol_id,
                witnesses,
                span: Span::SYNTHESIZED,
            },
        );

        // Record for later body synthesis
        self.auto_derived.insert(derive_key, derived_methods);

        first_method_sym
    }
}
