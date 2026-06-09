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
    types::{
        builtins::builtin_scope,
        callee::{Callee, Callees},
        conformance::{
            ConformanceClaim, ConformanceEvidence, ConformanceKey, ConformanceObligation,
            ConformanceOrigin, WitnessTable,
        },
        conformance_context::{ConformanceContext, ProjectionResolution},
        constraints::{constraint::Constraint, store::ConstraintStore},
        infer_row::{Row, RowMetaId, RowParamId},
        infer_ty::{Level, Meta, MetaVarId, SkolemId, Ty},
        predicate::Predicate,
        scheme::{ForAll, Scheme},
        solve_context::SolveContext,
        term_environment::{EnvEntry, TermEnv},
        type_args::TypeArgs,
        type_catalog::{MemberBinding, MemberSource, Nominal, TypeCatalog},
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, substitute},
        types::{TypeEntry, Types},
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
    conformance: ConformanceContext,
    pub(super) modules: Rc<ModuleEnvironment>,
    pub aliases: FxHashMap<Symbol, Scheme>,
    meta_origins: Rc<RefCell<FxHashMap<Meta, MetaOrigin>>>,

    callees: Callees,
    callee_owners: FxHashMap<NodeID, Symbol>,

    pub(crate) symbols: Symbols,
    pub(crate) resolved_names: ResolvedNames,

    meta_vars: InPlaceUnificationTable<MetaVarId>,
    row_vars: InPlaceUnificationTable<RowMetaId>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum AssociatedTypeResolution {
    Alias(Symbol),
    Witness(Ty),
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ShowDerivation {
    pub nominal: Symbol,
    pub protocol_id: ProtocolId,
    pub method: Symbol,
    pub self_param: Symbol,
    pub witnesses: WitnessTable,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MetaOrigin {
    TypeParam {
        param: Symbol,
        bounds: Vec<ProtocolId>,
    },
    RowParam {
        param: RowParamId,
    },
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

        // Import conformance claims and validated evidence from all modules.
        for (key, claim) in modules.all_conformance_claims() {
            catalog.conformance_claims.entry(key).or_insert(claim);
        }
        for (key, conformance) in modules.all_conformance_evidence() {
            catalog
                .conformance_evidence
                .entry(key)
                .or_insert_with(|| conformance.clone());
        }

        TypeSession {
            current_module_id,
            vars: Default::default(),
            skolem_map: Default::default(),
            meta_levels: Default::default(),
            term_env,
            meta_origins: Default::default(),
            types_by_node: Default::default(),
            typealiases: Default::default(),
            type_catalog: catalog,
            conformance: Default::default(),
            modules,
            aliases: Default::default(),
            callees: Default::default(),
            callee_owners: Default::default(),

            meta_vars: Default::default(),
            row_vars: Default::default(),

            symbols,
            resolved_names,
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

        let mut catalog = std::mem::take(&mut self.type_catalog);
        catalog.rebuild_member_index(self.modules.as_ref());
        self.type_catalog = catalog;

        let callees = self.finalize_callees(&entries, &types_by_symbol);
        let callee_owners = std::mem::take(&mut self.callee_owners);
        let catalog = std::mem::take(&mut self.type_catalog);

        let types = Types {
            catalog,
            types_by_node: entries,
            types_by_symbol,
            match_plans: Default::default(),
            callees,
            callee_owners,
        };

        let resolved_names = std::mem::take(&mut self.resolved_names);
        Ok((types, resolved_names))
    }

    fn finalize_callees(
        &mut self,
        entries: &FxHashMap<NodeID, TypeEntry>,
        types_by_symbol: &FxHashMap<Symbol, TypeEntry>,
    ) -> Callees {
        let mut result = Callees::default();
        let callees = std::mem::take(&mut self.callees);
        for (id, callee) in callees {
            let callee = self.finalize_callee(id, entries, types_by_symbol, callee);
            result.insert(id, callee);
        }

        result
    }

    fn finalize_callee(
        &mut self,
        id: NodeID,
        entries: &FxHashMap<NodeID, TypeEntry>,
        types_by_symbol: &FxHashMap<Symbol, TypeEntry>,
        callee: Callee,
    ) -> Callee {
        match callee {
            Callee::Function { symbol, type_args } => Callee::Function {
                symbol,
                type_args: self.finalize_type_args_for_symbol(
                    symbol,
                    &[],
                    type_args,
                    types_by_symbol,
                ),
            },
            Callee::Initializer {
                nominal,
                initializer: _,
                type_args,
            } => {
                let initializer = self.initializer_for_nominal(&nominal);
                let mut type_args = type_args;
                type_args.extend(self.nominal_type_args_from_entry(id, nominal, entries));
                Callee::Initializer {
                    nominal,
                    initializer,
                    type_args: self.finalize_type_args_for_symbol(
                        initializer,
                        &self.nominal_type_foralls(&nominal),
                        type_args,
                        types_by_symbol,
                    ),
                }
            }
            Callee::Method {
                symbol,
                self_ty,
                type_args,
            } => {
                let self_ty = self.finalize_infer_ty(self_ty);
                let mut type_args =
                    self.finalize_type_args_for_symbol(symbol, &[], type_args, types_by_symbol);
                self.add_receiver_type_args(symbol, &self_ty, &mut type_args, types_by_symbol);
                Callee::Method {
                    symbol,
                    self_ty,
                    type_args,
                }
            }
            Callee::Variant {
                enum_symbol,
                variant,
                type_args,
            } => {
                let mut type_args = type_args;
                type_args.extend(self.nominal_type_args_from_entry(id, enum_symbol, entries));
                Callee::Variant {
                    enum_symbol,
                    variant,
                    type_args: self.finalize_type_args_for_foralls(
                        id,
                        type_args,
                        &self.nominal_type_foralls(&enum_symbol),
                    ),
                }
            }
            Callee::Effect { symbol, type_args } => Callee::Effect {
                symbol,
                type_args: self.finalize_type_args_for_foralls(
                    id,
                    type_args,
                    &self.effect_foralls(symbol),
                ),
            },
        }
    }

    fn initializer_for_nominal(&self, nominal: &Symbol) -> Symbol {
        let init_label = Label::Named("init".into());
        self.type_catalog
            .initializers
            .get(nominal)
            .and_then(|initializers| initializers.get(&init_label).copied())
            .or_else(|| {
                self.modules
                    .lookup_initializers(nominal)
                    .and_then(|initializers| initializers.get(&init_label).copied())
            })
            .or_else(|| {
                self.type_catalog
                    .initializers
                    .get(nominal)
                    .and_then(|initializers| initializers.values().next().copied())
            })
            .or_else(|| {
                self.modules
                    .lookup_initializers(nominal)
                    .and_then(|initializers| initializers.values().next().copied())
            })
            .unwrap_or(*nominal)
    }

    fn nominal_type_args_from_entry(
        &self,
        id: NodeID,
        nominal: Symbol,
        entries: &FxHashMap<NodeID, TypeEntry>,
    ) -> TypeArgs {
        let mut result = TypeArgs::default();
        let Some(TypeEntry::Mono(Ty::Nominal { symbol, type_args })) = entries.get(&id) else {
            return result;
        };
        if *symbol != nominal {
            return result;
        }

        let Some(nominal_def) = self
            .type_catalog
            .nominals
            .get(&nominal)
            .or_else(|| self.modules.lookup_nominal(&nominal))
        else {
            return result;
        };

        for (param, arg) in nominal_def.type_params.iter().zip(type_args.iter()) {
            if let Ty::Param(param_id, _) = param {
                result.ty.insert(*param_id, arg.clone());
            }
        }

        result
    }

    fn nominal_type_foralls(&self, nominal: &Symbol) -> Vec<ForAll> {
        self.type_catalog
            .nominals
            .get(nominal)
            .or_else(|| self.modules.lookup_nominal(nominal))
            .map(|nominal| {
                nominal
                    .type_params
                    .iter()
                    .filter_map(|param| match param {
                        Ty::Param(id, _) => Some(ForAll::Ty(*id)),
                        _ => None,
                    })
                    .collect()
            })
            .unwrap_or_default()
    }

    fn effect_foralls(&self, effect: Symbol) -> Vec<ForAll> {
        self.type_catalog
            .effects
            .get(&effect)
            .cloned()
            .or_else(|| self.modules.lookup_effect(&effect))
            .map(|ty| ty.collect_foralls().into_iter().collect_vec())
            .unwrap_or_default()
    }

    fn finalize_type_args_for_symbol(
        &mut self,
        target: Symbol,
        extra_foralls: &[ForAll],
        type_args: TypeArgs,
        types_by_symbol: &FxHashMap<Symbol, TypeEntry>,
    ) -> TypeArgs {
        let mut foralls = self.foralls_for_symbol(target, types_by_symbol);
        for forall in extra_foralls {
            if !foralls.contains(forall) {
                foralls.push(*forall);
            }
        }
        self.finalize_type_args_for_foralls(NodeID::SYNTHESIZED, type_args, &foralls)
    }

    fn finalize_type_args_for_foralls(
        &mut self,
        site_id: NodeID,
        type_args: TypeArgs,
        foralls: &[ForAll],
    ) -> TypeArgs {
        let mut result = TypeArgs::default();
        let ty_foralls: FxHashSet<Symbol> = foralls
            .iter()
            .filter_map(|forall| match forall {
                ForAll::Ty(param) => Some(*param),
                ForAll::Row(_) => None,
            })
            .collect();
        let row_foralls: FxHashSet<RowParamId> = foralls
            .iter()
            .filter_map(|forall| match forall {
                ForAll::Ty(_) => None,
                ForAll::Row(param) => Some(*param),
            })
            .collect();

        for (param, ty) in type_args.ty {
            if ty_foralls.contains(&param) {
                result.ty.insert(param, self.finalize_infer_ty(ty));
            }
        }
        for (param, row) in type_args.row {
            if row_foralls.contains(&param) {
                result.row.insert(param, self.shallow_generalize_row(row));
            }
        }

        self.validate_type_args(site_id, &result);
        result
    }

    fn foralls_for_symbol(
        &self,
        target: Symbol,
        types_by_symbol: &FxHashMap<Symbol, TypeEntry>,
    ) -> Vec<ForAll> {
        match types_by_symbol
            .get(&target)
            .cloned()
            .or_else(|| self.modules.lookup(&target))
        {
            Some(TypeEntry::Poly(scheme)) => scheme.foralls.into_iter().collect(),
            Some(TypeEntry::Mono(ty)) => ty.collect_foralls().into_iter().collect(),
            None => vec![],
        }
    }

    fn validate_type_args(&self, site_id: NodeID, type_args: &TypeArgs) {
        for (param, ty) in &type_args.ty {
            if matches!(ty, Ty::Var { .. }) {
                tracing::debug!(
                    ?site_id,
                    ?param,
                    ?ty,
                    "unresolved type var in callee type args"
                );
            }
        }
        for (param, row) in &type_args.row {
            if matches!(row, Row::Var(..)) {
                tracing::debug!(
                    ?site_id,
                    ?param,
                    ?row,
                    "unresolved row var in callee type args"
                );
            }
        }
    }

    fn add_receiver_type_args(
        &self,
        member_sym: Symbol,
        receiver_ty: &Ty,
        type_args: &mut TypeArgs,
        types_by_symbol: &FxHashMap<Symbol, TypeEntry>,
    ) {
        let Ty::Nominal {
            type_args: args, ..
        } = receiver_ty
        else {
            return;
        };
        if args.is_empty() {
            return;
        }

        let Some(TypeEntry::Poly(scheme)) = types_by_symbol
            .get(&member_sym)
            .cloned()
            .or_else(|| self.modules.lookup(&member_sym))
        else {
            return;
        };

        for (forall, arg) in scheme
            .foralls
            .iter()
            .filter_map(|forall| match forall {
                ForAll::Ty(param) => Some(*param),
                ForAll::Row(_) => None,
            })
            .zip(args.iter())
        {
            type_args.ty.entry(forall).or_insert_with(|| arg.clone());
        }
    }

    pub(crate) fn record_function_callee(
        &mut self,
        call_id: NodeID,
        symbol: Symbol,
        type_args: TypeArgs,
    ) {
        if call_id == NodeID::SYNTHESIZED {
            return;
        }
        self.callees
            .insert(call_id, Callee::Function { symbol, type_args });
    }

    pub(crate) fn record_initializer_callee(&mut self, call_id: NodeID, nominal: Symbol) {
        if call_id == NodeID::SYNTHESIZED {
            return;
        }
        let initializer = self.initializer_for_nominal(&nominal);
        self.callees.insert(
            call_id,
            Callee::Initializer {
                nominal,
                initializer,
                type_args: TypeArgs::default(),
            },
        );
    }

    pub(crate) fn record_effect_callee(
        &mut self,
        call_id: NodeID,
        symbol: Symbol,
        type_args: TypeArgs,
    ) {
        if call_id == NodeID::SYNTHESIZED {
            return;
        }
        self.callees
            .insert(call_id, Callee::Effect { symbol, type_args });
    }

    pub(crate) fn record_method_callee(
        &mut self,
        call_id: NodeID,
        symbol: Symbol,
        self_ty: Ty,
        type_args: TypeArgs,
    ) {
        if call_id == NodeID::SYNTHESIZED {
            return;
        }
        self.callees.insert(
            call_id,
            Callee::Method {
                symbol,
                self_ty,
                type_args,
            },
        );
    }

    pub(crate) fn record_variant_callee(
        &mut self,
        call_id: NodeID,
        enum_symbol: Symbol,
        variant: Symbol,
        type_args: TypeArgs,
    ) {
        if call_id == NodeID::SYNTHESIZED {
            return;
        }
        self.callees.insert(
            call_id,
            Callee::Variant {
                enum_symbol,
                variant,
                type_args,
            },
        );
    }

    pub(crate) fn record_callee_owner(&mut self, call_id: NodeID, owner: Symbol) {
        if call_id == NodeID::SYNTHESIZED {
            return;
        }
        self.callee_owners.insert(call_id, owner);
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
                let id = self.lookup_row_param_origin(meta).unwrap_or_else(|| {
                    let Row::Param(id) = self.new_row_type_param(Some(meta)) else {
                        unreachable!()
                    };
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

                self.lookup_type_param_origin(meta).unwrap_or_else(|| {
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

    fn apply_type_args(
        &mut self,
        type_args: TypeArgs,
        substitutions: &mut UnificationSubstitutions,
    ) -> TypeArgs {
        TypeArgs {
            ty: type_args
                .ty
                .into_iter()
                .map(|(param, ty)| (param, self.apply(&ty, substitutions)))
                .collect(),
            row: type_args
                .row
                .into_iter()
                .map(|(param, row)| (param, self.apply_row(&row, substitutions)))
                .collect(),
        }
    }

    fn apply_callees(&mut self, substitutions: &mut UnificationSubstitutions) {
        let callees = std::mem::take(&mut self.callees);
        for (id, callee) in callees {
            let callee = match callee {
                Callee::Function { symbol, type_args } => Callee::Function {
                    symbol,
                    type_args: self.apply_type_args(type_args, substitutions),
                },
                Callee::Initializer {
                    nominal,
                    initializer,
                    type_args,
                } => Callee::Initializer {
                    nominal,
                    initializer,
                    type_args: self.apply_type_args(type_args, substitutions),
                },
                Callee::Method {
                    symbol,
                    self_ty,
                    type_args,
                } => Callee::Method {
                    symbol,
                    self_ty: self.apply(&self_ty, substitutions),
                    type_args: self.apply_type_args(type_args, substitutions),
                },
                Callee::Variant {
                    enum_symbol,
                    variant,
                    type_args,
                } => Callee::Variant {
                    enum_symbol,
                    variant,
                    type_args: self.apply_type_args(type_args, substitutions),
                },
                Callee::Effect { symbol, type_args } => Callee::Effect {
                    symbol,
                    type_args: self.apply_type_args(type_args, substitutions),
                },
            };
            self.callees.insert(id, callee);
        }
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

        self.apply_callees(substitutions);

        let mut nominals = std::mem::take(&mut self.type_catalog.nominals);
        for nominal in nominals.values_mut() {
            for ty in nominal.properties.values_mut() {
                *ty = self.apply(ty, substitutions);
            }
            for values in nominal.variants.values_mut() {
                for ty in values.iter_mut() {
                    *ty = self.apply(ty, substitutions);
                }
            }
        }
        _ = std::mem::replace(&mut self.type_catalog.nominals, nominals);

        let mut conformances = std::mem::take(&mut self.type_catalog.conformance_evidence);
        for conformance in conformances.values_mut() {
            for ty in conformance.witnesses.associated_types.values_mut() {
                *ty = self.apply(ty, substitutions);
            }
        }
        _ = std::mem::replace(&mut self.type_catalog.conformance_evidence, conformances);
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
        let origin = self.choose_origin(
            self.meta_origins.borrow().get(&Meta::Row(a)).cloned(),
            self.meta_origins.borrow().get(&Meta::Row(b)).cloned(),
        );
        self.row_vars
            .unify_var_var(a, b)
            .unwrap_or_else(|_| unreachable!());
        if let Some(origin) = origin {
            let canon = self.row_vars.find(a);
            self.meta_origins
                .borrow_mut()
                .insert(Meta::Row(canon), origin);
        }
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

    fn choose_origin(
        &self,
        lhs: Option<MetaOrigin>,
        rhs: Option<MetaOrigin>,
    ) -> Option<MetaOrigin> {
        fn has_bounds(origin: &MetaOrigin) -> bool {
            matches!(origin, MetaOrigin::TypeParam { bounds, .. } if !bounds.is_empty())
        }

        match (lhs, rhs) {
            (Some(lhs), Some(rhs)) if has_bounds(&rhs) && !has_bounds(&lhs) => Some(rhs),
            (Some(lhs), Some(_)) => Some(lhs),
            (Some(origin), None) | (None, Some(origin)) => Some(origin),
            (None, None) => None,
        }
    }

    fn set_meta_origin(&mut self, meta: Meta, origin: MetaOrigin) {
        self.meta_origins.borrow_mut().insert(meta, origin);
    }

    pub fn lookup_type_param_origin(&mut self, id: MetaVarId) -> Option<Ty> {
        let canon = self.try_canon_meta(id)?;
        match self.meta_origins.borrow().get(&Meta::Ty(canon)).cloned()? {
            MetaOrigin::TypeParam { param, bounds } => Some(Ty::Param(param, bounds)),
            MetaOrigin::RowParam { .. } => None,
        }
    }

    fn lookup_row_param_origin(&mut self, id: RowMetaId) -> Option<RowParamId> {
        let canon = self.try_canon_row(id)?;
        match self.meta_origins.borrow().get(&Meta::Row(canon)).cloned()? {
            MetaOrigin::RowParam { param } => Some(param),
            MetaOrigin::TypeParam { .. } => None,
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub fn link_meta(&mut self, a: MetaVarId, b: MetaVarId) {
        let origin = self.choose_origin(
            self.meta_origins.borrow().get(&Meta::Ty(a)).cloned(),
            self.meta_origins.borrow().get(&Meta::Ty(b)).cloned(),
        );
        self.meta_vars
            .unify_var_var(a, b)
            .unwrap_or_else(|_| unreachable!());
        if let Some(origin) = origin {
            let canon = self.meta_vars.find(a);
            self.meta_origins
                .borrow_mut()
                .insert(Meta::Ty(canon), origin);
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

                    let param = self.lookup_type_param_origin(*id).unwrap_or_else(|| {
                        let local_id: u32 = self.vars.type_params.next_id();
                        let sym = Symbol::TypeParameter(TypeParameterId::new(
                            self.current_module_id,
                            local_id,
                        ));
                        let param = Ty::Param(sym, vec![]);
                        self.set_meta_origin(
                            Meta::Ty(*id),
                            MetaOrigin::TypeParam {
                                param: sym,
                                bounds: vec![],
                            },
                        );
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
                    let level = self
                        .meta_levels
                        .borrow()
                        .get(&Meta::Row(*id))
                        .copied()
                        .unwrap_or_default();
                    if level < context.level() {
                        tracing::trace!(
                            "discarding {m:?} due to level ({level:?} < {:?})",
                            context.level()
                        );
                        continue;
                    }

                    let param_id = self.lookup_row_param_origin(*id).unwrap_or_else(|| {
                        let param_id = self.vars.row_params.next_id();
                        self.set_meta_origin(
                            Meta::Row(*id),
                            MetaOrigin::RowParam { param: param_id },
                        );
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

            let predicate = c
                .substitute(&self.skolem_map)
                .into_predicate(&mut substitutions, self);
            if predicate.is_some() {
                constraints.solve(c.id());
            }
            predicate
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

    pub fn declare_conformance(&mut self, claim: ConformanceClaim) {
        self.type_catalog.declare_conformance(claim);
    }

    pub fn declare_conformance_obligation(&mut self, obligation: ConformanceObligation) {
        self.conformance.declare_obligation(obligation);
    }

    pub fn associated_type_slot(&mut self, key: ConformanceKey, label: &Label, level: Level) -> Ty {
        if let Some(existing) = self.lookup_associated_type_slot(&key, label) {
            return existing;
        }

        let ty = self.new_ty_meta_var(level);
        self.conformance.associated_type_slot(
            &mut self.type_catalog,
            self.modules.as_ref(),
            key,
            label,
            ty,
        )
    }

    pub fn lookup_associated_type_slot(&self, key: &ConformanceKey, label: &Label) -> Option<Ty> {
        self.conformance.lookup_associated_type_slot(key, label)
    }

    pub fn lookup_conformance_claim(&mut self, key: &ConformanceKey) -> Option<ConformanceClaim> {
        self.conformance
            .lookup_claim(&mut self.type_catalog, self.modules.as_ref(), key)
    }

    pub fn lookup_conformance(&mut self, key: &ConformanceKey) -> Option<ConformanceEvidence> {
        self.conformance
            .lookup_evidence(&mut self.type_catalog, self.modules.as_ref(), key)
    }

    pub(crate) fn record_evidence(&mut self, key: ConformanceKey, evidence: ConformanceEvidence) {
        self.conformance
            .record_evidence(&mut self.type_catalog, key, evidence);
    }

    pub(crate) fn record_witnesses(
        &mut self,
        key: ConformanceKey,
        mut evidence: ConformanceEvidence,
        witnesses: WitnessTable,
    ) {
        evidence.witnesses = witnesses;
        self.record_evidence(key, evidence);
    }

    pub(crate) fn inherited_evidence(
        &self,
        evidence: &ConformanceEvidence,
        conforming_id: Symbol,
        protocol_id: ProtocolId,
    ) -> ConformanceEvidence {
        ConformanceEvidence::from_superprotocol(
            evidence.node_id,
            conforming_id,
            protocol_id,
            evidence.span,
        )
    }

    pub fn conformance_seed(
        &mut self,
        key: ConformanceKey,
        seed: Option<ConformanceEvidence>,
    ) -> Option<ConformanceEvidence> {
        self.conformance
            .conformance_seed(&mut self.type_catalog, self.modules.as_ref(), key, seed)
    }

    pub fn protocol_implies(
        &mut self,
        source_protocol_id: ProtocolId,
        target_protocol_id: ProtocolId,
    ) -> bool {
        self.conformance.protocol_implies(
            &mut self.type_catalog,
            self.modules.as_ref(),
            source_protocol_id,
            target_protocol_id,
        )
    }

    pub fn superprotocol_keys_for(&self, protocol_id: ProtocolId) -> Vec<ConformanceKey> {
        self.conformance
            .superprotocol_keys_for(&self.type_catalog, protocol_id)
    }

    pub fn claimed_protocol_member(
        &mut self,
        symbol: Symbol,
        label: &Label,
    ) -> Option<(ProtocolId, Symbol)> {
        for protocol_id in self
            .conformance
            .claimed_protocols_for(&self.type_catalog, symbol)
        {
            let protocol_symbol = Symbol::Protocol(protocol_id);
            let Some((member_sym, _source)) = self.lookup_member(&protocol_symbol, label) else {
                continue;
            };

            if matches!(
                member_sym,
                Symbol::InstanceMethod(..) | Symbol::MethodRequirement(..)
            ) {
                return Some((protocol_id, member_sym));
            }
        }

        None
    }

    pub fn associated_type_candidate(
        &mut self,
        key: ConformanceKey,
        label: &Label,
        origin: ConformanceOrigin,
    ) -> Option<Symbol> {
        self.conformance.associated_type_candidate(
            &mut self.type_catalog,
            self.modules.as_ref(),
            &self.resolved_names,
            key,
            label,
            origin,
        )
    }

    pub fn method_witness_candidate(
        &mut self,
        key: ConformanceKey,
        label: &Label,
        required_sym: &Symbol,
        origin: ConformanceOrigin,
        witness_table: &WitnessTable,
    ) -> Option<Symbol> {
        if let Some(sym) = self.conformance.method_candidate(
            &mut self.type_catalog,
            self.modules.as_ref(),
            key,
            label,
        ) {
            return Some(sym);
        }

        witness_table
            .get_witness(label, required_sym)
            .or_else(|| match origin {
                ConformanceOrigin::Declared => None,
                ConformanceOrigin::Inherited => {
                    self.direct_member_symbol(&key.conforming_id, label)
                }
            })
    }

    pub fn resolve_associated_projection(
        &mut self,
        protocol_id: Option<ProtocolId>,
        base_sym: Symbol,
        label: &Label,
        level: Level,
    ) -> Option<AssociatedTypeResolution> {
        match self.conformance.resolve_associated_projection(
            &mut self.type_catalog,
            self.modules.as_ref(),
            &self.resolved_names,
            protocol_id,
            base_sym,
            label,
        )? {
            ProjectionResolution::Alias(symbol) => Some(AssociatedTypeResolution::Alias(symbol)),
            ProjectionResolution::Witness(ty) => Some(AssociatedTypeResolution::Witness(ty)),
            ProjectionResolution::PendingSlot(key) => Some(AssociatedTypeResolution::Witness(
                self.associated_type_slot(key, label, level),
            )),
        }
    }

    pub(crate) fn can_generalize_projection(
        &mut self,
        protocol_id: Option<ProtocolId>,
        base: &Ty,
        label: &Label,
        substitutions: &mut UnificationSubstitutions,
    ) -> bool {
        if let Some(protocol_id) = protocol_id {
            return self.protocol_has_associated_type(protocol_id, label);
        }

        self.projection_base_bounds(base, substitutions)
            .into_iter()
            .any(|protocol_id| self.protocol_has_associated_type(protocol_id, label))
    }

    fn projection_base_bounds(
        &mut self,
        base: &Ty,
        substitutions: &mut UnificationSubstitutions,
    ) -> Vec<ProtocolId> {
        match self.apply(base, substitutions) {
            Ty::Param(_, bounds) => bounds,
            Ty::Var { id, .. } => {
                if let Some(Ty::Param(_, bounds)) = self.lookup_type_param_origin(id) {
                    bounds
                } else {
                    vec![]
                }
            }
            Ty::Rigid(id) => {
                if let Some(Ty::Param(_, bounds)) = self.skolem_map.get(&Ty::Rigid(id)) {
                    bounds.clone()
                } else {
                    vec![]
                }
            }
            _ => vec![],
        }
    }

    fn protocol_has_associated_type(&mut self, protocol_id: ProtocolId, label: &Label) -> bool {
        self.lookup_associated_types(Symbol::Protocol(protocol_id))
            .map(|entries| entries.contains_key(label))
            .unwrap_or(false)
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

        for key in self.type_catalog.conformance_evidence.keys() {
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

    fn direct_member(&mut self, receiver: &Symbol, label: &Label) -> Option<MemberBinding> {
        if let Some(binding) = self
            .type_catalog
            .lookup_direct_member_binding(receiver, label)
        {
            return Some(binding);
        }

        if let Some(binding) = self.modules.lookup_direct_member_binding(receiver, label) {
            self.cache_member(binding.symbol, receiver, label);
            return Some(binding);
        }

        None
    }

    fn direct_member_symbol(&mut self, receiver: &Symbol, label: &Label) -> Option<Symbol> {
        self.direct_member(receiver, label)
            .map(|binding| binding.symbol)
    }

    fn validated_protocol_member(
        &mut self,
        receiver: Symbol,
        label: &Label,
    ) -> Option<(Symbol, MemberSource)> {
        for protocol_id in self.validated_protocols_for(receiver) {
            let protocol_symbol = Symbol::Protocol(protocol_id);
            if let Some(member) = self.direct_member_symbol(&protocol_symbol, label) {
                return Some((member, MemberSource::Protocol(protocol_id)));
            }
        }

        None
    }

    fn claimed_superprotocol_member(
        &mut self,
        receiver: Symbol,
        label: &Label,
    ) -> Option<(Symbol, MemberSource)> {
        for protocol_id in self.claimed_superprotocols_for(receiver) {
            let protocol_symbol = Symbol::Protocol(protocol_id);
            if let Some(member) = self.direct_member_symbol(&protocol_symbol, label) {
                return Some((member, MemberSource::Protocol(protocol_id)));
            }
        }

        None
    }

    #[instrument(skip(self))]
    pub(super) fn lookup_member(
        &mut self,
        receiver: &Symbol,
        label: &Label,
    ) -> Option<(Symbol, MemberSource)> {
        if let Some(binding) = self.direct_member(receiver, label) {
            return Some((binding.symbol, binding.source));
        }

        if let Some(member) = self.validated_protocol_member(*receiver, label) {
            return Some(member);
        }

        if matches!(receiver, Symbol::Protocol(_)) {
            return self.claimed_superprotocol_member(*receiver, label);
        }

        None
    }

    fn validated_protocols_for(&self, receiver: Symbol) -> Vec<ProtocolId> {
        let mut protocols = self
            .type_catalog
            .conformance_evidence
            .keys()
            .filter(|key| key.conforming_id == receiver)
            .map(|key| key.protocol_id)
            .collect_vec();

        protocols.extend(
            self.modules
                .all_conformance_evidence()
                .into_iter()
                .filter(|(key, _)| key.conforming_id == receiver)
                .map(|(key, _)| key.protocol_id),
        );

        protocols.sort();
        protocols.dedup();
        protocols
    }

    fn claimed_superprotocols_for(&self, receiver: Symbol) -> Vec<ProtocolId> {
        let mut protocols = self
            .conformance
            .claimed_protocols_for(&self.type_catalog, receiver);

        protocols.extend(
            self.modules
                .all_conformance_claims()
                .into_iter()
                .filter(|(key, _)| key.conforming_id == receiver)
                .map(|(key, _)| key.protocol_id),
        );

        protocols.sort();
        protocols.dedup();
        protocols
    }

    pub(super) fn lookup_constructor_member(
        &mut self,
        receiver: &Symbol,
        label: &Label,
    ) -> Option<Symbol> {
        if let Some(sym) = self
            .type_catalog
            .lookup_direct_constructor_member(receiver, label)
        {
            return Some(sym);
        }

        if let Some(sym) = self
            .modules
            .lookup_direct_constructor_member(receiver, label)
        {
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
            Symbol::Struct(..)
            | Symbol::Enum(..)
            | Symbol::TypeAlias(..)
            | Symbol::Protocol(..) => {
                self.type_catalog
                    .child_types
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
            self.set_meta_origin(
                Meta::Ty(meta),
                MetaOrigin::TypeParam {
                    param: sym,
                    bounds: vec![],
                },
            );
        }

        tracing::trace!("Fresh type param {sym:?}");
        param
    }

    pub(crate) fn new_type_param_id(&mut self, meta: Option<MetaVarId>) -> Symbol {
        let local_id: u32 = self.vars.type_params.next_id();
        let sym = Symbol::TypeParameter(TypeParameterId::new(self.current_module_id, local_id));
        if let Some(meta) = meta {
            self.set_meta_origin(
                Meta::Ty(meta),
                MetaOrigin::TypeParam {
                    param: sym,
                    bounds: vec![],
                },
            );
        }

        tracing::trace!("Fresh type param {sym:?}");
        sym
    }

    pub(crate) fn new_row_type_param(&mut self, meta: Option<RowMetaId>) -> Row {
        let id = self.vars.row_params.next_id();

        if let Some(meta) = meta {
            self.set_meta_origin(Meta::Row(meta), MetaOrigin::RowParam { param: id });
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
        self.new_ty_meta_var_with_origin(level, None)
    }

    pub(crate) fn new_ty_meta_var_with_origin(
        &mut self,
        level: Level,
        origin: Option<MetaOrigin>,
    ) -> Ty {
        let id = self.meta_vars.new_key(level);
        self.meta_levels.borrow_mut().insert(Meta::Ty(id), level);
        if let Some(origin) = origin {
            self.set_meta_origin(Meta::Ty(id), origin);
        }
        Ty::Var { id, level }
    }

    pub(crate) fn new_ty_meta_var_id(&mut self, level: Level) -> MetaVarId {
        let id = self.meta_vars.new_key(level);
        self.meta_levels.borrow_mut().insert(Meta::Ty(id), level);
        id
    }

    pub(crate) fn new_row_meta_var(&mut self, level: Level) -> Row {
        self.new_row_meta_var_with_origin(level, None)
    }

    pub(crate) fn new_row_meta_var_with_origin(
        &mut self,
        level: Level,
        origin: Option<MetaOrigin>,
    ) -> Row {
        let id = self.row_vars.new_key(level);
        self.meta_levels.borrow_mut().insert(Meta::Row(id), level);
        if let Some(origin) = origin {
            self.set_meta_origin(Meta::Row(id), origin);
        }
        Row::Var(id)
    }

    fn showable_protocol_id(&self) -> Option<ProtocolId> {
        for (sym, name) in &self.resolved_names.symbol_names {
            if name == "Showable"
                && let Symbol::Protocol(id) = sym
            {
                return Some(*id);
            }
        }
        for (sym, name) in self.modules.imported_symbol_names() {
            if name == "Showable"
                && let Symbol::Protocol(id) = sym
            {
                return Some(id);
            }
        }
        None
    }

    pub(crate) fn is_showable_protocol(&self, protocol_id: ProtocolId) -> bool {
        self.showable_protocol_id() == Some(protocol_id)
    }

    pub(crate) fn derive_showable_for_nominals(
        &mut self,
        constraints: &mut ConstraintStore,
    ) -> Vec<ShowDerivation> {
        let Some(protocol_id) = self.showable_protocol_id() else {
            return vec![];
        };
        let nominals: Vec<_> = self
            .type_catalog
            .nominals
            .keys()
            .copied()
            .filter(|symbol| matches!(symbol, Symbol::Struct(..) | Symbol::Enum(..)))
            .filter(|symbol| symbol.module_id() == Some(self.current_module_id))
            .collect();

        nominals
            .into_iter()
            .filter_map(|nominal| {
                self.derive_showable_for_nominal(nominal, protocol_id, constraints)
            })
            .collect()
    }

    fn show_required_type_params(ty: &Ty, required: &mut FxHashSet<Symbol>) {
        match ty {
            Ty::Param(param, _) => {
                required.insert(*param);
            }
            Ty::Nominal { type_args, .. } | Ty::Tuple(type_args) => {
                for arg in type_args {
                    Self::show_required_type_params(arg, required);
                }
            }
            Ty::Constructor { params, ret, .. } => {
                for param in params {
                    Self::show_required_type_params(param, required);
                }
                Self::show_required_type_params(ret, required);
            }
            Ty::Record(_, row) => Self::show_required_row_params(row, required),
            Ty::Func(..) => {}
            Ty::Projection { base, .. } => Self::show_required_type_params(base, required),
            Ty::Primitive(..) | Ty::Rigid(..) | Ty::Var { .. } | Ty::Error(..) => {}
        }
    }

    fn show_required_row_params(row: &Row, required: &mut FxHashSet<Symbol>) {
        match row {
            Row::Extend { row, ty, .. } => {
                Self::show_required_row_params(row, required);
                Self::show_required_type_params(ty, required);
            }
            Row::Empty | Row::Param(..) | Row::Var(..) => {}
        }
    }

    fn showable_nominal_ty(
        &self,
        nominal_sym: Symbol,
        nominal: &Nominal,
        protocol_id: ProtocolId,
    ) -> Ty {
        let mut required = FxHashSet::default();
        for ty in nominal.properties.values() {
            Self::show_required_type_params(ty, &mut required);
        }
        for tys in nominal.variants.values() {
            for ty in tys {
                Self::show_required_type_params(ty, &mut required);
            }
        }

        let type_args = nominal
            .type_params
            .iter()
            .map(|ty| match ty {
                Ty::Param(param, bounds) if required.contains(param) => {
                    let mut bounds = bounds.clone();
                    if !bounds.contains(&protocol_id) {
                        bounds.push(protocol_id);
                    }
                    Ty::Param(*param, bounds)
                }
                _ => ty.clone(),
            })
            .collect();

        Ty::Nominal {
            symbol: nominal_sym,
            type_args,
        }
    }

    fn derive_showable_for_nominal(
        &mut self,
        nominal_sym: Symbol,
        protocol_id: ProtocolId,
        constraints: &mut ConstraintStore,
    ) -> Option<ShowDerivation> {
        if !matches!(nominal_sym, Symbol::Struct(..) | Symbol::Enum(..)) {
            return None;
        }

        let key = ConformanceKey {
            protocol_id,
            conforming_id: nominal_sym,
        };
        if self.lookup_conformance_claim(&key).is_some() || self.lookup_conformance(&key).is_some()
        {
            return None;
        }

        let protocol_symbol: Symbol = protocol_id.into();
        let Some(EnvEntry::Scheme(Scheme {
            ty: Ty::Param(self_id, _),
            ..
        })) = self.lookup(&protocol_symbol)
        else {
            return None;
        };

        let nominal = self.lookup_nominal(&nominal_sym)?;
        let nominal_ty = self.showable_nominal_ty(nominal_sym, &nominal, protocol_id);

        let mut subs = FxHashMap::default();
        subs.insert(Ty::Param(self_id, vec![]), nominal_ty.clone());

        let show_label = Label::Named("show".into());
        let requirements = self.lookup_method_requirements(protocol_symbol)?;
        let req_sym = *requirements.get(&show_label)?;
        let entry = self.lookup(&req_sym)?;
        let req_ty = substitute(&entry._as_ty(), &subs);

        let method_sym =
            Symbol::InstanceMethod(self.symbols.next_instance_method(self.current_module_id));
        let self_param_sym = Symbol::ParamLocal(self.symbols.next_param());

        self.insert(method_sym, req_ty, constraints);
        self.term_env
            .insert(self_param_sym, EnvEntry::Mono(nominal_ty));

        self.type_catalog
            .instance_methods
            .entry(nominal_sym)
            .or_default()
            .insert(show_label.clone(), method_sym);

        let mut witnesses = WitnessTable::default();
        witnesses.methods.insert(show_label.clone(), method_sym);
        witnesses.requirements.insert(req_sym, method_sym);

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
        self.resolved_names
            .symbol_names
            .insert(method_sym, format!("{type_name}.show"));
        self.resolved_names
            .symbol_names
            .insert(self_param_sym, "self".into());

        Some(ShowDerivation {
            nominal: nominal_sym,
            protocol_id,
            method: method_sym,
            self_param: self_param_sym,
            witnesses,
        })
    }
}
