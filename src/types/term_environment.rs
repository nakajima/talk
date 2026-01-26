use derive_visitor::{Drive, DriveMut};
use indexmap::IndexSet;
use rustc_hash::FxHashMap;

use crate::{
    compiling::module::ModuleId,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    types::{
        builtins::builtin_scope,
        constraints::store::ConstraintStore,
        infer_ty::Ty,
        predicate::Predicate,
        scheme::{ForAll, Scheme},
        solve_context::SolveContext,
        type_operations::{
            InstantiationSubstitutions, UnificationSubstitutions, substitute, substitute_row,
        },
        type_session::TypeSession,
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Hash, Drive, DriveMut)]
pub enum EnvEntry {
    Mono(Ty),
    Scheme(Scheme),
}

impl From<(Ty, Vec<Predicate>, IndexSet<ForAll>)> for EnvEntry {
    fn from(value: (Ty, Vec<Predicate>, IndexSet<ForAll>)) -> Self {
        let mut foralls = value.2;
        foralls.extend(value.0.collect_foralls());
        if value.1.is_empty() && foralls.is_empty() {
            EnvEntry::Mono(value.0)
        } else {
            EnvEntry::Scheme(Scheme {
                foralls,
                predicates: value.1,
                ty: value.0,
            })
        }
    }
}

impl From<EnvEntry> for (Ty, Vec<Predicate>, IndexSet<ForAll>) {
    fn from(val: EnvEntry) -> Self {
        match val {
            EnvEntry::Mono(ty) => (ty, vec![], Default::default()),
            EnvEntry::Scheme(scheme) => (scheme.ty, scheme.predicates, scheme.foralls),
        }
    }
}

impl EnvEntry {
    pub fn foralls(&self) -> IndexSet<ForAll> {
        match self {
            EnvEntry::Mono(..) => Default::default(),
            EnvEntry::Scheme(scheme) => scheme.foralls.clone(),
        }
    }

    pub fn predicates(&self) -> Vec<Predicate> {
        match self {
            EnvEntry::Mono(..) => Default::default(),
            EnvEntry::Scheme(scheme) => scheme.predicates.clone(),
        }
    }

    pub fn substitute(self, substitutions: &FxHashMap<Ty, Ty>) -> EnvEntry {
        match self {
            EnvEntry::Mono(ty) => {
                let ty = substitute(ty, substitutions);
                let foralls = ty.collect_foralls();
                if foralls.is_empty() {
                    EnvEntry::Mono(ty)
                } else {
                    EnvEntry::Scheme(Scheme {
                        ty,
                        foralls,
                        predicates: Default::default(),
                    })
                }
            }
            EnvEntry::Scheme(scheme) => {
                let ty = substitute(scheme.ty, substitutions);
                let foralls: IndexSet<ForAll> = ty.collect_foralls();
                let predicates: Vec<Predicate> = scheme
                    .predicates
                    .into_iter()
                    .map(|p| {
                        p.mapping(&mut |t| substitute(t, substitutions), &mut |r| {
                            substitute_row(r, substitutions)
                        })
                    })
                    .collect();
                if foralls.is_empty() {
                    EnvEntry::Mono(ty)
                } else {
                    EnvEntry::Scheme(Scheme {
                        ty,
                        foralls,
                        predicates,
                    })
                }
            }
        }
    }

    pub fn apply(
        &self,
        substitutions: &mut UnificationSubstitutions,
        session: &mut TypeSession,
    ) -> Self {
        match self.clone() {
            EnvEntry::Mono(ty) => {
                let ty = session.apply(ty, substitutions);
                let foralls = ty.collect_foralls();
                if foralls.is_empty() {
                    EnvEntry::Mono(ty)
                } else {
                    EnvEntry::Scheme(Scheme {
                        ty,
                        foralls,
                        predicates: Default::default(),
                    })
                }
            }
            EnvEntry::Scheme(scheme) => EnvEntry::Scheme(Scheme {
                foralls: scheme.foralls,
                predicates: scheme
                    .predicates
                    .into_iter()
                    .map(|p| p.apply(substitutions, session))
                    .collect(),
                ty: session.apply(scheme.ty, substitutions),
            }),
        }
    }

    pub fn import(&self, module_id: ModuleId) -> EnvEntry {
        match self.clone() {
            EnvEntry::Mono(ty) => EnvEntry::Mono(ty.import(module_id)),
            EnvEntry::Scheme(scheme) => EnvEntry::Scheme(Scheme {
                foralls: scheme.foralls,
                predicates: scheme.predicates,
                ty: scheme.ty.import(module_id),
            }),
        }
    }

    pub(super) fn _as_ty(&self) -> Ty {
        match self {
            EnvEntry::Mono(ty) => ty.clone(),
            EnvEntry::Scheme(scheme) => scheme.ty.clone(),
        }
    }

    pub fn instantiate_with_args(
        &self,
        id: NodeID,
        args: &[(Ty, NodeID)],
        session: &mut TypeSession,
        context: &mut SolveContext,
        constraints: &mut ConstraintStore,
    ) -> (Ty, InstantiationSubstitutions) {
        match self {
            EnvEntry::Mono(ty) => (ty.clone(), Default::default()),
            EnvEntry::Scheme(scheme) => {
                scheme.instantiate_with_args(id, args, session, context, constraints)
            }
        }
    }

    pub(super) fn instantiate(
        &self,
        id: NodeID,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
    ) -> Ty {
        tracing::debug!("inference instantiate (id: {id:?})");
        match self {
            EnvEntry::Mono(ty) => ty.clone(),
            EnvEntry::Scheme(scheme) => scheme.instantiate(id, constraints, context, session),
        }
    }
}

#[derive(Debug, Default, PartialEq, Clone)]
pub struct TermEnv {
    pub(super) symbols: FxHashMap<Symbol, EnvEntry>,
}

impl TermEnv {
    pub fn new() -> Self {
        let mut env = Self::default();
        env.symbols.extend(builtin_scope());
        env
    }

    pub fn insert_mono(&mut self, sym: Symbol, ty: Ty) {
        self.insert(sym, EnvEntry::Mono(ty));
    }

    pub fn lookup(&self, sym: &Symbol) -> Option<&EnvEntry> {
        self.symbols.get(sym)
    }

    pub fn lookup_mut(&mut self, sym: &Symbol) -> Option<&mut EnvEntry> {
        self.symbols.get_mut(sym)
    }

    pub fn insert(&mut self, sym: Symbol, entry: EnvEntry) {
        if let Some(existing) = self.symbols.get(&sym) {
            // Don't override a Scheme with a Mono - this happens when protocol
            // default methods get their bodies inferred in a specific context
            if matches!(existing, EnvEntry::Scheme(_)) && matches!(entry, EnvEntry::Mono(_)) {
                tracing::debug!(
                    "skipping override of {sym:?}: would replace Scheme with Mono. \
                   existing: {existing:?}, attempted: {entry:?}"
                );
                return;
            }

            if *existing != entry {
                tracing::warn!("overriding {sym:?} with {entry:?}. existing: {existing:?}");
            }
        }

        self.symbols.insert(sym, entry);
    }

    pub fn promote(&mut self, sym: Symbol, entry: EnvEntry) {
        tracing::debug!("promote {sym:?} = {entry:?}");
        self.symbols.insert(sym, entry);
    }
}
