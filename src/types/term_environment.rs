use indexmap::IndexSet;
use rustc_hash::FxHashMap;

use crate::{
    compiling::module::ModuleId,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    span::Span,
    types::{
        builtins::builtin_scope,
        infer_ty::{InferTy, Level},
        predicate::Predicate,
        scheme::{ForAll, Scheme},
        solve_context::Solve,
        ty::SomeType,
        type_operations::{InstantiationSubstitutions, UnificationSubstitutions, apply},
        type_session::{TypeEntry, TypeSession},
        wants::Wants,
    },
};

#[derive(Debug, Clone, PartialEq)]
pub enum EnvEntry<T: SomeType> {
    Mono(T),
    Scheme(Scheme<T>),
}

impl From<(InferTy, Vec<Predicate<InferTy>>, IndexSet<ForAll>)> for EnvEntry<InferTy> {
    fn from(value: (InferTy, Vec<Predicate<InferTy>>, IndexSet<ForAll>)) -> Self {
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

impl From<EnvEntry<InferTy>> for (InferTy, Vec<Predicate<InferTy>>, IndexSet<ForAll>) {
    fn from(val: EnvEntry<InferTy>) -> Self {
        match val {
            EnvEntry::Mono(ty) => (ty, vec![], Default::default()),
            EnvEntry::Scheme(scheme) => (scheme.ty, scheme.predicates, scheme.foralls),
        }
    }
}

impl From<EnvEntry<InferTy>> for TypeEntry {
    fn from(value: EnvEntry<InferTy>) -> Self {
        match value {
            EnvEntry::Mono(ty) => TypeEntry::Mono(ty.into()),
            EnvEntry::Scheme(scheme) => TypeEntry::Poly(Scheme {
                foralls: scheme.foralls,
                predicates: scheme.predicates.into_iter().map(|p| p.into()).collect(),
                ty: scheme.ty.into(),
            }),
        }
    }
}

impl From<TypeEntry> for EnvEntry<InferTy> {
    fn from(value: TypeEntry) -> Self {
        match value {
            TypeEntry::Mono(ty) => EnvEntry::Mono(ty.into()),
            TypeEntry::Poly(scheme) => EnvEntry::Scheme(Scheme {
                foralls: scheme.foralls,
                predicates: scheme.predicates.into_iter().map(|p| p.into()).collect(),
                ty: scheme.ty.into(),
            }),
        }
    }
}

impl<T: SomeType> EnvEntry<T> {
    pub fn foralls(&self) -> IndexSet<ForAll> {
        match self {
            EnvEntry::Mono(..) => Default::default(),
            EnvEntry::Scheme(scheme) => scheme.foralls.clone(),
        }
    }

    pub fn predicates(&self) -> Vec<Predicate<T>> {
        match self {
            EnvEntry::Mono(..) => Default::default(),
            EnvEntry::Scheme(scheme) => scheme.predicates.clone(),
        }
    }
}

impl EnvEntry<InferTy> {
    pub fn apply(&self, substitutions: &mut UnificationSubstitutions) -> Self {
        match self.clone() {
            EnvEntry::Mono(ty) => EnvEntry::Mono(apply(ty, substitutions)),
            EnvEntry::Scheme(scheme) => EnvEntry::Scheme(Scheme {
                foralls: scheme.foralls,
                predicates: scheme
                    .predicates
                    .into_iter()
                    .map(|p| p.apply(substitutions))
                    .collect(),
                ty: apply(scheme.ty, substitutions),
            }),
        }
    }

    pub fn import(&self, module_id: ModuleId) -> EnvEntry<InferTy> {
        match self.clone() {
            EnvEntry::Mono(ty) => EnvEntry::Mono(ty.import(module_id)),
            EnvEntry::Scheme(scheme) => EnvEntry::Scheme(Scheme {
                foralls: scheme.foralls,
                predicates: scheme.predicates,
                ty: scheme.ty.import(module_id),
            }),
        }
    }

    pub(super) fn _as_ty(&self) -> InferTy {
        match self {
            EnvEntry::Mono(ty) => ty.clone(),
            EnvEntry::Scheme(scheme) => scheme.ty.clone(),
        }
    }

    pub fn instantiate_with_args(
        &self,
        id: NodeID,
        args: &[(InferTy, NodeID)],
        session: &mut TypeSession,
        level: Level,
        wants: &mut Wants,
        span: Span,
    ) -> (InferTy, InstantiationSubstitutions) {
        tracing::debug!("inference instantiate: {self:?}");
        match self {
            EnvEntry::Mono(ty) => (ty.clone(), Default::default()),
            EnvEntry::Scheme(scheme) => {
                scheme.instantiate_with_args(id, args, session, level, wants, span)
            }
        }
    }

    pub(super) fn instantiate(
        &self,
        id: NodeID,
        context: &mut impl Solve,
        session: &mut TypeSession,
        span: Span,
    ) -> InferTy {
        tracing::debug!("inference instantiate: {self:?}");
        match self {
            EnvEntry::Mono(ty) => ty.clone(),
            EnvEntry::Scheme(scheme) => scheme.instantiate(id, context, session, span),
        }
    }
}

#[derive(Debug, Default, PartialEq, Clone)]
pub struct TermEnv {
    pub(super) symbols: FxHashMap<Symbol, EnvEntry<InferTy>>,
}

impl TermEnv {
    pub fn new() -> Self {
        let mut env = Self::default();
        env.symbols.extend(builtin_scope());
        env
    }

    pub fn insert_mono(&mut self, sym: Symbol, ty: InferTy) {
        self.insert(sym, EnvEntry::Mono(ty));
    }

    pub fn lookup(&self, sym: &Symbol) -> Option<&EnvEntry<InferTy>> {
        self.symbols.get(sym)
    }

    pub fn lookup_mut(&mut self, sym: &Symbol) -> Option<&mut EnvEntry<InferTy>> {
        self.symbols.get_mut(sym)
    }

    pub fn insert(&mut self, sym: Symbol, entry: EnvEntry<InferTy>) {
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

    pub fn promote(&mut self, sym: Symbol, entry: EnvEntry<InferTy>) {
        tracing::debug!("promote {sym:?} = {entry:?}");
        self.symbols.insert(sym, entry);
    }
}
