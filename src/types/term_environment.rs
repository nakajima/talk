use rustc_hash::{FxHashMap, FxHashSet};

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
        type_operations::{UnificationSubstitutions, apply},
        type_session::{TypeEntry, TypeSession},
        wants::Wants,
    },
};

#[derive(Debug, Clone, PartialEq)]
pub enum EnvEntry {
    Mono(InferTy),
    Scheme(Scheme<InferTy>),
}

impl From<(InferTy, Vec<Predicate<InferTy>>, FxHashSet<ForAll>)> for EnvEntry {
    fn from(value: (InferTy, Vec<Predicate<InferTy>>, FxHashSet<ForAll>)) -> Self {
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

impl From<EnvEntry> for (InferTy, Vec<Predicate<InferTy>>, FxHashSet<ForAll>) {
    fn from(val: EnvEntry) -> Self {
        match val {
            EnvEntry::Mono(ty) => (ty, vec![], Default::default()),
            EnvEntry::Scheme(scheme) => (scheme.ty, scheme.predicates, scheme.foralls),
        }
    }
}

impl From<EnvEntry> for TypeEntry {
    fn from(value: EnvEntry) -> Self {
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

impl From<TypeEntry> for EnvEntry {
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

impl EnvEntry {
    pub fn foralls(&self) -> FxHashSet<ForAll> {
        match self {
            EnvEntry::Mono(..) => Default::default(),
            EnvEntry::Scheme(scheme) => scheme.foralls.clone(),
        }
    }

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

    pub fn solver_instantiate(
        &self,
        id: NodeID,
        session: &mut TypeSession,
        level: Level,
        substitutions: &mut UnificationSubstitutions,
        wants: &mut Wants,
        span: Span,
    ) -> InferTy {
        match self {
            EnvEntry::Mono(ty) => ty.clone(),
            EnvEntry::Scheme(scheme) => {
                scheme
                    .solver_instantiate(id, session, level, wants, span, substitutions)
                    .0
            }
        }
    }

    pub(super) fn _as_ty(&self) -> InferTy {
        match self {
            EnvEntry::Mono(ty) => ty.clone(),
            EnvEntry::Scheme(scheme) => scheme.ty.clone(),
        }
    }

    pub fn inference_instantiate(
        &self,
        id: NodeID,
        session: &mut TypeSession,
        level: Level,
        wants: &mut Wants,
        span: Span,
    ) -> InferTy {
        tracing::debug!("inference instantiate: {self:?}");
        match self {
            EnvEntry::Mono(ty) => ty.clone(),
            EnvEntry::Scheme(scheme) => {
                scheme
                    .inference_instantiate(id, session, level, wants, span)
                    .0
            }
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

    pub fn insert_mono(&mut self, sym: Symbol, ty: InferTy) {
        self.insert(sym, EnvEntry::Mono(ty));
    }

    pub fn lookup(&self, sym: &Symbol) -> Option<&EnvEntry> {
        self.symbols.get(sym)
    }

    pub fn lookup_mut(&mut self, sym: &Symbol) -> Option<&mut EnvEntry> {
        self.symbols.get_mut(sym)
    }

    pub fn insert(&mut self, sym: Symbol, entry: EnvEntry) {
        if let Some(existing) = self.symbols.get(&sym)
            && *existing != entry
        {
            tracing::warn!("overriding {sym:?} with {entry:?}. existing: {existing:?}");
        }

        tracing::debug!("promote {sym:?} = {entry:?}");
        self.symbols.insert(sym, entry);
    }
}
