use rustc_hash::FxHashMap;

use crate::{
    name_resolution::symbol::Symbol,
    span::Span,
    types::{
        builtins::builtin_scope,
        predicate::Predicate,
        scheme::{ForAll, Scheme},
        ty::{Level, Ty},
        type_operations::UnificationSubstitutions,
        type_session::TypeSession,
        wants::Wants,
    },
};

#[derive(Debug, Clone, PartialEq)]
pub enum EnvEntry {
    Mono(Ty),
    Scheme(Scheme),
}

impl From<(Ty, Vec<Predicate>, Vec<ForAll>)> for EnvEntry {
    fn from(value: (Ty, Vec<Predicate>, Vec<ForAll>)) -> Self {
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

impl From<EnvEntry> for (Ty, Vec<Predicate>, Vec<ForAll>) {
    fn from(val: EnvEntry) -> Self {
        match val {
            EnvEntry::Mono(ty) => (ty, vec![], vec![]),
            EnvEntry::Scheme(scheme) => (scheme.ty, scheme.predicates, scheme.foralls),
        }
    }
}

impl EnvEntry {
    pub fn solver_instantiate(
        &self,
        session: &mut TypeSession,
        level: Level,
        substitutions: &mut UnificationSubstitutions,
        wants: &mut Wants,
        span: Span,
    ) -> Ty {
        match self {
            EnvEntry::Mono(ty) => ty.clone(),
            EnvEntry::Scheme(scheme) => {
                scheme
                    .solver_instantiate(session, level, wants, span, substitutions)
                    .0
            }
        }
    }

    pub fn inference_instantiate(
        &self,
        session: &mut TypeSession,
        level: Level,
        wants: &mut Wants,
        span: Span,
    ) -> Ty {
        tracing::debug!("inference instantiate: {self:?}");
        match self {
            EnvEntry::Mono(ty) => ty.clone(),
            EnvEntry::Scheme(scheme) => scheme.inference_instantiate(session, level, wants, span).0,
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
        if let Some(existing) = self.symbols.get(&sym)
            && *existing != entry
        {
            tracing::warn!("overriding {sym:?} with {entry:?}. existing: {existing:?}");
        }

        tracing::debug!("promote {sym:?} = {entry:?}");
        self.symbols.insert(sym, entry);
    }
}
