use rustc_hash::FxHashMap;

use crate::{
    name_resolution::symbol::Symbol,
    span::Span,
    types::{
        builtins::builtin_scope,
        passes::dependencies_pass::SCCResolved,
        scheme::Scheme,
        ty::{Level, Ty},
        type_operations::UnificationSubstitutions,
        type_session::{TypeSession, TypingPhase},
        wants::Wants,
    },
};

#[derive(Debug, Clone, PartialEq)]
pub enum EnvEntry {
    Mono(Ty),
    Scheme(Scheme),
}

impl EnvEntry {
    pub fn solver_instantiate<P: TypingPhase>(
        &self,
        session: &mut TypeSession<P>,
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
        session: &mut TypeSession<SCCResolved>,
        level: Level,
        wants: &mut Wants,
        span: Span,
    ) -> Ty {
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
        self.symbols.insert(sym, EnvEntry::Mono(ty));
    }

    pub fn lookup(&self, sym: &Symbol) -> Option<&EnvEntry> {
        self.symbols.get(sym)
    }

    pub fn lookup_mut(&mut self, sym: &Symbol) -> Option<&mut EnvEntry> {
        self.symbols.get_mut(sym)
    }

    pub fn promote(&mut self, sym: Symbol, entry: EnvEntry) {
        self.symbols.insert(sym, entry);
    }
}
