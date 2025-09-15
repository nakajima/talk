use rustc_hash::FxHashMap;

use crate::{
    name_resolution::symbol::Symbol,
    span::Span,
    types::{
        builtins::builtin_scope,
        passes::inference_pass::{InferencePass, Wants},
        scheme::Scheme,
        ty::{Level, Ty},
        type_operations::UnificationSubstitutions,
    },
};

#[derive(Debug, Clone)]
pub enum EnvEntry {
    Mono(Ty),
    Scheme(Scheme),
}

impl EnvEntry {
    pub fn solver_instantiate(
        &self,
        pass: &mut InferencePass,
        level: Level,
        substitutions: &mut UnificationSubstitutions,
        wants: &mut Wants,
        span: Span,
    ) -> Ty {
        match self {
            EnvEntry::Mono(ty) => ty.clone(),
            EnvEntry::Scheme(scheme) => {
                scheme
                    .solver_instantiate(pass, level, wants, span, substitutions)
                    .0
            }
        }
    }

    pub fn inference_instantiate(
        &self,
        pass: &mut InferencePass,
        level: Level,
        wants: &mut Wants,
        span: Span,
    ) -> Ty {
        match self {
            EnvEntry::Mono(ty) => ty.clone(),
            EnvEntry::Scheme(scheme) => scheme.inference_instantiate(pass, level, wants, span).0,
        }
    }
}

#[derive(Debug, Default)]
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

    pub fn promote(&mut self, sym: Symbol, entry: EnvEntry) {
        self.symbols.insert(sym, entry);
    }
}
