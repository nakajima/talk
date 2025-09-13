use rustc_hash::FxHashMap;

use crate::{
    name_resolution::symbol::Symbol,
    types::{builtins::builtin_scope, scheme::Scheme, ty::Ty},
};

#[derive(Debug, Clone)]
pub enum EnvEntry {
    Mono(Ty),
    Scheme(Scheme),
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
