use rustc_hash::FxHashMap;

use crate::{
    label::Label,
    name_resolution::symbol::{Symbol, TypeId},
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
    pub(super) methods: FxHashMap<(TypeId, Label), EnvEntry>,
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

    pub fn insert_method(&mut self, type_id: TypeId, label: Label, entry: EnvEntry) {
        self.methods.insert((type_id, label), entry);
    }

    pub fn lookup_method(&mut self, type_id: TypeId, label: Label) -> Option<&EnvEntry> {
        self.methods.get(&(type_id, label))
    }
}
