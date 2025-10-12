use indexmap::IndexMap;
use rustc_hash::FxHashMap;

use crate::{name_resolution::symbol::Symbol, types::type_session::Types};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub enum ModuleId {
    Core,
    Prelude,
    #[default]
    Current,
    External(u32),
}

#[derive(Debug, Default)]
pub struct ModuleEnvironment {
    pub modules_by_name: FxHashMap<String, ModuleId>,
    pub modules: FxHashMap<ModuleId, Module>,
}

impl ModuleEnvironment {
    pub fn import(&mut self, id: ModuleId, module: Module) {
        self.modules_by_name.insert(module.name.clone(), id);
        self.modules.insert(id, module);
    }
}

#[derive(Debug)]
pub struct Module {
    pub name: String,
    pub types: Types,
    pub exports: IndexMap<String, Symbol>,
}
