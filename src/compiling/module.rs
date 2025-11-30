use std::fmt::Display;

use indexmap::IndexMap;
use rustc_hash::FxHashMap;

use crate::{ir::program::Program, name_resolution::symbol::Symbol, types::type_session::Types};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct ModuleId(pub u16);

#[allow(non_snake_case, non_upper_case_globals)]
impl ModuleId {
    pub const Current: ModuleId = ModuleId(0);
    pub const Builtin: ModuleId = ModuleId(1);
    pub const Core: ModuleId = ModuleId(2);
    pub const fn External(i: u16) -> ModuleId {
        ModuleId(i + 3)
    }

    pub fn is_external_or_core(&self) -> bool {
        self.0 > 1
    }

    pub fn is_external(&self) -> bool {
        self.0 > 2
    }
}

impl Display for ModuleId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Self::Core => write!(f, "C"),
            Self::Builtin => write!(f, "B"),
            Self::Current => write!(f, "_"),
            id => write!(f, "{id}"),
        }
    }
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

#[derive(Debug, Clone)]
pub struct Module {
    pub name: String,
    pub types: Types,
    pub exports: IndexMap<String, Symbol>,
    pub program: Program,
}
