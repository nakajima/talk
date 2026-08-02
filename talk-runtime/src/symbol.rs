#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct ModuleId(pub u16);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ModuleSymbolId {
    pub module_id: ModuleId,
    pub local_id: u32,
}

impl ModuleSymbolId {
    pub fn new(module_id: ModuleId, local_id: u32) -> Self {
        Self {
            module_id,
            local_id,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LocalSymbolId(pub u32);

/// The identities the runtime can name: the aggregate identities the
/// layout table publishes (structs, enums), plus a fallback for
/// everything the compiler keeps to itself.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Symbol {
    Struct(ModuleSymbolId),
    Enum(ModuleSymbolId),
    Library,
}

impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
