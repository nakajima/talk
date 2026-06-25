#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct ModuleId(pub u16);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ModuleSymbolId {
    pub module_id: ModuleId,
    pub local_id: u32,
}

impl ModuleSymbolId {
    pub fn new(module_id: ModuleId, local_id: u32) -> Self {
        Self { module_id, local_id }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LocalSymbolId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Symbol {
    Struct(ModuleSymbolId),
    Enum(ModuleSymbolId),
    TypeAlias(ModuleSymbolId),
    TypeParameter(ModuleSymbolId),
    Global(ModuleSymbolId),
    DeclaredLocal(LocalSymbolId),
    PatternBindLocal(LocalSymbolId),
    ParamLocal(LocalSymbolId),
    Builtin(ModuleSymbolId),
    Property(ModuleSymbolId),
    Synthesized(ModuleSymbolId),
    InstanceMethod(ModuleSymbolId),
    Initializer(ModuleSymbolId),
    StaticMethod(ModuleSymbolId),
    Variant(ModuleSymbolId),
    Protocol(ModuleSymbolId),
    AssociatedType(ModuleSymbolId),
    MethodRequirement(ModuleSymbolId),
    Effect(ModuleSymbolId),
    Main,
    Library,
}

impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
