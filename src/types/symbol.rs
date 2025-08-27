use crate::id_generator::IDGenerator;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Symbol {
    Decl(DeclId),
    Local(LocalId),
    Field(FieldId),
    Builtin(BuiltinId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DeclId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LocalId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FieldId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BuiltinId(pub u32);

impl<T: Into<u32>> From<T> for DeclId {
    fn from(value: T) -> Self {
        DeclId(value.into())
    }
}

impl<T: Into<u32>> From<T> for LocalId {
    fn from(value: T) -> Self {
        LocalId(value.into())
    }
}

impl<T: Into<u32>> From<T> for FieldId {
    fn from(value: T) -> Self {
        FieldId(value.into())
    }
}

impl<T: Into<u32>> From<T> for BuiltinId {
    fn from(value: T) -> Self {
        BuiltinId(value.into())
    }
}

#[derive(Debug, Clone, Default)]
pub struct Symbols {
    decls: IDGenerator,
    locals: IDGenerator,
    fields: IDGenerator,
    builtins: IDGenerator,
}

impl Symbols {
    pub fn next_decl(&mut self) -> DeclId {
        DeclId(self.decls.next_id())
    }

    pub fn next_local(&mut self) -> LocalId {
        LocalId(self.locals.next_id())
    }

    pub fn next_field(&mut self) -> FieldId {
        FieldId(self.fields.next_id())
    }

    pub fn next_builtin(&mut self) -> BuiltinId {
        BuiltinId(self.builtins.next_id())
    }
}
