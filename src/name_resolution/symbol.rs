use crate::id_generator::IDGenerator;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Symbol {
    DeclId(DeclId),
    LocalId(LocalId),
    FieldId(FieldId),
    BuiltinId(BuiltinId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DeclId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LocalId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FieldId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BuiltinId(pub u32);

macro_rules! impl_symbol_id {
    ($ty: ident) => {
        impl<T: Into<u32>> From<T> for $ty {
            fn from(value: T) -> Self {
                $ty(value.into())
            }
        }

        impl From<$ty> for Symbol {
            fn from(value: $ty) -> Symbol {
                Symbol::$ty(value)
            }
        }
    };
}

impl_symbol_id!(DeclId);
impl_symbol_id!(LocalId);
impl_symbol_id!(FieldId);
impl_symbol_id!(BuiltinId);

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
