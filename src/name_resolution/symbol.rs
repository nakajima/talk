use crate::id_generator::IDGenerator;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Symbol {
    Type(DeclId),
    Value(DeclId),
    Local(LocalId),
    BuiltinType(BuiltinId),
    Synthesized(SynthesizedId),
}

#[allow(non_upper_case_globals)]
impl Symbol {
    pub const Int: Symbol = Symbol::BuiltinType(BuiltinId(1));
    pub const Float: Symbol = Symbol::BuiltinType(BuiltinId(2));
    pub const Bool: Symbol = Symbol::BuiltinType(BuiltinId(3));
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DeclId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LocalId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FieldId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BuiltinId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SynthesizedId(pub u32);

macro_rules! impl_symbol_id {
    ($case:ident, $ty: ident) => {
        impl<T: Into<u32>> From<T> for $ty {
            fn from(value: T) -> Self {
                $ty(value.into())
            }
        }

        impl From<$ty> for Symbol {
            fn from(value: $ty) -> Symbol {
                Symbol::$case(value)
            }
        }
    };
}

impl_symbol_id!(Type, DeclId);
impl_symbol_id!(Local, LocalId);

#[derive(Debug, Clone, Default)]
pub struct Symbols {
    decls: IDGenerator,
    locals: IDGenerator,
    fields: IDGenerator,
    synthesized: IDGenerator,
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

    pub fn next_synthesized(&mut self) -> SynthesizedId {
        SynthesizedId(self.synthesized.next_id())
    }
}
