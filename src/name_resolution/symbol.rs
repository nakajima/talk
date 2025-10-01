use crate::id_generator::IDGenerator;

macro_rules! impl_symbol_id {
    ($case:ident, $ty: ident) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $ty(pub u32);

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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Symbol {
    Type(TypeId),
    TypeParameter(TypeParameterId),
    Global(GlobalId),
    DeclaredLocal(DeclaredLocalId),
    PatternBindLocal(PatternBindLocalId),
    ParamLocal(ParamLocalId),
    Builtin(BuiltinId),
    Property(PropertyId),
    Synthesized(SynthesizedId),
    InstanceMethod(InstanceMethodId),
    StaticMethod(StaticMethodId),
    Variant(VariantId),
    AssociatedType(AssociatedTypeId),
}

#[allow(non_upper_case_globals)]
impl Symbol {
    pub const Int: Symbol = Symbol::Builtin(BuiltinId(1));
    pub const Float: Symbol = Symbol::Builtin(BuiltinId(2));
    pub const Bool: Symbol = Symbol::Builtin(BuiltinId(3));
}

impl_symbol_id!(Type, TypeId);
impl_symbol_id!(TypeParameter, TypeParameterId);
impl_symbol_id!(DeclaredLocal, DeclaredLocalId);
impl_symbol_id!(Global, GlobalId);
impl_symbol_id!(ParamLocal, ParamLocalId);
impl_symbol_id!(PatternBindLocal, PatternBindLocalId);
impl_symbol_id!(Property, PropertyId);
impl_symbol_id!(InstanceMethod, InstanceMethodId);
impl_symbol_id!(Builtin, BuiltinId);
impl_symbol_id!(Variant, VariantId);
impl_symbol_id!(Synthesized, SynthesizedId);
impl_symbol_id!(StaticMethod, StaticMethodId);
impl_symbol_id!(AssociatedType, AssociatedTypeId);

#[derive(Debug, Clone, Default)]
pub struct Symbols {
    decls: IDGenerator,
    values: IDGenerator,
    params: IDGenerator,
    pattern_binds: IDGenerator,
    locals: IDGenerator,
    properties: IDGenerator,
    instance_methods: IDGenerator,
    static_methods: IDGenerator,
    variants: IDGenerator,
    synthesized: IDGenerator,
    builtins: IDGenerator,
    associated_types: IDGenerator,
    type_parameters: IDGenerator,
}

impl Symbols {
    pub fn next_type(&mut self) -> TypeId {
        TypeId(self.decls.next_id())
    }

    pub fn next_type_parameter(&mut self) -> TypeParameterId {
        TypeParameterId(self.type_parameters.next_id())
    }

    pub fn next_property(&mut self) -> PropertyId {
        PropertyId(self.properties.next_id())
    }

    pub fn next_global(&mut self) -> GlobalId {
        GlobalId(self.values.next_id())
    }

    pub fn next_param(&mut self) -> ParamLocalId {
        ParamLocalId(self.params.next_id())
    }

    pub fn next_associated_type(&mut self) -> AssociatedTypeId {
        AssociatedTypeId(self.associated_types.next_id())
    }

    pub fn next_pattern_bind(&mut self) -> PatternBindLocalId {
        PatternBindLocalId(self.pattern_binds.next_id())
    }

    pub fn next_local(&mut self) -> DeclaredLocalId {
        DeclaredLocalId(self.locals.next_id())
    }

    pub fn next_variant(&mut self) -> VariantId {
        VariantId(self.variants.next_id())
    }

    pub fn next_instance_method(&mut self) -> InstanceMethodId {
        InstanceMethodId(self.instance_methods.next_id())
    }

    pub fn next_static_method(&mut self) -> StaticMethodId {
        StaticMethodId(self.static_methods.next_id())
    }

    pub fn next_builtin(&mut self) -> BuiltinId {
        BuiltinId(self.builtins.next_id())
    }

    pub fn next_synthesized(&mut self) -> SynthesizedId {
        SynthesizedId(self.synthesized.next_id())
    }
}
