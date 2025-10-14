use std::fmt::Display;

use crate::{compiling::module::ModuleId, id_generator::IDGenerator};

// Macro for cross-module IDs (with ModuleId)
macro_rules! impl_module_symbol_id {
    ($case:ident, $ty: ident) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $ty {
            pub module_id: ModuleId,
            pub local_id: u32,
        }

        impl std::fmt::Display for $ty {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(
                    f,
                    "{:?}({:?}:{:?})",
                    stringify!($ty),
                    self.module_id,
                    self.local_id
                )
            }
        }

        impl $ty {
            pub fn new(module_id: ModuleId, local_id: u32) -> Self {
                Self {
                    module_id,
                    local_id,
                }
            }

            pub fn import(self, module_id: ModuleId) -> Self {
                if matches!(module_id, ModuleId::Core | ModuleId::Prelude) {
                    return self;
                }

                Self {
                    module_id,
                    local_id: self.local_id,
                }
            }
        }

        // For tests and backwards compatibility
        impl From<u32> for $ty {
            fn from(local_id: u32) -> Self {
                Self {
                    module_id: ModuleId::Current,
                    local_id,
                }
            }
        }

        impl From<Symbol> for $ty {
            fn from(value: Symbol) -> $ty {
                if let Symbol::$case(value) = value {
                    return value;
                }

                panic!("unable to convert from symbol: {:?}", value);
            }
        }

        impl From<$ty> for Symbol {
            fn from(value: $ty) -> Symbol {
                Symbol::$case(value)
            }
        }

        impl From<&$ty> for Symbol {
            fn from(value: &$ty) -> Symbol {
                Symbol::$case(*value)
            }
        }
    };
}

// Macro for local-only IDs (simple u32 wrapper)
macro_rules! impl_local_symbol_id {
    ($case:ident, $ty: ident) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $ty(pub u32);

        impl std::fmt::Display for $ty {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{:?}", self)
            }
        }

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

        impl From<&$ty> for Symbol {
            fn from(value: &$ty) -> Symbol {
                Symbol::$case(*value)
            }
        }
    };
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
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
    Protocol(ProtocolId),
    AssociatedType(AssociatedTypeId),
}

impl std::fmt::Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Symbol::Type(type_id) => write!(f, "@Type({type_id:?})"),
            Symbol::TypeParameter(id) => write!(f, "@TypeParameter({id})"),
            Symbol::Global(id) => write!(f, "@Global({id})"),
            Symbol::DeclaredLocal(id) => write!(f, "@DeclaredLocal({id})"),
            Symbol::PatternBindLocal(id) => write!(f, "@PatternBindLocal({id})"),
            Symbol::ParamLocal(id) => write!(f, "@ParamLocal({id})"),
            Symbol::Builtin(id) => write!(f, "@Builtin({id})"),
            Symbol::Property(id) => write!(f, "@Property({id})"),
            Symbol::Synthesized(id) => write!(f, "@Synthesized({id})"),
            Symbol::InstanceMethod(id) => write!(f, "@InstanceMethod({id})"),
            Symbol::StaticMethod(id) => write!(f, "@StaticMethod({id})"),
            Symbol::Variant(id) => write!(f, "@Variant({id})"),
            Symbol::Protocol(id) => write!(f, "@Protocol({id})"),
            Symbol::AssociatedType(id) => write!(f, "@AssociatedType({id})"),
        }
    }
}

#[allow(non_upper_case_globals)]
impl Symbol {
    pub const Int: Symbol = Symbol::Builtin(BuiltinId {
        module_id: ModuleId::Prelude,
        local_id: 1,
    });
    pub const Float: Symbol = Symbol::Builtin(BuiltinId {
        module_id: ModuleId::Prelude,
        local_id: 2,
    });
    pub const Bool: Symbol = Symbol::Builtin(BuiltinId {
        module_id: ModuleId::Prelude,
        local_id: 3,
    });
    pub const Void: Symbol = Symbol::Builtin(BuiltinId {
        module_id: ModuleId::Prelude,
        local_id: 4,
    });
    pub const IR: Symbol = Symbol::Builtin(BuiltinId {
        module_id: ModuleId::Prelude,
        local_id: 5,
    });

    pub fn module_id(&self) -> Option<ModuleId> {
        let module_id = match self {
            Symbol::Type(TypeId { module_id, .. })
            | Symbol::Global(GlobalId { module_id, .. })
            | Symbol::Builtin(BuiltinId { module_id, .. })
            | Symbol::Property(PropertyId { module_id, .. })
            | Symbol::Synthesized(SynthesizedId { module_id, .. })
            | Symbol::InstanceMethod(InstanceMethodId { module_id, .. })
            | Symbol::StaticMethod(StaticMethodId { module_id, .. })
            | Symbol::Variant(VariantId { module_id, .. })
            | Symbol::Protocol(ProtocolId { module_id, .. })
            | Symbol::AssociatedType(AssociatedTypeId { module_id, .. }) => module_id,
            _ => return None,
        };

        match module_id {
            ModuleId::Current | ModuleId::Prelude => None,
            _ => Some(*module_id),
        }
    }

    pub fn import(self, module_id: ModuleId) -> Symbol {
        match self {
            Symbol::Type(type_id) => Symbol::Type(type_id.import(module_id)),
            Symbol::Global(global_id) => Symbol::Global(global_id.import(module_id)),
            Symbol::Builtin(builtin_id) => Symbol::Builtin(builtin_id.import(module_id)),
            Symbol::Property(property_id) => Symbol::Property(property_id.import(module_id)),
            Symbol::Synthesized(synthesized_id) => {
                Symbol::Synthesized(synthesized_id.import(module_id))
            }
            Symbol::InstanceMethod(instance_method_id) => {
                Symbol::InstanceMethod(instance_method_id.import(module_id))
            }
            Symbol::StaticMethod(static_method_id) => {
                Symbol::StaticMethod(static_method_id.import(module_id))
            }
            Symbol::Variant(variant_id) => Symbol::Variant(variant_id.import(module_id)),
            Symbol::Protocol(protocol_id) => Symbol::Protocol(protocol_id.import(module_id)),
            Symbol::AssociatedType(associated_type_id) => {
                Symbol::AssociatedType(associated_type_id.import(module_id))
            }
            _ => unreachable!("{self:?} not exportable"),
        }
    }

    pub fn current(self) -> Symbol {
        match self {
            Symbol::Type(type_id) => Symbol::Type(type_id.import(ModuleId::Current)),
            Symbol::Global(global_id) => Symbol::Global(global_id.import(ModuleId::Current)),
            Symbol::Builtin(builtin_id) => Symbol::Builtin(builtin_id.import(ModuleId::Current)),
            Symbol::Property(property_id) => {
                Symbol::Property(property_id.import(ModuleId::Current))
            }
            Symbol::Synthesized(synthesized_id) => {
                Symbol::Synthesized(synthesized_id.import(ModuleId::Current))
            }
            Symbol::InstanceMethod(instance_method_id) => {
                Symbol::InstanceMethod(instance_method_id.import(ModuleId::Current))
            }
            Symbol::StaticMethod(static_method_id) => {
                Symbol::StaticMethod(static_method_id.import(ModuleId::Current))
            }
            Symbol::Variant(variant_id) => Symbol::Variant(variant_id.import(ModuleId::Current)),
            Symbol::Protocol(protocol_id) => {
                Symbol::Protocol(protocol_id.import(ModuleId::Current))
            }
            Symbol::AssociatedType(associated_type_id) => {
                Symbol::AssociatedType(associated_type_id.import(ModuleId::Current))
            }
            _ => unreachable!("{self:?} not exportable"),
        }
    }
}

// Cross-module IDs (include ModuleId)
impl_module_symbol_id!(Type, TypeId);
impl_module_symbol_id!(Global, GlobalId);
impl_module_symbol_id!(Protocol, ProtocolId);
impl_module_symbol_id!(Variant, VariantId);
impl_module_symbol_id!(Property, PropertyId);
impl_module_symbol_id!(InstanceMethod, InstanceMethodId);
impl_module_symbol_id!(StaticMethod, StaticMethodId);
impl_module_symbol_id!(AssociatedType, AssociatedTypeId);
impl_module_symbol_id!(Builtin, BuiltinId);
impl_module_symbol_id!(Synthesized, SynthesizedId);

// Local-only IDs (simple u32)
impl_local_symbol_id!(TypeParameter, TypeParameterId);
impl_local_symbol_id!(DeclaredLocal, DeclaredLocalId);
impl_local_symbol_id!(ParamLocal, ParamLocalId);
impl_local_symbol_id!(PatternBindLocal, PatternBindLocalId);

impl Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Symbol::Type(type_id) => write!(f, "S_{}", type_id),
            Symbol::TypeParameter(type_parameter_id) => write!(f, "S_{}", type_parameter_id),
            Symbol::Global(global_id) => write!(f, "S_{}", global_id),
            Symbol::DeclaredLocal(declared_local_id) => write!(f, "S_{}", declared_local_id),
            Symbol::PatternBindLocal(pattern_bind_local_id) => {
                write!(f, "S_{}", pattern_bind_local_id)
            }
            Symbol::ParamLocal(param_local_id) => write!(f, "S_{}", param_local_id),
            Symbol::Builtin(builtin_id) => write!(f, "S_{}", builtin_id),
            Symbol::Property(property_id) => write!(f, "S_{}", property_id),
            Symbol::Synthesized(synthesized_id) => write!(f, "S_{}", synthesized_id),
            Symbol::InstanceMethod(instance_method_id) => write!(f, "S_{}", instance_method_id),
            Symbol::StaticMethod(static_method_id) => write!(f, "S_{}", static_method_id),
            Symbol::Variant(variant_id) => write!(f, "S_{}", variant_id),
            Symbol::Protocol(protocol_id) => write!(f, "S_{}", protocol_id),
            Symbol::AssociatedType(associated_type_id) => write!(f, "S_{}", associated_type_id),
        }
    }
}

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
    protocols: IDGenerator,
}

impl Symbols {
    // Cross-module IDs (need ModuleId)
    pub fn next_type(&mut self, module_id: ModuleId) -> TypeId {
        TypeId::new(module_id, self.decls.next_id())
    }

    pub fn next_property(&mut self, module_id: ModuleId) -> PropertyId {
        PropertyId::new(module_id, self.properties.next_id())
    }

    pub fn next_global(&mut self, module_id: ModuleId) -> GlobalId {
        GlobalId::new(module_id, self.values.next_id())
    }

    pub fn next_associated_type(&mut self, module_id: ModuleId) -> AssociatedTypeId {
        AssociatedTypeId::new(module_id, self.associated_types.next_id())
    }

    pub fn next_variant(&mut self, module_id: ModuleId) -> VariantId {
        VariantId::new(module_id, self.variants.next_id())
    }

    pub fn next_instance_method(&mut self, module_id: ModuleId) -> InstanceMethodId {
        InstanceMethodId::new(module_id, self.instance_methods.next_id())
    }

    pub fn next_static_method(&mut self, module_id: ModuleId) -> StaticMethodId {
        StaticMethodId::new(module_id, self.static_methods.next_id())
    }

    pub fn next_builtin(&mut self, module_id: ModuleId) -> BuiltinId {
        BuiltinId::new(module_id, self.builtins.next_id())
    }

    pub fn next_protocol(&mut self, module_id: ModuleId) -> ProtocolId {
        ProtocolId::new(module_id, self.protocols.next_id())
    }

    // Local-only IDs (no ModuleId needed)
    pub fn next_type_parameter(&mut self) -> TypeParameterId {
        TypeParameterId(self.type_parameters.next_id())
    }

    pub fn next_param(&mut self) -> ParamLocalId {
        ParamLocalId(self.params.next_id())
    }

    pub fn next_pattern_bind(&mut self) -> PatternBindLocalId {
        PatternBindLocalId(self.pattern_binds.next_id())
    }

    pub fn next_local(&mut self) -> DeclaredLocalId {
        DeclaredLocalId(self.locals.next_id())
    }

    pub fn next_synthesized(&mut self, module_id: ModuleId) -> SynthesizedId {
        SynthesizedId::new(module_id, self.synthesized.next_id())
    }
}
