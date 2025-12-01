use crate::{compiling::module::ModuleId, id_generator::IDGenerator, ir::ir_error::IRError};
use rustc_hash::FxHashMap;
use std::{cell::RefCell, fmt::Display, str::FromStr};

thread_local! {
    static SYMBOL_NAMES: RefCell<Option<FxHashMap<Symbol, String>>> = const { RefCell::new(None) };
}

/// RAII guard that clears symbol names on drop
pub struct SymbolDisplayContext;

impl Drop for SymbolDisplayContext {
    fn drop(&mut self) {
        SYMBOL_NAMES.with(|cell| cell.borrow_mut().take());
    }
}

/// Set symbol names for Display. Returns guard that clears on drop.
pub fn set_symbol_names(names: FxHashMap<Symbol, String>) -> SymbolDisplayContext {
    SYMBOL_NAMES.with(|cell| *cell.borrow_mut() = Some(names));
    SymbolDisplayContext
}

fn lookup_symbol_name(sym: &Symbol) -> Option<String> {
    SYMBOL_NAMES.with(|cell| cell.borrow().as_ref().and_then(|map| map.get(sym).cloned()))
}

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
                    "{}({}:{:?})",
                    stringify!($case),
                    self.module_id,
                    self.local_id
                )
            }
        }

        impl $ty {
            pub fn try_from(symbol: Symbol) -> Self {
                let Symbol::$case(id) = symbol else {
                    panic!("Unable to get {} from {symbol:?}", stringify!($ty));
                };

                id
            }

            pub fn new(module_id: ModuleId, local_id: u32) -> Self {
                Self {
                    module_id,
                    local_id,
                }
            }

            pub fn import(self, module_id: ModuleId) -> Self {
                if matches!(module_id, ModuleId::Core | ModuleId::Builtin) {
                    return self;
                }

                if matches!(self.module_id, ModuleId::Core | ModuleId::Builtin) {
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
#[repr(u8)]
pub enum Symbol {
    Struct(StructId),
    Enum(EnumId),
    TypeAlias(TypeAliasId),
    TypeParameter(TypeParameterId),
    Global(GlobalId),
    DeclaredLocal(DeclaredLocalId),
    PatternBindLocal(PatternBindLocalId),
    ParamLocal(ParamLocalId),
    Builtin(BuiltinId),
    Property(PropertyId),
    Synthesized(SynthesizedId),
    InstanceMethod(InstanceMethodId),
    Initializer(InitializerId),
    StaticMethod(StaticMethodId),
    Variant(VariantId),
    Protocol(ProtocolId),
    AssociatedType(AssociatedTypeId),
    MethodRequirement(MethodRequirementId),
}

impl std::fmt::Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Symbol::Int => write!(f, "Int"),
            Symbol::Float => write!(f, "Float"),
            Symbol::Bool => write!(f, "Bool"),
            Symbol::Void => write!(f, "Void"),
            Symbol::RawPtr => write!(f, "RawPtr"),
            Symbol::Byte => write!(f, "Byte"),
            Symbol::Struct(type_id) => write!(f, "@Struct({type_id:?})"),
            Symbol::Enum(type_id) => write!(f, "@Enum({type_id:?})"),
            Symbol::TypeAlias(type_id) => write!(f, "@TypeAlias({type_id:?})"),
            Symbol::TypeParameter(id) => write!(f, "@TypeParameter({id})"),
            Symbol::Global(id) => write!(f, "@Global({id})"),
            Symbol::DeclaredLocal(id) => write!(f, "@DeclaredLocal({id})"),
            Symbol::PatternBindLocal(id) => write!(f, "@PatternBindLocal({id})"),
            Symbol::ParamLocal(id) => write!(f, "@ParamLocal({id})"),
            Symbol::Builtin(id) => write!(f, "@Builtin({id})"),
            Symbol::Property(id) => write!(f, "@Property({id})"),
            Symbol::Synthesized(id) => write!(f, "@Synthesized({id})"),
            Symbol::InstanceMethod(id) => write!(f, "@InstanceMethod({id})"),
            Symbol::Initializer(id) => write!(f, "@Initializer({id})"),
            Symbol::StaticMethod(id) => write!(f, "@StaticMethod({id})"),
            Symbol::Variant(id) => write!(f, "@Variant({id})"),
            Symbol::Protocol(id) => write!(f, "@Protocol({id})"),
            Symbol::AssociatedType(id) => write!(f, "@AssociatedType({id})"),
            Symbol::MethodRequirement(id) => write!(f, "@MethodRequirement({id})"),
        }
    }
}

#[allow(non_upper_case_globals)]
impl Symbol {
    pub const Int: Symbol = Symbol::Builtin(BuiltinId {
        module_id: ModuleId::Builtin,
        local_id: 1,
    });
    pub const Float: Symbol = Symbol::Builtin(BuiltinId {
        module_id: ModuleId::Builtin,
        local_id: 2,
    });
    pub const Bool: Symbol = Symbol::Builtin(BuiltinId {
        module_id: ModuleId::Builtin,
        local_id: 3,
    });
    pub const Void: Symbol = Symbol::Builtin(BuiltinId {
        module_id: ModuleId::Builtin,
        local_id: 4,
    });
    pub const IR: Symbol = Symbol::Builtin(BuiltinId {
        module_id: ModuleId::Builtin,
        local_id: 5,
    });
    pub const PRINT: Symbol = Symbol::Builtin(BuiltinId {
        module_id: ModuleId::Builtin,
        local_id: 6,
    });
    pub const RawPtr: Symbol = Symbol::Builtin(BuiltinId {
        module_id: ModuleId::Builtin,
        local_id: 7,
    });
    pub const Byte: Symbol = Symbol::Builtin(BuiltinId {
        module_id: ModuleId::Builtin,
        local_id: 8,
    });

    pub const String: Symbol = Symbol::Struct(StructId {
        module_id: ModuleId::Core,
        local_id: 2,
    });

    #[allow(clippy::expect_used)]
    pub fn from_bytes(bytes: &[u8; 8]) -> Symbol {
        let discriminant = bytes[0];
        let local_id = u32::from_le_bytes(bytes[1..5].try_into().expect("did not get byte array"));
        let module_id = ModuleId(u16::from_le_bytes(
            bytes[5..7].try_into().expect("did not get byte array"),
        ));

        match discriminant {
            0 => Symbol::Struct(StructId {
                module_id,
                local_id,
            }),
            1 => Symbol::Enum(EnumId {
                module_id,
                local_id,
            }),
            2 => Symbol::TypeAlias(TypeAliasId {
                module_id,
                local_id,
            }),
            3 => Symbol::TypeParameter(TypeParameterId(local_id)),
            4 => Symbol::Global(GlobalId {
                module_id,
                local_id,
            }),
            5 => Symbol::DeclaredLocal(DeclaredLocalId(local_id)),
            6 => Symbol::PatternBindLocal(PatternBindLocalId(local_id)),
            7 => Symbol::ParamLocal(ParamLocalId(local_id)),
            8 => Symbol::Builtin(BuiltinId {
                module_id,
                local_id,
            }),
            9 => Symbol::Property(PropertyId {
                module_id,
                local_id,
            }),
            10 => Symbol::Synthesized(SynthesizedId {
                module_id,
                local_id,
            }),
            11 => Symbol::InstanceMethod(InstanceMethodId {
                module_id,
                local_id,
            }),
            12 => Symbol::Initializer(InitializerId {
                module_id,
                local_id,
            }),
            13 => Symbol::StaticMethod(StaticMethodId {
                module_id,
                local_id,
            }),
            14 => Symbol::Variant(VariantId {
                module_id,
                local_id,
            }),
            15 => Symbol::Protocol(ProtocolId {
                module_id,
                local_id,
            }),
            16 => Symbol::AssociatedType(AssociatedTypeId {
                module_id,
                local_id,
            }),
            17 => Symbol::MethodRequirement(MethodRequirementId {
                module_id,
                local_id,
            }),
            _ => unreachable!("Invalid Symbol discriminant: {}", discriminant),
        }
    }

    pub fn as_bytes(&self) -> [u8; 8] {
        let mut res = [0; 8];
        let mut c = vec![self.discriminant()];
        c.extend(self.inner_bytes());
        c.extend(if let Some(id) = self.module_id() {
            id.0.to_le_bytes()
        } else {
            [0, 0]
        });
        res.copy_from_slice(&c);
        res
    }

    fn discriminant(&self) -> u8 {
        // SAFETY: Because `Self` is marked `repr(u8)`, its layout is a `repr(C)` `union`
        // between `repr(C)` structs, each of which has the `u8` discriminant as its first
        // field, so we can read the discriminant without offsetting the pointer.
        unsafe { *<*const _>::from(self).cast::<u8>() }
    }

    fn inner_bytes(&self) -> Vec<u8> {
        match self {
            Symbol::Struct(v) => v.local_id.to_le_bytes(),
            Symbol::Enum(v) => v.local_id.to_le_bytes(),
            Symbol::TypeAlias(v) => v.local_id.to_le_bytes(),
            Symbol::TypeParameter(v) => v.0.to_le_bytes(),
            Symbol::Global(v) => v.local_id.to_le_bytes(),
            Symbol::DeclaredLocal(v) => v.0.to_le_bytes(),
            Symbol::PatternBindLocal(v) => v.0.to_le_bytes(),
            Symbol::ParamLocal(v) => v.0.to_le_bytes(),
            Symbol::Builtin(v) => v.local_id.to_le_bytes(),
            Symbol::Property(v) => v.local_id.to_le_bytes(),
            Symbol::Synthesized(v) => v.local_id.to_le_bytes(),
            Symbol::InstanceMethod(v) => v.local_id.to_le_bytes(),
            Symbol::Initializer(v) => v.local_id.to_le_bytes(),
            Symbol::StaticMethod(v) => v.local_id.to_le_bytes(),
            Symbol::Variant(v) => v.local_id.to_le_bytes(),
            Symbol::Protocol(v) => v.local_id.to_le_bytes(),
            Symbol::AssociatedType(v) => v.local_id.to_le_bytes(),
            Symbol::MethodRequirement(v) => v.local_id.to_le_bytes(),
        }
        .to_vec()
    }

    pub fn module_id(&self) -> Option<ModuleId> {
        let module_id = match self {
            Symbol::Struct(StructId { module_id, .. })
            | Symbol::Global(GlobalId { module_id, .. })
            | Symbol::Builtin(BuiltinId { module_id, .. })
            | Symbol::Property(PropertyId { module_id, .. })
            | Symbol::Synthesized(SynthesizedId { module_id, .. })
            | Symbol::InstanceMethod(InstanceMethodId { module_id, .. })
            | Symbol::MethodRequirement(MethodRequirementId { module_id, .. })
            | Symbol::Initializer(InitializerId { module_id, .. })
            | Symbol::StaticMethod(StaticMethodId { module_id, .. })
            | Symbol::Variant(VariantId { module_id, .. })
            | Symbol::Protocol(ProtocolId { module_id, .. })
            | Symbol::AssociatedType(AssociatedTypeId { module_id, .. })
            | Symbol::Enum(EnumId { module_id, .. }) => module_id,
            _ => {
                tracing::warn!("looking up module id for non-module symbol: {self:?}");
                return None;
            }
        };

        Some(*module_id)
    }

    pub fn external_module_id(&self) -> Option<ModuleId> {
        let module_id = match self {
            Symbol::Struct(StructId { module_id, .. })
            | Symbol::Global(GlobalId { module_id, .. })
            | Symbol::Builtin(BuiltinId { module_id, .. })
            | Symbol::Property(PropertyId { module_id, .. })
            | Symbol::Synthesized(SynthesizedId { module_id, .. })
            | Symbol::InstanceMethod(InstanceMethodId { module_id, .. })
            | Symbol::MethodRequirement(MethodRequirementId { module_id, .. })
            | Symbol::Initializer(InitializerId { module_id, .. })
            | Symbol::StaticMethod(StaticMethodId { module_id, .. })
            | Symbol::Variant(VariantId { module_id, .. })
            | Symbol::Protocol(ProtocolId { module_id, .. })
            | Symbol::AssociatedType(AssociatedTypeId { module_id, .. })
            | Symbol::Enum(EnumId { module_id, .. }) => module_id,
            _ => {
                tracing::warn!("looking up module id for non-module symbol: {self:?}");
                return None;
            }
        };

        match *module_id {
            ModuleId::Current | ModuleId::Builtin => None,
            _ => Some(*module_id),
        }
    }

    pub fn import(self, module_id: ModuleId) -> Symbol {
        match self {
            Symbol::Struct(type_id) => Symbol::Struct(type_id.import(module_id)),
            Symbol::Enum(type_id) => Symbol::Enum(type_id.import(module_id)),
            Symbol::TypeAlias(type_id) => Symbol::TypeAlias(type_id.import(module_id)),
            Symbol::Global(global_id) => Symbol::Global(global_id.import(module_id)),
            Symbol::Builtin(builtin_id) => Symbol::Builtin(builtin_id.import(module_id)),
            Symbol::Property(property_id) => Symbol::Property(property_id.import(module_id)),
            Symbol::Synthesized(synthesized_id) => {
                Symbol::Synthesized(synthesized_id.import(module_id))
            }
            Symbol::InstanceMethod(instance_method_id) => {
                Symbol::InstanceMethod(instance_method_id.import(module_id))
            }
            Symbol::Initializer(instance_method_id) => {
                Symbol::Initializer(instance_method_id.import(module_id))
            }
            Symbol::StaticMethod(static_method_id) => {
                Symbol::StaticMethod(static_method_id.import(module_id))
            }
            Symbol::Variant(variant_id) => Symbol::Variant(variant_id.import(module_id)),
            Symbol::Protocol(protocol_id) => Symbol::Protocol(protocol_id.import(module_id)),
            Symbol::AssociatedType(associated_type_id) => {
                Symbol::AssociatedType(associated_type_id.import(module_id))
            }
            Symbol::MethodRequirement(method_requirement_id) => {
                Symbol::MethodRequirement(method_requirement_id.import(module_id))
            }
            _ => unreachable!("{self:?} not exportable"),
        }
    }

    pub fn current(self) -> Symbol {
        match self {
            Symbol::Struct(type_id) => Symbol::Struct(type_id.import(ModuleId::Current)),
            Symbol::Enum(type_id) => Symbol::Enum(type_id.import(ModuleId::Current)),
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
            Symbol::Initializer(instance_method_id) => {
                Symbol::Initializer(instance_method_id.import(ModuleId::Current))
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
            Symbol::MethodRequirement(method_requirement_id) => {
                Symbol::MethodRequirement(method_requirement_id.import(ModuleId::Current))
            }
            _ => unreachable!("{self:?} not exportable"),
        }
    }
}

// Cross-module IDs (include ModuleId)
impl_module_symbol_id!(Struct, StructId);
impl_module_symbol_id!(Enum, EnumId);
impl_module_symbol_id!(TypeAlias, TypeAliasId);
impl_module_symbol_id!(Global, GlobalId);
impl_module_symbol_id!(Protocol, ProtocolId);
impl_module_symbol_id!(Variant, VariantId);
impl_module_symbol_id!(Property, PropertyId);
impl_module_symbol_id!(InstanceMethod, InstanceMethodId);
impl_module_symbol_id!(Initializer, InitializerId);
impl_module_symbol_id!(MethodRequirement, MethodRequirementId);
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
        if let Some(name) = lookup_symbol_name(self) {
            return write!(f, "{}", name);
        }

        match self {
            Symbol::Struct(type_id) => write!(f, "{}", type_id),
            Symbol::Enum(type_id) => write!(f, "{}", type_id),
            Symbol::TypeAlias(type_id) => write!(f, "{}", type_id),
            Symbol::TypeParameter(type_parameter_id) => write!(f, "{}", type_parameter_id),
            Symbol::Global(global_id) => write!(f, "{}", global_id),
            Symbol::DeclaredLocal(declared_local_id) => write!(f, "{}", declared_local_id),
            Symbol::PatternBindLocal(pattern_bind_local_id) => {
                write!(f, "{}", pattern_bind_local_id)
            }
            Symbol::ParamLocal(id) => write!(f, "{}", id),
            Symbol::Builtin(id) => write!(f, "{}", id),
            Symbol::Property(id) => write!(f, "{}", id),
            Symbol::Synthesized(id) => write!(f, "{}", id),
            Symbol::InstanceMethod(id) => write!(f, "{}", id),
            Symbol::Initializer(id) => write!(f, "{}", id),
            Symbol::StaticMethod(static_method_id) => write!(f, "{}", static_method_id),
            Symbol::Variant(variant_id) => write!(f, "{}", variant_id),
            Symbol::Protocol(protocol_id) => write!(f, "{}", protocol_id),
            Symbol::AssociatedType(associated_type_id) => write!(f, "{}", associated_type_id),
            Symbol::MethodRequirement(id) => write!(f, "{}", id),
        }
    }
}

impl FromStr for Symbol {
    type Err = IRError;
    fn from_str(_s: &str) -> Result<Self, Self::Err> {
        Err(IRError::CouldNotParse("todo".into()))
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
    initializers: IDGenerator,
    method_requirements: IDGenerator,
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
    pub fn next_struct(&mut self, module_id: ModuleId) -> StructId {
        StructId::new(module_id, self.decls.next_id())
    }

    pub fn next_type_alias(&mut self, module_id: ModuleId) -> TypeAliasId {
        TypeAliasId::new(module_id, self.decls.next_id())
    }

    pub fn next_enum(&mut self, module_id: ModuleId) -> EnumId {
        EnumId::new(module_id, self.decls.next_id())
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

    pub fn next_initializer(&mut self, module_id: ModuleId) -> InitializerId {
        InitializerId::new(module_id, self.initializers.next_id())
    }

    pub fn next_method_requirement(&mut self, module_id: ModuleId) -> MethodRequirementId {
        MethodRequirementId::new(module_id, self.method_requirements.next_id())
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
