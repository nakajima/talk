//! Compiler-facing VM module. Runtime bytecode data structures and the
//! interpreter live in `talk-runtime`; this crate keeps the scheduler that
//! lowers lambda-G into those runtime structures.

pub use talk_runtime::{Chunk, CmpOp, Insn, IoOp, MemKind, Module, Styles, bytecode, interp, io, symbol};

pub mod schedule;

#[cfg(test)]
pub mod vm_tests;

pub fn runtime_symbol(symbol: crate::name_resolution::symbol::Symbol) -> talk_runtime::symbol::Symbol {
    use crate::name_resolution::symbol::Symbol;
    use talk_runtime::symbol::{LocalSymbolId, ModuleId, ModuleSymbolId, Symbol as RtSymbol};

    fn module_id(id: crate::compiling::module::ModuleId) -> ModuleId {
        ModuleId(id.0)
    }

    fn module_symbol(
        module_id_value: crate::compiling::module::ModuleId,
        local_id: u32,
    ) -> ModuleSymbolId {
        ModuleSymbolId::new(module_id(module_id_value), local_id)
    }

    match symbol {
        Symbol::Struct(id) => RtSymbol::Struct(module_symbol(id.module_id, id.local_id)),
        Symbol::Enum(id) => RtSymbol::Enum(module_symbol(id.module_id, id.local_id)),
        Symbol::TypeAlias(id) => RtSymbol::TypeAlias(module_symbol(id.module_id, id.local_id)),
        Symbol::TypeParameter(id) => {
            RtSymbol::TypeParameter(module_symbol(id.module_id, id.local_id))
        }
        Symbol::Global(id) => RtSymbol::Global(module_symbol(id.module_id, id.local_id)),
        Symbol::DeclaredLocal(id) => RtSymbol::DeclaredLocal(LocalSymbolId(id.0)),
        Symbol::PatternBindLocal(id) => RtSymbol::PatternBindLocal(LocalSymbolId(id.0)),
        Symbol::ParamLocal(id) => RtSymbol::ParamLocal(LocalSymbolId(id.0)),
        Symbol::Builtin(id) => RtSymbol::Builtin(module_symbol(id.module_id, id.local_id)),
        Symbol::Property(id) => RtSymbol::Property(module_symbol(id.module_id, id.local_id)),
        Symbol::Synthesized(id) => RtSymbol::Synthesized(module_symbol(id.module_id, id.local_id)),
        Symbol::InstanceMethod(id) => {
            RtSymbol::InstanceMethod(module_symbol(id.module_id, id.local_id))
        }
        Symbol::Initializer(id) => RtSymbol::Initializer(module_symbol(id.module_id, id.local_id)),
        Symbol::StaticMethod(id) => {
            RtSymbol::StaticMethod(module_symbol(id.module_id, id.local_id))
        }
        Symbol::Variant(id) => RtSymbol::Variant(module_symbol(id.module_id, id.local_id)),
        Symbol::Protocol(id) => RtSymbol::Protocol(module_symbol(id.module_id, id.local_id)),
        Symbol::AssociatedType(id) => {
            RtSymbol::AssociatedType(module_symbol(id.module_id, id.local_id))
        }
        Symbol::MethodRequirement(id) => {
            RtSymbol::MethodRequirement(module_symbol(id.module_id, id.local_id))
        }
        Symbol::Effect(id) => RtSymbol::Effect(module_symbol(id.module_id, id.local_id)),
        Symbol::Main => RtSymbol::Main,
        Symbol::Library => RtSymbol::Library,
    }
}
