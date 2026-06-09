use rustc_hash::FxHashMap;

use crate::{
    compiling::module::ModuleId,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    types::{infer_ty::Ty, type_args::TypeArgs},
};

pub type Callees = FxHashMap<NodeID, Callee>;

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Callee {
    Function {
        symbol: Symbol,
        type_args: TypeArgs,
    },
    Initializer {
        nominal: Symbol,
        initializer: Symbol,
        type_args: TypeArgs,
    },
    Method {
        symbol: Symbol,
        self_ty: Ty,
        type_args: TypeArgs,
    },
    Variant {
        enum_symbol: Symbol,
        variant: Symbol,
        type_args: TypeArgs,
    },
    Effect {
        symbol: Symbol,
        type_args: TypeArgs,
    },
}

impl Callee {
    pub fn target_symbol(&self) -> Symbol {
        match self {
            Callee::Function { symbol, .. }
            | Callee::Method { symbol, .. }
            | Callee::Effect { symbol, .. } => *symbol,
            Callee::Initializer { initializer, .. } => *initializer,
            Callee::Variant { variant, .. } => *variant,
        }
    }

    pub fn type_args(&self) -> &TypeArgs {
        match self {
            Callee::Function { type_args, .. }
            | Callee::Initializer { type_args, .. }
            | Callee::Method { type_args, .. }
            | Callee::Variant { type_args, .. }
            | Callee::Effect { type_args, .. } => type_args,
        }
    }

    pub fn mapping(
        self,
        ty_map: &mut impl FnMut(Ty) -> Ty,
        row_map: &mut impl FnMut(crate::types::infer_row::Row) -> crate::types::infer_row::Row,
    ) -> Self {
        match self {
            Callee::Function { symbol, type_args } => Callee::Function {
                symbol,
                type_args: type_args.mapping(ty_map, row_map),
            },
            Callee::Initializer {
                nominal,
                initializer,
                type_args,
            } => Callee::Initializer {
                nominal,
                initializer,
                type_args: type_args.mapping(ty_map, row_map),
            },
            Callee::Method {
                symbol,
                self_ty,
                type_args,
            } => Callee::Method {
                symbol,
                self_ty: self_ty.mapping(ty_map, row_map),
                type_args: type_args.mapping(ty_map, row_map),
            },
            Callee::Variant {
                enum_symbol,
                variant,
                type_args,
            } => Callee::Variant {
                enum_symbol,
                variant,
                type_args: type_args.mapping(ty_map, row_map),
            },
            Callee::Effect { symbol, type_args } => Callee::Effect {
                symbol,
                type_args: type_args.mapping(ty_map, row_map),
            },
        }
    }

    pub fn import(self, module_id: ModuleId) -> Self {
        match self {
            Callee::Function { symbol, type_args } => Callee::Function {
                symbol: symbol.import(module_id),
                type_args: type_args.import(module_id),
            },
            Callee::Initializer {
                nominal,
                initializer,
                type_args,
            } => Callee::Initializer {
                nominal: nominal.import(module_id),
                initializer: initializer.import(module_id),
                type_args: type_args.import(module_id),
            },
            Callee::Method {
                symbol,
                self_ty,
                type_args,
            } => Callee::Method {
                symbol: symbol.import(module_id),
                self_ty: self_ty.import(module_id),
                type_args: type_args.import(module_id),
            },
            Callee::Variant {
                enum_symbol,
                variant,
                type_args,
            } => Callee::Variant {
                enum_symbol: enum_symbol.import(module_id),
                variant: variant.import(module_id),
                type_args: type_args.import(module_id),
            },
            Callee::Effect { symbol, type_args } => Callee::Effect {
                symbol: symbol.import(module_id),
                type_args: type_args.import(module_id),
            },
        }
    }
}
