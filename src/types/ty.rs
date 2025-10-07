use crate::{
    compiling::module::ModuleId,
    name_resolution::symbol::{Symbol, TypeId},
    types::{infer_ty::TypeParamId, row::Row, type_session::TypeDefKind},
};

pub trait SomeType: std::fmt::Debug + PartialEq + Clone {
    fn contains_var(&self) -> bool;
}

impl SomeType for Ty {
    fn contains_var(&self) -> bool {
        false
    }
}

// Finalized type info
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Ty {
    Primitive(Symbol),
    Param(TypeParamId),
    Constructor {
        symbol: Symbol,
        params: Vec<Ty>,
        ret: Box<Ty>,
    },

    Func(Box<Ty>, Box<Ty>),
    Tuple(Vec<Ty>),
    Record(Box<Row>),

    // Nominal types (we look up their information from the TypeCatalog)
    Nominal {
        symbol: Symbol,
        type_args: Vec<Ty>,
        row: Box<Row>,
    },
}

#[allow(non_upper_case_globals)]
#[allow(non_snake_case)]
impl Ty {
    pub const Int: Ty = Ty::Primitive(Symbol::Int);
    pub const Float: Ty = Ty::Primitive(Symbol::Float);
    pub const Bool: Ty = Ty::Primitive(Symbol::Bool);
    pub const Void: Ty = Ty::Primitive(Symbol::Void);
    pub fn String() -> Ty {
        Ty::Nominal {
            symbol: Symbol::Type(TypeId {
                module_id: ModuleId::Core,
                local_id: 2,
            }),
            type_args: vec![],
            row: Box::new(Row::Empty(TypeDefKind::Struct)),
        }
    }
    pub fn Array(t: Ty) -> Ty {
        Ty::Nominal {
            symbol: Symbol::Type(TypeId {
                module_id: ModuleId::Core,
                local_id: 3,
            }),
            type_args: vec![t],
            row: Box::new(Row::Empty(TypeDefKind::Struct)),
        }
    }
}
