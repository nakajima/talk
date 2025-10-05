use crate::{
    name_resolution::symbol::TypeId,
    types::{
        infer_ty::{Primitive, TypeParamId},
        row::Row,
    },
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
    Primitive(Primitive),
    Param(TypeParamId),
    Constructor {
        type_id: TypeId,
        params: Vec<Ty>,
        ret: Box<Ty>,
    },

    Func(Box<Ty>, Box<Ty>),
    Tuple(Vec<Ty>),
    Record(Box<Row>),

    // Nominal types (we look up their information from the TypeCatalog)
    Nominal {
        id: TypeId,
        type_args: Vec<Ty>,
        row: Box<Row>,
    },
}

#[allow(non_upper_case_globals)]
impl Ty {
    pub const Int: Ty = Ty::Primitive(Primitive::Int);
    pub const Float: Ty = Ty::Primitive(Primitive::Float);
    pub const Bool: Ty = Ty::Primitive(Primitive::Bool);
    pub const Void: Ty = Ty::Primitive(Primitive::Void);
}
