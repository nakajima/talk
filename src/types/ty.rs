use std::fmt::Display;

use crate::types::{
    row::{Label, Row},
    type_var::TypeVar,
};

#[derive(Debug, Clone, Hash, Copy, PartialEq, Eq)]
pub enum Primitive {
    Void,
    Int,
    Float,
    Bool,
    Pointer,
    Byte,
}

impl Display for Primitive {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Ty {
    Primitive(Primitive),
    Func { params: Vec<Ty>, returns: Box<Ty> },
    Product(Row),
    Var(TypeVar),
    Sum(Row),
    Label(Label, Box<Self>),
}

impl Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty::Primitive(primitive) => write!(f, "{primitive:?}"),
            _ => write!(f, "{self:?}"),
        }
    }
}

#[allow(non_upper_case_globals)]
impl Ty {
    pub const Int: Ty = Ty::Primitive(Primitive::Int);
    pub const Float: Ty = Ty::Primitive(Primitive::Float);
    pub const Bool: Ty = Ty::Primitive(Primitive::Bool);
    pub const Byte: Ty = Ty::Primitive(Primitive::Byte);
    pub const Pointer: Ty = Ty::Primitive(Primitive::Pointer);
    pub const Void: Ty = Ty::Primitive(Primitive::Void);

    pub fn optional(&self) -> Ty {
        self.clone() // TODO:
    }

    pub fn type_vars(&self) -> Vec<TypeVar> {
        match self {
            Self::Var(type_var) => vec![*type_var],
            _ => vec![],
        }
    }
}
