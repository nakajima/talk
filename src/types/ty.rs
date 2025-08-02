use crate::types::{
    row::{Label, Row},
    type_var::TypeVar,
};

#[derive(Debug, Clone, PartialEq)]
pub enum Primitive {
    Void,
    Int,
    Float,
    Bool,
    Pointer,
    Byte,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Ty {
    Primitive(Primitive),
    Product(Row),
    Var(TypeVar),
    Sum(Row),
    Label(Label, Box<Self>),
}

impl Ty {
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
