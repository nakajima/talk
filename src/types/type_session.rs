use rustc_hash::FxHashMap;

use crate::{
    name::Name,
    name_resolution::symbol::DeclId,
    node_id::NodeID,
    node_kinds::type_annotation::TypeAnnotation,
    types::{kind::Kind, ty::Ty},
};

#[derive(Debug, PartialEq)]
pub enum TyRepr {
    Annotated(TypeAnnotation), // already resolved names
    Hole(NodeID),              // no annotation; to be inferred later
}

#[derive(Debug, PartialEq)]
pub enum TypeFieldKind {
    Property {
        is_static: bool,
        ty_repr: TyRepr,
    },
    Method {
        is_static: bool,
        params: Vec<TyRepr>,
        ret: TyRepr,
    },
    MethodRequirement {
        params: Vec<TyRepr>,
        ret: TyRepr,
    },
    Initializer {
        params: Vec<TyRepr>,
    },
    Variant {
        fields: Vec<TyRepr>,
    },
    Associated,
}

#[derive(Debug, PartialEq)]
pub struct TypeField {
    pub kind: TypeFieldKind,
    pub name: Name,
}

#[derive(Debug, PartialEq)]
pub enum TypeDefKind {
    Struct,
    Enum,
    Protocol,
}

#[derive(Debug, PartialEq)]
pub struct TypeDef {
    pub name: Name,
    pub kind: Kind,
    pub def: TypeDefKind,
    pub fields: Vec<TypeField>,
}

#[derive(Debug, Default)]
pub struct TypeSession {
    pub type_constructors: FxHashMap<DeclId, TypeDef>,
    pub type_env: FxHashMap<DeclId, Ty>,
}
