use rustc_hash::FxHashMap;

use crate::{
    ast::AST,
    id_generator::IDGenerator,
    name::Name,
    name_resolution::{name_resolver::NameResolved, symbol::DeclId},
    node_id::NodeID,
    node_kinds::{generic_decl::GenericDecl, type_annotation::TypeAnnotation},
    types::{
        fields::TypeFields,
        kind::Kind,
        ty::{Primitive, Ty},
        type_header_decl_pass::TypeHeaderDeclPass,
    },
};

#[derive(Debug, PartialEq, Clone)]
pub enum ASTTyRepr {
    Annotated(TypeAnnotation), // already resolved names
    Generic(GenericDecl),
    Hole(NodeID), // no annotation; to be inferred later
}

pub trait TypingPhase: std::fmt::Debug + PartialEq {
    type TyPhase: std::fmt::Debug + PartialEq + Clone;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeDefKind {
    Struct,
    Enum,
    Protocol,
    Primitive(Primitive),
}

#[derive(Debug, PartialEq, Eq, Default)]
pub struct Raw {}
impl TypingPhase for Raw {
    type TyPhase = ASTTyRepr;
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeDef<Phase: TypingPhase> {
    pub name: Name,
    pub kind: Kind,
    pub def: TypeDefKind,
    pub generics: Vec<Phase::TyPhase>,
    pub fields: TypeFields<Phase>,
}

#[derive(Debug, Default)]
pub struct TypeSession<Phase: TypingPhase = Raw> {
    pub type_constructors: FxHashMap<DeclId, TypeDef<Phase>>,
    pub protocols: FxHashMap<DeclId, TypeDef<Phase>>,
    pub type_env: FxHashMap<DeclId, Ty>,
    pub synthsized_ids: IDGenerator,
}

pub struct Typed {}

impl<Phase: TypingPhase> TypeSession<Phase> {
    pub fn drive(ast: &AST<NameResolved>) -> TypeSession<Raw> {
        let mut session = TypeSession::<Raw>::default();
        TypeHeaderDeclPass::drive(&mut session, ast);
        session
    }
}
