use indexmap::IndexMap;
use rustc_hash::FxHashMap;

use crate::{
    ast::AST,
    id_generator::IDGenerator,
    name::Name,
    name_resolution::{name_resolver::NameResolved, symbol::DeclId},
    node_id::NodeID,
    node_kinds::{generic_decl::GenericDecl, type_annotation::TypeAnnotation},
    span::Span,
    types::{fields::TypeFields, kind::Kind, ty::Ty, type_header_decl_pass::TypeHeaderDeclPass},
};

#[derive(Debug, PartialEq, Clone)]
pub enum ASTTyRepr {
    Annotated(TypeAnnotation), // already resolved names
    Generic(GenericDecl),
    Hole(NodeID, Span), // no annotation; to be inferred later
}

impl ASTTyRepr {
    pub fn span(&self) -> Span {
        match self {
            Self::Annotated(ta) => ta.span,
            Self::Generic(gd) => gd.span,
            Self::Hole(_, span) => *span,
        }
    }
}

pub trait TypingPhase: std::fmt::Debug + PartialEq {
    type TyPhase: std::fmt::Debug + PartialEq + Clone;
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum TypeDefKind {
    Struct,
    Enum,
    Protocol,
}

#[derive(Debug, PartialEq, Eq, Default, Clone)]
pub struct Raw {}
impl TypingPhase for Raw {
    type TyPhase = ASTTyRepr;
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeDef<Phase: TypingPhase> {
    pub name: Name,
    pub span: Span,
    pub kind: Kind,
    pub def: TypeDefKind,
    pub generics: IndexMap<Name, Phase::TyPhase>,
    pub fields: TypeFields<Phase>,
}

#[derive(Debug, Default)]
pub struct TypeSession<Phase: TypingPhase = Raw> {
    pub path: String,
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
