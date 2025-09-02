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
    types::{
        fields::TypeFields, kind::Kind, type_header_decl_pass::TypeHeaderDeclPass,
        type_header_resolve_pass::HeadersResolved,
    },
};

#[derive(Debug, PartialEq, Eq, Clone)]
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

pub trait TypingPhase: std::fmt::Debug {
    type Next: TypingPhase;
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum TypeDefKind {
    Struct,
    Enum,
    Protocol,
}

#[derive(Debug, PartialEq, Default, Clone)]
pub struct Raw {
    pub type_constructors: FxHashMap<DeclId, TypeDef<ASTTyRepr>>,
    pub protocols: FxHashMap<DeclId, TypeDef<ASTTyRepr>>,
}

impl TypingPhase for Raw {
    type Next = HeadersResolved;
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeDef<T> {
    pub name: Name,
    pub span: Span,
    pub kind: Kind,
    pub def: TypeDefKind,
    pub generics: IndexMap<Name, T>,
    pub fields: TypeFields<T>,
}

#[derive(Debug, Default)]
pub struct TypeSession<Phase: TypingPhase = Raw> {
    pub path: String,
    pub synthsized_ids: IDGenerator,
    pub phase: Phase,
}

pub struct Typed {}

impl<Phase: TypingPhase> TypeSession<Phase> {
    pub fn drive(ast: &AST<NameResolved>) -> TypeSession<Raw> {
        let mut session = TypeSession::<Raw>::default();
        TypeHeaderDeclPass::drive(&mut session, ast);
        session
    }

    pub fn advance(self, phase: Phase::Next) -> TypeSession<Phase::Next> {
        TypeSession::<Phase::Next> {
            path: self.path,
            synthsized_ids: self.synthsized_ids,
            phase,
        }
    }
}
