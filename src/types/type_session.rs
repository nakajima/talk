use indexmap::IndexMap;
use rustc_hash::FxHashMap;

use crate::{
    ast::AST,
    id_generator::IDGenerator,
    label::Label,
    name::Name,
    name_resolution::{name_resolver::NameResolved, symbol::TypeId},
    node_id::NodeID,
    node_kinds::{generic_decl::GenericDecl, type_annotation::TypeAnnotation},
    span::Span,
    types::{
        builtins::builtin_scope,
        fields::{Method, TypeFields},
        kind::Kind,
        passes::{
            dependencies_pass::DependenciesPass,
            inference_pass::{InferencePass, Inferenced, Meta},
            type_headers_pass::TypeHeaderPass,
            type_resolve_pass::{HeadersResolved, TypeResolvePass},
        },
        row::Row,
        term_environment::TermEnv,
        ty::{Level, Ty},
        vars::Vars,
    },
};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ASTTyRepr {
    Annotated(TypeAnnotation), // already resolved names
    Generic(GenericDecl),
    Hole(NodeID, Span),           // no annotation; to be inferred later
    SelfType(Name, NodeID, Span), // For synthesized `self` param
}

impl ASTTyRepr {
    pub fn span(&self) -> Span {
        match self {
            Self::Annotated(ta) => ta.span,
            Self::Generic(gd) => gd.span,
            Self::Hole(_, span) => *span,
            Self::SelfType(_, _, span) => *span,
        }
    }
}

pub trait TypingPhase: std::fmt::Debug {
    type Next: TypingPhase;
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum TypeDefKind {
    Struct,
    Enum,
    Protocol,
    Extension,
}

#[derive(Debug, PartialEq, Default)]
pub struct Raw {
    pub type_constructors: FxHashMap<TypeId, TypeDef<ASTTyRepr>>,
    pub protocols: FxHashMap<TypeId, TypeDef<ASTTyRepr>>,
}

impl TypingPhase for Raw {
    type Next = HeadersResolved;
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeExtension<T> {
    pub node_id: NodeID,
    pub conformances: Vec<TypeId>,
    pub methods: IndexMap<Label, Method<T>>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeDef<T> {
    pub name: Name,
    pub node_id: NodeID,
    pub kind: Kind,
    pub def: TypeDefKind,
    pub generics: IndexMap<Name, T>,
    pub fields: TypeFields<T>,
    pub extensions: Vec<TypeExtension<T>>,
}

#[derive(Debug)]
pub struct TypeSession<Phase: TypingPhase = Raw> {
    pub vars: Vars,
    pub synthsized_ids: IDGenerator,
    pub phase: Phase,
    pub term_env: TermEnv,
    pub meta_levels: FxHashMap<Meta, Level>,
}

impl Default for TypeSession<Raw> {
    fn default() -> Self {
        let mut term_env = TermEnv {
            symbols: FxHashMap::default(),
        };

        for (sym, entry) in builtin_scope() {
            term_env.promote(sym, entry);
        }

        TypeSession {
            vars: Default::default(),
            synthsized_ids: Default::default(),
            phase: Raw {
                type_constructors: Default::default(),
                protocols: Default::default(),
            },
            meta_levels: Default::default(),
            term_env,
        }
    }
}

pub struct Typed {}

impl<Phase: TypingPhase> TypeSession<Phase> {
    pub fn drive(ast: &mut AST<NameResolved>) -> TypeSession<Inferenced> {
        let mut session = TypeSession::<Raw>::default();
        TypeHeaderPass::drive(&mut session, ast);
        let session = TypeResolvePass::drive(ast, session);
        let session = DependenciesPass::drive(session, ast);
        InferencePass::perform(session, ast)
    }

    pub fn advance(self, phase: Phase::Next) -> TypeSession<Phase::Next> {
        TypeSession::<Phase::Next> {
            vars: self.vars,
            synthsized_ids: self.synthsized_ids,
            phase,
            term_env: self.term_env,
            meta_levels: self.meta_levels,
        }
    }

    pub(crate) fn new_ty_meta_var(&mut self, level: Level) -> Ty {
        let id = self.vars.ty_metas.next_id();
        self.meta_levels.insert(Meta::Ty(id), level);
        tracing::trace!("Fresh {id:?}");
        Ty::UnificationVar { id, level }
    }

    pub(crate) fn new_row_meta_var(&mut self, level: Level) -> Row {
        let id = self.vars.row_metas.next_id();
        self.meta_levels.insert(Meta::Row(id), level);
        tracing::trace!("Fresh {id:?}");
        Row::Var(id)
    }
}
