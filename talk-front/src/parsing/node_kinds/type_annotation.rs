use derive_visitor::{Drive, DriveMut};

use crate::{
    impl_into_node,
    label::Label,
    name::Name,
    name_resolution::name_resolver::NameResolverError,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    node_kinds::{func::EffectSet, record_field::RecordFieldTypeAnnotation},
    parsing::span::Span,
};

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub struct AnyAssocBinding {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub name: Name,
    #[drive(skip)]
    pub name_span: Span,
    pub value: TypeAnnotation,
    #[drive(skip)]
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub enum TypeAnnotationKind {
    SelfType(#[drive(skip)] Name),
    Borrow {
        #[drive(skip)]
        mutable: bool,
        inner: Box<TypeAnnotation>,
    },
    /// `*T`: a uniquely-owned value.
    Unique {
        inner: Box<TypeAnnotation>,
    },
    Func {
        params: Vec<TypeAnnotation>,
        #[drive(skip)]
        effects: EffectSet,
        returns: Box<TypeAnnotation>,
    },
    /// A quantified function type `<T, U: Bound>(params) -> Ret`
    /// (rank-N field types): the declared generics and optional where
    /// clause scope over the inner function type.
    Quantified {
        generics: Vec<crate::node_kinds::generic_decl::GenericDecl>,
        where_clause: Option<crate::node_kinds::where_clause::WhereClause>,
        inner: Box<TypeAnnotation>,
    },
    NominalPath {
        base: Box<TypeAnnotation>,
        #[drive(skip)]
        member: Label,
        #[drive(skip)]
        member_span: Span,
        member_generics: Vec<crate::node_kinds::generic_arg::GenericArg>,
    },
    Nominal {
        #[drive(skip)]
        name: Name,
        #[drive(skip)]
        name_span: Span,
        generics: Vec<crate::node_kinds::generic_arg::GenericArg>,
    },
    Tuple(Vec<TypeAnnotation>),
    Record {
        fields: Vec<RecordFieldTypeAnnotation>,
    },
    Any {
        protocol: Box<TypeAnnotation>,
        assoc_bindings: Vec<AnyAssocBinding>,
    },
    /// An @macro invocation in type position (ADR 0026). Expansion
    /// replaces it with the parsed type before name resolution.
    MacroCall {
        #[drive(skip)]
        name: String,
        #[drive(skip)]
        name_span: Span,
        /// The complete balanced input, including its outer delimiters.
        #[drive(skip)]
        input_span: Span,
        /// Canonical invocation tokens, including the outer delimiters.
        #[drive(skip)]
        input_tokens: Vec<crate::node_kinds::expr::MacroToken>,
    },
}

impl TypeAnnotation {
    pub fn symbol(&self) -> Result<Symbol, NameResolverError> {
        match &self.kind {
            TypeAnnotationKind::Nominal { name, .. } | TypeAnnotationKind::SelfType(name) => {
                name.symbol()
            }
            _ => unreachable!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub struct TypeAnnotation {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: TypeAnnotationKind,
    #[drive(skip)]
    pub span: Span,
}

impl_into_node!(TypeAnnotation);
