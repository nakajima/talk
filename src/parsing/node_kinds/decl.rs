use derive_visitor::{Drive, DriveMut};

use crate::{
    impl_into_node,
    name::Name,
    node_id::NodeID,
    node_kinds::{
        block::Block, expr::Expr, func::Func, func_signature::FuncSignature,
        generic_decl::GenericDecl, parameter::Parameter, pattern::Pattern,
        type_annotation::TypeAnnotation,
    },
    parsing::span::Span,
};

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub enum DeclKind {
    Import(#[drive(skip)] String),
    Struct {
        #[drive(skip)]
        name: Name, /* name */
        #[drive(skip)]
        name_span: Span,
        generics: Vec<GenericDecl>, /* generics */
        conformances: Vec<TypeAnnotation>,
        body: Block, /* body */
    },

    Let {
        lhs: Pattern,
        type_annotation: Option<TypeAnnotation>,
        value: Option<Expr>,
    },

    Protocol {
        #[drive(skip)]
        name: Name,
        #[drive(skip)]
        name_span: Span,
        generics: Vec<GenericDecl>,
        body: Block,
        conformances: Vec<TypeAnnotation>,
    },

    Init {
        #[drive(skip)]
        name: Name,
        params: Vec<Parameter>, /* params tuple */
        body: Block,
    },

    Property {
        #[drive(skip)]
        name: Name,
        #[drive(skip)]
        name_span: Span,
        #[drive(skip)]
        is_static: bool,
        type_annotation: Option<TypeAnnotation>,
        default_value: Option<Expr>,
    },

    Method {
        func: Box<Func>,
        #[drive(skip)]
        is_static: bool,
    },

    Associated {
        generic: GenericDecl,
    },

    // Function stuff
    Func(Func),

    Extend {
        #[drive(skip)]
        name: Name, // TypeRepr name: Option
        #[drive(skip)]
        name_span: Span,
        conformances: Vec<TypeAnnotation>,
        generics: Vec<GenericDecl>, // Generics TypeParams <T>
        body: Block,
    },

    // Enum declaration
    Enum {
        #[drive(skip)]
        name: Name, // TypeRepr name: Option
        #[drive(skip)]
        name_span: Span,
        conformances: Vec<TypeAnnotation>,
        generics: Vec<GenericDecl>, // Generics TypeParams <T>
        body: Block,
    },

    // Individual enum variant in declaration
    EnumVariant(
        #[drive(skip)] Name, // name: "some"
        #[drive(skip)] Span, // name_span
        Vec<TypeAnnotation>, // associated types: [TypeRepr("T")]
    ),

    FuncSignature(FuncSignature),
    MethodRequirement(FuncSignature),

    TypeAlias(TypeAnnotation, TypeAnnotation),
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct Decl {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: DeclKind,
    #[drive(skip)]
    pub span: Span,
}

impl_into_node!(Decl);
