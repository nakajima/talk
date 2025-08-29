use derive_visitor::{Drive, DriveMut};

use crate::{
    impl_into_node,
    name::Name,
    node::Node,
    node_id::NodeID,
    node_kinds::{
        attribute::Attribute, block::Block, expr::Expr, func::Func, generic_decl::GenericDecl,
        parameter::Parameter, pattern::Pattern, type_annotation::TypeAnnotation,
    },
    parsing::span::Span,
};

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub enum DeclKind {
    Import(#[drive(skip)] String),
    Struct {
        #[drive(skip)]
        name: Name, /* name */
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
        generics: Vec<GenericDecl>,
        body: Block,
        conformances: Vec<TypeAnnotation>,
    },

    Init {
        params: Vec<Parameter>, /* params tuple */
        body: Block,
    },

    Property {
        #[drive(skip)]
        name: Name,
        #[drive(skip)]
        is_static: bool,
        type_annotation: Option<TypeAnnotation>,
        default_value: Option<Expr>,
    },

    Method {
        func: Box<Decl>,
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
        conformances: Vec<TypeAnnotation>,
        generics: Vec<GenericDecl>, // Generics TypeParams <T>
        body: Block,
    },

    // Enum declaration
    Enum {
        #[drive(skip)]
        name: Name, // TypeRepr name: Option
        conformances: Vec<TypeAnnotation>,
        generics: Vec<GenericDecl>, // Generics TypeParams <T>
        body: Block,
    },

    // Individual enum variant in declaration
    EnumVariant(
        #[drive(skip)] Name, // name: "some"
        Vec<TypeAnnotation>, // associated types: [TypeRepr("T")]
    ),

    FuncSignature {
        #[drive(skip)]
        name: Name,
        params: Vec<Parameter>,
        generics: Vec<GenericDecl>,
        ret: Box<TypeAnnotation>,
    },
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
