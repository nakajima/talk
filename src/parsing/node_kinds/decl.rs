use crate::{
    impl_into_node,
    name::Name,
    node::Node,
    node_id::NodeID,
    node_kinds::{
        attribute::Attribute, block::Block, expr::Expr, generic_decl::GenericDecl,
        parameter::Parameter, pattern::Pattern, type_annotation::TypeAnnotation,
    },
    parsing::span::Span,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclKind {
    Import(String),
    Struct {
        name: Name,                 /* name */
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
        name: Name,

        is_static: bool,
        type_annotation: Option<TypeAnnotation>,
        default_value: Option<Expr>,
    },

    Method {
        func: Box<Decl>,

        is_static: bool,
    },

    // Function stuff
    Func {
        name: Name,
        generics: Vec<GenericDecl>,
        params: Vec<Parameter>, /* params tuple */
        body: Block,
        ret: Option<TypeAnnotation>, /* return type */

        attributes: Vec<Attribute>,
    },

    Extend {
        name: Name, // TypeRepr name: Option
        conformances: Vec<TypeAnnotation>,
        generics: Vec<GenericDecl>, // Generics TypeParams <T>
        body: Block,
    },

    // Enum declaration
    Enum {
        name: Name, // TypeRepr name: Option
        conformances: Vec<TypeAnnotation>,
        generics: Vec<GenericDecl>, // Generics TypeParams <T>
        body: Block,
    },

    // Individual enum variant in declaration
    EnumVariant(
        Name,                // name: "some"
        Vec<TypeAnnotation>, // associated types: [TypeRepr("T")]
    ),

    FuncSignature {
        name: Name,
        params: Vec<Parameter>,
        generics: Vec<GenericDecl>,
        ret: Box<TypeAnnotation>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Decl {
    pub id: NodeID,
    pub kind: DeclKind,
    pub span: Span,
}

impl_into_node!(Decl);
