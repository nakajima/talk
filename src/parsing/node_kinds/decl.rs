use crate::{
    name::Name,
    node::Node,
    node_id::NodeID,
    node_kinds::{
        attribute::Attribute, block::Block, expr::Expr, generic_decl::GenericDecl,
        parameter::Parameter, type_annotation::TypeAnnotation,
    },
};
use derive_visitor::{Drive, DriveMut};

#[derive(Debug, Clone, PartialEq, Eq, DriveMut, Drive)]
pub enum DeclKind {
    Import(#[drive(skip)] String),
    Struct {
        #[drive(skip)]
        name: Name, /* name */
        generics: Vec<GenericDecl>, /* generics */
        conformances: Vec<TypeAnnotation>,
        body: Block, /* body */
    },

    Let(
        #[drive(skip)] Name,    /* name */
        Option<TypeAnnotation>, /* type annotation */
    ),

    Protocol {
        #[drive(skip)]
        name: Name,
        associated_types: Vec<GenericDecl>,
        body: Block,
        conformances: Vec<GenericDecl>,
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

    // Function stuff
    Func {
        #[drive(skip)]
        name: Name,
        generics: Vec<GenericDecl>,
        params: Vec<Parameter>, /* params tuple */
        body: Block,
        ret: Option<TypeAnnotation>, /* return type */
        #[drive(skip)]
        attributes: Vec<Attribute>,
    },

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
}

#[derive(Debug, Clone, PartialEq, Eq, DriveMut, Drive)]
pub struct Decl {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: DeclKind,
}

impl From<Decl> for Node {
    fn from(val: Decl) -> Self {
        Node::Decl(val)
    }
}
