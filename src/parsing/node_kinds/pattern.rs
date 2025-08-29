use derive_visitor::{Drive, DriveMut};

use crate::{impl_into_node, name::Name, node::Node, node_id::NodeID, parsing::span::Span};

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
pub enum PatternKind {
    // Literals that must match exactly
    LiteralInt(#[drive(skip)] String),
    LiteralFloat(#[drive(skip)] String),
    LiteralTrue,
    LiteralFalse,

    // Variable binding (always succeeds, binds value)
    Bind(#[drive(skip)] Name),

    // Wildcard (always succeeds, ignores value)
    Wildcard,

    // Enum variant destructuring
    Variant {
        #[drive(skip)]
        enum_name: Option<Name>, // None for .some, Some for Option.some
        #[drive(skip)]
        variant_name: String,
        fields: Vec<Pattern>, // Recursive patterns for fields
    },

    // Struct/Record destructuring
    Struct {
        #[drive(skip)]
        struct_name: Option<Name>, // The struct type name
        fields: Vec<Node>, // Field patterns (we'll store field names separately)
        #[drive(skip)]
        field_names: Vec<Name>, // Field names corresponding to patterns
        #[drive(skip)]
        rest: bool, // Whether there's a .. pattern to ignore remaining fields
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
pub struct Pattern {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: PatternKind,
    #[drive(skip)]
    pub span: Span,
}

impl_into_node!(Pattern);
