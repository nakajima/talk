use crate::{parsing::span::Span, impl_into_node, name::Name, node::Node, node_id::NodeID};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PatternKind {
    // Literals that must match exactly
    LiteralInt(String),

    LiteralFloat(String),
    LiteralTrue,
    LiteralFalse,

    // Variable binding (always succeeds, binds value)
    Bind(Name),

    // Wildcard (always succeeds, ignores value)
    Wildcard,

    // Enum variant destructuring
    Variant {
        enum_name: Option<Name>, // None for .some, Some for Option.some

        variant_name: String,
        fields: Vec<Pattern>, // Recursive patterns for fields
    },

    // Struct/Record destructuring
    Struct {
        struct_name: Option<Name>, // The struct type name
        fields: Vec<Node>,         // Field patterns (we'll store field names separately)

        field_names: Vec<Name>, // Field names corresponding to patterns

        rest: bool, // Whether there's a .. pattern to ignore remaining fields
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pattern {
    pub id: NodeID,
    pub kind: PatternKind,
    pub span: Span,
}

impl_into_node!(Pattern);
