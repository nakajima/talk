use derive_visitor::{Drive, DriveMut};

use crate::{
    impl_into_node, name::Name, name_resolution::symbol::Symbol, node::Node, node_id::NodeID,
    parsing::span::Span,
};

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
pub enum RecordFieldPatternKind {
    Bind(#[drive(skip)] Name),
    Equals {
        #[drive(skip)]
        name: Name,
        #[drive(skip)]
        name_span: Span,
        value: Pattern,
    },
    Rest,
}
#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
pub struct RecordFieldPattern {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub span: Span,
    pub kind: RecordFieldPatternKind,
}

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
pub enum PatternKind {
    // Literals that must match exactly
    LiteralInt(#[drive(skip)] String),
    LiteralFloat(#[drive(skip)] String),
    LiteralTrue,
    LiteralFalse,

    // Variable binding (always succeeds, binds value)
    Bind(#[drive(skip)] Name),

    Tuple(Vec<Pattern>),

    // Wildcard (always succeeds, ignores value)
    Wildcard,

    // Enum variant destructuring
    Variant {
        #[drive(skip)]
        enum_name: Option<Name>, // None for .some, Some for Option.some
        #[drive(skip)]
        variant_name: String,
        #[drive(skip)]
        variant_name_span: Span,
        fields: Vec<Pattern>, // Recursive patterns for fields
    },

    Record {
        fields: Vec<RecordFieldPattern>,
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

impl Pattern {
    pub fn collect_binders(&self) -> Vec<(NodeID, Symbol)> {
        let mut result = vec![];
        match &self.kind {
            PatternKind::LiteralInt(_) => (),
            PatternKind::LiteralFloat(_) => (),
            PatternKind::LiteralTrue => (),
            PatternKind::LiteralFalse => (),
            PatternKind::Bind(name) => result.push((self.id, name.symbol())),
            PatternKind::Tuple(patterns) => {
                for pattern in patterns {
                    result.extend(pattern.collect_binders());
                }
            }
            PatternKind::Wildcard => (),
            PatternKind::Variant { fields, .. } => {
                for pattern in fields {
                    result.extend(pattern.collect_binders());
                }
            }
            PatternKind::Record { fields } => {
                for field in fields {
                    match &field.kind {
                        RecordFieldPatternKind::Bind(name) => {
                            result.push((field.id, name.symbol()))
                        }
                        RecordFieldPatternKind::Equals { value, .. } => {
                            result.extend(value.collect_binders())
                        }
                        RecordFieldPatternKind::Rest => (),
                    }
                }
            }
            PatternKind::Struct { .. } => todo!(),
        }
        result
    }
}

impl_into_node!(Pattern);
