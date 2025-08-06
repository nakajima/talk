use derive_visitor::Drive;

/// The kind of row type - struct, protocol, or record
#[derive(Clone, PartialEq, Debug, Drive)]
pub enum RowKind {
    /// A struct - concrete type with storage
    Struct,
    /// A protocol - interface/trait type without storage
    Protocol,
    /// A record - structural type (anonymous)
    Record,
    /// An enum - sum type with variants
    Enum,
}
