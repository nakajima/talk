use crate::{diagnostic::AnyDiagnostic, node::Node, node_meta_storage::NodeMetaStorage};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AST {
    pub path: String,
    pub roots: Vec<Node>,
    pub diagnostics: Vec<AnyDiagnostic>,
    pub meta: NodeMetaStorage,
}
