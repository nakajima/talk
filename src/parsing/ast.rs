use crate::{diagnostic::AnyDiagnostic, node::Node, node_meta_storage::NodeMetaStorage};

pub trait ASTPhase: Clone + std::fmt::Debug + PartialEq + Eq {}

pub type NewAST = ();
impl ASTPhase for NewAST {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Parsed;
impl ASTPhase for Parsed {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AST<Phase: ASTPhase = NewAST> {
    pub path: String,
    pub roots: Vec<Node>,
    pub diagnostics: Vec<AnyDiagnostic>,
    pub meta: NodeMetaStorage,
    pub phase: Phase,
}
