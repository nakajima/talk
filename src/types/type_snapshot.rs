use rustc_hash::FxHashMap;

use crate::{
    ast::AST, name_resolution::name_resolver::NameResolved,
    types::type_operations::UnificationSubstitutions,
};

pub struct TypeSnapshot {
    ast: AST<NameResolved>,
    substitutions: UnificationSubstitutions,
    types_by_node: FxHashMap<NodeID, Ty>,
}

impl std::fmt::Debug for TypeSnapshot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {}
}
