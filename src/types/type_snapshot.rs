use rustc_hash::FxHashMap;

use crate::{
    ast::AST,
    formatter::{Formatter, FormatterDecorator, annotate, concat},
    name_resolution::name_resolver::NameResolved,
    node_id::NodeID,
    types::{ty::Ty, type_operations::UnificationSubstitutions},
};

#[derive(Clone)]
pub struct TypeSnapshot {
    pub generation: usize,
    pub ast: AST<NameResolved>,
    pub substitutions: UnificationSubstitutions,
    pub types_by_node: FxHashMap<NodeID, Ty>,
}

impl FormatterDecorator for TypeSnapshot {
    fn wrap_expr(
        &self,
        expr: &crate::node_kinds::expr::Expr,
        doc: crate::formatter::Doc,
    ) -> crate::formatter::Doc {
        let ty = self.types_by_node.get(&expr.id);
        concat(doc, annotate(format!("{ty:?}")))
    }

    fn wrap_decl(
        &self,
        decl: &crate::node_kinds::decl::Decl,
        doc: crate::formatter::Doc,
    ) -> crate::formatter::Doc {
        let ty = self.types_by_node.get(&decl.id);
        concat(doc, annotate(format!("{ty:?}")))
    }

    fn wrap_stmt(
        &self,
        stmt: &crate::node_kinds::stmt::Stmt,
        doc: crate::formatter::Doc,
    ) -> crate::formatter::Doc {
        let ty = self.types_by_node.get(&stmt.id);
        concat(doc, annotate(format!("{ty:?}")))
    }
}

impl std::fmt::Debug for TypeSnapshot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut parts = vec![];

        parts.push(
            "----------------------------------------------------------------------------------"
                .to_string(),
        );

        parts.push(format!("Generation {}", self.generation));

        let formatter = Formatter::new(&self.ast.meta);
        for (id, ty) in &self.types_by_node {
            let Some(node) = self.ast.find(*id) else {
                parts.push(format!("  ! didn't find node for id {id} {:#?}", self.ast));
                continue;
            };

            parts.push(format!("- {} -> {ty:?}", formatter.format(&[node], 80)));
        }

        write!(f, "{}", parts.join("\n"))
    }
}
