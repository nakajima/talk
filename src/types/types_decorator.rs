use rustc_hash::FxHashMap;

use crate::{
    formatter::{Doc, FormatterDecorator, annotate, wrap},
    node_id::NodeID,
    node_kinds::{
        decl::Decl,
        expr::{Expr, ExprKind},
        stmt::Stmt,
    },
    types::ty::Ty,
};

pub struct TypesDecorator {
    pub types_by_node: FxHashMap<NodeID, Ty>,
}

impl FormatterDecorator for TypesDecorator {
    fn wrap_expr(&self, expr: &Expr, doc: Doc) -> Doc {
        if let Some(ty) = self.types_by_node.get(&expr.id) {
            wrap(
                annotate(format!(
                    "<span title=\"{ty:?}\" class=\"expr-kind {}\">",
                    expr_class(&expr.kind)
                )),
                doc,
                annotate("</span>"),
            )
        } else {
            doc
        }
    }
    fn wrap_decl(&self, decl: &Decl, doc: Doc) -> Doc {
        if let Some(ty) = self.types_by_node.get(&decl.id) {
            wrap(
                annotate(format!("<span title=\"{ty:?}\" class=\"expr-kind\">",)),
                doc,
                annotate("</span>"),
            )
        } else {
            doc
        }
    }
    fn wrap_stmt(&self, _stmt: &Stmt, doc: Doc) -> Doc {
        doc
    }
}

fn expr_class(kind: &ExprKind) -> &'static str {
    match kind {
        ExprKind::Incomplete(..) => "incomplete",
        ExprKind::LiteralArray(..) => "array",
        ExprKind::LiteralInt(_) => "int",
        ExprKind::LiteralFloat(_) => "float",
        ExprKind::LiteralTrue => "bool",
        ExprKind::LiteralFalse => "bool",
        ExprKind::LiteralString(_) => "string",
        ExprKind::Unary(..) => "unary",
        ExprKind::Binary(..) => "binary",
        ExprKind::Tuple(..) => "tuple",
        ExprKind::Block(..) => "block",
        ExprKind::Call { .. } => "call",
        ExprKind::Member(..) => "member",
        ExprKind::Func(..) => "func",
        ExprKind::Variable(..) => "variable",
        ExprKind::If(..) => "if",
        ExprKind::Match(..) => "match",
        ExprKind::RecordLiteral { .. } => "record",
        ExprKind::RowVariable(..) => "row",
    }
}
