use derive_visitor::{DriveMut, VisitorMut};

use crate::{
    ast::{AST, Parsed},
    id_generator::IDGenerator,
    label::Label,
    name::Name,
    node_id::{FileID, NodeID},
    node_kinds::{
        call_arg::CallArg,
        expr::{Expr, ExprKind},
        stmt::{Stmt, StmtKind},
    },
};

/// Lowers subscript syntax to calls through the core subscript protocols.
///
/// `value[index]` becomes `SubscriptRead.subscript_read(value, index)`, and
/// `value[index] = replacement` becomes
/// `SubscriptWrite.subscript_write(value, index, replacement)`.
#[derive(Debug, VisitorMut)]
#[visitor(Stmt(enter), Expr(enter))]
pub struct LowerSubscripts {
    file_id: FileID,
    node_ids: IDGenerator,
}

impl LowerSubscripts {
    pub fn run(ast: &mut AST<Parsed>) {
        let node_ids = std::mem::take(&mut ast.node_ids);
        let mut instance = Self {
            file_id: ast.file_id,
            node_ids,
        };

        for root in &mut ast.roots {
            root.drive_mut(&mut instance);
        }

        _ = std::mem::replace(&mut ast.node_ids, instance.node_ids);
    }

    fn next_id(&mut self) -> NodeID {
        NodeID(self.file_id, self.node_ids.next_id())
    }

    fn protocol_call(
        &mut self,
        span: crate::span::Span,
        protocol: &str,
        method: &str,
        values: Vec<Expr>,
    ) -> ExprKind {
        let protocol = Expr {
            id: self.next_id(),
            span,
            kind: ExprKind::Variable(Name::Raw(protocol.into())),
        };
        let member = Expr {
            id: self.next_id(),
            span,
            kind: ExprKind::Member(Some(Box::new(protocol)), Label::Named(method.into()), span),
        };
        let args = values
            .into_iter()
            .enumerate()
            .map(|(position, value)| CallArg {
                mode: None,
                mode_span: None,
                id: value.id,
                label: Label::Positional(position),
                label_span: value.span,
                span: value.span,
                value,
            })
            .collect();

        ExprKind::Call {
            callee: Box::new(member),
            type_args: vec![],
            args,
            trailing_block: None,
            desugared_operator: None,
        }
    }

    fn enter_stmt(&mut self, stmt: &mut Stmt) {
        let StmtKind::Assignment(lhs, rhs) = stmt.kind.clone() else {
            return;
        };
        let ExprKind::Subscript(value, index) = lhs.kind else {
            return;
        };

        let call = Expr {
            id: lhs.id,
            span: stmt.span,
            kind: self.protocol_call(
                stmt.span,
                "SubscriptWrite",
                "subscript_write",
                vec![*value, *index, *rhs],
            ),
        };
        stmt.kind = StmtKind::Expr(call);
    }

    fn enter_expr(&mut self, expr: &mut Expr) {
        let ExprKind::Subscript(value, index) = expr.kind.clone() else {
            return;
        };

        expr.kind = self.protocol_call(
            expr.span,
            "SubscriptRead",
            "subscript_read",
            vec![*value, *index],
        );
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        desugar::lower_subscripts::LowerSubscripts,
        node_kinds::{expr::ExprKind, stmt::StmtKind},
        parser_tests::tests::parse,
    };

    #[test]
    fn lowers_read_subscript_to_protocol_call() {
        let mut parsed = parse("a[1]");
        LowerSubscripts::run(&mut parsed);

        let StmtKind::Expr(expr) = &parsed.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        let ExprKind::Call { callee, args, .. } = &expr.kind else {
            panic!("expected call");
        };
        let ExprKind::Member(Some(protocol), label, _) = &callee.kind else {
            panic!("expected protocol member");
        };
        assert!(
            matches!(protocol.kind, ExprKind::Variable(ref name) if name.name_str() == "SubscriptRead")
        );
        assert_eq!(label.to_string(), "subscript_read");
        assert_eq!(args.len(), 2);
    }

    #[test]
    fn lowers_write_subscript_to_protocol_call() {
        let mut parsed = parse("a[1] = 123");
        LowerSubscripts::run(&mut parsed);

        let StmtKind::Expr(expr) = &parsed.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        let ExprKind::Call { callee, args, .. } = &expr.kind else {
            panic!("expected call");
        };
        let ExprKind::Member(Some(protocol), label, _) = &callee.kind else {
            panic!("expected protocol member");
        };
        assert!(
            matches!(protocol.kind, ExprKind::Variable(ref name) if name.name_str() == "SubscriptWrite")
        );
        assert_eq!(label.to_string(), "subscript_write");
        assert_eq!(args.len(), 3);
    }
}
