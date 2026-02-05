use derive_visitor::{DriveMut, VisitorMut};

use crate::{
    ast::{AST, Parsed},
    id_generator::IDGenerator,
    label::Label,
    node::Node,
    node_id::{FileID, NodeID},
    node_kinds::{
        block::Block,
        decl::{Decl, DeclKind, Visibility},
        expr::{Expr, ExprKind},
        match_arm::MatchArm,
        pattern::{Pattern, PatternKind},
        stmt::{Stmt, StmtKind},
    },
    span::Span,
};

/// Desugars `for pattern in iterable { body }` into:
/// ```talk
/// {
///     let __iter# = iterable.iter()
///     loop {
///         match __iter#.next() {
///             .some(pattern) { body }
///             .none { break }
///         }
///     }
/// }
/// ```
#[derive(Debug, VisitorMut)]
#[visitor(Stmt(enter))]
pub struct LowerForLoops {
    node_ids: IDGenerator,
    file_id: FileID,
}

impl LowerForLoops {
    pub fn run(ast: &mut AST<Parsed>) {
        let node_ids = std::mem::take(&mut ast.node_ids);
        let mut instance = Self {
            node_ids,
            file_id: ast.file_id,
        };

        for root in ast.roots.iter_mut() {
            root.drive_mut(&mut instance);
        }

        _ = std::mem::replace(&mut ast.node_ids, instance.node_ids);
    }

    fn next_id(&mut self) -> NodeID {
        NodeID(self.file_id, self.node_ids.next_id())
    }

    fn enter_stmt(&mut self, stmt: &mut Stmt) {
        let StmtKind::For {
            pattern,
            iterable,
            body,
        } = stmt.kind.clone()
        else {
            return;
        };

        // Build: __iter#.next()
        let iter_var = Expr {
            id: self.next_id(),
            span: Span::SYNTHESIZED,
            kind: ExprKind::Variable("__iter#".into()),
        };

        let next_member = Expr {
            id: self.next_id(),
            span: Span::SYNTHESIZED,
            kind: ExprKind::Member(
                Some(Box::new(iter_var.clone())),
                Label::Named("next".into()),
                Span::SYNTHESIZED,
            ),
        };

        let next_call = Expr {
            id: self.next_id(),
            span: Span::SYNTHESIZED,
            kind: ExprKind::Call {
                callee: Box::new(next_member),
                type_args: vec![],
                args: vec![],
                trailing_block: None,
            },
        };

        // Build match arm: .some(pattern) { body }
        let some_arm = MatchArm {
            id: self.next_id(),
            pattern: Pattern {
                id: self.next_id(),
                span: pattern.span,
                kind: PatternKind::Variant {
                    enum_name: None,
                    variant_name: "some".to_string(),
                    variant_name_span: Span::SYNTHESIZED,
                    fields: vec![pattern],
                },
            },
            body,
            span: Span::SYNTHESIZED,
        };

        // Build match arm: .none { break }
        let break_stmt = Stmt {
            id: self.next_id(),
            span: Span::SYNTHESIZED,
            kind: StmtKind::Break,
        };

        let none_arm = MatchArm {
            id: self.next_id(),
            pattern: Pattern {
                id: self.next_id(),
                span: Span::SYNTHESIZED,
                kind: PatternKind::Variant {
                    enum_name: None,
                    variant_name: "none".to_string(),
                    variant_name_span: Span::SYNTHESIZED,
                    fields: vec![],
                },
            },
            body: Block {
                id: self.next_id(),
                span: Span::SYNTHESIZED,
                args: vec![],
                body: vec![Node::Stmt(break_stmt)],
            },
            span: Span::SYNTHESIZED,
        };

        // Build match expression
        let match_expr = Expr {
            id: self.next_id(),
            span: Span::SYNTHESIZED,
            kind: ExprKind::Match(Box::new(next_call), vec![some_arm, none_arm]),
        };

        // Build loop body: match __iter#.next() { ... }
        let loop_body = Block {
            id: self.next_id(),
            span: Span::SYNTHESIZED,
            args: vec![],
            body: vec![Node::Expr(match_expr)],
        };

        // Build: loop { ... }
        let loop_stmt = Stmt {
            id: self.next_id(),
            span: Span::SYNTHESIZED,
            kind: StmtKind::Loop(None, loop_body),
        };

        // Build: iterable.iter()
        let iter_member = Expr {
            id: self.next_id(),
            span: Span::SYNTHESIZED,
            kind: ExprKind::Member(
                Some(iterable),
                Label::Named("iter".into()),
                Span::SYNTHESIZED,
            ),
        };

        let iter_call = Expr {
            id: self.next_id(),
            span: Span::SYNTHESIZED,
            kind: ExprKind::Call {
                callee: Box::new(iter_member),
                type_args: vec![],
                args: vec![],
                trailing_block: None,
            },
        };

        // Build: let __iter# = iterable.iter()
        let let_decl = Decl {
            id: self.next_id(),
            span: Span::SYNTHESIZED,
            visibility: Visibility::Private,
            kind: DeclKind::Let {
                lhs: Pattern {
                    id: self.next_id(),
                    span: Span::SYNTHESIZED,
                    kind: PatternKind::Bind("__iter#".into()),
                },
                type_annotation: None,
                rhs: Some(iter_call),
            },
        };

        // Build outer block: { let __iter# = ...; loop { ... } }
        let outer_block = Expr {
            id: self.next_id(),
            span: stmt.span,
            kind: ExprKind::Block(Block {
                id: self.next_id(),
                span: stmt.span,
                args: vec![],
                body: vec![Node::Decl(let_decl), Node::Stmt(loop_stmt)],
            }),
        };

        // Replace the for statement with an expression statement containing the block
        stmt.kind = StmtKind::Expr(outer_block);
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        name_resolution::transforms::lower_for_loops::LowerForLoops, parser_tests::tests::parse,
    };

    #[test]
    fn parses_for_loop() {
        let parsed = parse("for x in items { print(x) }");
        assert!(parsed.roots.len() == 1);
    }

    #[test]
    fn desugars_for_loop() {
        let mut parsed = parse("for x in items { print(x) }");
        LowerForLoops::run(&mut parsed);

        // After desugaring, should be a block expression containing let + loop
        let stmt = parsed.roots[0].as_stmt();
        assert!(matches!(
            stmt.kind,
            crate::node_kinds::stmt::StmtKind::Expr(crate::node_kinds::expr::Expr {
                kind: crate::node_kinds::expr::ExprKind::Block(_),
                ..
            })
        ));
    }

    #[test]
    fn desugars_for_loop_with_tuple_pattern() {
        let mut parsed = parse("for (x, y) in pairs { print(x) }");
        LowerForLoops::run(&mut parsed);

        let stmt = parsed.roots[0].as_stmt();
        assert!(matches!(
            stmt.kind,
            crate::node_kinds::stmt::StmtKind::Expr(crate::node_kinds::expr::Expr {
                kind: crate::node_kinds::expr::ExprKind::Block(_),
                ..
            })
        ));
    }
}
