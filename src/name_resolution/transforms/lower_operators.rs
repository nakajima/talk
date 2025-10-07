use derive_visitor::{DriveMut, VisitorMut};

use crate::{
    ast::{AST, Parsed},
    id_generator::IDGenerator,
    label::Label,
    node_id::NodeID,
    node_kinds::{
        call_arg::CallArg,
        expr::{Expr, ExprKind},
    },
    token_kind::TokenKind,
};

#[derive(Debug, VisitorMut)]
#[visitor(Expr(enter))]
pub struct LowerOperators {
    node_ids: IDGenerator,
}
impl LowerOperators {
    pub fn run(ast: &mut AST<Parsed>) {
        let node_ids = std::mem::take(&mut ast.node_ids);
        let mut instance = Self { node_ids };

        for root in ast.roots.iter_mut() {
            root.drive_mut(&mut instance);
        }

        _ = std::mem::replace(&mut ast.node_ids, instance.node_ids);
    }

    fn enter_expr(&mut self, expr: &mut Expr) {
        let kind = match expr.kind.clone() {
            ExprKind::Unary(_op, _rhs) => todo!(),
            ExprKind::Binary(lhs, op, box rhs) => {
                let label = match op {
                    TokenKind::Plus => Label::Named("add".into()),
                    TokenKind::Minus => Label::Named("minus".into()),
                    TokenKind::Star => Label::Named("times".into()),
                    TokenKind::Slash => Label::Named("divide".into()),
                    TokenKind::EqualsEquals => Label::Named("equals".into()),
                    _ => return,
                };

                let member = Expr {
                    id: NodeID(expr.id.0, self.node_ids.next_id()),
                    span: lhs.span,
                    kind: ExprKind::Member(Some(lhs), label),
                };

                ExprKind::Call {
                    callee: member.into(),
                    type_args: vec![],
                    args: vec![CallArg {
                        id: NodeID(expr.id.0, self.node_ids.next_id()),
                        label: Label::Positional(0),
                        value: rhs,
                        span: expr.span,
                    }],
                }
            }
            _ => return,
        };

        expr.kind = kind;
    }
}

#[cfg(test)]
pub mod tests {
    use crate::{
        any_expr, any_stmt, assert_eq_diff, invocation,
        label::Label,
        name_resolution::transforms::lower_operators::LowerOperators,
        node_id::NodeID,
        node_kinds::{call_arg::CallArg, expr::ExprKind, stmt::StmtKind},
        parser_tests::tests::parse,
        span::Span,
    };

    #[test]
    fn lowers_plus() {
        let mut parsed = parse("1 + 2");
        LowerOperators::run(&mut parsed);

        assert_eq_diff!(
            *parsed.roots[0].as_stmt(),
            any_stmt!(StmtKind::Expr(invocation!(
                ExprKind::LiteralInt("1".into()),
                "add",
                vec![CallArg {
                    id: NodeID::ANY,
                    label: Label::Positional(0),
                    value: any_expr!(ExprKind::LiteralInt("2".into())),
                    span: Span::ANY,
                }]
            )))
        )
    }

    #[test]
    fn lowers_minus() {
        let mut parsed = parse("1 - 2");
        LowerOperators::run(&mut parsed);

        assert_eq_diff!(
            *parsed.roots[0].as_stmt(),
            any_stmt!(StmtKind::Expr(invocation!(
                ExprKind::LiteralInt("1".into()),
                "minus",
                vec![CallArg {
                    id: NodeID::ANY,
                    label: Label::Positional(0),
                    value: any_expr!(ExprKind::LiteralInt("2".into())),
                    span: Span::ANY,
                }]
            )))
        )
    }

    #[test]
    fn lowers_times() {
        let mut parsed = parse("1 * 2");
        LowerOperators::run(&mut parsed);

        assert_eq_diff!(
            *parsed.roots[0].as_stmt(),
            any_stmt!(StmtKind::Expr(invocation!(
                ExprKind::LiteralInt("1".into()),
                "times",
                vec![CallArg {
                    id: NodeID::ANY,
                    label: Label::Positional(0),
                    value: any_expr!(ExprKind::LiteralInt("2".into())),
                    span: Span::ANY,
                }]
            )))
        )
    }

    #[test]
    fn lowers_divide() {
        let mut parsed = parse("1 / 2");
        LowerOperators::run(&mut parsed);

        assert_eq_diff!(
            *parsed.roots[0].as_stmt(),
            any_stmt!(StmtKind::Expr(invocation!(
                ExprKind::LiteralInt("1".into()),
                "divide",
                vec![CallArg {
                    id: NodeID::ANY,
                    label: Label::Positional(0),
                    value: any_expr!(ExprKind::LiteralInt("2".into())),
                    span: Span::ANY,
                }]
            )))
        )
    }
}
