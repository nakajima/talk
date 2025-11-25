use derive_visitor::{DriveMut, VisitorMut};

use crate::{
    ast::{AST, Parsed},
    id_generator::IDGenerator,
    label::Label,
    node_id::NodeID,
    node_kinds::{
        call_arg::CallArg,
        expr::{Expr, ExprKind},
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
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
            ExprKind::Unary(op, rhs) => {
                let label = match op {
                    TokenKind::Bang => Label::Named("not".into()),
                    TokenKind::Minus => Label::Named("negated".into()),
                    _ => return,
                };

                let span = rhs.span;
                let member = Expr {
                    id: NodeID(expr.id.0, self.node_ids.next_id()),
                    span,
                    kind: ExprKind::Member(Some(rhs), label, span),
                };

                ExprKind::Call {
                    callee: member.into(),
                    type_args: vec![],
                    args: vec![],
                }
            }
            ExprKind::Binary(lhs, op, box rhs) => {
                let (protocol_name, label) = match op {
                    // Arithmetic
                    TokenKind::Plus => ("Add", Label::Named("add".into())),
                    TokenKind::Minus => ("Subtract", Label::Named("minus".into())),
                    TokenKind::Star => ("Multiply", Label::Named("times".into())),
                    TokenKind::Slash => ("Divide", Label::Named("divide".into())),

                    // Comparisons
                    TokenKind::Greater => ("Comparable", Label::Named("gt".into())),
                    TokenKind::GreaterEquals => ("Comparable", Label::Named("gte".into())),
                    TokenKind::Less => ("Comparable", Label::Named("lt".into())),
                    TokenKind::LessEquals => ("Comparable", Label::Named("lte".into())),

                    // Equatables
                    TokenKind::EqualsEquals => ("Equatable", Label::Named("equals".into())),
                    TokenKind::BangEquals => ("Equatable", Label::Named("notEquals".into())),
                    _ => return,
                };

                let span = lhs.span;
                let protocol_constructor = Expr {
                    id: NodeID(expr.id.0, self.node_ids.next_id()),
                    span,
                    kind: ExprKind::Variable(protocol_name.into()),
                };

                let member = Expr {
                    id: NodeID(expr.id.0, self.node_ids.next_id()),
                    span,
                    kind: ExprKind::Member(Some(protocol_constructor.into()), label, span),
                };

                ExprKind::Call {
                    callee: member.into(),
                    type_args: vec![],
                    args: vec![
                        CallArg {
                            id: expr.id,
                            label: Label::Positional(0),
                            label_span: expr.span,
                            value: *lhs,
                            span: expr.span,
                        },
                        CallArg {
                            id: rhs.id,
                            label: Label::Positional(1),
                            label_span: rhs.span,
                            value: rhs,
                            span: expr.span,
                        },
                    ],
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
        annotation, any_expr, any_stmt, assert_eq_diff, invocation,
        label::Label,
        name_resolution::transforms::lower_operators::LowerOperators,
        node_id::NodeID,
        node_kinds::{
            call_arg::CallArg, expr::ExprKind, stmt::StmtKind, type_annotation::TypeAnnotationKind,
        },
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
                ExprKind::Variable("Add".into()),
                "add",
                vec![
                    CallArg {
                        id: NodeID::ANY,
                        label: Label::Positional(0),
                        label_span: Span::ANY,
                        value: any_expr!(ExprKind::LiteralInt("1".into())),
                        span: Span::ANY,
                    },
                    CallArg {
                        id: NodeID::ANY,
                        label: Label::Positional(1),
                        label_span: Span::ANY,
                        value: any_expr!(ExprKind::LiteralInt("2".into())),
                        span: Span::ANY,
                    }
                ]
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
                ExprKind::Variable("Subtract".into()),
                "minus",
                vec![
                    CallArg {
                        id: NodeID::ANY,
                        label: Label::Positional(0),
                        label_span: Span::ANY,
                        value: any_expr!(ExprKind::LiteralInt("1".into())),
                        span: Span::ANY,
                    },
                    CallArg {
                        id: NodeID::ANY,
                        label: Label::Positional(1),
                        label_span: Span::ANY,
                        value: any_expr!(ExprKind::LiteralInt("2".into())),
                        span: Span::ANY,
                    }
                ]
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
                ExprKind::Variable("Multiply".into()),
                "times",
                vec![
                    CallArg {
                        id: NodeID::ANY,
                        label: Label::Positional(0),
                        label_span: Span::ANY,
                        value: any_expr!(ExprKind::LiteralInt("1".into())),
                        span: Span::ANY,
                    },
                    CallArg {
                        id: NodeID::ANY,
                        label: Label::Positional(1),
                        label_span: Span::ANY,
                        value: any_expr!(ExprKind::LiteralInt("2".into())),
                        span: Span::ANY,
                    }
                ]
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
                ExprKind::Variable("Divide".into()),
                "divide",
                vec![
                    CallArg {
                        id: NodeID::ANY,
                        label: Label::Positional(0),
                        label_span: Span::ANY,
                        value: any_expr!(ExprKind::LiteralInt("1".into())),
                        span: Span::ANY,
                    },
                    CallArg {
                        id: NodeID::ANY,
                        label: Label::Positional(1),
                        label_span: Span::ANY,
                        value: any_expr!(ExprKind::LiteralInt("2".into())),
                        span: Span::ANY,
                    }
                ]
            )))
        )
    }
}
