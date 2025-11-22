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
                let lhs_as = Expr {
                    id: NodeID(expr.id.0, self.node_ids.next_id()),
                    span,
                    kind: ExprKind::As(
                        lhs,
                        TypeAnnotation {
                            id: NodeID(expr.id.0, self.node_ids.next_id()),
                            span,
                            kind: TypeAnnotationKind::Nominal {
                                name: protocol_name.into(),
                                name_span: span,
                                generics: vec![],
                            },
                        },
                    ),
                };

                let member = Expr {
                    id: NodeID(expr.id.0, self.node_ids.next_id()),
                    span,
                    kind: ExprKind::Member(Some(lhs_as.into()), label, span),
                };

                ExprKind::Call {
                    callee: member.into(),
                    type_args: vec![],
                    args: vec![CallArg {
                        id: expr.id,
                        label: Label::Positional(0),
                        label_span: expr.span,
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
                ExprKind::As(
                    any_expr!(ExprKind::LiteralInt("1".into())).into(),
                    annotation!(TypeAnnotationKind::Nominal {
                        name: "Add".into(),
                        name_span: Span::ANY,
                        generics: vec![]
                    })
                ),
                "add",
                vec![CallArg {
                    id: NodeID::ANY,
                    label: Label::Positional(0),
                    label_span: Span::ANY,
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
                ExprKind::As(
                    any_expr!(ExprKind::LiteralInt("1".into())).into(),
                    annotation!(TypeAnnotationKind::Nominal {
                        name: "Subtract".into(),
                        name_span: Span::ANY,
                        generics: vec![]
                    })
                ),
                "minus",
                vec![CallArg {
                    id: NodeID::ANY,
                    label: Label::Positional(0),
                    label_span: Span::ANY,
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
                ExprKind::As(
                    any_expr!(ExprKind::LiteralInt("1".into())).into(),
                    annotation!(TypeAnnotationKind::Nominal {
                        name: "Multiply".into(),
                        name_span: Span::ANY,
                        generics: vec![]
                    })
                ),
                "times",
                vec![CallArg {
                    id: NodeID::ANY,
                    label: Label::Positional(0),
                    label_span: Span::ANY,
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
                ExprKind::As(
                    any_expr!(ExprKind::LiteralInt("1".into())).into(),
                    annotation!(TypeAnnotationKind::Nominal {
                        name: "Divide".into(),
                        name_span: Span::ANY,
                        generics: vec![]
                    })
                ),
                "divide",
                vec![CallArg {
                    id: NodeID::ANY,
                    label: Label::Positional(0),
                    label_span: Span::ANY,
                    value: any_expr!(ExprKind::LiteralInt("2".into())),
                    span: Span::ANY,
                }]
            )))
        )
    }
}
