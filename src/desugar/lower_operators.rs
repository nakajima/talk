use derive_visitor::{DriveMut, VisitorMut};

use crate::{
    ast::{AST, Parsed},
    id_generator::IDGenerator,
    label::Label,
    node::Node,
    node_id::NodeID,
    node_kinds::{
        block::Block,
        call_arg::CallArg,
        expr::{Expr, ExprKind},
    },
    span::Span,
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
            ExprKind::Unary(
                TokenKind::Minus,
                box Expr {
                    kind: ExprKind::LiteralInt(value),
                    ..
                },
            ) => ExprKind::LiteralInt(format!("-{value}")),
            ExprKind::Unary(op, rhs) => {
                let label = match op {
                    TokenKind::Bang => Label::Named("not".into()),
                    TokenKind::Minus => Label::Named("negated".into()),
                    TokenKind::Tilde => Label::Named("complement".into()),
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
                    trailing_block: None,
                    desugared_operator: None,
                }
            }
            ExprKind::Binary(lhs, op, box rhs) => {
                if op == TokenKind::AmpAmp {
                    ExprKind::If(
                        lhs,
                        Block {
                            id: rhs.id,
                            span: rhs.span,
                            args: Default::default(),
                            body: vec![Node::Expr(rhs)],
                        },
                        Block {
                            id: expr.id,
                            span: expr.span,
                            args: Default::default(),
                            body: vec![Node::Expr(Expr {
                                id: NodeID(expr.id.0, self.node_ids.next_id()),
                                kind: ExprKind::LiteralFalse,
                                span: Span::SYNTHESIZED,
                            })],
                        },
                    )
                } else if op == TokenKind::PipePipe {
                    ExprKind::If(
                        lhs,
                        Block {
                            id: expr.id,
                            span: expr.span,
                            args: Default::default(),
                            body: vec![Node::Expr(Expr {
                                id: NodeID(expr.id.0, self.node_ids.next_id()),
                                kind: ExprKind::LiteralTrue,
                                span: Span::SYNTHESIZED,
                            })],
                        },
                        Block {
                            id: rhs.id,
                            span: rhs.span,
                            args: Default::default(),
                            body: vec![Node::Expr(rhs)],
                        },
                    )
                } else if matches!(op, TokenKind::DotDot | TokenKind::DotDotLess) {
                    // Range operators construct the core range types
                    // directly, like Swift: `a..b` is an inclusive
                    // ClosedRange, `a..<b` a half-open Range.
                    let range_type = if op == TokenKind::DotDot {
                        "ClosedRange"
                    } else {
                        "Range"
                    };
                    let span = lhs.span;
                    let constructor = Expr {
                        id: NodeID(expr.id.0, self.node_ids.next_id()),
                        span,
                        kind: ExprKind::Variable(range_type.into()),
                    };
                    ExprKind::Call {
                        callee: constructor.into(),
                        type_args: vec![],
                        args: vec![
                            CallArg {
                                mode: None,
                                mode_span: None,
                                id: expr.id,
                                label: Label::Named("lower".into()),
                                label_span: expr.span,
                                value: *lhs,
                                span: expr.span,
                            },
                            CallArg {
                                mode: None,
                                mode_span: None,
                                id: rhs.id,
                                label: Label::Named("upper".into()),
                                label_span: rhs.span,
                                value: rhs,
                                span: expr.span,
                            },
                        ],
                        trailing_block: None,
                        desugared_operator: None,
                    }
                } else {
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

                        // Bitwise
                        TokenKind::Amp => ("BitwiseAnd", Label::Named("bitAnd".into())),
                        TokenKind::Pipe => ("BitwiseOr", Label::Named("bitOr".into())),
                        TokenKind::Caret => ("BitwiseXor", Label::Named("bitXor".into())),
                        TokenKind::LessLess => ("ShiftLeft", Label::Named("shiftLeft".into())),
                        TokenKind::GreaterGreater => {
                            ("ShiftRight", Label::Named("shiftRight".into()))
                        }
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
                                mode: None,
                                mode_span: None,
                                id: expr.id,
                                label: Label::Positional(0),
                                label_span: expr.span,
                                value: *lhs,
                                span: expr.span,
                            },
                            CallArg {
                                mode: None,
                                mode_span: None,
                                id: rhs.id,
                                label: Label::Positional(1),
                                label_span: rhs.span,
                                value: rhs,
                                span: expr.span,
                            },
                        ],
                        trailing_block: None,
                        desugared_operator: matches!(
                            op,
                            TokenKind::EqualsEquals | TokenKind::BangEquals
                        )
                        .then_some(op),
                    }
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
        any_expr, any_stmt, assert_eq_diff,
        desugar::lower_operators::LowerOperators,
        invocation,
        label::Label,
        node_id::NodeID,
        node_kinds::{call_arg::CallArg, expr::ExprKind, stmt::StmtKind},
        parser_tests::tests::parse,
        span::Span,
    };

    #[test]
    fn folds_negative_integer_literals_before_operator_lowering() {
        let mut parsed = parse("-9_223_372_036_854_775_808");
        LowerOperators::run(&mut parsed);

        assert_eq_diff!(
            *parsed.roots[0].as_stmt(),
            any_stmt!(StmtKind::Expr(any_expr!(ExprKind::LiteralInt(
                "-9_223_372_036_854_775_808".into()
            ))))
        )
    }

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
                        mode: None,
                        mode_span: None,
                        id: NodeID::ANY,
                        label: Label::Positional(0),
                        label_span: Span::ANY,
                        value: any_expr!(ExprKind::LiteralInt("1".into())),
                        span: Span::ANY,
                    },
                    CallArg {
                        mode: None,
                        mode_span: None,
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
                        mode: None,
                        mode_span: None,
                        id: NodeID::ANY,
                        label: Label::Positional(0),
                        label_span: Span::ANY,
                        value: any_expr!(ExprKind::LiteralInt("1".into())),
                        span: Span::ANY,
                    },
                    CallArg {
                        mode: None,
                        mode_span: None,
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
                        mode: None,
                        mode_span: None,
                        id: NodeID::ANY,
                        label: Label::Positional(0),
                        label_span: Span::ANY,
                        value: any_expr!(ExprKind::LiteralInt("1".into())),
                        span: Span::ANY,
                    },
                    CallArg {
                        mode: None,
                        mode_span: None,
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
                        mode: None,
                        mode_span: None,
                        id: NodeID::ANY,
                        label: Label::Positional(0),
                        label_span: Span::ANY,
                        value: any_expr!(ExprKind::LiteralInt("1".into())),
                        span: Span::ANY,
                    },
                    CallArg {
                        mode: None,
                        mode_span: None,
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

    fn assert_lowers_range_literal(source: &'static str, expected_type: &str) {
        let mut parsed = parse(source);
        LowerOperators::run(&mut parsed);

        let StmtKind::Expr(expr) = &parsed.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        let ExprKind::Call { callee, args, .. } = &expr.kind else {
            panic!("expected call, got {:?}", expr.kind);
        };
        let ExprKind::Variable(range_type) = &callee.kind else {
            panic!("expected range constructor callee, got {:?}", callee.kind);
        };

        assert_eq!(range_type.name_str(), expected_type);
        assert_eq!(args.len(), 2);
        assert_eq!(args[0].label, Label::Named("lower".into()));
        assert_eq!(args[1].label, Label::Named("upper".into()));
    }

    #[test]
    fn lowers_inclusive_range_literal() {
        assert_lowers_range_literal("1..3", "ClosedRange");
    }

    #[test]
    fn lowers_half_open_range_literal() {
        assert_lowers_range_literal("1..<3", "Range");
    }

    #[test]
    fn range_binds_tighter_than_equality_looser_than_addition() {
        let mut parsed = parse("0..n - 1 == r");
        LowerOperators::run(&mut parsed);

        // `(0..(n - 1)) == r`: the equality callee receives the range
        // construction as its first argument.
        let StmtKind::Expr(expr) = &parsed.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        let ExprKind::Call { callee, args, .. } = &expr.kind else {
            panic!("expected call, got {:?}", expr.kind);
        };
        let ExprKind::Member(Some(receiver), Label::Named(method), _) = &callee.kind else {
            panic!("expected equality callee, got {:?}", callee.kind);
        };
        assert!(
            matches!(&receiver.kind, ExprKind::Variable(name) if name.name_str() == "Equatable")
        );
        assert_eq!(method, "equals");
        let ExprKind::Call { callee, .. } = &args[0].value.kind else {
            panic!(
                "expected range construction lhs, got {:?}",
                args[0].value.kind
            );
        };
        assert!(
            matches!(&callee.kind, ExprKind::Variable(name) if name.name_str() == "ClosedRange")
        );
    }

    fn assert_lowers_binary(source: &'static str, expected_protocol: &str, expected_method: &str) {
        let mut parsed = parse(source);
        LowerOperators::run(&mut parsed);

        let StmtKind::Expr(expr) = &parsed.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        let ExprKind::Call { callee, args, .. } = &expr.kind else {
            panic!("expected call, got {:?}", expr.kind);
        };
        let ExprKind::Member(Some(receiver), Label::Named(method), _) = &callee.kind else {
            panic!("expected protocol method callee, got {:?}", callee.kind);
        };
        let ExprKind::Variable(protocol) = &receiver.kind else {
            panic!("expected protocol receiver, got {:?}", receiver.kind);
        };

        assert_eq!(protocol.name_str(), expected_protocol);
        assert_eq!(method, expected_method);
        assert_eq!(args.len(), 2);
    }

    #[test]
    fn lowers_bitwise_binary_operators() {
        for (source, protocol, method) in [
            ("1 & 2", "BitwiseAnd", "bitAnd"),
            ("1 | 2", "BitwiseOr", "bitOr"),
            ("1 ^ 2", "BitwiseXor", "bitXor"),
            ("1 << 2", "ShiftLeft", "shiftLeft"),
            ("1 >> 2", "ShiftRight", "shiftRight"),
        ] {
            assert_lowers_binary(source, protocol, method);
        }
    }

    #[test]
    fn lowers_bitwise_complement() {
        let mut parsed = parse("~1");
        LowerOperators::run(&mut parsed);

        let StmtKind::Expr(expr) = &parsed.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        let ExprKind::Call { callee, args, .. } = &expr.kind else {
            panic!("expected call, got {:?}", expr.kind);
        };
        let ExprKind::Member(Some(receiver), Label::Named(method), _) = &callee.kind else {
            panic!("expected complement method callee, got {:?}", callee.kind);
        };

        assert_eq!(method, "complement");
        assert!(matches!(receiver.kind, ExprKind::LiteralInt(_)));
        assert!(args.is_empty());
    }
}
