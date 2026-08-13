use derive_visitor::{DriveMut, VisitorMut};

use crate::{
    ast::{AST, Parsed},
    id_generator::IDGenerator,
    label::Label,
    node::Node,
    node_id::NodeID,
    node_kinds::{
        block::Block,
        call_arg::{CallArg, CallArgOrigin},
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
                                origin: CallArgOrigin::Synthesized,
                                mode: None,
                                mode_span: None,
                                id: expr.id,
                                label: Label::Named("lower".into()),
                                label_span: expr.span,
                                value: *lhs,
                                span: expr.span,
                            },
                            CallArg {
                                origin: CallArgOrigin::Synthesized,
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
                        TokenKind::Star => ("Multiply", Label::Named("multiply".into())),
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
                                origin: CallArgOrigin::Synthesized,
                                mode: None,
                                mode_span: None,
                                id: expr.id,
                                label: Label::Positional(0),
                                label_span: expr.span,
                                value: *lhs,
                                span: expr.span,
                            },
                            CallArg {
                                origin: CallArgOrigin::Synthesized,
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

