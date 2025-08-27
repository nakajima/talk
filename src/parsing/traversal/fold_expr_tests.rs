#[cfg(test)]
mod tests {
    use super::super::fold::*;
    use super::super::fold_mut::*;
    use crate::lexing::token_kind::TokenKind;
    use crate::name::Name;
    use crate::node_id::NodeID;
    use crate::node_kinds::expr::{Expr, ExprKind};
    use crate::span::Span;

    #[test]
    fn test_specific_expr_variant_enter_exit() {
        #[derive(Debug)]
        struct ExprTracker {
            events: Vec<String>,
        }

        impl Fold for ExprTracker {
            fn enter_expr_binary(&mut self, _expr: &Expr) {
                self.events.push("enter:binary".to_string());
            }
            fn exit_expr_binary(&mut self, _expr: &Expr) {
                self.events.push("exit:binary".to_string());
            }
            fn enter_expr_variable(&mut self, expr: &Expr) {
                if let ExprKind::Variable(name) = &expr.kind {
                    self.events.push(format!("enter:var:{name:?}"));
                }
            }
            fn exit_expr_variable(&mut self, expr: &Expr) {
                if let ExprKind::Variable(name) = &expr.kind {
                    self.events.push(format!("exit:var:{name:?}"));
                }
            }
            fn enter_expr_literal_int(&mut self, expr: &Expr) {
                if let ExprKind::LiteralInt(s) = &expr.kind {
                    self.events.push(format!("enter:int:{s}"));
                }
            }
            fn exit_expr_literal_int(&mut self, expr: &Expr) {
                if let ExprKind::LiteralInt(s) = &expr.kind {
                    self.events.push(format!("exit:int:{s}"));
                }
            }
        }

        let expr = Expr {
            id: NodeID::ANY,
            span: Span::ANY,
            kind: ExprKind::Binary(
                Box::new(Expr {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: ExprKind::Variable(Name::from("x")),
                }),
                TokenKind::Plus,
                Box::new(Expr {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: ExprKind::LiteralInt("42".to_string()),
                }),
            ),
        };

        let mut tracker = ExprTracker { events: vec![] };
        let _ = tracker.fold_expr(expr);

        assert_eq!(
            tracker.events,
            vec![
                "enter:binary",
                "enter:var:Raw(\"x\")",
                "exit:var:Raw(\"x\")",
                "enter:int:42",
                "exit:int:42",
                "exit:binary",
            ]
        );
    }

    #[test]
    fn test_specific_expr_variant_enter_exit_mut() {
        struct ExprMutator {
            events: Vec<String>,
        }

        impl FoldMut for ExprMutator {
            fn enter_expr_binary_mut(&mut self, _expr: &mut Expr) {
                self.events.push("enter:binary".to_string());
            }
            fn exit_expr_binary_mut(&mut self, _expr: &mut Expr) {
                self.events.push("exit:binary".to_string());
            }
            fn enter_expr_variable_mut(&mut self, expr: &mut Expr) {
                if let ExprKind::Variable(ref mut name) = expr.kind {
                    self.events.push(format!("enter:var:{name:?}"));
                    // Mutate the variable name
                    let current = format!("{name:?}",);
                    let base = current.trim_start_matches("Raw(\"").trim_end_matches("\")");
                    *name = Name::from(format!("{base}_modified",));
                }
            }
            fn exit_expr_variable_mut(&mut self, expr: &mut Expr) {
                if let ExprKind::Variable(ref name) = expr.kind {
                    self.events.push(format!("exit:var:{name:?}"));
                }
            }
        }

        let mut expr = Expr {
            id: NodeID::ANY,
            span: Span::ANY,
            kind: ExprKind::Binary(
                Box::new(Expr {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: ExprKind::Variable(Name::from("x")),
                }),
                TokenKind::Plus,
                Box::new(Expr {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: ExprKind::Variable(Name::from("y")),
                }),
            ),
        };

        let mut mutator = ExprMutator { events: vec![] };
        mutator.fold_expr_mut(&mut expr);

        assert_eq!(
            mutator.events,
            vec![
                "enter:binary",
                "enter:var:Raw(\"x\")",
                "exit:var:Raw(\"x_modified\")", // Modified in enter
                "enter:var:Raw(\"y\")",
                "exit:var:Raw(\"y_modified\")", // Modified in enter
                "exit:binary",
            ]
        );

        // Check that the variables were actually modified
        if let ExprKind::Binary(ref lhs, _, ref rhs) = expr.kind {
            match &lhs.kind {
                ExprKind::Variable(name) => assert_eq!(*name, Name::from("x_modified")),
                _ => panic!("Expected Variable"),
            }
            match &rhs.kind {
                ExprKind::Variable(name) => assert_eq!(*name, Name::from("y_modified")),
                _ => panic!("Expected Variable"),
            }
        }
    }

    #[test]
    fn test_all_expr_variants_called() {
        #[derive(Debug)]
        struct ExprVariantCollector {
            variants_seen: Vec<String>,
        }

        impl Fold for ExprVariantCollector {
            fn enter_expr_literal_true(&mut self, _expr: &Expr) {
                self.variants_seen.push("literal_true".to_string());
            }
            fn enter_expr_literal_false(&mut self, _expr: &Expr) {
                self.variants_seen.push("literal_false".to_string());
            }
            fn enter_expr_if(&mut self, _expr: &Expr) {
                self.variants_seen.push("if".to_string());
            }
            fn enter_expr_block(&mut self, _expr: &Expr) {
                self.variants_seen.push("block".to_string());
            }
        }

        use crate::node_kinds::block::Block;
        let expr = Expr {
            id: NodeID::ANY,
            span: Span::ANY,
            kind: ExprKind::If(
                Box::new(Expr {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: ExprKind::LiteralTrue,
                }),
                Block {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    args: vec![],
                    body: vec![],
                },
                Block {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    args: vec![],
                    body: vec![],
                },
            ),
        };

        let mut collector = ExprVariantCollector {
            variants_seen: vec![],
        };
        let _ = collector.fold_expr(expr);

        assert!(collector.variants_seen.contains(&"if".to_string()));
        assert!(
            collector
                .variants_seen
                .contains(&"literal_true".to_string())
        );
    }
}
