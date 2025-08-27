#[cfg(test)]
mod tests {
    use super::super::fold_mut::*;
    use crate::lexing::token_kind::TokenKind;
    use crate::name::Name;
    use crate::node::Node;
    use crate::node_id::NodeID;
    use crate::node_kinds::{
        block::Block,
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        pattern::{Pattern, PatternKind},
    };
    use crate::span::Span;

    #[test]
    fn test_mutate_node_ids() {
        struct IdReplacer {
            next_id: u32,
        }

        impl FoldMut for IdReplacer {
            fn enter_expr_mut(&mut self, expr: &mut Expr) {
                expr.id = NodeID(self.next_id);
                self.next_id += 1;
            }

            fn enter_block_mut(&mut self, block: &mut Block) {
                block.id = NodeID(self.next_id);
                self.next_id += 1;
            }
        }

        let mut expr = Expr {
            id: NodeID::ANY,
            span: Span::ANY,
            kind: ExprKind::Block(Block {
                id: NodeID::ANY,
                span: Span::ANY,
                args: vec![],
                body: vec![Node::Expr(Expr {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: ExprKind::LiteralInt("42".to_string()),
                })],
            }),
        };

        let mut replacer = IdReplacer { next_id: 100 };
        replacer.fold_expr_mut(&mut expr);

        // Check that IDs were replaced
        assert_eq!(expr.id, NodeID(100));
        if let ExprKind::Block(ref block) = expr.kind {
            assert_eq!(block.id, NodeID(101));
            if let Node::Expr(ref inner_expr) = block.body[0] {
                assert_eq!(inner_expr.id, NodeID(102));
            }
        }
    }

    #[test]
    fn test_mutate_variable_names() {
        struct VariableRenamer {
            prefix: String,
            counter: usize,
        }

        impl FoldMut for VariableRenamer {
            fn enter_expr_mut(&mut self, expr: &mut Expr) {
                if let ExprKind::Variable(ref mut name) = expr.kind {
                    *name = Name::from(format!("{}_{}", self.prefix, self.counter));
                    self.counter += 1;
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

        let mut renamer = VariableRenamer {
            prefix: "var".to_string(),
            counter: 0,
        };
        renamer.fold_expr_mut(&mut expr);

        // Check that variables were renamed
        if let ExprKind::Binary(ref lhs, _, ref rhs) = expr.kind {
            match &lhs.kind {
                ExprKind::Variable(name) => assert_eq!(*name, Name::from("var_0")),
                _ => panic!("Expected Variable"),
            }
            match &rhs.kind {
                ExprKind::Variable(name) => assert_eq!(*name, Name::from("var_1")),
                _ => panic!("Expected Variable"),
            }
        }
    }

    #[test]
    fn test_enter_exit_order_mut() {
        struct OrderTracker {
            events: Vec<String>,
        }

        impl FoldMut for OrderTracker {
            fn enter_expr_mut(&mut self, expr: &mut Expr) {
                match &expr.kind {
                    ExprKind::Binary(_, _, _) => self.events.push("enter:binary".to_string()),
                    ExprKind::Variable(name) => self.events.push(format!("enter:var:{name:?}")),
                    _ => {}
                }
            }

            fn exit_expr_mut(&mut self, expr: &mut Expr) {
                match &expr.kind {
                    ExprKind::Binary(_, _, _) => self.events.push("exit:binary".to_string()),
                    ExprKind::Variable(name) => self.events.push(format!("exit:var:{name:?}")),
                    _ => {}
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
                    kind: ExprKind::Variable(Name::from("a")),
                }),
                TokenKind::Plus,
                Box::new(Expr {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: ExprKind::Variable(Name::from("b")),
                }),
            ),
        };

        let mut tracker = OrderTracker { events: vec![] };
        tracker.fold_expr_mut(&mut expr);

        assert_eq!(
            tracker.events,
            vec![
                "enter:binary",
                "enter:var:Raw(\"a\")",
                "exit:var:Raw(\"a\")",
                "enter:var:Raw(\"b\")",
                "exit:var:Raw(\"b\")",
                "exit:binary"
            ]
        );
    }

    #[test]
    fn test_mutate_specific_decl_variant() {
        struct FuncModifier {
            functions_seen: usize,
        }

        impl FoldMut for FuncModifier {
            fn enter_decl_func_mut(&mut self, decl: &mut Decl) {
                if let DeclKind::Func { ref mut name, .. } = decl.kind {
                    self.functions_seen += 1;
                    *name = Name::from(format!("modified_{}", self.functions_seen));
                }
            }
        }

        let mut func_decl = Decl {
            id: NodeID::ANY,
            span: Span::ANY,
            kind: DeclKind::Func {
                name: Name::from("original"),
                generics: vec![],
                params: vec![],
                body: Block {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    args: vec![],
                    body: vec![],
                },
                ret: None,
                attributes: vec![],
            },
        };

        let mut modifier = FuncModifier { functions_seen: 0 };
        modifier.fold_decl_mut(&mut func_decl);

        match &func_decl.kind {
            DeclKind::Func { name, .. } => {
                assert_eq!(*name, Name::from("modified_1"));
            }
            _ => panic!("Expected Func declaration"),
        }
        assert_eq!(modifier.functions_seen, 1);
    }

    #[test]
    fn test_mutate_let_declarations() {
        struct LetMutator;

        impl FoldMut for LetMutator {
            fn enter_decl_let_mut(&mut self, decl: &mut Decl) {
                if let DeclKind::Let {
                    ref mut lhs,
                    ref mut value,
                    ..
                } = decl.kind
                {
                    // Change the binding pattern
                    if let PatternKind::Bind(ref mut name) = lhs.kind {
                        *name = Name::from("mutated_binding");
                    }
                    // Add a value if there isn't one
                    if value.is_none() {
                        *value = Some(Expr {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: ExprKind::LiteralInt("0".to_string()),
                        });
                    }
                }
            }
        }

        let mut let_decl = Decl {
            id: NodeID::ANY,
            span: Span::ANY,
            kind: DeclKind::Let {
                lhs: Pattern {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: PatternKind::Bind(Name::from("x")),
                },
                type_annotation: None,
                value: None,
            },
        };

        let mut mutator = LetMutator;
        mutator.fold_decl_mut(&mut let_decl);

        match &let_decl.kind {
            DeclKind::Let { lhs, value, .. } => {
                match &lhs.kind {
                    PatternKind::Bind(name) => {
                        assert_eq!(*name, Name::from("mutated_binding"));
                    }
                    _ => panic!("Expected Bind pattern"),
                }
                assert!(value.is_some());
                if let Some(expr) = value {
                    match &expr.kind {
                        ExprKind::LiteralInt(s) => assert_eq!(s, "0"),
                        _ => panic!("Expected LiteralInt"),
                    }
                }
            }
            _ => panic!("Expected Let declaration"),
        }
    }

    #[test]
    fn test_depth_tracking_with_mutation() {
        struct DepthAnnotator {
            depth: usize,
        }

        impl FoldMut for DepthAnnotator {
            fn enter_block_mut(&mut self, block: &mut Block) {
                self.depth += 1;
                // Mutate the block by adding the depth as a fake argument name
                block.args.push(Name::from(format!("depth_{}", self.depth)));
            }

            fn exit_block_mut(&mut self, _block: &mut Block) {
                self.depth -= 1;
            }
        }

        let mut nested_block = Block {
            id: NodeID::ANY,
            span: Span::ANY,
            args: vec![],
            body: vec![Node::Expr(Expr {
                id: NodeID::ANY,
                span: Span::ANY,
                kind: ExprKind::Block(Block {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    args: vec![],
                    body: vec![],
                }),
            })],
        };

        let mut annotator = DepthAnnotator { depth: 0 };
        annotator.fold_block_mut(&mut nested_block);

        // Check that depths were added as arguments
        assert_eq!(nested_block.args, vec![Name::from("depth_1")]);
        if let Node::Expr(ref expr) = nested_block.body[0]
            && let ExprKind::Block(ref inner_block) = expr.kind
        {
            assert_eq!(inner_block.args, vec![Name::from("depth_2")]);
        }
    }
}
