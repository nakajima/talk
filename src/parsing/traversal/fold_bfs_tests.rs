#[cfg(test)]
mod tests {
    use super::super::fold_bfs::*;
    use crate::lexing::token_kind::TokenKind;
    use crate::name::Name;
    use crate::node::Node;
    use crate::node_id::NodeID;
    use crate::node_kinds::{
        block::Block,
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        pattern::{Pattern, PatternKind},
        stmt::{Stmt, StmtKind},
    };
    use crate::span::Span;

    #[test]
    fn test_breadth_first_traversal_order() {
        struct BfsTracker {
            events: Vec<(usize, String)>, // (depth, description)
        }

        impl BfsFold for BfsTracker {
            fn begin_level(&mut self, depth: usize) {
                self.events.push((depth, format!("begin_level_{depth}",)));
            }

            fn end_level(&mut self, depth: usize) {
                self.events.push((depth, format!("end_level_{depth}",)));
            }

            fn enter_node(&mut self, node: &Node, depth: usize) {
                if matches!(node, Node::Expr(_)) {
                    self.events.push((depth, "node:expr".to_string()));
                }
            }

            fn enter_expr(&mut self, expr: &Expr, depth: usize) {
                match &expr.kind {
                    ExprKind::Variable(name) => {
                        self.events.push((depth, format!("var:{name:?}")));
                    }
                    ExprKind::Binary(_, _, _) => {
                        self.events.push((depth, "binary".to_string()));
                    }
                    _ => {}
                }
            }
        }

        // Create a binary expression tree: (a + b) + (c + d)
        let tree = Expr {
            id: NodeID::ANY,
            span: Span::ANY,
            kind: ExprKind::Binary(
                Box::new(Expr {
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
                }),
                TokenKind::Plus,
                Box::new(Expr {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: ExprKind::Binary(
                        Box::new(Expr {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: ExprKind::Variable(Name::from("c")),
                        }),
                        TokenKind::Plus,
                        Box::new(Expr {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: ExprKind::Variable(Name::from("d")),
                        }),
                    ),
                }),
            ),
        };

        let mut tracker = BfsTracker { events: vec![] };
        tracker.traverse(Node::Expr(tree));

        // Check that we visit level by level
        // Level 0: Node wrapper
        // Level 1: root binary expr
        // Level 2: left binary, right binary
        // Level 3: a, b, c, d
        let expected = vec![
            (0, "begin_level_0".to_string()),
            (0, "node:expr".to_string()), // Node::Expr wrapper
            (0, "end_level_0".to_string()),
            (1, "begin_level_1".to_string()),
            (1, "binary".to_string()), // root expr
            (1, "end_level_1".to_string()),
            (2, "begin_level_2".to_string()),
            (2, "binary".to_string()), // left subtree
            (2, "binary".to_string()), // right subtree
            (2, "end_level_2".to_string()),
            (3, "begin_level_3".to_string()),
            (3, "var:Raw(\"a\")".to_string()),
            (3, "var:Raw(\"b\")".to_string()),
            (3, "var:Raw(\"c\")".to_string()),
            (3, "var:Raw(\"d\")".to_string()),
            (3, "end_level_3".to_string()),
        ];

        assert_eq!(tracker.events, expected);
    }

    #[test]
    fn test_bfs_with_nested_blocks() {
        struct BlockDepthTracker {
            blocks_at_depth: Vec<usize>, // Count of blocks at each depth
        }

        impl BfsFold for BlockDepthTracker {
            fn enter_block(&mut self, _block: &Block, depth: usize) {
                // Ensure we have enough slots
                while self.blocks_at_depth.len() <= depth {
                    self.blocks_at_depth.push(0);
                }
                self.blocks_at_depth[depth] += 1;
            }
        }

        // Create nested blocks
        let nested = Block {
            id: NodeID::ANY,
            span: Span::ANY,
            args: vec![],
            body: vec![
                Node::Expr(Expr {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: ExprKind::Block(Block {
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
                    }),
                }),
                Node::Expr(Expr {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: ExprKind::Block(Block {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        args: vec![],
                        body: vec![],
                    }),
                }),
            ],
        };

        let mut tracker = BlockDepthTracker {
            blocks_at_depth: vec![],
        };
        tracker.traverse(Node::Block(nested));

        // The structure is:
        // Depth 0: Node::Block wrapper
        // Depth 1: 1 block (root)
        // Depth 2: 2 Node::Expr in body
        // Depth 3: 2 Expr nodes
        // Depth 4: 2 blocks (the two child blocks)
        // Depth 5: 1 Node::Expr in first child block
        // Depth 6: 1 Expr node
        // Depth 7: 1 block (nested in first child)

        // blocks_at_depth shows blocks are at depths: 1, 4, 7
        // With an extra spot at position 4 that has 2 blocks
        let expected = vec![0, 1, 0, 0, 2, 0, 0, 1];
        assert_eq!(tracker.blocks_at_depth, expected);
    }

    #[test]
    fn test_bfs_with_declarations() {
        struct DeclVisitor {
            decl_order: Vec<String>,
            level_info: Vec<(usize, String)>,
        }

        impl BfsFold for DeclVisitor {
            fn enter_decl(&mut self, decl: &Decl, depth: usize) {
                let name = match &decl.kind {
                    DeclKind::Func { name, .. } => format!("func:{name:?}"),
                    DeclKind::Let { .. } => "let".to_string(),
                    DeclKind::Struct { name, .. } => format!("struct:{name:?}"),
                    _ => "other".to_string(),
                };
                self.decl_order.push(name.clone());
                self.level_info.push((depth, name));
            }
        }

        let func_with_nested = Decl {
            id: NodeID::ANY,
            span: Span::ANY,
            kind: DeclKind::Func {
                name: Name::from("outer"),
                generics: vec![],
                params: vec![],
                body: Block {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    args: vec![],
                    body: vec![
                        Node::Decl(Decl {
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
                        }),
                        Node::Decl(Decl {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: DeclKind::Func {
                                name: Name::from("inner"),
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
                        }),
                    ],
                },
                ret: None,
                attributes: vec![],
            },
        };

        let mut visitor = DeclVisitor {
            decl_order: vec![],
            level_info: vec![],
        };
        visitor.traverse(Node::Decl(func_with_nested));

        // Should visit outer first (depth 1, after Node wrapper), then let and inner (depth 3, after block at depth 2)
        assert_eq!(
            visitor.decl_order,
            vec!["func:Raw(\"outer\")", "let", "func:Raw(\"inner\")"]
        );

        // Check depths
        assert_eq!(visitor.level_info[0].0, 1); // outer at depth 1 (after Node wrapper)
        assert_eq!(visitor.level_info[1].0, 4); // let at depth 4 (Node -> Decl -> Block -> Node -> Decl)
        assert_eq!(visitor.level_info[2].0, 4); // inner at depth 4
    }

    #[test]
    fn test_bfs_if_statement() {
        struct IfTraverser {
            visit_order: Vec<String>,
        }

        impl BfsFold for IfTraverser {
            fn enter_stmt(&mut self, stmt: &Stmt, depth: usize) {
                if matches!(stmt.kind, StmtKind::If(_, _)) {
                    self.visit_order.push(format!("if_at_depth_{depth}",));
                }
            }

            fn enter_expr(&mut self, expr: &Expr, depth: usize) {
                match &expr.kind {
                    ExprKind::LiteralTrue => {
                        self.visit_order.push(format!("true_at_depth_{depth}",));
                    }
                    ExprKind::LiteralInt(s) => {
                        self.visit_order.push(format!("int_{s}_at_depth_{depth}",));
                    }
                    _ => {}
                }
            }

            fn enter_block(&mut self, _block: &Block, depth: usize) {
                self.visit_order.push(format!("block_at_depth_{depth}"));
            }
        }

        let if_stmt = Stmt {
            id: NodeID::ANY,
            span: Span::ANY,
            kind: StmtKind::If(
                Expr {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: ExprKind::LiteralTrue,
                },
                Block {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    args: vec![],
                    body: vec![Node::Expr(Expr {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        kind: ExprKind::LiteralInt("42".to_string()),
                    })],
                },
            ),
        };

        let mut traverser = IfTraverser {
            visit_order: vec![],
        };
        traverser.traverse(Node::Stmt(if_stmt));

        // BFS order:
        // Depth 0: Node::Stmt wrapper
        // Depth 1: if statement
        // Depth 2: condition (true) and block
        // Depth 3: Node::Expr in block body
        // Depth 4: literal int
        assert_eq!(
            traverser.visit_order,
            vec![
                "if_at_depth_1",
                "true_at_depth_2",
                "block_at_depth_2",
                "int_42_at_depth_4"
            ]
        );
    }

    #[test]
    fn test_bfs_maintains_sibling_order() {
        struct SiblingTracker {
            expr_order: Vec<String>,
        }

        impl BfsFold for SiblingTracker {
            fn enter_expr(&mut self, expr: &Expr, _depth: usize) {
                if let ExprKind::LiteralInt(s) = &expr.kind {
                    self.expr_order.push(s.clone());
                }
            }
        }

        let block = Block {
            id: NodeID::ANY,
            span: Span::ANY,
            args: vec![],
            body: vec![
                Node::Expr(Expr {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: ExprKind::LiteralInt("1".to_string()),
                }),
                Node::Expr(Expr {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: ExprKind::LiteralInt("2".to_string()),
                }),
                Node::Expr(Expr {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: ExprKind::LiteralInt("3".to_string()),
                }),
                Node::Expr(Expr {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: ExprKind::Binary(
                        Box::new(Expr {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: ExprKind::LiteralInt("4".to_string()),
                        }),
                        TokenKind::Plus,
                        Box::new(Expr {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: ExprKind::LiteralInt("5".to_string()),
                        }),
                    ),
                }),
            ],
        };

        let mut tracker = SiblingTracker { expr_order: vec![] };
        tracker.traverse(Node::Block(block));

        // Should visit siblings in order at same depth before descending
        assert_eq!(tracker.expr_order, vec!["1", "2", "3", "4", "5"]);
    }
}
