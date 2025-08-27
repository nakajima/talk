#[cfg(test)]
mod tests {
    use super::super::fold_bfs_mut::*;
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
    fn test_bfs_mut_basic_traversal() {
        struct DepthTracker {
            visited_depths: Vec<usize>,
        }

        impl BfsFoldMut for DepthTracker {
            fn begin_level_mut(&mut self, depth: usize) {
                self.visited_depths.push(depth);
            }

            fn enter_node_mut(&mut self, _node: &mut Node, _depth: usize) {
                // Just track that we visited
            }
        }

        // Create a simple tree
        let mut tree = Node::Expr(Expr {
            id: NodeID::ANY,
            span: Span::ANY,
            kind: ExprKind::LiteralInt("42".to_string()),
        });

        let mut tracker = DepthTracker {
            visited_depths: vec![],
        };
        tracker.traverse_mut(&mut tree);

        // Should have visited at least depth 0
        assert!(!tracker.visited_depths.is_empty());
        assert_eq!(tracker.visited_depths[0], 0);
    }

    #[test]
    fn test_bfs_mut_level_tracking() {
        struct LevelTracker {
            levels_visited: Vec<usize>,
        }

        impl BfsFoldMut for LevelTracker {
            fn begin_level_mut(&mut self, depth: usize) {
                self.levels_visited.push(depth);
            }

            fn enter_block_mut(&mut self, block: &mut Block, depth: usize) {
                // Add a marker to block args to show we visited
                block
                    .args
                    .push(Name::from(format!("visited_at_depth_{}", depth)));
            }
        }

        let mut root = Node::Block(Block {
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
        });

        let mut tracker = LevelTracker {
            levels_visited: vec![],
        };
        tracker.traverse_mut(&mut root);

        // Check that we visited the expected levels
        assert!(!tracker.levels_visited.is_empty());
        assert_eq!(tracker.levels_visited[0], 0);

        // Check that blocks were modified
        if let Node::Block(ref block) = root {
            assert!(!block.args.is_empty());
            // The root block should have been visited at depth 1 (after Node wrapper at depth 0)
            assert!(
                block
                    .args
                    .iter()
                    .any(|arg| { format!("{:?}", arg).contains("visited_at_depth_1") })
            );
        }
    }

    #[test]
    fn test_bfs_mut_modify_declarations() {
        struct DeclModifier {
            decl_count: usize,
        }

        impl BfsFoldMut for DeclModifier {
            fn enter_decl_mut(&mut self, decl: &mut Decl, _depth: usize) {
                match &mut decl.kind {
                    DeclKind::Func { name, .. } => {
                        *name = Name::from(format!("func_{}", self.decl_count));
                        self.decl_count += 1;
                    }
                    DeclKind::Let { .. } => {
                        self.decl_count += 1;
                    }
                    _ => {}
                }
            }
        }

        let mut root = Node::Decl(Decl {
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
                    body: vec![Node::Decl(Decl {
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
                    })],
                },
                ret: None,
                attributes: vec![],
            },
        });

        let mut modifier = DeclModifier { decl_count: 0 };
        modifier.traverse_mut(&mut root);

        // Check that the function name was modified
        if let Node::Decl(decl) = &root
            && let DeclKind::Func { name, .. } = &decl.kind
        {
            assert_eq!(*name, Name::from("func_0"));
        }

        // Check that we counted both declarations
        assert_eq!(modifier.decl_count, 2);
    }

    #[test]
    fn test_bfs_mut_breadth_first_order() {
        struct OrderTracker {
            visit_order: Vec<String>,
        }

        impl BfsFoldMut for OrderTracker {
            fn enter_expr_mut(&mut self, expr: &mut Expr, depth: usize) {
                if let ExprKind::LiteralInt(s) = &expr.kind {
                    self.visit_order.push(format!("int_{}@{}", s, depth));
                }
            }
        }

        let mut root = Node::Block(Block {
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
                    kind: ExprKind::Block(Block {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        args: vec![],
                        body: vec![Node::Expr(Expr {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: ExprKind::LiteralInt("3".to_string()),
                        })],
                    }),
                }),
            ],
        });

        let mut tracker = OrderTracker {
            visit_order: vec![],
        };
        tracker.traverse_mut(&mut root);

        // Should visit 1 and 2 at same depth before visiting 3
        assert!(tracker.visit_order.len() >= 3);

        // Find the depths
        let depth_1 = tracker
            .visit_order
            .iter()
            .find(|s| s.starts_with("int_1@"))
            .and_then(|s| s.split('@').nth(1))
            .and_then(|s| s.parse::<usize>().ok());

        let depth_2 = tracker
            .visit_order
            .iter()
            .find(|s| s.starts_with("int_2@"))
            .and_then(|s| s.split('@').nth(1))
            .and_then(|s| s.parse::<usize>().ok());

        let depth_3 = tracker
            .visit_order
            .iter()
            .find(|s| s.starts_with("int_3@"))
            .and_then(|s| s.split('@').nth(1))
            .and_then(|s| s.parse::<usize>().ok());

        if let (Some(d1), Some(d2), Some(d3)) = (depth_1, depth_2, depth_3) {
            // 1 and 2 should be at the same depth
            assert_eq!(d1, d2);
            // 3 should be at a deeper level
            assert!(d3 > d1);
        }
    }
}
