#[cfg(test)]
mod tests {
    use super::super::fold::*;
    use crate::lexing::token_kind::TokenKind;
    use crate::name::Name;
    use crate::node::Node;
    use crate::node_id::NodeID;
    use crate::node_kinds::{
        attribute::Attribute,
        block::Block,
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        generic_decl::GenericDecl,
        parameter::Parameter,
        pattern::{Pattern, PatternKind},
        stmt::{Stmt, StmtKind},
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    };
    use crate::span::Span;

    // A simple fold implementation that counts nodes
    #[derive(Debug)]
    struct NodeCounter {
        count: usize,
    }

    impl Fold for NodeCounter {
        fn fold_node(&mut self, node: Node) -> Node {
            self.count += 1;
            walk_node(self, node)
        }
    }

    #[test]
    fn test_count_nodes_in_simple_expr() {
        let expr = Expr {
            id: NodeID::ANY,
            span: Span::ANY,
            kind: ExprKind::LiteralInt("42".to_string()),
        };

        let mut counter = NodeCounter { count: 0 };
        let _ = counter.fold_expr(expr);
        assert_eq!(counter.count, 0); // Literals don't create Node wrappers
    }

    #[test]
    fn test_count_nodes_in_block() {
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
            ],
        };

        let mut counter = NodeCounter { count: 0 };
        let _ = counter.fold_block(block);
        assert_eq!(counter.count, 2); // Two Node::Expr in the body
    }

    // A fold that transforms all integer literals
    struct IntTransformer {
        transform_fn: Box<dyn Fn(String) -> String>,
    }
    impl std::fmt::Debug for IntTransformer {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "")
        }
    }

    impl Fold for IntTransformer {
        fn fold_expr(&mut self, expr: Expr) -> Expr {
            let mut expr = walk_expr(self, expr);
            if let ExprKind::LiteralInt(ref mut s) = expr.kind {
                *s = (self.transform_fn)(s.clone());
            }
            expr
        }
    }

    #[test]
    fn test_transform_integers() {
        let expr = Expr {
            id: NodeID::ANY,
            span: Span::ANY,
            kind: ExprKind::Binary(
                Box::new(Expr {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: ExprKind::LiteralInt("10".to_string()),
                }),
                TokenKind::Plus,
                Box::new(Expr {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: ExprKind::LiteralInt("20".to_string()),
                }),
            ),
        };

        let mut transformer = IntTransformer {
            transform_fn: Box::new(|s| format!("{s}0")),
        };
        let result = transformer.fold_expr(expr);

        match result.kind {
            ExprKind::Binary(lhs, _, rhs) => {
                match lhs.kind {
                    ExprKind::LiteralInt(s) => assert_eq!(s, "100"),
                    _ => panic!("Expected LiteralInt"),
                }
                match rhs.kind {
                    ExprKind::LiteralInt(s) => assert_eq!(s, "200"),
                    _ => panic!("Expected LiteralInt"),
                }
            }
            _ => panic!("Expected Binary expression"),
        }
    }

    // A fold that renames all variables
    #[derive(Debug)]
    struct VariableRenamer {
        mapping: std::collections::HashMap<Name, Name>,
    }

    impl Fold for VariableRenamer {
        fn fold_expr(&mut self, expr: Expr) -> Expr {
            let mut expr = walk_expr(self, expr);
            if let ExprKind::Variable(ref mut name) = expr.kind
                && let Some(new_name) = self.mapping.get(name)
            {
                *name = new_name.clone();
            }
            expr
        }

        fn fold_name(&mut self, name: Name) -> Name {
            self.mapping.get(&name).cloned().unwrap_or(name)
        }
    }

    #[test]
    fn test_rename_variables() {
        let expr = Expr {
            id: NodeID::ANY,
            span: Span::ANY,
            kind: ExprKind::Variable(Name::from("old_name")),
        };

        let mut mapping = std::collections::HashMap::new();
        mapping.insert(Name::from("old_name"), Name::from("new_name"));

        let mut renamer = VariableRenamer { mapping };
        let result = renamer.fold_expr(expr);

        match result.kind {
            ExprKind::Variable(name) => assert_eq!(name, Name::from("new_name")),
            _ => panic!("Expected Variable"),
        }
    }

    #[test]
    fn test_fold_function_declaration() {
        let func = Decl {
            id: NodeID::ANY,
            span: Span::ANY,
            kind: DeclKind::Func {
                name: Name::from("test_func"),
                generics: vec![],
                params: vec![Parameter {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    name: Name::from("x"),
                    type_annotation: Some(TypeAnnotation {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        kind: TypeAnnotationKind::Nominal {
                            name: Name::from("Int"),
                            generics: vec![],
                        },
                    }),
                }],
                body: Block {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    args: vec![],
                    body: vec![Node::Stmt(Stmt {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        kind: StmtKind::Return(Some(Expr {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: ExprKind::Variable(Name::from("x")),
                        })),
                    })],
                },
                ret: Some(TypeAnnotation {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: TypeAnnotationKind::Nominal {
                        name: Name::from("Int"),
                        generics: vec![],
                    },
                }),
                attributes: vec![],
            },
        };

        let mut counter = NodeCounter { count: 0 };
        let _ = counter.fold_decl(func);
        assert_eq!(counter.count, 1); // One Node::Stmt in the body
    }

    #[test]
    fn test_fold_pattern_matching() {
        let pattern = Pattern {
            id: NodeID::ANY,
            span: Span::ANY,
            kind: PatternKind::Variant {
                enum_name: Some(Name::from("Option")),
                variant_name: "Some".to_string(),
                fields: vec![Pattern {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: PatternKind::Bind(Name::from("x")),
                }],
            },
        };

        #[derive(Debug)]
        struct PatternVariableCollector {
            vars: Vec<Name>,
        }

        impl Fold for PatternVariableCollector {
            fn fold_pattern(&mut self, pattern: Pattern) -> Pattern {
                let pattern = walk_pattern(self, pattern);
                if let PatternKind::Bind(ref name) = pattern.kind {
                    self.vars.push(name.clone());
                }
                pattern
            }
        }

        let mut collector = PatternVariableCollector { vars: vec![] };
        let _ = collector.fold_pattern(pattern);
        assert_eq!(collector.vars, vec![Name::from("x")]);
    }

    #[test]
    fn test_fold_nested_blocks() {
        let inner_block = Block {
            id: NodeID::ANY,
            span: Span::ANY,
            args: vec![],
            body: vec![Node::Expr(Expr {
                id: NodeID::ANY,
                span: Span::ANY,
                kind: ExprKind::LiteralInt("42".to_string()),
            })],
        };

        let outer_block = Block {
            id: NodeID::ANY,
            span: Span::ANY,
            args: vec![],
            body: vec![Node::Expr(Expr {
                id: NodeID::ANY,
                span: Span::ANY,
                kind: ExprKind::Block(inner_block),
            })],
        };

        let mut counter = NodeCounter { count: 0 };
        let _ = counter.fold_block(outer_block);
        assert_eq!(counter.count, 2); // Two Node::Expr total
    }

    #[test]
    fn test_fold_if_statement() {
        let stmt = Stmt {
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
                    body: vec![Node::Stmt(Stmt {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        kind: StmtKind::Expr(Expr {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: ExprKind::LiteralInt("1".to_string()),
                        }),
                    })],
                },
            ),
        };

        let mut counter = NodeCounter { count: 0 };
        let _ = counter.fold_stmt(stmt);
        assert_eq!(counter.count, 1); // One Node::Stmt in the if body
    }

    #[test]
    fn test_fold_type_annotation() {
        let ty = TypeAnnotation {
            id: NodeID::ANY,
            span: Span::ANY,
            kind: TypeAnnotationKind::Func {
                params: vec![TypeAnnotation {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: TypeAnnotationKind::Nominal {
                        name: Name::from("String"),
                        generics: vec![],
                    },
                }],
                returns: Box::new(TypeAnnotation {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: TypeAnnotationKind::Nominal {
                        name: Name::from("Int"),
                        generics: vec![],
                    },
                }),
            },
        };

        #[derive(Debug)]
        struct TypeNameCollector {
            names: Vec<Name>,
        }

        impl Fold for TypeNameCollector {
            fn fold_type_annotation(&mut self, ty: TypeAnnotation) -> TypeAnnotation {
                let ty = walk_type_annotation(self, ty);
                if let TypeAnnotationKind::Nominal { ref name, .. } = ty.kind {
                    self.names.push(name.clone());
                }
                ty
            }
        }

        let mut collector = TypeNameCollector { names: vec![] };
        let _ = collector.fold_type_annotation(ty);
        assert_eq!(
            collector.names,
            vec![Name::from("String"), Name::from("Int")]
        );
    }

    #[test]
    fn test_fold_preserves_structure() {
        // Test that folding without changes preserves the exact structure
        #[derive(Debug)]
        struct IdentityFold;
        impl Fold for IdentityFold {}

        let expr = Expr {
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

        let original = expr.clone();
        let mut fold = IdentityFold;
        let result = fold.fold_expr(expr);

        assert_eq!(original, result);
    }

    #[test]
    fn test_enter_exit_callbacks() {
        // Test that enter and exit are called in the correct order
        #[derive(Debug)]
        struct TraversalTracker {
            events: Vec<String>,
        }

        impl Fold for TraversalTracker {
            fn enter_expr(&mut self, expr: &Expr) {
                match &expr.kind {
                    ExprKind::Binary(_, _, _) => self.events.push("enter:binary".to_string()),
                    ExprKind::Variable(name) => self.events.push(format!("enter:var:{name:?}")),
                    _ => {}
                }
            }

            fn exit_expr(&mut self, expr: &Expr) {
                match &expr.kind {
                    ExprKind::Binary(_, _, _) => self.events.push("exit:binary".to_string()),
                    ExprKind::Variable(name) => self.events.push(format!("exit:var:{name:?}")),
                    _ => {}
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

        let mut tracker = TraversalTracker { events: vec![] };
        let _ = tracker.fold_expr(expr);

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
    fn test_override_specific_decl_handler() {
        // Test that we can override specific declaration handlers
        #[derive(Debug)]
        struct FuncRenamer {
            rename_count: usize,
        }

        impl Fold for FuncRenamer {
            fn fold_decl_func(
                &mut self,
                _name: Name,
                generics: Vec<GenericDecl>,
                params: Vec<Parameter>,
                body: Block,
                ret: Option<TypeAnnotation>,
                attributes: Vec<Attribute>,
            ) -> DeclKind {
                // Custom logic: rename all functions
                self.rename_count += 1;
                let new_name = Name::from(format!("renamed_func_{}", self.rename_count));

                // Still need to fold the children
                DeclKind::Func {
                    name: new_name,
                    generics: generics
                        .into_iter()
                        .map(|g| self.fold_generic_decl(g))
                        .collect(),
                    params: params.into_iter().map(|p| self.fold_parameter(p)).collect(),
                    body: self.fold_block(body),
                    ret: ret.map(|r| self.fold_type_annotation(r)),
                    attributes: attributes
                        .into_iter()
                        .map(|a| self.fold_attribute(a))
                        .collect(),
                }
            }
        }

        let func_decl = Decl {
            id: NodeID::ANY,
            span: Span::ANY,
            kind: DeclKind::Func {
                name: Name::from("original_func"),
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

        let mut renamer = FuncRenamer { rename_count: 0 };
        let result = renamer.fold_decl(func_decl);

        match result.kind {
            DeclKind::Func { name, .. } => {
                assert_eq!(name, Name::from("renamed_func_1"));
            }
            _ => panic!("Expected Func declaration"),
        }
        assert_eq!(renamer.rename_count, 1);
    }

    #[test]
    fn test_enter_exit_specific_decl_variants() {
        // Test that enter/exit are called for specific declaration variants
        #[derive(Debug)]
        struct DeclTracker {
            events: Vec<String>,
        }

        impl Fold for DeclTracker {
            fn enter_decl_func(
                &mut self,
                name: &Name,
                _: &[GenericDecl],
                _: &[Parameter],
                _: &Block,
                _: &Option<TypeAnnotation>,
                _: &[Attribute],
            ) {
                self.events.push(format!("enter:func:{name:?}"));
            }

            fn exit_decl_func(
                &mut self,
                name: &Name,
                _: &[GenericDecl],
                _: &[Parameter],
                _: &Block,
                _: &Option<TypeAnnotation>,
                _: &[Attribute],
            ) {
                self.events.push(format!("exit:func:{name:?}"));
            }

            fn enter_decl_let(
                &mut self,
                _lhs: &Pattern,
                _: &Option<TypeAnnotation>,
                value: &Option<Expr>,
            ) {
                if value.is_some() {
                    self.events.push("enter:let:with_value".to_string());
                } else {
                    self.events.push("enter:let:no_value".to_string());
                }
            }

            fn exit_decl_let(
                &mut self,
                _lhs: &Pattern,
                _: &Option<TypeAnnotation>,
                value: &Option<Expr>,
            ) {
                if value.is_some() {
                    self.events.push("exit:let:with_value".to_string());
                } else {
                    self.events.push("exit:let:no_value".to_string());
                }
            }
        }

        // Test with a function declaration
        let func_decl = Decl {
            id: NodeID::ANY,
            span: Span::ANY,
            kind: DeclKind::Func {
                name: Name::from("test_func"),
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

        let mut tracker = DeclTracker { events: vec![] };
        let _ = tracker.fold_decl(func_decl);

        assert_eq!(
            tracker.events,
            vec![
                "enter:func:Raw(\"test_func\")",
                "exit:func:Raw(\"test_func\")"
            ]
        );

        // Test with a let declaration
        let let_decl = Decl {
            id: NodeID::ANY,
            span: Span::ANY,
            kind: DeclKind::Let {
                lhs: Pattern {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: PatternKind::Bind(Name::from("x")),
                },
                type_annotation: None,
                value: Some(Expr {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: ExprKind::LiteralInt("42".to_string()),
                }),
            },
        };

        tracker.events.clear();
        let _ = tracker.fold_decl(let_decl);

        assert_eq!(
            tracker.events,
            vec!["enter:let:with_value", "exit:let:with_value"]
        );
    }

    #[test]
    fn test_enter_exit_with_nested_blocks() {
        #[derive(Debug)]
        struct DepthTracker {
            depth: usize,
            max_depth: usize,
        }

        impl Fold for DepthTracker {
            fn enter_block(&mut self, _: &Block) {
                self.depth += 1;
                self.max_depth = self.max_depth.max(self.depth);
            }

            fn exit_block(&mut self, _: &Block) {
                self.depth -= 1;
            }
        }

        let nested_block = Block {
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
            })],
        };

        let mut tracker = DepthTracker {
            depth: 0,
            max_depth: 0,
        };
        let _ = tracker.fold_block(nested_block);

        assert_eq!(tracker.max_depth, 3);
        assert_eq!(tracker.depth, 0); // Should be back to 0 after all exits
    }
}
