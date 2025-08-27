#[cfg(test)]
mod tests {
    use super::super::fold_decl_mut::*;
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
    fn test_mutate_declaration_names() {
        struct DeclRenamer {
            prefix: String,
            counter: usize,
        }

        impl DeclFoldMut for DeclRenamer {
            fn enter_decl_func_mut(&mut self, decl: &mut Decl) {
                if let DeclKind::Func { ref mut name, .. } = decl.kind {
                    *name = Name::from(format!("{}_{}", self.prefix, self.counter));
                    self.counter += 1;
                }
            }

            fn enter_decl_struct_mut(&mut self, decl: &mut Decl) {
                if let DeclKind::Struct { ref mut name, .. } = decl.kind {
                    *name = Name::from(format!("{}_{}", self.prefix, self.counter));
                    self.counter += 1;
                }
            }

            fn enter_decl_property_mut(&mut self, decl: &mut Decl) {
                if let DeclKind::Property { ref mut name, .. } = decl.kind {
                    *name = Name::from(format!("prop_{}", self.counter));
                    self.counter += 1;
                }
            }
        }

        let mut struct_decl = Decl {
            id: NodeID::ANY,
            span: Span::ANY,
            kind: DeclKind::Struct {
                name: Name::from("MyStruct"),
                generics: vec![],
                conformances: vec![],
                body: Block {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    args: vec![],
                    body: vec![
                        Node::Decl(Decl {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: DeclKind::Property {
                                name: Name::from("x"),
                                is_static: false,
                                type_annotation: None,
                                default_value: None,
                            },
                        }),
                        Node::Decl(Decl {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: DeclKind::Func {
                                name: Name::from("doSomething"),
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
            },
        };

        let mut renamer = DeclRenamer {
            prefix: "renamed".to_string(),
            counter: 0,
        };

        renamer.fold_decl_mut(&mut struct_decl);

        // Check that names were renamed
        match &struct_decl.kind {
            DeclKind::Struct { name, body, .. } => {
                assert_eq!(*name, Name::from("renamed_0"));

                // Check nested declarations
                match &body.body[0] {
                    Node::Decl(decl) => match &decl.kind {
                        DeclKind::Property { name, .. } => {
                            assert_eq!(*name, Name::from("prop_1"));
                        }
                        _ => panic!("Expected Property"),
                    },
                    _ => panic!("Expected Decl"),
                }

                match &body.body[1] {
                    Node::Decl(decl) => match &decl.kind {
                        DeclKind::Func { name, .. } => {
                            assert_eq!(*name, Name::from("renamed_2"));
                        }
                        _ => panic!("Expected Func"),
                    },
                    _ => panic!("Expected Decl"),
                }
            }
            _ => panic!("Expected Struct"),
        }
    }

    #[test]
    fn test_expressions_not_mutated() {
        struct ExpressionChecker {
            saw_let_with_value: bool,
        }

        impl DeclFoldMut for ExpressionChecker {
            fn enter_decl_let_mut(&mut self, decl: &mut Decl) {
                if let DeclKind::Let { value, .. } = &decl.kind
                    && value.is_some()
                {
                    self.saw_let_with_value = true;
                    // We can see the expression exists but we don't mutate it
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
                value: Some(Expr {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: ExprKind::LiteralInt("42".to_string()),
                }),
            },
        };

        let original_value = match &let_decl.kind {
            DeclKind::Let { value, .. } => value.clone(),
            _ => panic!("Expected Let"),
        };

        let mut checker = ExpressionChecker {
            saw_let_with_value: false,
        };

        checker.fold_decl_mut(&mut let_decl);

        assert!(checker.saw_let_with_value);

        // Verify the expression wasn't changed
        match &let_decl.kind {
            DeclKind::Let { value, .. } => {
                assert_eq!(*value, original_value);
            }
            _ => panic!("Expected Let"),
        }
    }

    #[test]
    fn test_nested_functions() {
        struct FunctionDepthTracker {
            depth: usize,
            max_depth: usize,
            function_depths: Vec<(String, usize)>,
        }

        impl DeclFoldMut for FunctionDepthTracker {
            fn enter_decl_func_mut(&mut self, decl: &mut Decl) {
                self.depth += 1;
                self.max_depth = self.max_depth.max(self.depth);

                if let DeclKind::Func { name, .. } = &decl.kind {
                    self.function_depths
                        .push((format!("{:?}", name), self.depth));
                }
            }

            fn exit_decl_func_mut(&mut self, _decl: &mut Decl) {
                self.depth -= 1;
            }
        }

        let mut outer_func = Decl {
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
                    body: vec![Node::Decl(Decl {
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
                                body: vec![Node::Decl(Decl {
                                    id: NodeID::ANY,
                                    span: Span::ANY,
                                    kind: DeclKind::Func {
                                        name: Name::from("innermost"),
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
                                })],
                            },
                            ret: None,
                            attributes: vec![],
                        },
                    })],
                },
                ret: None,
                attributes: vec![],
            },
        };

        let mut tracker = FunctionDepthTracker {
            depth: 0,
            max_depth: 0,
            function_depths: vec![],
        };

        tracker.fold_decl_mut(&mut outer_func);

        assert_eq!(tracker.max_depth, 3);
        assert_eq!(tracker.function_depths.len(), 3);
        assert_eq!(
            tracker.function_depths[0],
            ("Raw(\"outer\")".to_string(), 1)
        );
        assert_eq!(
            tracker.function_depths[1],
            ("Raw(\"inner\")".to_string(), 2)
        );
        assert_eq!(
            tracker.function_depths[2],
            ("Raw(\"innermost\")".to_string(), 3)
        );
        assert_eq!(tracker.depth, 0); // Should be back to 0 after all exits
    }

    #[test]
    fn test_enum_variant_mutation() {
        struct EnumVariantMutator {
            variant_count: usize,
        }

        impl DeclFoldMut for EnumVariantMutator {
            fn enter_decl_enum_variant_mut(&mut self, decl: &mut Decl) {
                if let DeclKind::EnumVariant(ref mut name, _) = decl.kind {
                    *name = Name::from(format!("Variant{}", self.variant_count));
                    self.variant_count += 1;
                }
            }
        }

        let mut enum_decl = Decl {
            id: NodeID::ANY,
            span: Span::ANY,
            kind: DeclKind::Enum {
                name: Name::from("MyEnum"),
                conformances: vec![],
                generics: vec![],
                body: Block {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    args: vec![],
                    body: vec![
                        Node::Decl(Decl {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: DeclKind::EnumVariant(Name::from("First"), vec![]),
                        }),
                        Node::Decl(Decl {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: DeclKind::EnumVariant(Name::from("Second"), vec![]),
                        }),
                        Node::Decl(Decl {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: DeclKind::EnumVariant(Name::from("Third"), vec![]),
                        }),
                    ],
                },
            },
        };

        let mut mutator = EnumVariantMutator { variant_count: 0 };
        mutator.fold_decl_mut(&mut enum_decl);

        // Check that variants were renamed
        match &enum_decl.kind {
            DeclKind::Enum { body, .. } => {
                for (i, node) in body.body.iter().enumerate() {
                    match node {
                        Node::Decl(decl) => match &decl.kind {
                            DeclKind::EnumVariant(name, _) => {
                                assert_eq!(*name, Name::from(format!("Variant{}", i)));
                            }
                            _ => panic!("Expected EnumVariant"),
                        },
                        _ => panic!("Expected Decl"),
                    }
                }
            }
            _ => panic!("Expected Enum"),
        }
    }
}
