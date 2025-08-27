#[cfg(test)]
mod tests {
    use super::super::fold_decl::*;
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
    fn test_decl_only_traversal() {
        // This fold only counts declarations, ignoring expressions
        struct DeclCounter {
            count: usize,
            func_names: Vec<Name>,
        }

        impl DeclFold for DeclCounter {
            fn enter_decl(&mut self, _decl: &Decl) {
                self.count += 1;
            }

            fn enter_decl_func(
                &mut self,
                name: &Name,
                _generics: &[crate::node_kinds::generic_decl::GenericDecl],
                _params: &[crate::node_kinds::parameter::Parameter],
                _body: &Block,
                _ret: &Option<crate::node_kinds::type_annotation::TypeAnnotation>,
                _attributes: &[crate::node_kinds::attribute::Attribute],
            ) {
                self.func_names.push(name.clone());
            }
        }

        // Create a function with nested declarations
        let func = Decl {
            id: NodeID::ANY,
            span: Span::ANY,
            kind: DeclKind::Func {
                name: Name::from("outer_func"),
                generics: vec![],
                params: vec![],
                body: Block {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    args: vec![],
                    body: vec![
                        // Nested function declaration
                        Node::Decl(Decl {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: DeclKind::Func {
                                name: Name::from("inner_func"),
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
                        // Expression node (should be ignored)
                        Node::Expr(Expr {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: ExprKind::LiteralInt("42".to_string()),
                        }),
                        // Let declaration
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
                                value: Some(Expr {
                                    id: NodeID::ANY,
                                    span: Span::ANY,
                                    kind: ExprKind::LiteralInt("10".to_string()),
                                }),
                            },
                        }),
                    ],
                },
                ret: None,
                attributes: vec![],
            },
        };

        let mut counter = DeclCounter {
            count: 0,
            func_names: vec![],
        };

        let _ = counter.fold_decl(func);

        // Should count 3 declarations: outer_func, inner_func, and let
        assert_eq!(counter.count, 3);
        assert_eq!(counter.func_names.len(), 2);
        assert_eq!(counter.func_names[0], Name::from("outer_func"));
        assert_eq!(counter.func_names[1], Name::from("inner_func"));
    }

    #[test]
    fn test_struct_with_nested_decls() {
        struct DeclTypeCollector {
            decl_types: Vec<String>,
        }

        impl DeclFold for DeclTypeCollector {
            fn enter_decl_struct(
                &mut self,
                name: &Name,
                _generics: &[crate::node_kinds::generic_decl::GenericDecl],
                _conformances: &[crate::node_kinds::type_annotation::TypeAnnotation],
                _body: &Block,
            ) {
                self.decl_types.push(format!("struct:{name:?}"));
            }

            fn enter_decl_property(
                &mut self,
                name: &Name,
                is_static: bool,
                _type_annotation: &Option<crate::node_kinds::type_annotation::TypeAnnotation>,
                _default_value: &Option<Expr>,
            ) {
                let kind = if is_static { "static_property" } else { "property" };
                self.decl_types.push(format!("{kind}:{name:?}"));
            }

            fn enter_decl_method(&mut self, _func: &Decl, is_static: bool) {
                let kind = if is_static { "static_method" } else { "method" };
                self.decl_types.push(kind.to_string());
            }
        }

        let struct_decl = Decl {
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
                            kind: DeclKind::Property {
                                name: Name::from("count"),
                                is_static: true,
                                type_annotation: None,
                                default_value: None,
                            },
                        }),
                        Node::Decl(Decl {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: DeclKind::Method {
                                func: Box::new(Decl {
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
                                is_static: false,
                            },
                        }),
                    ],
                },
            },
        };

        let mut collector = DeclTypeCollector {
            decl_types: vec![],
        };

        let _ = collector.fold_decl(struct_decl);

        assert_eq!(
            collector.decl_types,
            vec![
                "struct:Raw(\"MyStruct\")",
                "property:Raw(\"x\")",
                "static_property:Raw(\"count\")",
                "method"
            ]
        );
    }

    #[test]
    fn test_expressions_not_traversed() {
        // This test ensures expressions are not traversed
        struct ExpressionIgnorer {
            saw_expression: bool,
            decl_count: usize,
        }

        impl DeclFold for ExpressionIgnorer {
            fn enter_decl(&mut self, _decl: &Decl) {
                self.decl_count += 1;
            }

            fn fold_decl_let(
                &mut self,
                lhs: Pattern,
                type_annotation: Option<crate::node_kinds::type_annotation::TypeAnnotation>,
                value: Option<Expr>,
            ) -> DeclKind {
                // Check that we have an expression but don't traverse it
                if value.is_some() {
                    // We can see there's an expression, but we won't traverse into it
                    self.saw_expression = true;
                }
                
                DeclKind::Let {
                    lhs,
                    type_annotation,
                    value,
                }
            }
        }

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
                    kind: ExprKind::Binary(
                        Box::new(Expr {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: ExprKind::LiteralInt("1".to_string()),
                        }),
                        crate::lexing::token_kind::TokenKind::Plus,
                        Box::new(Expr {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: ExprKind::LiteralInt("2".to_string()),
                        }),
                    ),
                }),
            },
        };

        let mut ignorer = ExpressionIgnorer {
            saw_expression: false,
            decl_count: 0,
        };

        let _ = ignorer.fold_decl(let_decl);

        assert!(ignorer.saw_expression);
        assert_eq!(ignorer.decl_count, 1);
        // If expressions were traversed, we might see more activity
        // but since they're not, we only process the declaration itself
    }

    #[test]
    fn test_enum_variants() {
        struct EnumTraverser {
            variants: Vec<String>,
        }

        impl DeclFold for EnumTraverser {
            fn enter_decl_enum(
                &mut self,
                name: &Name,
                _conformances: &[crate::node_kinds::type_annotation::TypeAnnotation],
                _generics: &[crate::node_kinds::generic_decl::GenericDecl],
                _body: &Block,
            ) {
                self.variants.push(format!("enum:{name:?}"));
            }

            fn enter_decl_enum_variant(
                &mut self,
                name: &Name,
                fields: &[crate::node_kinds::type_annotation::TypeAnnotation],
            ) {
                self.variants.push(format!("variant:{name:?}:fields={}", fields.len()));
            }
        }

        let enum_decl = Decl {
            id: NodeID::ANY,
            span: Span::ANY,
            kind: DeclKind::Enum {
                name: Name::from("Option"),
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
                            kind: DeclKind::EnumVariant(Name::from("None"), vec![]),
                        }),
                        Node::Decl(Decl {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: DeclKind::EnumVariant(
                                Name::from("Some"),
                                vec![crate::node_kinds::type_annotation::TypeAnnotation {
                                    id: NodeID::ANY,
                                    span: Span::ANY,
                                    kind: crate::node_kinds::type_annotation::TypeAnnotationKind::Nominal {
                                        name: Name::from("T"),
                                        generics: vec![],
                                    },
                                }],
                            ),
                        }),
                    ],
                },
            },
        };

        let mut traverser = EnumTraverser { variants: vec![] };
        let _ = traverser.fold_decl(enum_decl);

        assert_eq!(
            traverser.variants,
            vec![
                "enum:Raw(\"Option\")",
                "variant:Raw(\"None\"):fields=0",
                "variant:Raw(\"Some\"):fields=1"
            ]
        );
    }
}