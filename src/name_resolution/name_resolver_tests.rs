#[cfg(test)]
pub mod tests {
    use rustc_hash::FxHashSet;

    use crate::{
        annotation, any_block, any_decl, any_expr, any_expr_stmt, any_stmt, assert_eq_diff,
        ast::AST,
        diagnostic::{AnyDiagnostic, Diagnostic},
        name::Name,
        name_resolution::{
            name_resolver::{NameResolved, NameResolver, NameResolverError},
            symbol::{
                AssociatedTypeId, BuiltinId, DeclaredLocalId, GlobalId, InstanceMethodId,
                ParamLocalId, PropertyId, ProtocolId, StaticMethodId, Symbol, TypeId,
                TypeParameterId, VariantId,
            },
        },
        node::Node,
        node_id::{FileID, NodeID},
        node_kinds::{
            decl::DeclKind,
            expr::{Expr, ExprKind},
            func::Func,
            func_signature::FuncSignature,
            generic_decl::GenericDecl,
            match_arm::MatchArm,
            parameter::Parameter,
            pattern::{Pattern, PatternKind},
            stmt::StmtKind,
            type_annotation::TypeAnnotationKind,
        },
        parsing::parser_tests::tests::parse,
        span::Span,
    };

    #[macro_export]
    macro_rules! param {
        ($id:expr, $name:expr) => {
            Parameter {
                id: NodeID::ANY,
                name: Name::Resolved($id.into(), $name.into()),
                type_annotation: None,
                span: Span::ANY,
            }
        };
        ($id:expr, $name:expr, $ty:expr) => {
            Parameter {
                id: NodeID::ANY,
                name: Name::Resolved($id.into(), $name.into()),
                type_annotation: Some($ty),
                span: Span::ANY,
            }
        };
    }

    macro_rules! variable {
        ($id:expr, $name:expr) => {
            Expr {
                id: NodeID::ANY,
                span: Span::ANY,
                kind: ExprKind::Variable(Name::Resolved($id.into(), $name.into())),
            }
        };
        ($name:expr) => {
            Expr {
                id: NodeID::ANY,
                span: Span::ANY,
                kind: ExprKind::Variable(Name::Raw($name.into())),
            }
        };
    }

    macro_rules! any_pattern {
        ($kind: expr) => {
            $crate::parsing::node_kinds::pattern::Pattern {
                id: NodeID::ANY,
                span: Span::ANY,
                kind: $kind,
            }
        };
    }

    pub fn resolve(code: &'static str) -> AST<NameResolved> {
        let res = resolve_err(code);
        assert!(
            res.diagnostics.is_empty(),
            "diagnostics not empty: {:?}",
            res.diagnostics
        );
        res
    }

    fn resolve_err(code: &'static str) -> AST<NameResolved> {
        let parsed = parse(code);
        let name_resolver = NameResolver::new();
        name_resolver.resolve(vec![parsed]).into_iter().next().unwrap()
    }

    #[test]
    fn resolves_simple_variable() {
        let tree = resolve("let hello = 1; hello");
        assert_eq!(
            *tree.roots[1].as_stmt(),
            any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                Symbol::Global(GlobalId(1)),
                "hello".into()
            )))
        );
    }

    #[test]
    fn resolves_builtin_type() {
        let resolved = resolve("let hello: Int");
        assert_eq!(
            *resolved.roots[0].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: Pattern {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: PatternKind::Bind(Name::Resolved(
                        Symbol::Global(GlobalId(1)),
                        "hello".into()
                    ))
                },
                type_annotation: Some(annotation!(TypeAnnotationKind::Nominal {
                    name: Name::Resolved(Symbol::Builtin(BuiltinId(1)), "Int".into()),
                    generics: vec![]
                })),
                value: None
            })
        );
    }

    #[test]
    fn block_scoping_prevents_let_leak() {
        let resolved = resolve_err(
            "{
            let x = 123
            x // This one is fine.
        }
        x // This one is not
        ",
        );
        assert_eq!(1, resolved.diagnostics.len());
        assert_eq!(
            resolved.diagnostics[0],
            AnyDiagnostic::NameResolution(Diagnostic::<NameResolverError> {
                span: Span::ANY,
                kind: NameResolverError::UndefinedName("x".into())
            })
        )
    }

    #[test]
    fn resolves_func_params() {
        let tree = resolve("func foo(x, y) { x ; y }");

        assert_eq_diff!(
            *tree.roots[0].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: Pattern {
                    id: NodeID::ANY,
                    kind: PatternKind::Bind(Name::Resolved(
                        Symbol::Global(GlobalId(1)),
                        "foo".into()
                    )),
                    span: Span::ANY
                },
                type_annotation: None,
                value: Some(any_expr!(ExprKind::Func(Func {
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::Global(GlobalId(1)), "foo".into()),
                    generics: vec![],
                    params: vec![param!(ParamLocalId(1), "x"), param!(ParamLocalId(2), "y"),],
                    body: any_block!(vec![
                        any_stmt!(StmtKind::Expr(variable!(ParamLocalId(1), "x"))).into(),
                        any_stmt!(StmtKind::Expr(variable!(ParamLocalId(2), "y"))).into(),
                    ]),
                    ret: None,
                    attributes: vec![],
                })))
            })
        );
    }

    #[test]
    fn resolves_mutual_recursion() {
        let resolved = resolve(
            "
          func odd() { even() }
          func even() { odd() }
          ",
        );

        assert_eq_diff!(
            *resolved.roots[0].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: Pattern {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: PatternKind::Bind(Name::Resolved(
                        Symbol::Global(GlobalId(1)),
                        "odd".into()
                    ))
                },
                type_annotation: None,
                value: Some(any_expr!(ExprKind::Func(Func {
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::Global(GlobalId(1)), "odd".into()),
                    generics: vec![],
                    params: vec![],
                    body: any_block!(vec![any_expr_stmt!(ExprKind::Call {
                        callee: Box::new(variable!(Symbol::Global(GlobalId(2)), "even")),
                        type_args: vec![],
                        args: vec![]
                    })]),
                    ret: None,
                    attributes: vec![]
                })))
            })
        );

        assert_eq_diff!(
            *resolved.roots[1].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: Pattern {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: PatternKind::Bind(Name::Resolved(
                        Symbol::Global(GlobalId(2)),
                        "even".into()
                    ))
                },
                type_annotation: None,
                value: Some(any_expr!(ExprKind::Func(Func {
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::Global(GlobalId(2)), "even".into()),
                    generics: vec![],
                    params: vec![],
                    body: any_block!(vec![any_expr_stmt!(ExprKind::Call {
                        callee: Box::new(variable!(Symbol::Global(GlobalId(1)), "odd")),
                        type_args: vec![],
                        args: vec![]
                    })]),
                    ret: None,
                    attributes: vec![]
                })))
            })
        );
    }

    #[test]
    fn resolves_nested_shadowing_correctly() {
        let tree = resolve("func foo(x, y) { func bar(x) { x \n y }\nx }\n");

        assert_eq_diff!(
            *tree.roots[0].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: Pattern {
                    id: NodeID::ANY,
                    kind: PatternKind::Bind(Name::Resolved(
                        Symbol::Global(GlobalId(1)),
                        "foo".into()
                    )),
                    span: Span::ANY
                },
                type_annotation: None,
                value: Some(any_expr!(ExprKind::Func(Func {
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::Global(GlobalId(1)), "foo".into()),
                    generics: vec![],
                    params: vec![param!(ParamLocalId(1), "x"), param!(ParamLocalId(2), "y")],
                    body: any_block!(vec![
                        any_decl!(DeclKind::Let {
                            lhs: Pattern {
                                id: NodeID::ANY,
                                kind: PatternKind::Bind(Name::Resolved(
                                    Symbol::DeclaredLocal(DeclaredLocalId(1)),
                                    "bar".into()
                                )),
                                span: Span::ANY
                            },
                            type_annotation: None,
                            value: Some(any_expr!(ExprKind::Func(Func {
                                id: NodeID::ANY,
                                name: Name::Resolved(
                                    Symbol::DeclaredLocal(DeclaredLocalId(1)),
                                    "bar".into()
                                ),
                                generics: vec![],
                                params: vec![param!(ParamLocalId(3), "x")],
                                body: any_block!(vec![
                                    any_stmt!(StmtKind::Expr(variable!(ParamLocalId(3), "x")))
                                        .into(),
                                    any_stmt!(StmtKind::Expr(variable!(ParamLocalId(2), "y")))
                                        .into(),
                                ]),
                                ret: None,
                                attributes: vec![],
                            })))
                        })
                        .into(),
                        any_stmt!(StmtKind::Expr(variable!(ParamLocalId(1), "x"))).into(),
                    ]),
                    ret: None,
                    attributes: vec![],
                })))
            }),
        );
    }

    #[test]
    fn resolves_captures() {
        let resolved = resolve(
            "
        let count = 0
        func counter(x) {
            x
            count
            count
        }
        ",
        );

        assert_eq!(
            *resolved.roots[0].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: any_pattern!(PatternKind::Bind(Name::Resolved(
                    Symbol::Global(GlobalId(1)),
                    "count".into()
                ))),
                type_annotation: None,
                value: Some(any_expr!(ExprKind::LiteralInt("0".into())))
            })
        );

        assert_eq_diff!(
            *resolved.roots[1].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: any_pattern!(PatternKind::Bind(Name::Resolved(
                    Symbol::Global(GlobalId(2)),
                    "counter".into()
                ))),
                type_annotation: None,
                value: Some(any_expr!(ExprKind::Func(Func {
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::Global(GlobalId(2)), "counter".into()),
                    generics: vec![],
                    params: vec![param!(ParamLocalId(1), "x")],
                    body: any_block!(vec![
                        any_stmt!(StmtKind::Expr(variable!(ParamLocalId(1), "x"))).into(),
                        any_stmt!(StmtKind::Expr(variable!(GlobalId(1), "count"))).into(),
                        any_stmt!(StmtKind::Expr(variable!(GlobalId(1), "count"))).into(),
                    ]),
                    ret: None,
                    attributes: vec![]
                })))
            })
        );

        let mut expected = FxHashSet::default();
        expected.insert(Symbol::Global(GlobalId(1)));

        assert_eq!(
            resolved.phase.captures.get(&NodeID(FileID(0), 9)),
            Some(&expected),
            "{:?}",
            resolved.phase.captures
        );
    }

    #[test]
    fn resolves_func_generics() {
        let resolved = resolve(
            "
        func fizz<T>(t: T) -> T { t }
        ",
        );

        assert_eq_diff!(
            *resolved.roots[0].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: Pattern {
                    id: NodeID::ANY,
                    kind: PatternKind::Bind(Name::Resolved(
                        Symbol::Global(GlobalId(1),),
                        "fizz".into()
                    )),
                    span: Span::ANY
                },
                type_annotation: None,
                value: Some(any_expr!(ExprKind::Func(Func {
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::Global(GlobalId(1)), "fizz".into()),
                    generics: vec![GenericDecl {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        name: Name::Resolved(Symbol::TypeParameter(TypeParameterId(1)), "T".into()),
                        generics: vec![],
                        conformances: vec![],
                    }],
                    params: vec![param!(
                        ParamLocalId(1),
                        "t",
                        annotation!(TypeAnnotationKind::Nominal {
                            name: Name::Resolved(
                                Symbol::TypeParameter(TypeParameterId(1)),
                                "T".into()
                            ),
                            generics: vec![]
                        })
                    ),],
                    body: any_block!(vec![
                        any_stmt!(StmtKind::Expr(variable!(ParamLocalId(1), "t"))).into(),
                    ]),
                    ret: Some(annotation!(TypeAnnotationKind::Nominal {
                        name: Name::Resolved(Symbol::TypeParameter(TypeParameterId(1)), "T".into()),
                        generics: vec![]
                    })),
                    attributes: vec![],
                })),)
            })
        );
    }

    #[test]
    fn resolves_type_alias() {
        let resolved = resolve("typealias Intyfresh = Int ; Intyfresh");
        assert_eq!(
            *resolved.roots[0].as_decl(),
            any_decl!(DeclKind::TypeAlias(
                annotation!(TypeAnnotationKind::Nominal {
                    name: Name::Resolved(Symbol::Type(TypeId(1)), "Intyfresh".into()),
                    generics: vec![]
                }),
                annotation!(TypeAnnotationKind::Nominal {
                    name: Name::Resolved(Symbol::Int, "Int".into()),
                    generics: vec![]
                })
            ))
        );

        assert_eq!(
            *resolved.roots[1].as_stmt(),
            any_expr_stmt!(ExprKind::Constructor(Name::Resolved(
                Symbol::Type(TypeId(1)),
                "Intyfresh".into()
            )))
        );
    }

    #[test]
    fn resolves_struct() {
        let resolved = resolve("struct Person {}");
        assert_eq!(
            *resolved.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                name: Name::Resolved(TypeId(1).into(), "Person".into()),
                generics: vec![],
                conformances: vec![],
                body: any_block!(vec![])
            })
        )
    }

    #[test]
    fn resolves_struct_properties() {
        let resolved = resolve(
            "
        struct Person {
            let me: Person
        }
        ",
        );
        assert_eq!(
            *resolved.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                name: Name::Resolved(TypeId(1).into(), "Person".into()),
                generics: vec![],
                conformances: vec![],
                body: any_block!(vec![Node::Decl(any_decl!(DeclKind::Property {
                    name: Name::Resolved(Symbol::Property(PropertyId(1)), "me".into()),
                    is_static: false,
                    type_annotation: Some(annotation!(TypeAnnotationKind::Nominal {
                        name: Name::Resolved(TypeId(1).into(), "Person".into()),
                        generics: vec![]
                    })),
                    default_value: None
                }))])
            })
        )
    }

    #[test]
    fn resolves_struct_init() {
        let resolved = resolve(
            "
        struct Person {
            init() {}
        }
        ",
        );
        assert_eq_diff!(
            *resolved.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                name: Name::Resolved(TypeId(1).into(), "Person".into()),
                generics: vec![],
                conformances: vec![],
                body: any_block!(vec![Node::Decl(any_decl!(DeclKind::Init {
                    name: Name::Resolved(Symbol::Global(GlobalId(1)), "init".into()),
                    params: vec![param!(
                        Symbol::ParamLocal(ParamLocalId(1)),
                        "self",
                        annotation!(TypeAnnotationKind::SelfType(Name::Resolved(
                            Symbol::Type(TypeId(1)),
                            "Self".into()
                        )))
                    )],
                    body: any_block!(vec![])
                }))])
            })
        )
    }

    #[test]
    fn resolves_generic_struct_properties() {
        let resolved = resolve(
            "
        struct Person<T> {
            let me: T
        }
        ",
        );
        assert_eq_diff!(
            *resolved.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                name: Name::Resolved(TypeId(1).into(), "Person".into()),
                generics: vec![GenericDecl {
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::TypeParameter(TypeParameterId(1)), "T".into()),
                    generics: vec![],
                    conformances: vec![],
                    span: Span::ANY
                }],
                conformances: vec![],
                body: any_block!(vec![Node::Decl(any_decl!(DeclKind::Property {
                    name: Name::Resolved(Symbol::Property(PropertyId(1)), "me".into()),
                    is_static: false,
                    type_annotation: Some(annotation!(TypeAnnotationKind::Nominal {
                        name: Name::Resolved(Symbol::TypeParameter(TypeParameterId(1)), "T".into()),
                        generics: vec![]
                    })),
                    default_value: None
                }))])
            })
        )
    }

    #[test]
    fn resolves_static_struct_methods() {
        let resolved = resolve(
            "struct Person {
                static func fizz() {}
            }",
        );
        assert_eq_diff!(
            *resolved.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                name: Name::Resolved(TypeId(1).into(), "Person".into()),
                generics: vec![],
                conformances: vec![],
                body: any_block!(vec![
                    any_decl!(DeclKind::Method {
                        func: Box::new(Func {
                            id: NodeID::ANY,
                            name: Name::Resolved(
                                Symbol::StaticMethod(StaticMethodId(1)),
                                "fizz".into()
                            ),
                            generics: vec![],
                            params: vec![],
                            body: any_block!(vec![]),
                            ret: None,
                            attributes: vec![]
                        }),
                        is_static: true
                    })
                    .into(),
                ])
            })
        )
    }

    #[test]
    fn resolves_struct_methods() {
        let resolved = resolve(
            "struct Person {
                func fizz() {
                    self.buzz()
                }

                func buzz() {
                    self.fizz()
                }
            }",
        );
        assert_eq_diff!(
            *resolved.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                name: Name::Resolved(TypeId(1).into(), "Person".into()),
                generics: vec![],
                conformances: vec![],
                body: any_block!(vec![
                    any_decl!(DeclKind::Method {
                        func: Box::new(Func {
                            id: NodeID::ANY,
                            name: Name::Resolved(
                                Symbol::InstanceMethod(InstanceMethodId(1)),
                                "fizz".into()
                            ),
                            generics: vec![],
                            params: vec![param!(
                                Symbol::ParamLocal(ParamLocalId(1)),
                                "self",
                                annotation!(TypeAnnotationKind::SelfType(Name::Resolved(
                                    TypeId(1).into(),
                                    "Self".into()
                                )))
                            )],
                            body: any_block!(vec![any_expr_stmt!(ExprKind::Call {
                                callee: any_expr!(ExprKind::Member(
                                    Some(
                                        any_expr!(ExprKind::Variable(Name::Resolved(
                                            Symbol::ParamLocal(ParamLocalId(1)),
                                            "self".into()
                                        )))
                                        .into()
                                    ),
                                    "buzz".into()
                                ))
                                .into(),
                                type_args: vec![],
                                args: vec![]
                            })]),
                            ret: None,
                            attributes: vec![]
                        }),
                        is_static: false
                    })
                    .into(),
                    any_decl!(DeclKind::Method {
                        func: Box::new(Func {
                            id: NodeID::ANY,
                            name: Name::Resolved(
                                Symbol::InstanceMethod(InstanceMethodId(2)),
                                "buzz".into()
                            ),
                            generics: vec![],
                            params: vec![param!(
                                Symbol::ParamLocal(ParamLocalId(2)),
                                "self",
                                annotation!(TypeAnnotationKind::SelfType(Name::Resolved(
                                    TypeId(1).into(),
                                    "Self".into()
                                )))
                            )],
                            body: any_block!(vec![any_expr_stmt!(ExprKind::Call {
                                callee: any_expr!(ExprKind::Member(
                                    Some(Box::new(any_expr!(ExprKind::Variable(Name::Resolved(
                                        Symbol::ParamLocal(ParamLocalId(2)),
                                        "self".into()
                                    ))))),
                                    "fizz".into()
                                ))
                                .into(),
                                type_args: vec![],
                                args: vec![]
                            })]),
                            ret: None,
                            attributes: vec![]
                        }),
                        is_static: false
                    })
                    .into()
                ])
            })
        )
    }

    #[test]
    fn resolves_struct_constructor() {
        let resolved = resolve(
            "
        struct Person {}
        Person()
        ",
        );
        assert_eq!(
            *resolved.roots[1].as_stmt(),
            any_expr_stmt!(ExprKind::Call {
                callee: any_expr!(ExprKind::Constructor(Name::Resolved(
                    Symbol::Type(TypeId(1)),
                    "Person".into()
                )))
                .into(),
                type_args: vec![],
                args: vec![]
            })
        )
    }

    #[test]
    fn resolves_struct_extension() {
        let resolved = resolve(
            "
        struct Person {}
        extend Person {}
        ",
        );
        assert_eq!(
            *resolved.roots[1].as_decl(),
            any_decl!(DeclKind::Extend {
                name: Name::Resolved(Symbol::Type(TypeId(1)), "Person".into()),
                conformances: vec![],
                generics: vec![],
                body: any_block!(vec![])
            }),
        )
    }

    #[test]
    fn resolves_enum() {
        let resolved = resolve(
            "
        enum Fizz {
            case foo, bar
        }
        ",
        );

        assert_eq!(
            *resolved.roots[0].as_decl(),
            any_decl!(DeclKind::Enum {
                name: Name::Resolved(Symbol::Type(TypeId(1)), "Fizz".into()),
                conformances: vec![],
                generics: vec![],
                body: any_block!(vec![
                    Node::Decl(any_decl!(DeclKind::EnumVariant(
                        Name::Resolved(Symbol::Variant(VariantId(1)), "foo".into()),
                        vec![]
                    ))),
                    Node::Decl(any_decl!(DeclKind::EnumVariant(
                        Name::Resolved(Symbol::Variant(VariantId(2)), "bar".into()),
                        vec![]
                    ))),
                ])
            })
        )
    }

    #[test]
    fn resolves_protocol() {
        let resolved = resolve(
            "
            protocol Fizzable {
                func buzz() -> ()
            }
        ",
        );

        assert_eq_diff!(
            *resolved.roots[0].as_decl(),
            any_decl!(DeclKind::Protocol {
                name: Name::Resolved(Symbol::Protocol(ProtocolId(1)), "Fizzable".into()),
                conformances: vec![],
                generics: vec![],
                body: any_block!(vec![Node::Decl(any_decl!(DeclKind::MethodRequirement(
                    FuncSignature {
                        name: Name::Resolved(
                            Symbol::InstanceMethod(InstanceMethodId(1)),
                            "buzz".into()
                        ),
                        params: vec![Parameter {
                            id: NodeID::ANY,
                            name: "self".into(),
                            type_annotation: Some(annotation!(TypeAnnotationKind::SelfType(
                                Name::Resolved(ProtocolId(1).into(), "Self".into())
                            ))),
                            span: Span::ANY
                        }],
                        generics: vec![],
                        ret: Some(Box::new(annotation!(TypeAnnotationKind::Tuple(vec![]))))
                    }
                )))])
            })
        )
    }

    #[test]
    fn resolves_protocol_associated_types() {
        let resolved = resolve(
            "
            protocol Fizzable {
                associated T

                func buzz() -> T
            }
        ",
        );

        assert_eq_diff!(
            *resolved.roots[0].as_decl(),
            any_decl!(DeclKind::Protocol {
                name: Name::Resolved(Symbol::Protocol(ProtocolId(1)), "Fizzable".into()),
                conformances: vec![],
                generics: vec![],
                body: any_block!(vec![
                    Node::Decl(any_decl!(DeclKind::Associated {
                        generic: GenericDecl {
                            id: NodeID::ANY,
                            name: Name::Resolved(
                                Symbol::AssociatedType(AssociatedTypeId(1)),
                                "T".into()
                            ),
                            generics: vec![],
                            conformances: vec![],
                            span: Span::ANY
                        }
                    })),
                    Node::Decl(any_decl!(DeclKind::MethodRequirement(FuncSignature {
                        name: Name::Resolved(
                            Symbol::InstanceMethod(InstanceMethodId(1)),
                            "buzz".into()
                        ),
                        params: vec![Parameter {
                            id: NodeID::ANY,
                            name: "self".into(),
                            type_annotation: Some(annotation!(TypeAnnotationKind::SelfType(
                                Name::Resolved(ProtocolId(1).into(), "Self".into())
                            ))),
                            span: Span::ANY
                        }],
                        generics: vec![],
                        ret: Some(Box::new(annotation!(TypeAnnotationKind::Nominal {
                            name: Name::Resolved(
                                Symbol::AssociatedType(AssociatedTypeId(1)),
                                "T".into()
                            ),
                            generics: vec![]
                        })))
                    }))),
                ])
            })
        )
    }

    #[test]
    fn resolves_match() {
        let resolved = resolve(
            "
        let a = 123
        match a {
            b -> b
        }
        ",
        );

        assert_eq!(
            *resolved.roots[1].as_stmt(),
            any_expr_stmt!(ExprKind::Match(
                Box::new(variable!(GlobalId(1), "a")),
                vec![MatchArm {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    pattern: Pattern {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        kind: PatternKind::Bind(Name::Resolved(
                            Symbol::DeclaredLocal(DeclaredLocalId(1)),
                            "b".into()
                        ))
                    },
                    body: any_block!(vec![any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                        Symbol::DeclaredLocal(DeclaredLocalId(1)),
                        "b".into()
                    )))])
                }]
            ))
        );
    }

    #[test]
    fn match_doesnt_leak() {
        let resolved = resolve_err(
            "
        match 123 {
            b -> b
        }

        b
        ",
        );

        assert_eq!(resolved.diagnostics.len(), 1, "{:?}", resolved.diagnostics);
    }
}
