#[cfg(test)]
pub mod tests {
    use std::rc::Rc;

    use rustc_hash::FxHashSet;

    use crate::{
        annotation, any, any_block, any_body, any_decl, any_expr, any_expr_stmt, any_stmt,
        assert_eq_diff,
        ast::{AST, NameResolved},
        compiling::module::{ModuleEnvironment, ModuleId},
        diagnostic::{AnyDiagnostic, Diagnostic, Severity},
        label::Label,
        name::Name,
        name_resolution::{
            name_resolver::{Capture, NameResolver, NameResolverError, ResolvedNames},
            symbol::{
                AssociatedTypeId, BuiltinId, DeclaredLocalId, EnumId, GlobalId, InitializerId,
                InstanceMethodId, MethodRequirementId, ParamLocalId, PatternBindLocalId,
                PropertyId, ProtocolId, StaticMethodId, StructId, Symbol, SynthesizedId,
                TypeAliasId, TypeParameterId, VariantId,
            },
        },
        node_id::{FileID, NodeID},
        node_kinds::{
            call_arg::CallArg,
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
        types::infer_ty::Level,
    };

    #[macro_export]
    macro_rules! param {
        ($id:expr, $name:expr) => {
            Parameter {
                id: NodeID::ANY,
                name: Name::Resolved($id.into(), $name.into()),
                name_span: Span::ANY,
                type_annotation: None,
                span: Span::ANY,
            }
        };
        ($id:expr, $name:expr, $ty:expr) => {
            Parameter {
                id: NodeID::ANY,
                name: Name::Resolved($id.into(), $name.into()),
                name_span: Span::ANY,
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

    #[macro_export]
    macro_rules! any_pattern {
        ($kind: expr) => {
            $crate::parsing::node_kinds::pattern::Pattern {
                id: NodeID::ANY,
                span: Span::ANY,
                kind: $kind,
            }
        };
    }

    pub fn resolve(code: &'static str) -> (AST<NameResolved>, ResolvedNames) {
        let (ast, resolved) = resolve_err(code);
        assert!(
            resolved.diagnostics.is_empty(),
            "diagnostics not empty: {:?}",
            resolved.diagnostics
        );
        (ast, resolved)
    }

    fn resolve_err(code: &'static str) -> (AST<NameResolved>, ResolvedNames) {
        let parsed = parse(code);
        let modules = ModuleEnvironment::default();
        let mut name_resolver = NameResolver::new(Rc::new(modules), ModuleId::Current);
        let parseds = vec![parsed];
        let (asts, resolved) = name_resolver.resolve(parseds);
        (asts[0].clone(), resolved)
    }

    #[test]
    fn resolves_simple_variable() {
        let tree = resolve("let hello = 1; hello");
        assert_eq!(
            *tree.0.roots[1].as_stmt(),
            any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                Symbol::Global(GlobalId::from(1)),
                "hello".into()
            )))
        );

        assert_eq!(
            *tree
                .1
                .symbols_to_node
                .get(&Symbol::Global(GlobalId::from(1)))
                .unwrap(),
            NodeID(FileID(0), 1)
        );
    }

    #[test]
    fn resolves_builtin_type() {
        let resolved = resolve("let hello: Int");
        assert_eq!(
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: Pattern {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: PatternKind::Bind(Name::Resolved(
                        Symbol::Global(GlobalId::from(1)),
                        "hello".into()
                    ))
                },
                type_annotation: Some(annotation!(TypeAnnotationKind::Nominal {
                    name: Name::Resolved(
                        Symbol::Builtin(BuiltinId::new(
                            crate::compiling::module::ModuleId::Core,
                            1
                        )),
                        "Int".into()
                    ),
                    name_span: Span::ANY,
                    generics: vec![]
                })),
                rhs: None
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
        assert_eq!(1, resolved.1.diagnostics.len());
        assert_eq!(
            resolved.1.diagnostics[0],
            AnyDiagnostic::NameResolution(Diagnostic::<NameResolverError> {
                id: NodeID::ANY,
                severity: Severity::Error,
                kind: NameResolverError::UndefinedName("x".into())
            })
        )
    }

    #[test]
    fn resolves_func_params() {
        let tree = resolve("func foo(x, y) { x ; y }");

        assert_eq_diff!(
            *tree.0.roots[0].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: Pattern {
                    id: NodeID::ANY,
                    kind: PatternKind::Bind(Name::Resolved(
                        Symbol::Global(GlobalId::from(1)),
                        "foo".into()
                    )),
                    span: Span::ANY
                },
                type_annotation: None,
                rhs: Some(any_expr!(ExprKind::Func(Func {
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::Global(GlobalId::from(1)), "foo".into()),
                    name_span: Span::ANY,
                    generics: vec![],
                    params: vec![param!(ParamLocalId(1), "x"), param!(ParamLocalId(2), "y"),],
                    body: any_block!(vec![
                        any_stmt!(StmtKind::Expr(variable!(ParamLocalId(1), "x")))
                            .try_into()
                            .unwrap(),
                        any_stmt!(StmtKind::Expr(variable!(ParamLocalId(2), "y")))
                            .try_into()
                            .unwrap(),
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
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: Pattern {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: PatternKind::Bind(Name::Resolved(
                        Symbol::Global(GlobalId::from(1)),
                        "odd".into()
                    ))
                },
                type_annotation: None,
                rhs: Some(any_expr!(ExprKind::Func(Func {
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::Global(GlobalId::from(1)), "odd".into()),
                    name_span: Span::ANY,
                    generics: vec![],
                    params: vec![],
                    body: any_block!(vec![any_expr_stmt!(ExprKind::Call {
                        callee: Box::new(variable!(Symbol::Global(GlobalId::from(2)), "even")),
                        type_args: vec![],
                        args: vec![]
                    })]),
                    ret: None,
                    attributes: vec![]
                })))
            })
        );

        assert_eq_diff!(
            *resolved.0.roots[1].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: Pattern {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: PatternKind::Bind(Name::Resolved(
                        Symbol::Global(GlobalId::from(2)),
                        "even".into()
                    ))
                },
                type_annotation: None,
                rhs: Some(any_expr!(ExprKind::Func(Func {
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::Global(GlobalId::from(2)), "even".into()),
                    name_span: Span::ANY,
                    generics: vec![],
                    params: vec![],
                    body: any_block!(vec![any_expr_stmt!(ExprKind::Call {
                        callee: Box::new(variable!(Symbol::Global(GlobalId::from(1)), "odd")),
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
            *tree.0.roots[0].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: Pattern {
                    id: NodeID::ANY,
                    kind: PatternKind::Bind(Name::Resolved(
                        Symbol::Global(GlobalId::from(1)),
                        "foo".into()
                    )),
                    span: Span::ANY
                },
                type_annotation: None,
                rhs: Some(any_expr!(ExprKind::Func(Func {
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::Global(GlobalId::from(1)), "foo".into()),
                    name_span: Span::ANY,
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
                            rhs: Some(any_expr!(ExprKind::Func(Func {
                                id: NodeID::ANY,
                                name: Name::Resolved(
                                    Symbol::DeclaredLocal(DeclaredLocalId(1)),
                                    "bar".into()
                                ),
                                name_span: Span::ANY,
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
        func fizz() {
            let count = 0
            func counter(x) {
                x
                count
                count
            }
        }
        ",
        );

        assert_eq!(
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: any_pattern!(PatternKind::Bind(Name::Resolved(
                    Symbol::Global(GlobalId::from(1)),
                    "fizz".into()
                ))),
                type_annotation: None,
                rhs: Some(any_expr!(ExprKind::Func(Func {
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::Global(GlobalId::from(1)), "fizz".into()),
                    name_span: Span::ANY,
                    generics: Default::default(),
                    params: Default::default(),
                    body: any_block!(vec![
                        any_decl!(DeclKind::Let {
                            lhs: any_pattern!(PatternKind::Bind(Name::Resolved(
                                Symbol::DeclaredLocal(DeclaredLocalId(1)),
                                "count".into()
                            ))),
                            type_annotation: None,
                            rhs: Some(any_expr!(ExprKind::LiteralInt("0".into())))
                        })
                        .into(),
                        any_decl!(DeclKind::Let {
                            lhs: any_pattern!(PatternKind::Bind(Name::Resolved(
                                Symbol::DeclaredLocal(DeclaredLocalId(2)),
                                "counter".into()
                            ))),
                            type_annotation: None,
                            rhs: Some(any_expr!(ExprKind::Func(Func {
                                id: NodeID::ANY,
                                name: Name::Resolved(
                                    Symbol::DeclaredLocal(DeclaredLocalId(2)),
                                    "counter".into()
                                ),
                                name_span: Span::ANY,
                                generics: vec![],
                                params: vec![param!(ParamLocalId(1), "x")],
                                body: any_block!(vec![
                                    any_stmt!(StmtKind::Expr(variable!(ParamLocalId(1), "x")))
                                        .into(),
                                    any_stmt!(StmtKind::Expr(variable!(
                                        DeclaredLocalId(1),
                                        "count"
                                    )))
                                    .into(),
                                    any_stmt!(StmtKind::Expr(variable!(
                                        DeclaredLocalId(1),
                                        "count"
                                    )))
                                    .into(),
                                ]),
                                ret: None,
                                attributes: vec![]
                            })))
                        })
                        .into()
                    ]),
                    ret: None,
                    attributes: Default::default()
                })))
            })
        );

        let mut expected = FxHashSet::default();
        expected.insert(Capture {
            symbol: Symbol::DeclaredLocal(DeclaredLocalId(1)),
            parent_binder: Some(Symbol::Global(GlobalId::from(1))),
            level: Level(1),
        });

        assert_eq!(
            resolved.1.captures.get(&DeclaredLocalId(2).into()),
            Some(&expected),
            "{:?}",
            resolved.1.captures
        );
    }

    #[test]
    fn types_arent_captured() {
        let resolved = resolve(
            "
        struct Foo {}
        func bar() { Foo() }
        ",
        );

        assert!(
            !resolved.1.captures.contains_key(&GlobalId::from(1).into()),
            "captures: {:?}",
            resolved.1.captures.get(&GlobalId::from(1).into()).unwrap()
        );
    }

    #[test]
    fn resolves_nested_captures() {
        let resolved = resolve(
            "
        func outer(x) {
            let y = 123
            func inner() {
                (x, y)
            }
        }
        ",
        );

        let mut expected = FxHashSet::default();
        expected.insert(Capture {
            symbol: Symbol::DeclaredLocal(DeclaredLocalId(1)),
            parent_binder: Some(GlobalId::from(1).into()),
            level: Level(1),
        });

        expected.insert(Capture {
            symbol: Symbol::ParamLocal(ParamLocalId(1)),
            parent_binder: Some(Symbol::Global(GlobalId::from(1))),
            level: Level(1),
        });

        assert_eq!(
            resolved.1.captures.get(&DeclaredLocalId(2).into()),
            Some(&expected),
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
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: Pattern {
                    id: NodeID::ANY,
                    kind: PatternKind::Bind(Name::Resolved(
                        Symbol::Global(GlobalId::from(1),),
                        "fizz".into()
                    )),
                    span: Span::ANY
                },
                type_annotation: None,
                rhs: Some(any_expr!(ExprKind::Func(Func {
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::Global(GlobalId::from(1)), "fizz".into()),
                    name_span: Span::ANY,
                    generics: vec![GenericDecl {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        name: Name::Resolved(Symbol::TypeParameter(TypeParameterId(1)), "T".into()),
                        name_span: Span::ANY,
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
                            name_span: Span::ANY,
                            generics: vec![]
                        })
                    ),],
                    body: any_block!(vec![
                        any_stmt!(StmtKind::Expr(variable!(ParamLocalId(1), "t"))).into(),
                    ]),
                    ret: Some(annotation!(TypeAnnotationKind::Nominal {
                        name: Name::Resolved(Symbol::TypeParameter(TypeParameterId(1)), "T".into()),
                        name_span: Span::ANY,
                        generics: vec![]
                    })),
                    attributes: vec![],
                })),)
            })
        );
    }

    #[test]
    #[allow(non_snake_case)]
    fn resolves___IR() {
        let resolved = resolve(
            "
        __IR(\"$0 = add int 1 2\")
        ",
        );
        assert_eq!(
            *resolved.0.roots[0].as_stmt(),
            any_expr_stmt!(ExprKind::Call {
                callee: any_expr!(ExprKind::Variable(Name::Resolved(
                    Symbol::IR,
                    "__IR".into()
                )))
                .into(),
                type_args: vec![],
                args: vec![any!(CallArg, {
                    label: Label::Positional(0),
                    label_span: Span::ANY,
                    value: any_expr!(ExprKind::LiteralString("$0 = add int 1 2".into()))
                })]
            })
        );
    }

    #[test]
    #[ignore = "requires core"]
    #[allow(non_snake_case)]
    fn resolves_Optional() {
        let resolved = resolve(
            "
            Optional.none
        ",
        );
        assert_eq!(
            *resolved.0.roots[0].as_stmt(),
            any_expr_stmt!(ExprKind::Member(
                Some(
                    any_expr!(ExprKind::Constructor(Name::Resolved(
                        EnumId {
                            local_id: 1,
                            module_id: ModuleId::Core
                        }
                        .into(),
                        "Optional".into(),
                    )))
                    .into()
                ),
                "none".into(),
                Span::ANY,
            ))
        )
    }

    #[test]
    fn resolves_type_alias() {
        let resolved = resolve("typealias Intyfresh = Int ; Intyfresh");
        assert_eq!(
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::TypeAlias(
                Name::Resolved(Symbol::TypeAlias(TypeAliasId::from(1)), "Intyfresh".into()),
                Span::ANY,
                annotation!(TypeAnnotationKind::Nominal {
                    name: Name::Resolved(Symbol::Int, "Int".into()),
                    name_span: Span::ANY,
                    generics: vec![]
                })
            ))
        );

        assert_eq!(
            *resolved.0.roots[1].as_stmt(),
            any_expr_stmt!(ExprKind::Constructor(Name::Resolved(
                Symbol::TypeAlias(TypeAliasId::from(1)),
                "Intyfresh".into()
            )))
        );
    }

    #[test]
    fn resolves_struct() {
        let resolved = resolve("struct Person {}");
        assert_eq_diff!(
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                name: Name::Resolved(StructId::from(1).into(), "Person".into()),
                name_span: Span::ANY,
                generics: vec![],
                body: any_body!(vec![any_decl!(DeclKind::Init {
                    name: Name::Resolved(SynthesizedId::from(1).into(), "init".into()),
                    params: vec![param!(
                        ParamLocalId(2),
                        "self",
                        annotation!(TypeAnnotationKind::SelfType(Name::Resolved(
                            StructId::from(1).into(),
                            "Self".into()
                        )))
                    )],
                    body: any_block!(vec![any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                        ParamLocalId(2).into(),
                        "self".into()
                    )))])
                })])
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
        assert_eq_diff!(
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                name: Name::Resolved(StructId::from(1).into(), "Person".into()),
                name_span: Span::ANY,
                generics: vec![],
                body: any_body!(vec![
                    any_decl!(DeclKind::Init {
                        name: Name::Resolved(SynthesizedId::from(1).into(), "init".into()),
                        params: vec![
                            param!(
                                ParamLocalId(3),
                                "self",
                                annotation!(TypeAnnotationKind::SelfType(Name::Resolved(
                                    StructId::from(1).into(),
                                    "Self".into()
                                )))
                            ),
                            param!(
                                ParamLocalId(4),
                                "me",
                                annotation!(TypeAnnotationKind::Nominal {
                                    name: Name::Resolved(StructId::from(1).into(), "Person".into()),
                                    name_span: Span::ANY,
                                    generics: vec![],
                                })
                            )
                        ],
                        body: any_block!(vec![
                            any_stmt!(StmtKind::Assignment(
                                any_expr!(ExprKind::Member(
                                    Some(variable!(ParamLocalId(3), "self").into()),
                                    Label::Named("me".into()),
                                    Span::ANY
                                )),
                                variable!(ParamLocalId(4), "me")
                            ))
                            .into(),
                            any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                                ParamLocalId(3).into(),
                                "self".into()
                            )))
                        ])
                    }),
                    any_decl!(DeclKind::Property {
                        name: Name::Resolved(Symbol::Property(PropertyId::from(1)), "me".into()),
                        name_span: Span::ANY,
                        is_static: false,
                        type_annotation: Some(annotation!(TypeAnnotationKind::Nominal {
                            name: Name::Resolved(StructId::from(1).into(), "Person".into()),
                            name_span: Span::ANY,
                            generics: vec![]
                        })),
                        default_value: None
                    })
                ])
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
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                name: Name::Resolved(StructId::from(1).into(), "Person".into()),
                name_span: Span::ANY,
                generics: vec![],
                body: any_body!(vec![any_decl!(DeclKind::Init {
                    name: Name::Resolved(
                        Symbol::Initializer(InitializerId::from(1)),
                        "init".into()
                    ),
                    params: vec![param!(
                        Symbol::ParamLocal(ParamLocalId(1)),
                        "self",
                        annotation!(TypeAnnotationKind::SelfType(Name::Resolved(
                            Symbol::Struct(StructId::from(1)),
                            "Self".into()
                        )))
                    )],
                    body: any_block!(vec![])
                })])
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
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                name: Name::Resolved(StructId::from(1).into(), "Person".into()),
                name_span: Span::ANY,
                generics: vec![GenericDecl {
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::TypeParameter(TypeParameterId(1)), "T".into()),
                    name_span: Span::ANY,
                    generics: vec![],
                    conformances: vec![],
                    span: Span::ANY
                }],
                body: any_body!(vec![
                    any_decl!(DeclKind::Init {
                        name: Name::Resolved(SynthesizedId::from(1).into(), "init".into()),
                        params: vec![
                            param!(
                                ParamLocalId(3),
                                "self",
                                annotation!(TypeAnnotationKind::SelfType(Name::Resolved(
                                    StructId::from(1).into(),
                                    "Self".into()
                                )))
                            ),
                            param!(
                                ParamLocalId(4),
                                "me",
                                annotation!(TypeAnnotationKind::Nominal {
                                    name: Name::Resolved(TypeParameterId(1).into(), "T".into()),
                                    name_span: Span::ANY,
                                    generics: vec![],
                                })
                            )
                        ],
                        body: any_block!(vec![
                            any_stmt!(StmtKind::Assignment(
                                any_expr!(ExprKind::Member(
                                    Some(variable!(ParamLocalId(3), "self").into()),
                                    Label::Named("me".into()),
                                    Span::ANY
                                )),
                                variable!(ParamLocalId(4), "me")
                            ))
                            .into(),
                            any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                                ParamLocalId(3).into(),
                                "self".into()
                            )))
                        ])
                    }),
                    any_decl!(DeclKind::Property {
                        name: Name::Resolved(Symbol::Property(PropertyId::from(1)), "me".into()),
                        name_span: Span::ANY,
                        is_static: false,
                        type_annotation: Some(annotation!(TypeAnnotationKind::Nominal {
                            name: Name::Resolved(
                                Symbol::TypeParameter(TypeParameterId(1)),
                                "T".into()
                            ),
                            name_span: Span::ANY,
                            generics: vec![]
                        })),
                        default_value: None
                    })
                ])
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
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                name: Name::Resolved(StructId::from(1).into(), "Person".into()),
                name_span: Span::ANY,
                generics: vec![],
                body: any_body!(vec![
                    any_decl!(DeclKind::Init {
                        name: Name::Resolved(SynthesizedId::from(1).into(), "init".into()),
                        params: vec![param!(
                            ParamLocalId(2),
                            "self",
                            annotation!(TypeAnnotationKind::SelfType(Name::Resolved(
                                StructId::from(1).into(),
                                "Self".into()
                            )))
                        )],
                        body: any_block!(vec![any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                            ParamLocalId(2).into(),
                            "self".into()
                        )))])
                    }),
                    any_decl!(DeclKind::Method {
                        func: Box::new(Func {
                            id: NodeID::ANY,
                            name: Name::Resolved(
                                Symbol::StaticMethod(StaticMethodId::from(1)),
                                "fizz".into()
                            ),
                            name_span: Span::ANY,
                            generics: vec![],
                            params: vec![],
                            body: any_block!(vec![]),
                            ret: None,
                            attributes: vec![]
                        }),
                        is_static: true
                    }),
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
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                name: Name::Resolved(StructId::from(1).into(), "Person".into()),
                name_span: Span::ANY,
                generics: vec![],
                body: any_body!(vec![
                    any_decl!(DeclKind::Init {
                        name: Name::Resolved(SynthesizedId::from(1).into(), "init".into()),
                        params: vec![param!(
                            ParamLocalId(4),
                            "self",
                            annotation!(TypeAnnotationKind::SelfType(Name::Resolved(
                                StructId::from(1).into(),
                                "Self".into()
                            )))
                        )],
                        body: any_block!(vec![any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                            ParamLocalId(4).into(),
                            "self".into()
                        )))])
                    }),
                    any_decl!(DeclKind::Method {
                        func: Box::new(Func {
                            id: NodeID::ANY,
                            name: Name::Resolved(
                                Symbol::InstanceMethod(InstanceMethodId::from(1)),
                                "fizz".into()
                            ),
                            name_span: Span::ANY,
                            generics: vec![],
                            params: vec![param!(
                                Symbol::ParamLocal(ParamLocalId(1)),
                                "self",
                                annotation!(TypeAnnotationKind::SelfType(Name::Resolved(
                                    StructId::from(1).into(),
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
                                    "buzz".into(),
                                    Span::ANY,
                                ))
                                .into(),
                                type_args: vec![],
                                args: vec![]
                            })]),
                            ret: None,
                            attributes: vec![]
                        }),
                        is_static: false
                    }),
                    any_decl!(DeclKind::Method {
                        func: Box::new(Func {
                            id: NodeID::ANY,
                            name: Name::Resolved(
                                Symbol::InstanceMethod(InstanceMethodId::from(2)),
                                "buzz".into()
                            ),
                            name_span: Span::ANY,
                            generics: vec![],
                            params: vec![param!(
                                Symbol::ParamLocal(ParamLocalId(2)),
                                "self",
                                annotation!(TypeAnnotationKind::SelfType(Name::Resolved(
                                    StructId::from(1).into(),
                                    "Self".into()
                                )))
                            )],
                            body: any_block!(vec![any_expr_stmt!(ExprKind::Call {
                                callee: any_expr!(ExprKind::Member(
                                    Some(Box::new(any_expr!(ExprKind::Variable(Name::Resolved(
                                        Symbol::ParamLocal(ParamLocalId(2)),
                                        "self".into()
                                    ))))),
                                    "fizz".into(),
                                    Span::ANY,
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
            *resolved.0.roots[1].as_stmt(),
            any_expr_stmt!(ExprKind::Call {
                callee: any_expr!(ExprKind::Constructor(Name::Resolved(
                    Symbol::Struct(StructId::from(1)),
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
            *resolved.0.roots[1].as_decl(),
            any_decl!(DeclKind::Extend {
                name: Name::Resolved(Symbol::Struct(StructId::from(1)), "Person".into()),
                name_span: Span::ANY,
                conformances: vec![],
                generics: vec![],
                body: any_body!(vec![])
            }),
        )
    }

    #[test]
    fn resolves_struct_extension_out_of_order() {
        let resolved = resolve(
            "
        extend Person {
            func fizz() {}
        }
        struct Person {}
        ",
        );
        assert_eq_diff!(
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Extend {
                name: Name::Resolved(Symbol::Struct(StructId::from(1)), "Person".into()),
                name_span: Span::ANY,
                conformances: vec![],
                generics: vec![],
                body: any_body!(vec![any_decl!(DeclKind::Method {
                    func: Box::new(Func {
                        id: NodeID::ANY,
                        name: Name::Resolved(
                            Symbol::InstanceMethod(InstanceMethodId::from(1)),
                            "fizz".into()
                        ),
                        name_span: Span::ANY,
                        generics: vec![],
                        params: vec![Parameter {
                            id: NodeID::ANY,
                            name: Name::Resolved(
                                Symbol::ParamLocal(ParamLocalId(1)),
                                "self".into()
                            ),
                            name_span: Span::ANY,
                            type_annotation: Some(annotation!(TypeAnnotationKind::SelfType(
                                Name::Resolved(Symbol::Struct(StructId::from(1)), "Self".into())
                            ))),
                            span: Span::ANY,
                        }],
                        body: any_block!(vec![]),
                        ret: None,
                        attributes: vec![]
                    }),
                    is_static: false
                })])
            }),
        )
    }

    #[test]
    fn resolves_struct_child_types() {
        let resolved = resolve(
            "
        struct A {
            struct B {}
            typealias C = Int
            enum D {}
        }
        ",
        );
        assert_eq!(
            *resolved
                .1
                .child_types
                .get(&Symbol::Struct(StructId::from(1)))
                .unwrap(),
            indexmap::indexmap! {
                "B".into() => Symbol::Struct(StructId::from(2)),
                "C".into() => Symbol::TypeAlias(TypeAliasId::from(4)),
                "D".into() => Symbol::Enum(EnumId::from(3))
            }
        )
    }

    #[test]
    fn resolves_enum_child_types() {
        let resolved = resolve(
            "
        enum A {
            struct B {}
            typealias C = Int
            enum D {}
        }
        ",
        );
        assert_eq!(
            *resolved
                .1
                .child_types
                .get(&Symbol::Enum(EnumId::from(1)))
                .unwrap(),
            indexmap::indexmap! {
                "B".into() => Symbol::Struct(StructId::from(2)),
                "C".into() => Symbol::TypeAlias(TypeAliasId::from(4)),
                "D".into() => Symbol::Enum(EnumId::from(3))
            }
        )
    }

    #[test]
    fn resolves_protocol_child_types() {
        let resolved = resolve(
            "
        protocol A {
            struct B {}
            typealias C = Int
            enum D {}
            associated E
        }
        ",
        );
        assert_eq!(
            *resolved
                .1
                .child_types
                .get(&Symbol::Protocol(ProtocolId::from(1)))
                .unwrap(),
            indexmap::indexmap! {
                "B".into() => Symbol::Struct(StructId::from(1)),
                "C".into() => Symbol::TypeAlias(TypeAliasId::from(3)),
                "D".into() => Symbol::Enum(EnumId::from(2)),
                "E".into() => Symbol::AssociatedType(AssociatedTypeId::from(1))
            }
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
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Enum {
                name: Name::Resolved(Symbol::Enum(EnumId::from(1)), "Fizz".into()),
                name_span: Span::ANY,
                generics: vec![],
                body: any_body!(vec![
                    any_decl!(DeclKind::EnumVariant(
                        Name::Resolved(Symbol::Variant(VariantId::from(1)), "foo".into()),
                        Span::ANY,
                        vec![]
                    )),
                    any_decl!(DeclKind::EnumVariant(
                        Name::Resolved(Symbol::Variant(VariantId::from(2)), "bar".into()),
                        Span::ANY,
                        vec![]
                    )),
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
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Protocol {
                name: Name::Resolved(Symbol::Protocol(ProtocolId::from(1)), "Fizzable".into()),
                name_span: Span::ANY,
                conformances: vec![],
                generics: vec![],
                body: any_body!(vec![any_decl!(DeclKind::MethodRequirement(
                    FuncSignature {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        name: Name::Resolved(
                            Symbol::MethodRequirement(MethodRequirementId::from(1)),
                            "buzz".into()
                        ),
                        params: vec![Parameter {
                            id: NodeID::ANY,
                            name: Name::Resolved(ParamLocalId::from(1u32).into(), "self".into()),
                            name_span: Span::ANY,
                            type_annotation: Some(annotation!(TypeAnnotationKind::SelfType(
                                Name::Resolved(ProtocolId::from(1).into(), "Self".into())
                            ))),
                            span: Span::ANY
                        }],
                        generics: vec![],
                        ret: Some(Box::new(annotation!(TypeAnnotationKind::Tuple(vec![]))))
                    }
                ))])
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
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Protocol {
                name: Name::Resolved(Symbol::Protocol(ProtocolId::from(1)), "Fizzable".into()),
                name_span: Span::ANY,
                conformances: vec![],
                generics: vec![],
                body: any_body!(vec![
                    any_decl!(DeclKind::Associated {
                        generic: GenericDecl {
                            id: NodeID::ANY,
                            name: Name::Resolved(
                                Symbol::AssociatedType(AssociatedTypeId::from(1)),
                                "T".into()
                            ),
                            name_span: Span::ANY,
                            generics: vec![],
                            conformances: vec![],
                            span: Span::ANY
                        }
                    }),
                    any_decl!(DeclKind::MethodRequirement(FuncSignature {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        name: Name::Resolved(
                            Symbol::MethodRequirement(MethodRequirementId::from(1)),
                            "buzz".into()
                        ),
                        params: vec![Parameter {
                            id: NodeID::ANY,
                            name: Name::Resolved(ParamLocalId::from(1u32).into(), "self".into()),
                            name_span: Span::ANY,
                            type_annotation: Some(annotation!(TypeAnnotationKind::SelfType(
                                Name::Resolved(ProtocolId::from(1).into(), "Self".into())
                            ))),
                            span: Span::ANY
                        }],
                        generics: vec![],
                        ret: Some(Box::new(annotation!(TypeAnnotationKind::Nominal {
                            name: Name::Resolved(
                                Symbol::AssociatedType(AssociatedTypeId::from(1)),
                                "T".into()
                            ),
                            name_span: Span::ANY,
                            generics: vec![]
                        })))
                    })),
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
            *resolved.0.roots[1].as_stmt(),
            any_expr_stmt!(ExprKind::Match(
                Box::new(variable!(GlobalId::from(1), "a")),
                vec![MatchArm {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    pattern: Pattern {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        kind: PatternKind::Bind(Name::Resolved(
                            Symbol::PatternBindLocal(PatternBindLocalId(1)),
                            "b".into()
                        ))
                    },
                    body: any_block!(vec![any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                        Symbol::PatternBindLocal(PatternBindLocalId(1)),
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

        assert_eq!(
            resolved.1.diagnostics.len(),
            1,
            "{:?}",
            resolved.1.diagnostics
        );
    }

    #[test]
    fn or_patterns_resolve_binds() {
        let resolved = resolve(
            "
        let .a(x) | .b(x)
        ",
        );

        assert_eq_diff!(
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: any_pattern!(PatternKind::Or(vec![
                    any_pattern!(PatternKind::Variant {
                        enum_name: None,
                        variant_name: "a".into(),
                        variant_name_span: Span::ANY,
                        fields: vec![any_pattern!(PatternKind::Bind(Name::Resolved(
                            Symbol::Global(1u32.into()),
                            "x".into()
                        )))]
                    }),
                    any_pattern!(PatternKind::Variant {
                        enum_name: None,
                        variant_name: "b".into(),
                        variant_name_span: Span::ANY,
                        fields: vec![any_pattern!(PatternKind::Bind(Name::Resolved(
                            Symbol::Global(1u32.into()), // This should be the same symbol as above.
                            "x".into()
                        )))]
                    })
                ])),
                type_annotation: None,
                rhs: None
            })
        );
    }

    #[test]
    fn or_patterns_require_matching_binds() {
        let resolved = resolve_err(
            "
        let .a(x) | .b(y)
        ",
        );

        assert_eq!(
            resolved.1.diagnostics.len(),
            1,
            "{:?}",
            resolved.1.diagnostics
        );
    }
}
