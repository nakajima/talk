#[cfg(test)]
pub mod tests {
    use std::rc::Rc;

    use indexmap::indexset;

    use crate::{
        annotation, any, any_block, any_body, any_decl, any_expr, any_expr_stmt, any_stmt,
        assert_eq_diff,
        ast::{AST, NameResolved},
        compiling::module::{ModuleEnvironment, ModuleId},
        diagnostic::{AnyDiagnostic, Diagnostic, Severity},
        label::Label,
        name::Name,
        name_resolution::{
            name_resolver::{NameResolver, NameResolverError, ResolvedNames},
            symbol::{
                AssociatedTypeId, BuiltinId, DeclaredLocalId, EffectId, EnumId, GlobalId,
                InitializerId, InstanceMethodId, MethodRequirementId, ParamLocalId,
                PatternBindLocalId, PropertyId, ProtocolId, StaticMethodId, StructId, Symbol,
                SynthesizedId, TypeAliasId, TypeParameterId, VariantId,
            },
        },
        node_id::{FileID, NodeID},
        node_kinds::{
            block::Block,
            call_arg::CallArg,
            decl::{Decl, DeclKind, ReceiverMode},
            expr::{Expr, ExprKind},
            func::{CaptureMode, EffectSet, Func},
            func_signature::FuncSignature,
            generic_decl::GenericDecl,
            match_arm::MatchArm,
            parameter::Parameter,
            pattern::{Pattern, PatternKind},
            stmt::{Stmt, StmtKind},
            type_annotation::{TypeAnnotation, TypeAnnotationKind},
        },
        parsing::parser_tests::tests::parse,
        span::Span,
    };

    fn enum_variant(name: Name, name_span: Span, payloads: Vec<TypeAnnotation>) -> DeclKind {
        DeclKind::EnumVariant {
            name,
            name_span,
            generics: vec![],
            payloads,
            result: None,
        }
    }

    /// Helper to create a test TypeParameterId using ModuleId::Current
    fn test_type_param(id: u32) -> Symbol {
        Symbol::TypeParameter(TypeParameterId::new(ModuleId::Current, id))
    }

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
        let mut parseds = vec![parsed];
        crate::desugar::desugar(&mut parseds);
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
                rhs: None,
            })
        );
    }

    /// The ids of every resolved `Variable` of symbol kind `kind` (e.g.
    /// "DeclaredLocal", "ParamLocal", "Global") named `needle`, in source
    /// order, scraped from the AST's debug rendering.
    fn variable_uses(rendered: &str, kind: &str, needle: &str) -> Vec<u32> {
        let pattern = format!("Variable(Resolved(@{kind}({kind}Id(");
        rendered
            .match_indices(&pattern)
            .filter_map(|(at, _)| {
                let rest = &rendered[at + pattern.len()..];
                let close = rest.find(')')?;
                let id = rest[..close].parse::<u32>().ok()?;
                let suffix = &rest[close..];
                suffix
                    .starts_with(&format!(")), \"{needle}\""))
                    .then_some(id)
            })
            .collect()
    }

    fn local_variable_uses(rendered: &str, needle: &str) -> Vec<u32> {
        variable_uses(rendered, "DeclaredLocal", needle)
    }

    /// Like [`variable_uses`], for `Global` symbols (module ids render as
    /// `@Global(Global(_:1))`, not `GlobalId`).
    fn global_variable_uses(rendered: &str, needle: &str) -> Vec<u32> {
        let pattern = "Variable(Resolved(@Global(Global(_:";
        rendered
            .match_indices(pattern)
            .filter_map(|(at, _)| {
                let rest = &rendered[at + pattern.len()..];
                let close = rest.find(')')?;
                let id = rest[..close].parse::<u32>().ok()?;
                let suffix = &rest[close..];
                suffix
                    .starts_with(&format!(")), \"{needle}\""))
                    .then_some(id)
            })
            .collect()
    }

    #[test]
    fn sibling_blocks_declare_same_named_lets_independently() {
        // Each branch's `y` is its own binding; the uses must resolve to
        // their own block's declaration, not whichever declared last.
        let (ast, _) = resolve(
            "func f(a: Bool, x: Int) -> Int {\n\tlet out = 0\n\tif a {\n\t\tlet y = x\n\t\tout = y\n\t}\n\tif a {\n\t\tlet y = x\n\t\tout = y\n\t}\n\tout\n}",
        );
        let rendered = format!("{ast:?}");
        let y_uses = local_variable_uses(&rendered, "y");
        assert_eq!(y_uses.len(), 2, "two y uses: {rendered}");
        assert_ne!(
            y_uses[0], y_uses[1],
            "each use must reference its own block's y"
        );
    }

    #[test]
    fn nested_shadowing_resolves_innermost_first() {
        let (ast, _) = resolve(
            "func f(a: Bool, x: Int) -> Int {\n\tlet y = x\n\tlet inner = 0\n\tif a {\n\t\tlet y = x\n\t\tinner = y\n\t}\n\ty\n}",
        );
        let rendered = format!("{ast:?}");
        let y_uses = local_variable_uses(&rendered, "y");
        // In order: the inner block's use, then the tail's outer use.
        assert_eq!(y_uses.len(), 2, "{rendered}");
        assert_ne!(
            y_uses[0], y_uses[1],
            "inner use shadows, outer use sees the outer y: {y_uses:?}"
        );
    }

    #[test]
    fn sequential_rebinding_is_legal() {
        // Rule 2: a later same-named `let` shadows from its point of
        // declaration on; earlier uses (including the shadow's own rhs)
        // keep the earlier binding.
        let (ast, _) = resolve("func f(x: Int) -> Int {\n\tlet y = x\n\tlet y = y\n\ty\n}");
        let rendered = format!("{ast:?}");
        let y_uses = variable_uses(&rendered, "DeclaredLocal", "y");
        // In source order: the second let's rhs, then the tail.
        assert_eq!(y_uses.len(), 2, "{rendered}");
        assert_ne!(
            y_uses[0], y_uses[1],
            "the rhs sees the first y, the tail sees the rebinding"
        );
    }

    #[test]
    fn duplicate_binders_in_one_pattern_are_an_error() {
        // Rebinding across `let`s is legal; binding one name twice in a
        // single pattern is not (each would silently orphan the other).
        let resolved = resolve_err("match (1, 2) {\n\t(a, a) -> a\n}");
        assert!(
            matches!(
                &resolved.1.diagnostics[0],
                AnyDiagnostic::NameResolution(Diagnostic::<NameResolverError> {
                    kind: NameResolverError::DuplicateDeclaration(name),
                    ..
                }) if name == "a"
            ),
            "{:?}",
            resolved.1.diagnostics
        );
    }

    ///////////////////////////////////////////////////////////////////////
    // Sequential-scoping characterization matrix
    // (docs/sequential-scoping-plan.md). Each test locks today's
    // behavior; the ones marked "flips at step N" record the current
    // locals-hoisting semantics that sequential scoping replaces.
    ///////////////////////////////////////////////////////////////////////

    #[test]
    fn let_rhs_resolves_to_the_outer_binding() {
        // Rule 1: a binding is visible from just after its initializer, so
        // `let y = y` sees the *outer* y on the rhs.
        let (ast, _) = resolve(
            "func f(a: Bool) -> Int {\n\tlet y = 1\n\tif a {\n\t\tlet y = y\n\t\ty\n\t}\n\ty\n}",
        );
        let rendered = format!("{ast:?}");
        let y_uses = variable_uses(&rendered, "DeclaredLocal", "y");
        // In source order: the inner rhs, the inner tail, the outer tail.
        assert_eq!(y_uses.len(), 3, "{rendered}");
        assert_eq!(y_uses[0], y_uses[2], "the rhs use resolves to the outer y");
        assert_ne!(y_uses[0], y_uses[1], "the inner tail sees the shadow");
    }

    #[test]
    fn body_let_rhs_sees_the_param_it_shadows() {
        // Rule 3: parameters live in the function's scope; a body-level
        // `let x = x` reads the parameter on the rhs and shadows it after.
        let (ast, _) = resolve("func f(x: Int) -> Int {\n\tlet x = x\n\tx\n}");
        let rendered = format!("{ast:?}");
        let local = variable_uses(&rendered, "DeclaredLocal", "x");
        let param = variable_uses(&rendered, "ParamLocal", "x");
        assert_eq!(param.len(), 1, "the rhs reads the param: {rendered}");
        assert_eq!(local.len(), 1, "the tail reads the shadow: {rendered}");
    }

    #[test]
    fn use_before_declaration_is_undefined() {
        // Rule 1: a binding is not visible before its declaration.
        let resolved = resolve_err("func f() -> Int {\n\tlet a = b\n\tlet b = 2\n\tb\n}");
        assert_eq!(
            resolved.1.diagnostics,
            vec![AnyDiagnostic::NameResolution(Diagnostic::<
                NameResolverError,
            > {
                id: NodeID::ANY,
                severity: Severity::Error,
                kind: NameResolverError::UndefinedName("b".into())
            })],
            "{:?}",
            resolved.1.diagnostics
        );
    }

    #[test]
    fn closure_sees_the_binding_visible_at_the_closure() {
        // A shadow *after* (and inside a sibling block of) the closure must
        // not change which binding the closure body resolved to.
        let (ast, _) = resolve(
            "func outer() {\n\tlet x = 1\n\tfunc inner() { x }\n\tif true {\n\t\tlet x = 2\n\t\tx\n\t}\n}",
        );
        let rendered = format!("{ast:?}");
        let x_uses = variable_uses(&rendered, "DeclaredLocal", "x");
        // In source order: inner's body use, then the if-block's use.
        assert_eq!(x_uses.len(), 2, "{rendered}");
        assert_ne!(
            x_uses[0], x_uses[1],
            "inner reads the outer x, the block reads its shadow"
        );
    }

    #[test]
    fn local_named_funcs_are_mutually_visible_in_their_block() {
        // Item behavior (Rust's fn-in-block): `func a` / `func b` in one
        // block see each other regardless of order. They desugar to
        // func-valued lets before resolution; their binders must keep
        // block-wide visibility under sequential scoping.
        let (ast, _) = resolve("func outer() {\n\tfunc a() { b() }\n\tfunc b() { a() }\n\ta()\n}");
        let rendered = format!("{ast:?}");
        let a_uses = variable_uses(&rendered, "DeclaredLocal", "a");
        let b_uses = variable_uses(&rendered, "DeclaredLocal", "b");
        assert_eq!(b_uses.len(), 1, "{rendered}");
        assert_eq!(a_uses.len(), 2, "{rendered}");
        assert_eq!(a_uses[0], a_uses[1], "both a uses hit the same binder");
    }

    #[test]
    fn func_valued_let_is_visible_inside_its_own_body() {
        // Self-recursion through the binder: `func f` sugar and
        // `let f = func ...` both resolve the body's f to the binder.
        let (ast, _) = resolve("func outer() {\n\tlet f = func() { f() }\n\tf()\n}");
        let rendered = format!("{ast:?}");
        let f_uses = variable_uses(&rendered, "DeclaredLocal", "f");
        assert_eq!(f_uses.len(), 2, "{rendered}");
        assert_eq!(f_uses[0], f_uses[1]);
    }

    #[test]
    fn module_scope_rebinding_is_legal_and_last_wins() {
        // Matrix rule 4: module scope keeps its declare-then-resolve
        // semantics — redeclaration is allowed and every use resolves to
        // the newest binder (the REPL depends on this).
        let (ast, _) = resolve("let x = 1\nlet x = 2\nx");
        let rendered = format!("{ast:?}");
        let x_uses = global_variable_uses(&rendered, "x");
        assert_eq!(x_uses.len(), 1, "{rendered}");
        assert_eq!(x_uses[0], 2, "the use sees the last declaration");
    }

    #[test]
    fn each_method_body_resolves_its_own_params() {
        let (ast, _) = resolve(
            "struct P {\n\tfunc m1(a: Int) -> Int { a }\n\tfunc m2(a: Int) -> Int { a }\n}",
        );
        let rendered = format!("{ast:?}");
        let a_uses = variable_uses(&rendered, "ParamLocal", "a");
        assert_eq!(a_uses.len(), 2, "{rendered}");
        assert_ne!(
            a_uses[0], a_uses[1],
            "each method body sees its own parameter"
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
                    captures: vec![],
                    where_clause: None,
                    effects: Default::default(),
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
                }))),
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
                    captures: vec![],
                    where_clause: None,
                    params: vec![],
                    effects: Default::default(),
                    body: any_block!(vec![any_expr_stmt!(ExprKind::Call {
                        callee: Box::new(variable!(Symbol::Global(GlobalId::from(2)), "even")),
                        type_args: vec![],
                        args: vec![],
                        trailing_block: None,
                    })]),
                    ret: None,
                    attributes: vec![]
                }))),
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
                    captures: vec![],
                    where_clause: None,
                    params: vec![],
                    effects: Default::default(),
                    body: any_block!(vec![any_expr_stmt!(ExprKind::Call {
                        callee: Box::new(variable!(Symbol::Global(GlobalId::from(1)), "odd")),
                        type_args: vec![],
                        args: vec![],
                        trailing_block: None,
                    })]),
                    ret: None,
                    attributes: vec![]
                }))),
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
                    captures: vec![],
                    where_clause: None,
                    effects: Default::default(),
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
                                captures: vec![],
                                where_clause: None,
                                effects: Default::default(),
                                params: vec![param!(ParamLocalId(3), "x")],
                                body: any_block!(vec![
                                    any_stmt!(StmtKind::Expr(variable!(ParamLocalId(3), "x")))
                                        .into(),
                                    any_stmt!(StmtKind::Expr(variable!(ParamLocalId(2), "y")))
                                        .into(),
                                ]),
                                ret: None,
                                attributes: vec![],
                            }))),
                        })
                        .into(),
                        any_stmt!(StmtKind::Expr(variable!(ParamLocalId(1), "x"))).into(),
                    ]),
                    ret: None,
                    attributes: vec![],
                }))),
            }),
        );
    }

    #[test]
    fn resolves_nested_func_bodies_against_enclosing_locals() {
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
                    captures: vec![],
                    where_clause: None,
                    params: Default::default(),
                    effects: Default::default(),
                    body: any_block!(vec![
                        any_decl!(DeclKind::Let {
                            lhs: any_pattern!(PatternKind::Bind(Name::Resolved(
                                Symbol::DeclaredLocal(DeclaredLocalId(2)),
                                "count".into()
                            ))),
                            type_annotation: None,
                            rhs: Some(any_expr!(ExprKind::LiteralInt("0".into()))),
                        })
                        .into(),
                        any_decl!(DeclKind::Let {
                            lhs: any_pattern!(PatternKind::Bind(Name::Resolved(
                                Symbol::DeclaredLocal(DeclaredLocalId(1)),
                                "counter".into()
                            ))),
                            type_annotation: None,
                            rhs: Some(any_expr!(ExprKind::Func(Func {
                                id: NodeID::ANY,
                                name: Name::Resolved(
                                    Symbol::DeclaredLocal(DeclaredLocalId(1)),
                                    "counter".into()
                                ),
                                name_span: Span::ANY,
                                generics: vec![],
                                captures: vec![],
                                where_clause: None,
                                effects: Default::default(),
                                params: vec![param!(ParamLocalId(1), "x")],
                                body: any_block!(vec![
                                    any_stmt!(StmtKind::Expr(variable!(ParamLocalId(1), "x")))
                                        .into(),
                                    any_stmt!(StmtKind::Expr(variable!(
                                        DeclaredLocalId(2),
                                        "count"
                                    )))
                                    .into(),
                                    any_stmt!(StmtKind::Expr(variable!(
                                        DeclaredLocalId(2),
                                        "count"
                                    )))
                                    .into(),
                                ]),
                                ret: None,
                                attributes: vec![]
                            }))),
                        })
                        .into()
                    ]),
                    ret: None,
                    attributes: Default::default()
                }))),
            })
        );
    }

    #[test]
    fn resolves_explicit_capture_specs() {
        let resolved = resolve(
            "
        func outer() {
            let a = 1
            let b = 2
            let c = 3
            let d = 4
            let e = 5
            let f = func [a, copy b, consuming c, &d, &mut e]() {
                a
            }
        }
        ",
        );

        let DeclKind::Let {
            rhs: Some(outer_expr),
            ..
        } = &resolved.0.roots[0].as_decl().kind
        else {
            panic!("expected outer function declaration");
        };
        let ExprKind::Func(outer) = &outer_expr.kind else {
            panic!("expected outer function literal");
        };
        let DeclKind::Let {
            rhs: Some(inner_expr),
            ..
        } = &outer.body.body[5].as_decl().kind
        else {
            panic!("expected nested function binding");
        };
        let ExprKind::Func(inner) = &inner_expr.kind else {
            panic!("expected nested function literal");
        };

        let captures: Vec<_> = inner
            .captures
            .iter()
            .map(|capture| {
                assert!(
                    capture.name.symbol().is_ok(),
                    "capture should be resolved: {:?}",
                    capture
                );
                (capture.name.name_str(), capture.mode)
            })
            .collect();
        assert_eq!(
            captures,
            vec![
                ("a".to_string(), CaptureMode::Copy),
                ("b".to_string(), CaptureMode::Copy),
                ("c".to_string(), CaptureMode::Move),
                ("d".to_string(), CaptureMode::BorrowShared),
                ("e".to_string(), CaptureMode::BorrowMut),
            ]
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
                        name: Name::Resolved(test_type_param(1), "T".into()),
                        name_span: Span::ANY,
                        generics: vec![],
                        conformances: vec![],
                    }],
                    captures: vec![],
                    where_clause: None,
                    effects: Default::default(),
                    params: vec![param!(
                        ParamLocalId(1),
                        "t",
                        annotation!(TypeAnnotationKind::Nominal {
                            name: Name::Resolved(test_type_param(1), "T".into()),
                            name_span: Span::ANY,
                            generics: vec![]
                        })
                    ),],
                    body: any_block!(vec![
                        any_stmt!(StmtKind::Expr(variable!(ParamLocalId(1), "t"))).into(),
                    ]),
                    ret: Some(annotation!(TypeAnnotationKind::Nominal {
                        name: Name::Resolved(test_type_param(1), "T".into()),
                        name_span: Span::ANY,
                        generics: vec![]
                    })),
                    attributes: vec![],
                })),),
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
                })],
                trailing_block: None,
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
                linear: false,
                heap: false,
                name: Name::Resolved(StructId::from(1).into(), "Person".into()),
                name_span: Span::ANY,
                generics: vec![],
                where_clause: None,
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
                linear: false,
                heap: false,
                name: Name::Resolved(StructId::from(1).into(), "Person".into()),
                name_span: Span::ANY,
                generics: vec![],
                where_clause: None,
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
                                ))
                                .into(),
                                variable!(ParamLocalId(4), "me").into()
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
                linear: false,
                heap: false,
                name: Name::Resolved(StructId::from(1).into(), "Person".into()),
                name_span: Span::ANY,
                generics: vec![],
                where_clause: None,
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
                linear: false,
                heap: false,
                name: Name::Resolved(StructId::from(1).into(), "Person".into()),
                name_span: Span::ANY,
                generics: vec![GenericDecl {
                    id: NodeID::ANY,
                    name: Name::Resolved(test_type_param(1), "T".into()),
                    name_span: Span::ANY,
                    generics: vec![],
                    conformances: vec![],
                    span: Span::ANY
                }],
                where_clause: None,
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
                                    name: Name::Resolved(test_type_param(1), "T".into()),
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
                                ))
                                .into(),
                                variable!(ParamLocalId(4), "me").into()
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
                            name: Name::Resolved(test_type_param(1), "T".into()),
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
                linear: false,
                heap: false,
                name: Name::Resolved(StructId::from(1).into(), "Person".into()),
                name_span: Span::ANY,
                generics: vec![],
                where_clause: None,
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
                            effects: Default::default(),
                            generics: vec![],
                            captures: vec![],
                            where_clause: None,
                            params: vec![],
                            body: any_block!(vec![]),
                            ret: None,
                            attributes: vec![]
                        }),
                        is_static: true,
                        receiver_mode: ReceiverMode::None
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
                linear: false,
                heap: false,
                name: Name::Resolved(StructId::from(1).into(), "Person".into()),
                name_span: Span::ANY,
                generics: vec![],
                where_clause: None,
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
                                Symbol::InstanceMethod(InstanceMethodId::from(1)),
                                "fizz".into()
                            ),
                            name_span: Span::ANY,
                            generics: vec![],
                            captures: vec![],
                            where_clause: None,
                            effects: Default::default(),
                            params: vec![param!(
                                Symbol::ParamLocal(ParamLocalId(3)),
                                "self",
                                annotation!(TypeAnnotationKind::Borrow {
                                    mutable: false,
                                    inner: Box::new(annotation!(TypeAnnotationKind::SelfType(
                                        Name::Resolved(StructId::from(1).into(), "Self".into())
                                    )))
                                })
                            )],
                            body: any_block!(vec![any_expr_stmt!(ExprKind::Call {
                                callee: any_expr!(ExprKind::Member(
                                    Some(
                                        any_expr!(ExprKind::Variable(Name::Resolved(
                                            Symbol::ParamLocal(ParamLocalId(3)),
                                            "self".into()
                                        )))
                                        .into()
                                    ),
                                    "buzz".into(),
                                    Span::ANY,
                                ))
                                .into(),
                                type_args: vec![],
                                args: vec![],
                                trailing_block: None,
                            })]),
                            ret: None,
                            attributes: vec![]
                        }),
                        is_static: false,
                        receiver_mode: ReceiverMode::None
                    }),
                    any_decl!(DeclKind::Method {
                        func: Box::new(Func {
                            id: NodeID::ANY,
                            name: Name::Resolved(
                                Symbol::InstanceMethod(InstanceMethodId::from(2)),
                                "buzz".into()
                            ),
                            name_span: Span::ANY,
                            effects: Default::default(),
                            generics: vec![],
                            captures: vec![],
                            where_clause: None,
                            params: vec![param!(
                                Symbol::ParamLocal(ParamLocalId(4)),
                                "self",
                                annotation!(TypeAnnotationKind::Borrow {
                                    mutable: false,
                                    inner: Box::new(annotation!(TypeAnnotationKind::SelfType(
                                        Name::Resolved(StructId::from(1).into(), "Self".into())
                                    )))
                                })
                            )],
                            body: any_block!(vec![any_expr_stmt!(ExprKind::Call {
                                callee: any_expr!(ExprKind::Member(
                                    Some(Box::new(any_expr!(ExprKind::Variable(Name::Resolved(
                                        Symbol::ParamLocal(ParamLocalId(4)),
                                        "self".into()
                                    ))))),
                                    "fizz".into(),
                                    Span::ANY,
                                ))
                                .into(),
                                type_args: vec![],
                                args: vec![],
                                trailing_block: None,
                            })]),
                            ret: None,
                            attributes: vec![]
                        }),
                        is_static: false,
                        receiver_mode: ReceiverMode::None
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
                args: vec![],
                trailing_block: None,
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
                row_generics: vec![],
                conformances: vec![],
                generics: vec![],
                where_clause: None,
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
                row_generics: vec![],
                conformances: vec![],
                generics: vec![],
                where_clause: None,
                body: any_body!(vec![any_decl!(DeclKind::Method {
                    func: Box::new(Func {
                        id: NodeID::ANY,
                        name: Name::Resolved(
                            Symbol::InstanceMethod(InstanceMethodId::from(1)),
                            "fizz".into()
                        ),
                        name_span: Span::ANY,
                        generics: vec![],
                        captures: vec![],
                        where_clause: None,
                        effects: Default::default(),
                        params: vec![Parameter {
                            id: NodeID::ANY,
                            name: Name::Resolved(
                                Symbol::ParamLocal(ParamLocalId(2)),
                                "self".into()
                            ),
                            name_span: Span::ANY,
                            type_annotation: Some(annotation!(TypeAnnotationKind::Borrow {
                                mutable: false,
                                inner: Box::new(annotation!(TypeAnnotationKind::SelfType(
                                    Name::Resolved(
                                        Symbol::Struct(StructId::from(1)),
                                        "Self".into()
                                    )
                                )))
                            })),
                            span: Span::ANY,
                        }],
                        body: any_block!(vec![]),
                        ret: None,
                        attributes: vec![]
                    }),
                    is_static: false,
                    receiver_mode: ReceiverMode::None
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
                linear: false,
                name: Name::Resolved(Symbol::Enum(EnumId::from(1)), "Fizz".into()),
                name_span: Span::ANY,
                generics: vec![],
                where_clause: None,
                body: any_body!(vec![
                    any_decl!(enum_variant(
                        Name::Resolved(Symbol::Variant(VariantId::from(1)), "foo".into()),
                        Span::ANY,
                        vec![]
                    )),
                    any_decl!(enum_variant(
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
                where_clause: None,
                body: any_body!(vec![any_decl!(DeclKind::MethodRequirement {
                    signature: FuncSignature {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        name: Name::Resolved(
                            Symbol::MethodRequirement(MethodRequirementId::from(1)),
                            "buzz".into()
                        ),
                        effects: Default::default(),
                        params: vec![Parameter {
                            id: NodeID::ANY,
                            name: Name::Resolved(ParamLocalId::from(1u32).into(), "self".into()),
                            name_span: Span::ANY,
                            type_annotation: Some(annotation!(TypeAnnotationKind::Borrow {
                                mutable: false,
                                inner: Box::new(annotation!(TypeAnnotationKind::SelfType(
                                    Name::Resolved(ProtocolId::from(1).into(), "Self".into())
                                )))
                            })),
                            span: Span::ANY
                        }],
                        generics: vec![],
                        where_clause: None,
                        ret: Some(Box::new(annotation!(TypeAnnotationKind::Tuple(vec![]))))
                    },
                    receiver_mode: ReceiverMode::None
                })])
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
                where_clause: None,
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
                        },
                        where_clause: None
                    }),
                    any_decl!(DeclKind::MethodRequirement {
                        signature: FuncSignature {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            name: Name::Resolved(
                                Symbol::MethodRequirement(MethodRequirementId::from(1)),
                                "buzz".into()
                            ),
                            params: vec![Parameter {
                                id: NodeID::ANY,
                                name: Name::Resolved(
                                    ParamLocalId::from(1u32).into(),
                                    "self".into()
                                ),
                                name_span: Span::ANY,
                                type_annotation: Some(annotation!(TypeAnnotationKind::Borrow {
                                    mutable: false,
                                    inner: Box::new(annotation!(TypeAnnotationKind::SelfType(
                                        Name::Resolved(ProtocolId::from(1).into(), "Self".into())
                                    )))
                                })),
                                span: Span::ANY
                            }],
                            effects: Default::default(),
                            generics: vec![],
                            where_clause: None,
                            ret: Some(Box::new(annotation!(TypeAnnotationKind::Nominal {
                                name: Name::Resolved(
                                    Symbol::AssociatedType(AssociatedTypeId::from(1)),
                                    "T".into()
                                ),
                                name_span: Span::ANY,
                                generics: vec![]
                            })))
                        },
                        receiver_mode: ReceiverMode::None
                    }),
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
        // An or-pattern let desugars (in the parser) to
        // `let x = match … { .a(x) | .b(x) -> x }`; both alternatives
        // must bind the same symbol, and the outer binder carries the
        // name into the enclosing scope.
        let resolved = resolve(
            "
        let .a(x) | .b(x)
        ",
        );

        let decl = resolved.0.roots[0].as_decl().clone();
        let DeclKind::Let {
            lhs,
            rhs: Some(rhs),
            ..
        } = &decl.kind
        else {
            panic!("expected a desugared let, got {decl:?}");
        };
        assert!(
            matches!(&lhs.kind, PatternKind::Bind(name) if name.name_str() == "x"),
            "outer binder: {lhs:?}"
        );
        let ExprKind::Match(_, arms) = &rhs.kind else {
            panic!("expected a match rhs, got {rhs:?}");
        };
        assert_eq!(arms.len(), 1, "no else: a miss is the match machinery's");
        let PatternKind::Or(alternatives) = &arms[0].pattern.kind else {
            panic!("expected the or-pattern in the arm: {:?}", arms[0].pattern);
        };
        let binder_symbol = |pattern: &Pattern| match &pattern.kind {
            PatternKind::Variant { fields, .. } => match &fields[0].kind {
                PatternKind::Bind(name) => name.symbol().expect("resolved"),
                other => panic!("expected a bind, got {other:?}"),
            },
            other => panic!("expected a variant alternative, got {other:?}"),
        };
        assert_eq!(
            binder_symbol(&alternatives[0]),
            binder_symbol(&alternatives[1]),
            "both alternatives bind the same symbol"
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

    #[test]
    fn resolves_effect_decl() {
        let resolved = resolve(
            "
        effect 'fizz(x: Int) -> ()
        ",
        );

        let Decl {
            kind:
                DeclKind::Effect {
                    name: Name::Resolved(Symbol::Effect(..), ..),
                    params,
                    ..
                },
            ..
        } = &resolved.0.roots[0].as_decl()
        else {
            panic!("didn't get decl");
        };

        assert_eq!(
            *params,
            vec![any!(Parameter ,{
                name: Name::Resolved(ParamLocalId(1).into(), "x".into()),
                name_span: Span::ANY,
                type_annotation: Some(any!(TypeAnnotation, {
                    kind: TypeAnnotationKind::Nominal { name: Name::Resolved(Symbol::Int, "Int".into()), name_span: Span::ANY, generics: vec![] }
                })),
            })],
        );
    }

    #[test]
    fn resolves_handle_stmt() {
        let resolved = resolve(
            "
        effect 'fizz(x: Int) -> ()
        @handle 'fizz { x in
            continue x
        }
        ",
        );

        let Stmt {
            kind:
                StmtKind::Handling {
                    effect_name: Name::Resolved(Symbol::Effect(..), ..),
                    body: Block { args, body, .. },
                    ..
                },
            ..
        } = resolved.0.roots[1].as_stmt()
        else {
            panic!("didn't get decl: {:?}", resolved.0.roots[1])
        };

        assert_eq!(
            *args,
            vec![any!(Parameter, {
                name: Name::Resolved(Symbol::ParamLocal(ParamLocalId(2)), "x".into()),
                name_span: Span::ANY,
                type_annotation: None
            })]
        );

        assert_eq!(
            *body,
            vec![
                any_stmt!(StmtKind::Continue(Some(any_expr!(ExprKind::Variable(
                    Name::Resolved(Symbol::ParamLocal(ParamLocalId(2)), "x".into())
                )))))
                .into()
            ]
        )
    }

    #[test]
    fn resolves_effect_call() {
        let resolved = resolve(
            "
        effect 'fizz(x: Int) -> ()
        'fizz(123)
        ",
        );

        assert_eq!(
            resolved.0.roots[1],
            any_expr_stmt!(ExprKind::CallEffect {
                effect_name: Name::Resolved(Symbol::Effect(EffectId::from(1)), "fizz".into()),
                effect_name_span: Span::ANY,
                type_args: vec![],
                args: vec![any!(CallArg, {
                    label: Label::Positional(0),
                    label_span: Span::ANY,
                    value: any_expr!(ExprKind::LiteralInt("123".into()))
                })]
            })
        );
    }

    #[test]
    fn resolves_effect_annotation() {
        let resolved = resolve(
            "
        effect 'fizz(x: Int) -> ()
        func fizzes() 'fizz {}
        ",
        );

        assert_eq_diff!(
            *resolved.0.roots[1].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: any!(Pattern, {
                    kind: PatternKind::Bind(Name::Resolved(Symbol::Global(1.into()), "fizzes".into()))
                }),
                type_annotation: None,
                rhs: Some(any_expr!(ExprKind::Func(Func {
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::Global(1.into()), "fizzes".into()),
                    name_span: Span::ANY,
                    effects: EffectSet {
                        names: vec![Name::Resolved(Symbol::Effect(1.into()), "fizz".into())],
                        spans: vec![Span::ANY],
                        is_open: false
                    },
                    generics: vec![],
                    captures: vec![],
                    where_clause: None,
                    params: vec![],
                    body: any_block!(vec![]),
                    ret: None,
                    attributes: vec![]
                }))),
            })
        );
    }

    #[test]
    fn tracks_mutated_globals() {
        let resolved = resolve(
            "
            let foo = 123
            let bar = 456
            foo = 789
        ",
        );

        assert_eq!(
            resolved.1.mutated_symbols,
            indexset! { Symbol::Global(1.into()) }
        );
    }

    #[test]
    fn tracks_mutated_members() {
        let resolved = resolve(
            "
            let a = { b: 123 }
            a.b = 123
        ",
        );

        assert_eq!(
            resolved.1.mutated_symbols,
            indexset! { Symbol::Global(1.into()) }
        );
    }

    #[test]
    fn tracks_nested_mutated_members() {
        let resolved = resolve(
            "
            let a = { b: { c: 123 }}
            a.b.c = 456
        ",
        );

        assert_eq!(
            resolved.1.mutated_symbols,
            indexset! { Symbol::Global(1.into()) }
        );
    }

    /// Helper to resolve multiple files with isolated modules enabled
    fn resolve_multi(files: &[(&str, &str)]) -> (Vec<AST<NameResolved>>, ResolvedNames) {
        use crate::lexer::Lexer;
        use crate::parser::Parser;

        let modules = ModuleEnvironment::default();
        let mut name_resolver = NameResolver::new(Rc::new(modules), ModuleId::Current);
        let mut parseds = Vec::new();

        for (i, (path, code)) in files.iter().enumerate() {
            let lexer = Lexer::new(code);
            let parser = Parser::new(path.to_string(), FileID(i as u32), lexer);
            let ast = parser.parse().unwrap().0;
            parseds.push(ast);
        }

        crate::desugar::desugar(&mut parseds);
        name_resolver.resolve(parseds)
    }

    #[test]
    fn resolves_named_import() {
        let (asts, resolved) = resolve_multi(&[
            ("./utils.tlk", "public let helper = 42"),
            ("./main.tlk", "use { helper } from ./utils.tlk\nhelper"),
        ]);

        // Check that the main file resolved 'helper' to the symbol from utils
        assert!(
            resolved.diagnostics.is_empty(),
            "Expected no errors but got: {:?}",
            resolved.diagnostics
        );

        // The second file should have resolved the variable reference
        let main_ast = &asts[1];
        // Check the last statement (the 'helper' reference) resolved correctly
        if let crate::node::Node::Stmt(Stmt {
            kind:
                StmtKind::Expr(Expr {
                    kind: ExprKind::Variable(name),
                    ..
                }),
            ..
        }) = &main_ast.roots[1]
        {
            assert!(
                matches!(name, Name::Resolved(Symbol::Global(_), _)),
                "Expected resolved global, got {name:?}"
            );
        } else {
            panic!("Expected variable expression");
        }
    }

    #[test]
    fn resolves_import_all() {
        let (asts, resolved) = resolve_multi(&[
            ("./lib.tlk", "public let a = 1\npublic let b = 2"),
            ("./main.tlk", "use _ from ./lib.tlk\na\nb"),
        ]);

        assert!(
            resolved.diagnostics.is_empty(),
            "Expected no errors but got: {:?}",
            resolved.diagnostics
        );

        // Both 'a' and 'b' should be resolved in main
        let main_ast = &asts[1];
        assert!(main_ast.roots.len() >= 3, "Expected at least 3 roots");
    }

    #[test]
    fn import_nonexistent_symbol_errors() {
        let (_, resolved) = resolve_multi(&[
            ("./lib.tlk", "let existing = 1"),
            ("./main.tlk", "use { nonexistent } from ./lib.tlk"),
        ]);

        assert!(
            !resolved.diagnostics.is_empty(),
            "Expected error for nonexistent symbol"
        );
    }

    #[test]
    fn import_nonexistent_module_errors() {
        let (_, resolved) = resolve_multi(&[("./main.tlk", "use { a } from ./missing.tlk")]);

        assert!(
            !resolved.diagnostics.is_empty(),
            "Expected error for missing module"
        );
    }

    #[test]
    fn import_private_symbol_errors() {
        let (_, resolved) = resolve_multi(&[
            ("./lib.tlk", "let private_val = 42"),
            ("./main.tlk", "use { private_val } from ./lib.tlk"),
        ]);

        assert!(
            !resolved.diagnostics.is_empty(),
            "Expected error for importing private symbol"
        );
        // Verify it's specifically a SymbolNotPublic error
        let has_private_error = resolved.diagnostics.iter().any(|d| {
            matches!(
                d,
                AnyDiagnostic::NameResolution(Diagnostic {
                    kind: NameResolverError::SymbolNotPublic(_),
                    ..
                })
            )
        });
        assert!(has_private_error, "Expected SymbolNotPublic error");
    }

    #[test]
    fn duplicate_export_emits_error() {
        let code = r#"
public let a = 1
public let a = 2
"#;
        let (_, resolved) = resolve_err(code);
        let has_duplicate_error = resolved.diagnostics.iter().any(|d| {
            matches!(
                d,
                AnyDiagnostic::NameResolution(Diagnostic {
                    kind: NameResolverError::DuplicateExport(_),
                    ..
                })
            )
        });
        assert!(has_duplicate_error, "Expected DuplicateExport error");
    }

    #[test]
    fn core_prelude_imports_types_and_values() {
        use crate::compiling::core;

        // Get the compiled Core module
        let core_module = core::compile();
        let mut modules = ModuleEnvironment::default();
        modules.import_core(core_module);

        // Now resolve code that uses Core types without imports
        let code = "let x: Optional<Int> = Optional.some(42)";
        let parsed = parse(code);
        let mut name_resolver = NameResolver::new(Rc::new(modules), ModuleId::Current);
        let mut parseds = vec![parsed];
        crate::desugar::desugar(&mut parseds);
        let (_, resolved) = name_resolver.resolve(parseds);

        assert!(
            resolved.diagnostics.is_empty(),
            "Expected no errors using Core prelude, got: {:?}",
            resolved.diagnostics
        );
    }

    #[test]
    fn no_core_directive_skips_core_prelude() {
        use crate::compiling::core;

        let code = "let x = 1";

        // Verify that without skip_core_prelude, the file scope contains Core symbols
        {
            let core_module = core::compile();
            let mut modules = ModuleEnvironment::default();
            modules.import_core(core_module);
            let parsed = parse(code);
            let mut name_resolver = NameResolver::new(Rc::new(modules), ModuleId::Current);
            let mut parseds = vec![parsed];
            crate::desugar::desugar(&mut parseds);
            let (_, resolved) = name_resolver.resolve(parseds);
            let file_scope = resolved.scopes.get(&NodeID(FileID(0), 0)).unwrap();
            assert!(
                file_scope.types.contains_key("Optional"),
                "Without skip_core_prelude, file scope should contain Core types"
            );
        }

        // Now verify that with skip_core_prelude, the file scope does NOT contain Core symbols
        {
            let core_module = core::compile();
            let mut modules = ModuleEnvironment::default();
            modules.import_core(core_module);
            let mut parsed = parse(code);
            parsed.skip_core_prelude = true;
            let mut name_resolver = NameResolver::new(Rc::new(modules), ModuleId::Current);
            let mut parseds = vec![parsed];
            crate::desugar::desugar(&mut parseds);
            let (_, resolved) = name_resolver.resolve(parseds);
            let file_scope = resolved.scopes.get(&NodeID(FileID(0), 0)).unwrap();
            assert!(
                !file_scope.types.contains_key("Optional"),
                "With skip_core_prelude, file scope should NOT contain Core types"
            );
        }
    }
}
