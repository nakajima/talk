#[cfg(test)]
pub mod tests {
    use crate::{
        any_block, any_decl, any_expr, any_expr_stmt, assert_eq_diff,
        ast::AST,
        name::Name,
        name_resolution::{
            name_resolver::{NameResolved, NameResolver},
            symbol::{DeclId, LocalId, Symbol},
        },
        node_id::NodeID,
        node_kinds::{
            decl::DeclKind,
            expr::{Expr, ExprKind},
            parameter::Parameter,
            pattern::PatternKind,
        },
        parsing::parser_tests::tests::parse,
        span::Span,
    };

    macro_rules! param {
        ($id:expr, $name:expr) => {
            Parameter {
                id: NodeID::ANY,
                name: Name::Resolved(Symbol::LocalId($id), $name.into()),
                type_annotation: None,
                span: Span::ANY,
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

    fn resolve(code: &'static str) -> AST<NameResolved> {
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
        NameResolver::resolve(parsed)
    }

    #[test]
    fn resolves_simple_variable() {
        let tree = resolve("let hello = 1; hello");
        assert_eq!(
            *tree.roots[1].as_stmt(),
            any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                Symbol::LocalId(LocalId(1)),
                "hello".into()
            )))
        );
    }

    #[test]
    fn block_scoping_prevents_let_leak() {
        let resolved = resolve_err("{ let x = 123 }; x");
        assert_eq!(1, resolved.diagnostics.len());
    }

    #[test]
    fn resolves_func_params() {
        let tree = resolve("func foo(x, y) { x ; y }");

        assert_eq_diff!(
            *tree.roots[0].as_decl(),
            any_decl!(DeclKind::Func {
                name: Name::Resolved(Symbol::DeclId(DeclId(1)), "foo".into()),
                generics: vec![],
                params: vec![param!(LocalId(1), "x"), param!(LocalId(2), "y"),],
                body: any_block!(vec![
                    any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                        Symbol::LocalId(LocalId(1)),
                        "x".into()
                    ))),
                    any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                        Symbol::LocalId(LocalId(2)),
                        "y".into()
                    ))),
                ]),
                ret: None,
                attributes: vec![],
            }),
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

        assert_eq!(
            *resolved.roots[0].as_decl(),
            any_decl!(DeclKind::Func {
                name: Name::Resolved(DeclId(1).into(), "odd".into()),
                generics: vec![],
                params: vec![],
                body: any_block!(vec![
                    any_expr!(ExprKind::Call {
                        callee: Box::new(any_expr!(ExprKind::Variable(Name::Resolved(
                            LocalId(2).into(),
                            "even".into()
                        )))),
                        type_args: vec![],
                        args: vec![]
                    })
                    .into()
                ]),
                ret: None,
                attributes: vec![]
            })
        );

        assert_eq!(
            *resolved.roots[0].as_decl(),
            any_decl!(DeclKind::Func {
                name: Name::Resolved(DeclId(2).into(), "even".into()),
                generics: vec![],
                params: vec![],
                body: any_block!(vec![
                    any_expr!(ExprKind::Call {
                        callee: Box::new(any_expr!(ExprKind::Variable(Name::Resolved(
                            LocalId(1).into(),
                            "odd".into()
                        )))),
                        type_args: vec![],
                        args: vec![]
                    })
                    .into()
                ]),
                ret: None,
                attributes: vec![]
            })
        )
    }

    #[test]
    fn resolves_nested_shadowing_correctly() {
        let tree = resolve("func foo(x, y) { func bar(x) { x \n y }\nx }\n");

        assert_eq_diff!(
            *tree.roots[0].as_decl(),
            any_decl!(DeclKind::Func {
                name: Name::Resolved(Symbol::DeclId(DeclId(1)), "foo".into()),
                generics: vec![],
                params: vec![param!(LocalId(1), "x"), param!(LocalId(2), "y")],
                body: any_block!(vec![
                    any_decl!(DeclKind::Func {
                        name: Name::Resolved(Symbol::DeclId(DeclId(2)), "bar".into()),
                        generics: vec![],
                        params: vec![param!(LocalId(3), "x")],
                        body: any_block!(vec![
                            any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                                Symbol::LocalId(LocalId(3)),
                                "x".into()
                            ))),
                            any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                                Symbol::LocalId(LocalId(2)),
                                "y".into()
                            )))
                        ]),
                        ret: None,
                        attributes: vec![],
                    })
                    .into(),
                    any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                        Symbol::LocalId(LocalId(1)),
                        "x".into()
                    ))),
                ]),
                ret: None,
                attributes: vec![],
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
                    LocalId(1).into(),
                    "count".into()
                ))),
                type_annotation: None,
                value: Some(any_expr!(ExprKind::LiteralInt("0".into())))
            })
        );

        assert_eq!(
            *resolved.roots[1].as_decl(),
            any_decl!(DeclKind::Func {
                name: Name::Resolved(DeclId(1).into(), "counter".into()),
                generics: vec![],
                params: vec![param!(LocalId(2), "x")],
                body: any_block!(vec![
                    any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                        Symbol::LocalId(LocalId(2)),
                        "x".into()
                    ))),
                    any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                        Symbol::LocalId(LocalId(1)),
                        "count".into()
                    ))),
                    any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                        Symbol::LocalId(LocalId(1)),
                        "count".into()
                    )))
                ]),
                ret: None,
                attributes: vec![]
            })
        );

        assert_eq!(
            resolved.phase.captures.get(&DeclId(1).into()),
            Some(&[LocalId(1)].into())
        );
    }

    #[test]
    fn resolves_struct() {
        let resolved = resolve("struct Person {}");
        assert_eq!(
            *resolved.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                name: Name::Resolved(DeclId(1).into(), "Person".into()),
                generics: vec![],
                conformances: vec![],
                body: any_block!(vec![])
            })
        )
    }
}
