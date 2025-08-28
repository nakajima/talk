#[cfg(test)]
pub mod tests {
    use rustc_hash::FxHashSet;

    use crate::{
        any_block, any_decl, any_expr, any_expr_stmt, any_stmt, assert_eq_diff,
        ast::AST,
        diagnostic::{AnyDiagnostic, Diagnostic},
        name::Name,
        name_resolution::{
            name_resolver::{NameResolved, NameResolver, NameResolverError},
            symbol::{DeclId, LocalId, Symbol},
        },
        node_id::NodeID,
        node_kinds::{
            decl::{Decl, DeclKind},
            expr::{Expr, ExprKind},
            parameter::Parameter,
            pattern::PatternKind,
            stmt::StmtKind,
        },
        parsing::parser_tests::tests::parse,
        span::Span,
    };

    macro_rules! param {
        ($id:expr, $name:expr) => {
            Parameter {
                id: NodeID::ANY,
                name: Name::Resolved($id.into(), $name.into()),
                type_annotation: None,
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
                Symbol::Local(LocalId(1)),
                "hello".into()
            )))
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
                path: "".into(),
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
            any_decl!(DeclKind::Func {
                name: Name::Resolved(Symbol::Value(DeclId(1)), "foo".into()),
                generics: vec![],
                params: vec![param!(LocalId(1), "x"), param!(LocalId(2), "y"),],
                body: any_block!(vec![
                    any_stmt!(StmtKind::Expr(variable!(LocalId(1), "x"))).into(),
                    any_stmt!(StmtKind::Expr(variable!(LocalId(2), "y"))).into(),
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

        assert_eq_diff!(
            *resolved.roots[0].as_decl(),
            any_decl!(DeclKind::Func {
                name: Name::Resolved(Symbol::Value(DeclId(1)), "odd".into()),
                generics: vec![],
                params: vec![],
                body: any_block!(vec![any_expr_stmt!(ExprKind::Call {
                    callee: Box::new(variable!(Symbol::Value(DeclId(2)), "even")),
                    type_args: vec![],
                    args: vec![]
                })]),
                ret: None,
                attributes: vec![]
            })
        );

        assert_eq_diff!(
            *resolved.roots[1].as_decl(),
            any_decl!(DeclKind::Func {
                name: Name::Resolved(Symbol::Value(DeclId(2)), "even".into()),
                generics: vec![],
                params: vec![],
                body: any_block!(vec![any_expr_stmt!(ExprKind::Call {
                    callee: Box::new(variable!(Symbol::Value(DeclId(1)), "odd")),
                    type_args: vec![],
                    args: vec![]
                })]),
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
                name: Name::Resolved(Symbol::Value(DeclId(1)), "foo".into()),
                generics: vec![],
                params: vec![param!(LocalId(1), "x"), param!(LocalId(2), "y")],
                body: any_block!(vec![
                    any_decl!(DeclKind::Func {
                        name: Name::Resolved(Symbol::Value(DeclId(2)), "bar".into()),
                        generics: vec![],
                        params: vec![param!(LocalId(3), "x")],
                        body: any_block!(vec![
                            any_stmt!(StmtKind::Expr(variable!(LocalId(3), "x"))).into(),
                            any_stmt!(StmtKind::Expr(variable!(LocalId(2), "y"))).into(),
                        ]),
                        ret: None,
                        attributes: vec![],
                    })
                    .into(),
                    any_stmt!(StmtKind::Expr(variable!(LocalId(1), "x"))).into(),
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

        assert_eq_diff!(
            *resolved.roots[1].as_decl(),
            Decl {
                id: NodeID(9),
                span: Span::ANY,
                kind: DeclKind::Func {
                    name: Name::Resolved(Symbol::Value(DeclId(1)), "counter".into()),
                    generics: vec![],
                    params: vec![param!(LocalId(2), "x")],
                    body: any_block!(vec![
                        any_stmt!(StmtKind::Expr(variable!(LocalId(2), "x"))).into(),
                        any_stmt!(StmtKind::Expr(variable!(LocalId(1), "count"))).into(),
                        any_stmt!(StmtKind::Expr(variable!(LocalId(1), "count"))).into(),
                    ]),
                    ret: None,
                    attributes: vec![]
                }
            }
        );

        let mut expected = FxHashSet::default();
        expected.insert(Symbol::Local(LocalId(1)));

        assert_eq!(
            resolved.phase.captures.get(&NodeID(9)),
            Some(&expected),
            "{:?}",
            resolved.phase.captures
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
