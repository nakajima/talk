#[cfg(test)]
pub mod tests {
    use indexmap::indexset;

    use crate::{
        assert_eq_diff,
        ast::{AST, NameResolved},
        compiling::driver::{Driver, DriverConfig, Source},
        diagnostic::{AnyDiagnostic, Diagnostic, Severity},
        label::Label,
        name::Name,
        name_resolution::name_resolver::NameResolverError,
        name_resolution::symbol::{EffectId, GlobalId, ParamLocalId, Symbol},
        node::Node,
        node_id::NodeID,
        node_kinds::{
            block::Block,
            decl::DeclKind,
            expr::ExprKind,
            pattern::PatternKind,
            stmt::StmtKind,
        },
        types::{
            infer_row::RowParamId,
            row::Row,
            scheme::{ForAll, Scheme},
            ty::Ty,
            type_error::TypeError,
            type_session::TypeEntry,
            types_tests::tests::{typecheck, typecheck_err},
        },
    };

    #[test]
    fn infers_func_with_indirect_effect() {
        let (_ast, types) = typecheck(
            "
          effect 'fizz() -> Int

          func fizzes() {
            'fizz()
          }

          func callsFizzes() {
              fizzes()
          }
        ",
        );

        assert_eq_diff!(
            types
                .get_symbol(&Symbol::Global(GlobalId::from(2)))
                .cloned(),
            Some(TypeEntry::Poly(Scheme {
                foralls: indexset! {ForAll::Row(1.into()),ForAll::Row(2.into())},
                predicates: vec![],
                ty: Ty::Func(
                    Ty::Void.into(),
                    Ty::Int.into(),
                    Row::Extend {
                        row: Row::Param(RowParamId(2)).into(),
                        label: Label::_Symbol(EffectId::from(1).into()),
                        ty: Ty::Func(Ty::Void.into(), Ty::Int.into(), Row::Empty.into())
                    }
                    .into()
                )
            }))
        )
    }

    #[test]
    fn infers_func_with_effect() {
        let (_ast, types) = typecheck(
            "
          effect 'fizz() -> Int

          func fizzes() {
            'fizz()
          }
        ",
        );

        assert_eq!(
            types
                .get_symbol(&Symbol::Global(GlobalId::from(1)))
                .cloned(),
            Some(TypeEntry::Poly(Scheme {
                foralls: indexset! {ForAll::Row(1.into())},
                predicates: vec![],
                ty: Ty::Func(
                    Ty::Void.into(),
                    Ty::Int.into(),
                    Row::Extend {
                        row: Row::Param(RowParamId(1)).into(),
                        label: Label::_Symbol(EffectId::from(1).into()),
                        ty: Ty::Func(Ty::Void.into(), Ty::Int.into(), Row::Empty.into())
                    }
                    .into()
                )
            }))
        )
    }

    #[test]
    fn checks_pure_func_has_no_effects() {
        let (_ast, _types, diagnostics) = typecheck_err(
            "
          effect 'fizz() -> Int

          func fizzes() '[] {
            'fizz()
          }
        ",
        );

        assert_eq!(1, diagnostics.len(), "{diagnostics:?}");
    }

    #[test]
    fn checks_pure_func_has_no_indirect_effects() {
        let (_ast, _types, diagnostics) = typecheck_err(
            "
          effect 'fizz() -> Int

          func callsFizzes() {
              'fizz()
          }

          func fizzes() '[] {
              callsFizzes()
          }
        ",
        );

        assert_eq!(1, diagnostics.len(), "{diagnostics:?}");
    }

    #[test]
    fn types_handlers() {
        let (_ast, types) = typecheck(
            "
            effect 'fizz(x: Int, y: Bool) -> Int

            let handler = @handle 'fizz { a, b in
                0
            }
            ",
        );

        assert_eq!(
            Ty::Int,
            *types
                .get_symbol(&ParamLocalId(3).into())
                .unwrap()
                .as_mono_ty()
        );

        assert_eq!(
            Ty::Bool,
            *types
                .get_symbol(&ParamLocalId(4).into())
                .unwrap()
                .as_mono_ty()
        );
    }

    #[test]
    fn checks_handler_return() {
        let (.., diagnostics) = typecheck_err(
            "
            effect 'fizz(x: Int, y: Bool) -> Bool

            let handler = @handle 'fizz { a, b in
                0
            }
            ",
        );

        assert_eq!(diagnostics.len(), 1);
    }

    #[test]
    fn checks_handler_args() {
        let (.., diagnostics) = typecheck_err(
            "
            effect 'fizz(x: Int, y: Bool) -> Bool

            let handler = @handle 'fizz { a in
                true
            }
            ",
        );

        assert_eq!(diagnostics.len(), 1);
    }

    #[test]
    fn continue_in_handler_uses_effect_return_type() {
        let (_ast, _types) = typecheck(
            "
            effect 'fizz() -> Int

            let handler = @handle 'fizz {
                continue 123
            }
            ",
        );
    }

    #[test]
    fn continue_in_handler_checks_return_type() {
        let (.., diagnostics) = typecheck_err(
            "
            effect 'fizz() -> Int

            let handler = @handle 'fizz {
                continue true
            }
            ",
        );

        assert!(
            diagnostics.iter().any(|diag| matches!(
                diag,
                AnyDiagnostic::Typing(Diagnostic {
                    kind: TypeError::InvalidUnification(..),
                    ..
                })
            )),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn continue_with_value_outside_handler_errors() {
        let (.., diagnostics) = typecheck_err("continue 1");

        assert!(
            diagnostics.iter().any(|diag| matches!(
                diag,
                AnyDiagnostic::Typing(Diagnostic {
                    kind: TypeError::ContinueOutsideHandler,
                    ..
                })
            )),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn handler_must_be_bound() {
        let (.., diagnostics) = typecheck_err(
            "
            effect 'fizz() -> Int

            @handle 'fizz {
                continue 0
            }
            ",
        );

        assert!(
            diagnostics.iter().any(|diag| matches!(
                diag,
                AnyDiagnostic::Typing(Diagnostic {
                    kind: TypeError::HandlerMustBeBound,
                    ..
                })
            )),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn nested_handlers_warn_and_use_nearest() {
        let driver = Driver::new_bare(
            vec![Source::from(
                "
                effect 'fizz() -> Int

                let outer = @handle 'fizz { continue 0 }

                func test() {
                    let inner = @handle 'fizz { continue 1 }
                    'fizz()
                }

                'fizz()
                ",
            )],
            DriverConfig::new("TestDriver"),
        )
        .parse()
        .unwrap()
        .resolve_names()
        .unwrap();

        let ast = driver
            .phase
            .asts
            .values()
            .next()
            .expect("missing ast");
        let resolved = &driver.phase.resolved_names;

        let outer_handler = find_let_symbol_in_roots(ast, "outer").expect("outer handler missing");
        let test_body = find_func_block(ast, "test").expect("test func missing");
        let inner_handler =
            find_let_symbol_in_block(test_body, "inner").expect("inner handler missing");

        let inner_call = find_call_effect_in_block(test_body).expect("inner call missing");
        let outer_call = find_call_effect_in_roots(ast).expect("outer call missing");

        assert_eq!(
            resolved.effect_handlers.get(&inner_call).copied(),
            Some(inner_handler)
        );
        assert_eq!(
            resolved.effect_handlers.get(&outer_call).copied(),
            Some(outer_handler)
        );

        assert!(
            driver.phase.diagnostics.iter().any(|diag| matches!(
                diag,
                AnyDiagnostic::NameResolution(Diagnostic {
                    severity: Severity::Warn,
                    kind: NameResolverError::ShadowedEffectHandler(_),
                    ..
                })
            )),
            "{:?}",
            driver.phase.diagnostics
        );
    }

    fn find_let_symbol_in_roots(ast: &AST<NameResolved>, name: &str) -> Option<Symbol> {
        for root in &ast.roots {
            if let Node::Decl(decl) = root
                && let DeclKind::Let { lhs, .. } = &decl.kind
                && let PatternKind::Bind(Name::Resolved(sym, ident)) = &lhs.kind
                && ident == name
            {
                return Some(*sym);
            }
        }

        None
    }

    fn find_func_block<'a>(ast: &'a AST<NameResolved>, name: &str) -> Option<&'a Block> {
        for root in &ast.roots {
            if let Node::Decl(decl) = root
                && let DeclKind::Let { lhs, rhs, .. } = &decl.kind
                && let PatternKind::Bind(Name::Resolved(_, ident)) = &lhs.kind
                && ident == name
                && let Some(expr) = rhs
                && let ExprKind::Func(func) = &expr.kind
            {
                return Some(&func.body);
            }
        }

        None
    }

    fn find_let_symbol_in_block(block: &Block, name: &str) -> Option<Symbol> {
        for node in &block.body {
            if let Node::Decl(decl) = node
                && let DeclKind::Let { lhs, .. } = &decl.kind
                && let PatternKind::Bind(Name::Resolved(sym, ident)) = &lhs.kind
                && ident == name
            {
                return Some(*sym);
            }
        }

        None
    }

    fn find_call_effect_in_roots(ast: &AST<NameResolved>) -> Option<NodeID> {
        for root in &ast.roots {
            match root {
                Node::Stmt(stmt) => {
                    if let StmtKind::Expr(expr) = &stmt.kind
                        && matches!(expr.kind, ExprKind::CallEffect { .. })
                    {
                        return Some(expr.id);
                    }
                }
                Node::Expr(expr) => {
                    if matches!(expr.kind, ExprKind::CallEffect { .. }) {
                        return Some(expr.id);
                    }
                }
                _ => {}
            }
        }

        None
    }

    fn find_call_effect_in_block(block: &Block) -> Option<NodeID> {
        for node in &block.body {
            match node {
                Node::Stmt(stmt) => {
                    if let StmtKind::Expr(expr) = &stmt.kind
                        && matches!(expr.kind, ExprKind::CallEffect { .. })
                    {
                        return Some(expr.id);
                    }
                }
                Node::Expr(expr) => {
                    if matches!(expr.kind, ExprKind::CallEffect { .. }) {
                        return Some(expr.id);
                    }
                }
                _ => {}
            }
        }

        None
    }
}
