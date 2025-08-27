#[cfg(test)]
mod tests {
    use crate::{
        any_expr_stmt,
        ast::AST,
        name::Name,
        node_kinds::expr::{Expr, ExprKind},
        parsing::parser_tests::tests::parse,
        types::{name_resolver::NameResolver, symbol::Symbol},
    };

    fn resolve(code: &'static str) -> AST {
        let res = resolve_err(code);
        assert!(
            res.diagnostics.is_empty(),
            "diagnostics not empty: {:?}",
            res.diagnostics
        );
        res
    }

    fn resolve_err(code: &'static str) -> AST {
        let parsed = parse(code);
        NameResolver::resolve(parsed)
    }

    #[test]
    fn resolves_simple_variable_to_depth_0() {
        let tree = resolve("let hello = 1; hello");
        assert_eq!(
            *tree.roots[1].as_stmt(),
            any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                Symbol::Local(1u32.into()),
                "hello".into()
            )))
        );
    }

    #[test]
    fn block_scoping_prevents_let_leak() {
        let resolved = resolve_err("{ let x = 123 }; x");
        assert_eq!(1, resolved.diagnostics.len());
    }
}
