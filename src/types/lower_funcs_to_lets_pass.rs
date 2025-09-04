use crate::ast::Parsed;
use crate::{ast::AST, node_kinds::decl::Decl};
use derive_visitor::DriveMut;
use derive_visitor::VisitorMut;

#[derive(VisitorMut)]
#[visitor(Decl(enter))]
pub struct LowerFuncsToLets;

impl LowerFuncsToLets {
    pub fn run(ast: &mut AST<Parsed>) {
        let mut pass = LowerFuncsToLets;
        for root in ast.roots.iter_mut() {
            root.drive_mut(&mut pass);
        }
    }

    fn enter_decl(&mut self, decl: &mut Decl) {
        use crate::node_kinds::{
            decl::DeclKind,
            expr::{Expr, ExprKind},
            func::Func,
        };

        if let DeclKind::Func(Func {
            id,
            name,
            generics,
            params,
            body,
            ret,
            attributes,
        }) = decl.kind.clone()
        {
            // Build an Expr::Func from the decl’s parts (reusing nodes)
            let func_expr = Expr {
                id, // ok to reuse: it’s now the expr id
                span: decl.span,
                kind: ExprKind::Func(Func {
                    id,
                    name: name.clone(),
                    generics,
                    params,
                    body,
                    ret,
                    attributes,
                }),
            };

            // Replace decl with: let <name> = <func_expr>;
            decl.kind = DeclKind::Let {
                lhs: crate::node_kinds::pattern::Pattern {
                    id,
                    span: decl.span,
                    kind: crate::node_kinds::pattern::PatternKind::Bind(name.clone()),
                },
                type_annotation: None,
                value: Some(func_expr),
            };
        }
    }
}

#[cfg(test)]
pub mod tests {
    use derive_visitor::DriveMut;

    use crate::{
        any_block, any_decl, any_expr,
        name::Name,
        node_id::NodeID,
        node_kinds::{
            decl::DeclKind,
            expr::ExprKind,
            func::Func,
            pattern::{Pattern, PatternKind},
        },
        parser_tests::tests::parse,
        span::Span,
        types::lower_funcs_to_lets_pass::LowerFuncsToLets,
    };

    #[test]
    fn lowers_func_decl() {
        let mut parsed = parse(
            "
        func fizz() {}
        ",
        );

        let mut lowerer = LowerFuncsToLets {};

        for root in parsed.roots.iter_mut() {
            root.drive_mut(&mut lowerer)
        }

        assert_eq!(
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: Pattern {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: PatternKind::Bind(Name::Raw("fizz".into()))
                },
                type_annotation: None,
                value: Some(any_expr!(ExprKind::Func(Func {
                    id: NodeID::ANY,
                    name: Name::Raw("fizz".into()),
                    generics: vec![],
                    params: vec![],
                    body: any_block!(vec![]),
                    ret: None,
                    attributes: vec![]
                })))
            })
        )
    }
}
