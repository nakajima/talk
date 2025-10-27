use crate::ast::Parsed;
use crate::id_generator::IDGenerator;
use crate::node_id::{FileID, NodeID};
use crate::node_kinds::pattern::{Pattern, PatternKind};
use crate::{ast::AST, node_kinds::decl::Decl};
use derive_visitor::DriveMut;
use derive_visitor::VisitorMut;

#[derive(VisitorMut)]
#[visitor(Decl(enter))]
pub struct LowerFuncsToLets {
    node_ids: IDGenerator,
    file_id: FileID,
}

impl LowerFuncsToLets {
    pub fn run(ast: &mut AST<Parsed>) {
        // Take the id generator
        let ids = std::mem::take(&mut ast.node_ids);
        let mut pass = LowerFuncsToLets {
            file_id: ast.file_id,
            node_ids: ids,
        };
        for root in ast.roots.iter_mut() {
            root.drive_mut(&mut pass);
        }

        // Give the id generator back
        _ = std::mem::replace(&mut ast.node_ids, pass.node_ids);
    }

    fn enter_decl(&mut self, decl: &mut Decl) {
        use crate::node_kinds::{
            decl::DeclKind,
            expr::{Expr, ExprKind},
            func::Func,
        };

        if let DeclKind::Let {
            lhs:
                Pattern {
                    kind: PatternKind::Bind(name),
                    ..
                },
            rhs:
                Some(Expr {
                    kind: ExprKind::Func(func),
                    ..
                }),
            ..
        } = &mut decl.kind
        {
            // If we get `let foo = func bar() {}`, just rename the func to foo
            // because who has time for this nonsense anyway.
            // TODO: Maybe handle this during name resolution instead?
            func.name = name.clone();
            return;
        }

        if let DeclKind::Func(Func {
            id,
            name,
            name_span,
            generics,
            params,
            body,
            ret,
            attributes,
        }) = decl.kind.clone()
        {
            // Build an Expr::Func from the decl’s parts (reusing nodes)
            let func_expr = Expr {
                id: NodeID(self.file_id, self.node_ids.next_id()),
                span: decl.span,
                kind: ExprKind::Func(Func {
                    id,
                    name: name.clone(),
                    name_span,
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
                    id: NodeID(self.file_id, self.node_ids.next_id()),
                    span: decl.span,
                    kind: crate::node_kinds::pattern::PatternKind::Bind(name.clone()),
                },
                type_annotation: None,
                rhs: Some(func_expr),
            };
        }
    }
}

#[cfg(test)]
pub mod tests {
    use crate::{
        any_block, any_body, any_decl, any_expr, assert_eq_diff,
        name::Name,
        name_resolution::transforms::lower_funcs_to_lets::LowerFuncsToLets,
        node_id::{FileID, NodeID},
        node_kinds::{
            decl::DeclKind,
            expr::ExprKind,
            func::Func,
            pattern::{Pattern, PatternKind},
        },
        parser_tests::tests::parse,
        span::Span,
    };

    #[test]
    fn lowers_func_decl() {
        let mut parsed = parse(
            "
        func fizz() {}
        ",
        );

        LowerFuncsToLets::run(&mut parsed);

        assert_eq_diff!(
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: Pattern {
                    id: NodeID(FileID(0), 5),
                    span: Span::ANY,
                    kind: PatternKind::Bind(Name::Raw("fizz".into()))
                },
                type_annotation: None,
                rhs: Some(any_expr!(ExprKind::Func(Func {
                    id: NodeID(FileID(0), 2),
                    name: Name::Raw("fizz".into()),
                    name_span: Span::ANY,
                    generics: vec![],
                    params: vec![],
                    body: any_block!(vec![]),
                    ret: None,
                    attributes: vec![]
                })))
            })
        )
    }

    #[test]
    fn ignores_methods() {
        let mut parsed = parse(
            "
            struct Person { func fizz() {} }
        ",
        );

        LowerFuncsToLets::run(&mut parsed);

        assert_eq_diff!(
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                name: "Person".into(),
                name_span: Span::ANY,
                generics: vec![],
                conformances: vec![],
                body: any_body!(vec![
                    any_decl!(DeclKind::Method {
                        func: Box::new(Func {
                            id: NodeID::ANY,
                            name: "fizz".into(),
                            name_span: Span::ANY,
                            generics: vec![],
                            params: vec![],
                            body: any_block!(vec![]),
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
}
