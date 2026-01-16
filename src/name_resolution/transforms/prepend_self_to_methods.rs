use derive_visitor::{DriveMut, VisitorMut};

use crate::{
    ast::{AST, Parsed},
    id_generator::IDGenerator,
    label::Label,
    name::Name,
    node_id::{FileID, NodeID},
    node_kinds::{
        call_arg::CallArg,
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        parameter::Parameter,
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
    span::Span,
    types::constraints::member::Member,
};

#[derive(VisitorMut)]
#[visitor(Decl(enter), Expr(enter))]
pub struct PrependSelfToMethods {
    file_id: FileID,
    node_ids: IDGenerator,
}

impl PrependSelfToMethods {
    pub fn run(ast: &mut AST<Parsed>) {
        let node_ids = std::mem::take(&mut ast.node_ids);
        let mut pass = PrependSelfToMethods {
            file_id: ast.file_id,
            node_ids,
        };
        for root in &mut ast.roots {
            root.drive_mut(&mut pass);
        }
        _ = std::mem::replace(&mut ast.node_ids, pass.node_ids);
    }

    fn enter_expr(&mut self, expr: &mut Expr) {
        // if let ExprKind::Call {
        //     callee:
        //         box Expr {
        //             kind: ExprKind::Member(Some(receiver), ..),
        //             ..
        //         },
        //     args,
        //     ..
        // } = &mut expr.kind
        //     && let box Expr {
        //         kind: ExprKind::Variable(name),
        //         ..
        //     } = receiver
        //     && *name == Name::Raw("self".to_string())
        // {
        //     args.insert(
        //         0,
        //         CallArg {
        //             id: receiver.id,
        //             value: *receiver.clone(),
        //             label: Label::Positional(0),
        //             label_span: Span::SYNTHESIZED,
        //             span: receiver.span,
        //         },
        //     );

        //     *receiver = Expr {
        //         id: NodeID(self.file_id, self.node_ids.next_id()),
        //         span: Span::SYNTHESIZED,
        //         kind: ExprKind::Variable(Name::Raw("Self".into())),
        //     }
        //     .into();
        // }
    }

    fn enter_decl(&mut self, decl: &mut Decl) {
        if let DeclKind::Method {
            func,
            is_static: false,
        } = &mut decl.kind
        {
            func.params.insert(
                0,
                Parameter {
                    id: NodeID(self.file_id, self.node_ids.next_id()),
                    name: "self".into(),
                    name_span: Span::ANY,
                    type_annotation: Some(TypeAnnotation {
                        id: NodeID(self.file_id, self.node_ids.next_id()),
                        span: decl.span,
                        kind: TypeAnnotationKind::SelfType("Self".into()),
                    }),
                    // type_annotation: None,
                    span: decl.span,
                },
            );
        }

        if let DeclKind::MethodRequirement(signature) = &mut decl.kind {
            signature.params.insert(
                0,
                Parameter {
                    id: NodeID(self.file_id, self.node_ids.next_id()),
                    name: "self".into(),
                    name_span: signature.span,
                    type_annotation: Some(TypeAnnotation {
                        id: NodeID(self.file_id, self.node_ids.next_id()),
                        span: decl.span,
                        kind: TypeAnnotationKind::SelfType("Self".into()),
                    }),
                    // type_annotation: None,
                    span: decl.span,
                },
            );
        }

        if let DeclKind::Init { params, .. } = &mut decl.kind {
            params.insert(
                0,
                Parameter {
                    id: NodeID(self.file_id, self.node_ids.next_id()),
                    name: "self".into(),
                    name_span: decl.span,
                    type_annotation: Some(TypeAnnotation {
                        id: NodeID(self.file_id, self.node_ids.next_id()),
                        span: decl.span,
                        kind: TypeAnnotationKind::SelfType("Self".into()),
                    }),
                    // type_annotation: None,
                    span: decl.span,
                },
            );
        }
    }
}

#[cfg(test)]
pub mod tests {
    use crate::{
        annotation, any_block, any_body, any_decl, assert_eq_diff,
        name_resolution::transforms::prepend_self_to_methods::PrependSelfToMethods,
        node_id::NodeID,
        node_kinds::{
            decl::DeclKind, func::Func, parameter::Parameter, type_annotation::TypeAnnotationKind,
        },
        parser_tests::tests::parse,
        span::Span,
    };

    #[test]
    fn prepends_self_to_methods() {
        let mut parsed = parse(
            "
        struct Person {
          func fizz(x) {
          }
        }
        ",
        );

        PrependSelfToMethods::run(&mut parsed);

        assert_eq_diff!(
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                name: "Person".into(),
                name_span: Span::ANY,
                generics: vec![],
                body: any_body!(vec![any_decl!(DeclKind::Method {
                    func: Box::new(Func {
                        id: NodeID::ANY,
                        name: "fizz".into(),
                        name_span: Span::ANY,
                        generics: vec![],
                        effects: Default::default(),
                        params: vec![
                            Parameter {
                                id: NodeID::ANY,
                                span: Span::ANY,
                                name: "self".into(),
                                name_span: Span::ANY,
                                type_annotation: Some(annotation!(TypeAnnotationKind::SelfType(
                                    "Self".into()
                                )))
                            },
                            Parameter {
                                id: NodeID::ANY,
                                span: Span::ANY,
                                name: "x".into(),
                                name_span: Span::ANY,
                                type_annotation: None
                            }
                        ],
                        body: any_block!(vec![]),
                        ret: None,
                        attributes: vec![]
                    }),
                    is_static: false
                })])
            })
        )
    }

    #[test]
    fn prepends_self_to_inits() {
        let mut parsed = parse(
            "
        struct Person {
            init() {}
        }
        ",
        );

        PrependSelfToMethods::run(&mut parsed);

        assert_eq_diff!(
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                name: "Person".into(),
                name_span: Span::ANY,
                generics: vec![],
                body: any_body!(vec![any_decl!(DeclKind::Init {
                    name: "init".into(),
                    params: vec![Parameter {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        name: "self".into(),
                        name_span: Span::ANY,
                        type_annotation: Some(annotation!(TypeAnnotationKind::SelfType(
                            "Self".into()
                        )))
                    },],
                    body: any_block!(vec![]),
                })])
            })
        )
    }
}
