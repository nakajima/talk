use derive_visitor::{DriveMut, VisitorMut};

use crate::{
    ast::{AST, Parsed},
    id_generator::IDGenerator,
    node_id::{FileID, NodeID},
    node_kinds::{
        decl::{Decl, DeclKind, ReceiverMode},
        parameter::Parameter,
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
    span::Span,
};

#[derive(VisitorMut)]
#[visitor(Decl(enter))]
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

    fn enter_decl(&mut self, decl: &mut Decl) {
        if let DeclKind::Method {
            func,
            is_static: false,
            receiver_mode,
        } = &mut decl.kind
        {
            let span = decl.span;
            func.params
                .insert(0, self.implicit_self_param(span, span, *receiver_mode));
        }

        if let DeclKind::MethodRequirement {
            signature,
            receiver_mode,
        } = &mut decl.kind
        {
            signature.params.insert(
                0,
                self.implicit_self_param(signature.span, decl.span, *receiver_mode),
            );
        }

        if let DeclKind::Init { params, .. } = &mut decl.kind {
            params.insert(
                0,
                self.implicit_self_param(decl.span, decl.span, ReceiverMode::Consuming),
            );
        }
    }

    fn implicit_self_param(
        &mut self,
        name_span: Span,
        annotation_span: Span,
        receiver_mode: ReceiverMode,
    ) -> Parameter {
        let self_ty = TypeAnnotation {
            id: NodeID(self.file_id, self.node_ids.next_id()),
            span: annotation_span,
            kind: TypeAnnotationKind::SelfType("Self".into()),
        };
        let kind = match receiver_mode {
            ReceiverMode::None => TypeAnnotationKind::Borrow {
                mutable: false,
                inner: Box::new(self_ty),
            },
            ReceiverMode::Ref => TypeAnnotationKind::Borrow {
                mutable: true,
                inner: Box::new(self_ty),
            },
            ReceiverMode::Consuming => self_ty.kind,
        };
        Parameter {
            id: NodeID(self.file_id, self.node_ids.next_id()),
            name: "self".into(),
            name_span,
            type_annotation: Some(TypeAnnotation {
                id: NodeID(self.file_id, self.node_ids.next_id()),
                span: annotation_span,
                kind,
            }),
            span: annotation_span,
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
            decl::{DeclKind, ReceiverMode},
            func::Func,
            parameter::Parameter,
            type_annotation::TypeAnnotationKind,
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
            any_decl!(DeclKind::Struct { linear: false,
                name: "Person".into(),
                name_span: Span::ANY,
                generics: vec![],
                where_clause: None,
                body: any_body!(vec![any_decl!(DeclKind::Method {
                    func: Box::new(Func {
                        id: NodeID::ANY,
                        name: "fizz".into(),
                        name_span: Span::ANY,
                        generics: vec![],
                        captures: vec![],
                        where_clause: None,
                        effects: Default::default(),
                        params: vec![
                            Parameter {
                                id: NodeID::ANY,
                                span: Span::ANY,
                                name: "self".into(),
                                name_span: Span::ANY,
                                type_annotation: Some(annotation!(TypeAnnotationKind::Borrow {
                                    mutable: false,
                                    inner: Box::new(annotation!(TypeAnnotationKind::SelfType(
                                        "Self".into()
                                    )))
                                }))
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
                    is_static: false,
                    receiver_mode: ReceiverMode::None
                })])
            })
        )
    }

    #[test]
    fn prepends_mutable_self_to_mut_methods() {
        let mut parsed = parse(
            "
        struct Person {
          mut func fizz(x) {
          }
        }
        ",
        );

        PrependSelfToMethods::run(&mut parsed);

        let DeclKind::Struct { body, .. } = &parsed.roots[0].as_decl().kind else {
            panic!("expected struct");
        };
        let DeclKind::Method { func, .. } = &body.decls[0].kind else {
            panic!("expected method");
        };
        assert_eq!(
            func.params[0].type_annotation.clone().unwrap().kind,
            TypeAnnotationKind::Borrow {
                mutable: true,
                inner: Box::new(annotation!(TypeAnnotationKind::SelfType("Self".into())))
            }
        );
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
            any_decl!(DeclKind::Struct { linear: false,
                name: "Person".into(),
                name_span: Span::ANY,
                generics: vec![],
                where_clause: None,
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
