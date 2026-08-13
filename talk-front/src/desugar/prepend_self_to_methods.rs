use derive_visitor::{DriveMut, VisitorMut};

use crate::{
    ast::{AST, Parsed},
    id_generator::IDGenerator,
    name::Name,
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
            // A macro-generated method stamps its body names with the
            // expansion's context; the synthesized receiver must carry the
            // same context or template-written `self` references cannot
            // resolve to it.
            let context = func.name.syntax_context().cloned();
            func.params.insert(
                0,
                self.implicit_self_param(span, span, *receiver_mode, context),
            );
        }

        if let DeclKind::MethodRequirement {
            signature,
            receiver_mode,
        } = &mut decl.kind
        {
            signature.params.insert(
                0,
                self.implicit_self_param(signature.span, decl.span, *receiver_mode, None),
            );
        }

        if let DeclKind::Init { params, .. } = &mut decl.kind {
            params.insert(
                0,
                self.implicit_self_param(decl.span, decl.span, ReceiverMode::Consuming, None),
            );
        }

        // An init requirement takes no receiver; its implicit return is
        // `Self`, made explicit here so requirement lowering treats it
        // like any annotated signature.
        if let DeclKind::InitRequirement { signature } = &mut decl.kind {
            signature.ret = Some(Box::new(TypeAnnotation {
                id: NodeID(self.file_id, self.node_ids.next_id()),
                span: signature.span,
                kind: TypeAnnotationKind::SelfType("Self".into()),
            }));
        }
    }

    fn implicit_self_param(
        &mut self,
        name_span: Span,
        annotation_span: Span,
        receiver_mode: ReceiverMode,
        context: Option<crate::hygiene::SyntaxContext>,
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
            label: None,
            label_span: None,
            mode: None,
            mode_span: None,
            id: NodeID(self.file_id, self.node_ids.next_id()),
            name: match context {
                Some(context) => Name::Syntax("self".into(), context),
                None => "self".into(),
            },
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

