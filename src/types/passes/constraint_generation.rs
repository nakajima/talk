use crate::{
    ast::AST,
    name_resolution::name_resolver::NameResolved,
    node::Node,
    node_kinds::{
        decl::{Decl, DeclKind},
        expr::Expr,
        pattern::Pattern,
        stmt::Stmt,
        type_annotation::TypeAnnotation,
    },
    types::{
        constraints::constraint::Constraint,
        infer_ty::{InferTy, Level},
        type_session::TypeSession,
        wants::Wants,
    },
};

pub struct ConstraintGenerationPass<'a> {
    ast: &'a AST<NameResolved>,
    session: &'a mut TypeSession,
    wants: Wants,
}

impl<'a> ConstraintGenerationPass<'a> {
    pub fn drive(asts: &'a [AST<NameResolved>], session: &'a mut TypeSession) -> Wants {
        let mut result = Wants::default();

        for ast in asts.iter() {
            let mut pass = ConstraintGenerationPass {
                ast,
                wants: Default::default(),
                session,
            };

            result.extend(pass.generate());
        }

        result
    }

    fn generate(mut self) -> Wants {
        for group in self.ast.phase.scc_graph.groups() {
            for binder in group.binders.iter() {
                let rhs_id = self.ast.phase.scc_graph.rhs_id_for(binder);
                let rhs = self.ast.find(*rhs_id).unwrap();

                println!("rhs: {rhs:?}");
            }
        }
        self.wants
    }

    fn visit_node(&mut self, node: &Node, level: Level) -> InferTy {
        let ty = match &node {
            Node::Decl(decl) => self.visit_decl(decl, level),
            Node::Stmt(stmt) => self.visit_stmt(stmt),
            Node::Expr(expr) => self.visit_expr(expr),
            _ => todo!(),
        };

        self.session
            .types_by_node
            .insert(node.node_id(), ty.clone());

        ty
    }

    fn visit_decl(&mut self, decl: &Decl, level: Level) -> InferTy {
        match &decl.kind {
            DeclKind::Let {
                lhs,
                type_annotation,
                rhs,
            } => self.visit_let(lhs, type_annotation, rhs, level),
            DeclKind::Struct {
                name,
                name_span,
                generics,
                conformances,
                body,
            } => todo!(),
            DeclKind::Protocol {
                name,
                name_span,
                generics,
                body,
                conformances,
            } => todo!(),
            DeclKind::Init { name, params, body } => todo!(),
            DeclKind::Property {
                name,
                name_span,
                is_static,
                type_annotation,
                default_value,
            } => todo!(),
            DeclKind::Method { func, is_static } => todo!(),
            DeclKind::Associated { generic } => todo!(),
            DeclKind::Func(func) => todo!(),
            DeclKind::Extend {
                name,
                name_span,
                conformances,
                generics,
                body,
            } => todo!(),
            DeclKind::Enum {
                name,
                name_span,
                conformances,
                generics,
                body,
            } => todo!(),
            DeclKind::EnumVariant(name, span, type_annotations) => todo!(),
            DeclKind::FuncSignature(func_signature) => todo!(),
            DeclKind::MethodRequirement(func_signature) => todo!(),
            DeclKind::TypeAlias(type_annotation, type_annotation1) => {
                todo!()
            }
            _ => InferTy::Void,
        }
    }

    fn visit_stmt(&mut self, stmt: &Stmt) -> InferTy {
        InferTy::Void
    }

    fn visit_expr(&mut self, expr: &Expr) -> InferTy {
        InferTy::Void
    }

    // Decls

    fn visit_let(
        &mut self,
        lhs: &Pattern,
        type_annotation: &Option<TypeAnnotation>,
        rhs: &Option<Expr>,
        level: Level,
    ) -> InferTy {
        match (&type_annotation, &rhs) {
            (Some(annotation), Some(rhs)) => {}
            (None, Some(rhs)) => {}
            (Some(annotation), None) => {}
            (None, None) => {}
        };

        InferTy::Void
    }
}

#[cfg(test)]
pub mod tests {
    use crate::{
        compiling::module::ModuleId,
        name_resolution::name_resolver_tests::tests::resolve,
        node_id::NodeID,
        span::Span,
        types::{
            constraints::{constraint::ConstraintCause, equals::Equals},
            infer_ty::InferTy,
        },
    };

    use super::*;

    fn generate(code: &'static str) -> Wants {
        let resolved = resolve(code);
        let mut session = TypeSession::new(ModuleId::Current, Default::default());
        ConstraintGenerationPass::drive(&vec![resolved], &mut session)
    }

    #[test]
    fn let_int() {
        let wants = generate(
            r#"
            let a = 123
            "#,
        );

        assert_eq!(
            wants.all(),
            vec![Constraint::Equals(Equals {
                lhs: InferTy::Void,
                rhs: InferTy::Int,
                cause: ConstraintCause::Assignment(NodeID::ANY),
                span: Span::ANY
            })]
        );
    }
}
