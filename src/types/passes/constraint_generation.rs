use itertools::Itertools;

use crate::{
    ast::AST,
    name::Name,
    name_resolution::{name_resolver::NameResolved, scc_graph::BindingGroup, symbol::Symbol},
    node::Node,
    node_kinds::{
        block::Block,
        call_arg::CallArg,
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        func::Func,
        pattern::{Pattern, PatternKind},
        stmt::{Stmt, StmtKind},
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
    types::{
        builtins::resolve_builtin_type,
        constraints::{call, constraint::ConstraintCause},
        infer_ty::{InferTy, Level},
        type_operations::curry,
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
            let pass = ConstraintGenerationPass {
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
            self.generate_for_group(group);
        }

        for id in &self.ast.phase.unbound_nodes {
            let node = self.ast.find(*id).unwrap();
            self.visit_node(&node, Level::default());
        }

        self.wants
    }

    fn generate_for_group(&mut self, group: BindingGroup) {
        // Create placeholders
        let mut placeholders = group
            .binders
            .iter()
            .rev()
            .map(|sym| {
                let placeholder = self.session.new_ty_meta_var(group.level);
                tracing::trace!("placeholder {sym:?} = {placeholder:?}");
                self.session.insert_term(*sym, placeholder.to_entry());
                placeholder
            })
            .collect_vec();

        // Visit each binder
        for binder in group.binders.iter() {
            let rhs_id = self.ast.phase.scc_graph.rhs_id_for(binder);
            let rhs = self.ast.find(*rhs_id).unwrap();
            let ty = self.visit_node(&rhs, group.level);
            self.wants.equals(
                ty,
                placeholders.pop().unwrap(),
                ConstraintCause::Internal,
                rhs.span(),
            );
        }
    }

    fn visit_node(&mut self, node: &Node, level: Level) -> InferTy {
        match &node {
            Node::Decl(decl) => self.visit_decl(decl, level),
            Node::Stmt(stmt) => self.visit_stmt(stmt, level),
            Node::Expr(expr) => self.visit_expr(expr, level),
            _ => todo!(),
        }
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

    fn visit_stmt(&mut self, stmt: &Stmt, level: Level) -> InferTy {
        let ty = match &stmt.kind {
            StmtKind::Expr(expr) => self.visit_expr(expr, level),
            _ => todo!(),
        };

        self.session.types_by_node.insert(stmt.id, ty.clone());

        ty
    }

    fn visit_expr(&mut self, expr: &Expr, level: Level) -> InferTy {
        let ty = match &expr.kind {
            ExprKind::LiteralArray(exprs) => todo!(),
            ExprKind::LiteralInt(_) => InferTy::Int,
            ExprKind::LiteralFloat(_) => InferTy::Float,
            ExprKind::LiteralTrue | ExprKind::LiteralFalse => InferTy::Bool,
            ExprKind::LiteralString(_) => todo!(),
            ExprKind::Unary(token_kind, expr) => todo!(),
            ExprKind::Binary(expr, token_kind, expr1) => todo!(),
            ExprKind::Tuple(exprs) => todo!(),
            ExprKind::Block(block) => todo!(),
            ExprKind::Call {
                callee,
                type_args,
                args,
            } => self.visit_call(callee, type_args, args, level),
            ExprKind::Member(expr, label, span) => todo!(),
            ExprKind::Func(func) => self.visit_func(func, level),
            ExprKind::Variable(name) => self.visit_variable(expr, name, level),
            ExprKind::Constructor(name) => todo!(),
            ExprKind::If(expr, block, block1) => todo!(),
            ExprKind::Match(expr, match_arms) => todo!(),
            ExprKind::RecordLiteral { fields, spread } => todo!(),
            ExprKind::RowVariable(name) => todo!(),
            _ => unimplemented!(),
        };

        self.session.types_by_node.insert(expr.id, ty.clone());

        ty
    }

    fn visit_variable(&mut self, expr: &Expr, name: &Name, level: Level) -> InferTy {
        self.session.lookup(&name.symbol()).unwrap().instantiate(
            expr.id,
            self.session,
            level,
            &mut self.wants,
            expr.span,
        )
    }

    fn visit_call(
        &mut self,
        callee: &Expr,
        type_args: &[TypeAnnotation],
        args: &[CallArg],
        level: Level,
    ) -> InferTy {
        let arg_tys = args
            .iter()
            .map(|a| self.visit_expr(&a.value, level))
            .collect_vec();
        let type_args = type_args
            .iter()
            .map(|a| self.visit_type_annotation(&a, level))
            .collect_vec();
        let callee_ty = self.visit_expr(callee, level);
        let ret = self.session.new_ty_meta_var(level);
        self.wants.call(
            callee.id,
            callee_ty,
            arg_tys,
            type_args,
            ret.clone(),
            None,
            ConstraintCause::Call(callee.id),
            callee.span,
        );
        ret
    }

    fn visit_func(&mut self, func: &Func, level: Level) -> InferTy {
        let params = func
            .params
            .iter()
            .map(|param| {
                let ty = if let Some(type_annotation) = &param.type_annotation {
                    self.visit_type_annotation(type_annotation, level)
                } else {
                    self.session.new_ty_meta_var(level)
                };

                self.session
                    .insert_term(param.name.symbol(), ty.clone().to_entry());

                ty
            })
            .collect_vec();

        let ret = if let Some(ret) = &func.ret {
            self.visit_type_annotation(ret, level)
        } else {
            self.session.new_ty_meta_var(level)
        };

        self.check_block(&func.body, ret.clone(), level);

        curry(params, ret)
    }

    fn check_block(&mut self, block: &Block, expected: InferTy, level: Level) {
        let mut ret = InferTy::Void;
        for node in &block.body {
            ret = self.visit_node(node, level);
        }
        self.wants
            .equals(ret, expected, ConstraintCause::Internal, block.span);
    }

    fn infer_block(&mut self, block: &Block, level: Level) -> InferTy {
        let mut ret = InferTy::Void;
        for node in &block.body {
            ret = self.visit_node(node, level);
        }
        ret
    }

    fn visit_type_annotation(&mut self, type_annotation: &TypeAnnotation, level: Level) -> InferTy {
        match &type_annotation.kind {
            TypeAnnotationKind::Nominal { name, generics, .. } => {
                if matches!(name.symbol(), Symbol::Builtin(..)) {
                    return resolve_builtin_type(&name.symbol()).0;
                }

                if !generics.is_empty() {
                    todo!()
                }

                InferTy::Nominal {
                    symbol: name.symbol(),
                    row: Box::new(self.session.new_row_meta_var(level)),
                }
            }
            TypeAnnotationKind::SelfType(_) => todo!(),
            _ => todo!(),
        }
    }

    fn visit_let(
        &mut self,
        lhs: &Pattern,
        type_annotation: &Option<TypeAnnotation>,
        rhs: &Option<Expr>,
        level: Level,
    ) -> InferTy {
        let ty = match (&type_annotation, &rhs) {
            (None, Some(expr)) => self.visit_expr(expr, level),
            (Some(annotation), None) => self.visit_type_annotation(annotation, level),
            (Some(annotation), Some(rhs)) => {
                let annotated_ty = self.visit_type_annotation(annotation, level);
                let rhs_ty = self.visit_expr(rhs, level);
                self.wants.equals(
                    annotated_ty.clone(),
                    rhs_ty,
                    ConstraintCause::Annotation(annotation.id),
                    annotation.span,
                );
                annotated_ty
            }
            (None, None) => self.session.new_ty_meta_var(level),
        };

        match &lhs.kind {
            PatternKind::Bind(name) => {
                self.session.insert_term(name.symbol(), ty.to_entry());
            }
            PatternKind::Record { .. } => todo!(),
            _ => todo!(),
        };

        ty
    }
}

#[cfg(test)]
pub mod tests {
    use crate::{
        compiling::module::ModuleId,
        name_resolution::{name_resolver_tests::tests::resolve, symbol::Symbol},
        node_id::NodeID,
        span::Span,
        types::{
            constraints::{
                constraint::{Constraint, ConstraintCause},
                equals::Equals,
            },
            infer_ty::InferTy,
            term_environment::EnvEntry,
        },
    };

    use super::*;

    fn generate(code: &'static str) -> (Wants, TypeSession) {
        let resolved = resolve(code);
        let mut session = TypeSession::new(ModuleId::Current, Default::default());
        let wants = ConstraintGenerationPass::drive(&vec![resolved], &mut session);
        (wants, session)
    }

    #[test]
    fn let_int() {
        let (wants, mut session) = generate(
            r#"
            let a = 123
            "#,
        );

        assert!(wants.is_empty(), "generated unnecessary constraint");
        assert_eq!(
            session.lookup(&Symbol::Global(1.into())).unwrap(),
            EnvEntry::Mono(InferTy::Int)
        );
    }

    #[test]
    fn let_float() {
        let (wants, mut session) = generate(
            r#"
            let a = 1.23
            "#,
        );

        assert!(wants.is_empty(), "generated unnecessary constraint");
        assert_eq!(
            session.lookup(&Symbol::Global(1.into())).unwrap(),
            EnvEntry::Mono(InferTy::Float)
        );
    }

    #[test]
    fn let_with_annotation_no_value() {
        let (wants, mut session) = generate(
            r#"
            let a: Bool
            "#,
        );

        assert!(wants.is_empty(), "generated unnecessary constraint");
        assert_eq!(
            session.lookup(&Symbol::Global(1.into())).unwrap(),
            EnvEntry::Mono(InferTy::Bool)
        );
    }

    #[test]
    fn let_with_annotation_and_value() {
        let (wants, mut session) = generate(
            r#"
            let a: Bool = 123
            "#,
        );

        assert_eq!(
            wants.all(),
            vec![Constraint::Equals(Equals {
                lhs: InferTy::Bool,
                rhs: InferTy::Int,
                cause: ConstraintCause::Annotation(NodeID::ANY),
                span: Span::ANY
            })]
        );
        assert_eq!(
            session.lookup(&Symbol::Global(1.into())).unwrap(),
            EnvEntry::Mono(InferTy::Bool)
        );
    }

    #[test]
    fn annotated_param_func_returning_monotype() {
        let (wants, mut session) = generate(
            r#"
            func foo(x: Int) { x }
            "#,
        );

        assert_eq!(
            wants.all(),
            vec![Constraint::Equals(Equals {
                lhs: InferTy::Int,
                rhs: InferTy::Var {
                    id: 1.into(),
                    level: Level(1)
                },
                cause: ConstraintCause::Internal,
                span: Span::ANY
            })]
        );
        assert_eq!(
            session.lookup(&Symbol::Global(1.into())).unwrap(),
            EnvEntry::Mono(InferTy::Func(
                InferTy::Int.into(),
                InferTy::Var {
                    id: 1.into(),
                    level: Level(1)
                }
                .into()
            ))
        );
    }

    #[test]
    fn annotated_ret_func_returning_monotype() {
        let (wants, mut session) = generate(
            r#"
            func foo(x) -> Int { x }
            "#,
        );

        assert_eq!(
            wants.all(),
            vec![Constraint::Equals(Equals {
                lhs: InferTy::Var {
                    id: 1.into(),
                    level: Level(1)
                },
                rhs: InferTy::Int,
                cause: ConstraintCause::Internal,
                span: Span::ANY
            })]
        );
        assert_eq!(
            session.lookup(&Symbol::Global(1.into())).unwrap(),
            EnvEntry::Mono(InferTy::Func(
                InferTy::Var {
                    id: 1.into(),
                    level: Level(1)
                }
                .into(),
                InferTy::Int.into(),
            ))
        );
    }

    #[test]
    fn identity() {
        let (wants, mut session) = generate(
            r#"
            func id(x) { x }
            id(123)
            id(1.23)
            "#,
        );

        assert_eq!(
            wants.all(),
            vec![Constraint::Equals(Equals {
                lhs: InferTy::Var {
                    id: 1.into(),
                    level: Level(1)
                },
                rhs: InferTy::Int,
                cause: ConstraintCause::Internal,
                span: Span::ANY
            })]
        );
        assert_eq!(
            session.lookup(&Symbol::Global(1.into())).unwrap(),
            EnvEntry::Mono(InferTy::Func(
                InferTy::Var {
                    id: 1.into(),
                    level: Level(1)
                }
                .into(),
                InferTy::Int.into(),
            ))
        );
    }
}
