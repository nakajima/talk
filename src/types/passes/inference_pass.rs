use tracing::instrument;

use crate::{
    ast::AST,
    diagnostic::{AnyDiagnostic, Diagnostic},
    name_resolution::name_resolver::NameResolved,
    node::Node,
    node_kinds::{
        block::Block,
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        func::Func,
        parameter::Parameter,
        pattern::{Pattern, PatternKind},
        stmt::{Stmt, StmtKind},
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
    types::{
        constraints::constraint::{Constraint, ConstraintCause},
        infer_ty::{InferTy, Level},
        passes::elaboration_pass::{Binder, ElaboratedToSchemes, ElaboratedTypes},
        type_operations::{UnificationSubstitutions, unify},
        type_session::TypeSession,
        wants::Wants,
    },
};

pub struct InferencePass<'a> {
    session: &'a mut TypeSession,
    asts: &'a mut [AST<NameResolved>],
    elaborated_types: ElaboratedTypes<ElaboratedToSchemes>,
    unsolved_constraints: Vec<Constraint>,
    substitutions: UnificationSubstitutions,
}

#[allow(unused_variables)]
impl<'a> InferencePass<'a> {
    pub fn drive(
        asts: &'a mut [AST<NameResolved>],
        session: &'a mut TypeSession,
        elaborated_types: ElaboratedTypes<ElaboratedToSchemes>,
    ) {
        let substitutions = UnificationSubstitutions::new(session.meta_levels.clone());
        let mut pass = InferencePass {
            asts,
            session,
            elaborated_types,
            unsolved_constraints: Default::default(),
            substitutions,
        };

        let level = Level::default();

        for group in pass.elaborated_types.groups() {
            pass.infer_group(group, level.next());
        }

        pass.final_pass(level);
        pass.apply_substitutions();
    }

    fn final_pass(&mut self, level: Level) {
        let mut wants = Wants::default();
        for i in 0..self.asts.len() {
            let roots = self.asts[i].roots.clone(); // TODO: It'd be nice to avoid this clone.
            self.infer_nodes(&roots, level.next(), &mut wants);
        }
        self.solve(wants);
    }

    fn apply_substitutions(&mut self) {
        self.session.apply(&mut self.substitutions);
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn solve(&mut self, mut wants: Wants) {
        let mut substitutions = UnificationSubstitutions::new(self.session.meta_levels.clone());
        let mut unsolved = vec![];

        // Add our current unsolved constraints to the end of the list of wants to see if any of the new
        // information we've collected can satisfy them.
        wants
            .defer
            .extend(std::mem::take(&mut self.unsolved_constraints));

        while let Some(want) = wants.pop() {
            let constraint = want.apply(&mut substitutions);
            let solution = match constraint {
                Constraint::Equals(ref equals) => {
                    unify(&equals.lhs, &equals.rhs, &mut substitutions, self.session)
                }
                Constraint::Call(call) => todo!(),
                Constraint::HasField(has_field) => todo!(),
                Constraint::Member(member) => todo!(),
                Constraint::Construction(construction) => todo!(),
                Constraint::Conforms(conforms) => todo!(),
                Constraint::AssociatedEquals(associated_equals) => todo!(),
                Constraint::TypeMember(type_member) => todo!(),
            };

            match solution {
                Ok(true) => (), // We're good
                Ok(false) => {
                    unsolved.push(constraint);
                }
                Err(e) => {
                    tracing::error!("Error solving constraint: {e:?}");
                    self.asts[constraint.span().file_id.0 as usize]
                        .diagnostics
                        .push(AnyDiagnostic::Typing(Diagnostic {
                            span: constraint.span(),
                            kind: e,
                        }));
                }
            }
        }

        // Stash our unsolved constraints for later
        self.unsolved_constraints.extend(unsolved.clone());
        self.substitutions.extend(substitutions);
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn infer_group(&mut self, group: Vec<Binder>, level: Level) {
        let mut wants = Wants::default();

        for binder in group {
            let rhs_id = self.elaborated_types.scc_graph.rhs_id_for(&binder);
            let ast = &self.asts[rhs_id.0.0 as usize];
            let rhs = ast.find(*rhs_id).unwrap();

            self.infer_node(&rhs, level, &mut wants);
        }

        self.solve(wants);
    }

    fn infer_nodes(&mut self, nodes: &[Node], level: Level, wants: &mut Wants) -> Vec<InferTy> {
        nodes
            .iter()
            .map(|node| self.infer_node(node, level, wants))
            .collect()
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, node, wants))]
    fn infer_node(&mut self, node: impl Into<Node>, level: Level, wants: &mut Wants) -> InferTy {
        let node: Node = node.into();

        if let Some(known) = self.session.types_by_node.get(&node.node_id()) {
            return known.clone();
        }

        let ty = match node {
            Node::Attribute(..) => todo!(),
            Node::Decl(ref decl) => self.infer_decl(&decl, level, wants),
            Node::Func(ref func) => self.infer_func(&func, level, wants),
            Node::Parameter(ref parameter) => self.infer_parameter(&parameter, level, wants),
            Node::Stmt(ref stmt) => self.infer_stmt(&stmt, level, wants),
            Node::Expr(ref expr) => self.infer_expr(&expr, level, wants),
            Node::CallArg(..) => todo!(),
            Node::Pattern(..) => todo!(),
            Node::MatchArm(..) => todo!(),
            Node::Block(ref block) => self.infer_block(block, level, wants),
            Node::FuncSignature(..) | Node::GenericDecl(..) | Node::TypeAnnotation(..) => {
                unreachable!()
            }
            Node::RecordField(..) => todo!(),
            Node::IncompleteExpr(..) => todo!(),
        };

        self.session
            .types_by_node
            .insert(node.node_id(), ty.clone());

        ty
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, wants))]
    fn check_expr(&mut self, expr: &Expr, expected: InferTy, level: Level, wants: &mut Wants) {
        if let Some(known) = self.session.types_by_node.get(&expr.id) {
            wants.equals(
                known.clone(),
                expected,
                ConstraintCause::Internal,
                expr.span,
            );

            return;
        }

        // We can assume that our type will be what is expected for the types_by_node
        self.session.types_by_node.insert(expr.id, expected.clone());

        match &expr.kind {
            ExprKind::Func(func) => {
                self.check_func(func, expected, level, wants);
            }
            _ => todo!(),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, wants, decl), fields(decl.kind = ?decl.kind))]
    fn infer_decl(&mut self, decl: &Decl, level: Level, wants: &mut Wants) -> InferTy {
        match &decl.kind {
            DeclKind::Let {
                lhs,
                type_annotation,
                rhs,
            } => self.infer_let(lhs, type_annotation, rhs, level, wants),
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
            DeclKind::TypeAlias(type_annotation, type_annotation1) => todo!(),
            DeclKind::Import(_) => InferTy::Void,
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, wants))]
    fn infer_let(
        &mut self,
        lhs: &Pattern,
        type_annotation: &Option<TypeAnnotation>,
        rhs: &Option<Expr>,
        level: Level,
        wants: &mut Wants,
    ) -> InferTy {
        let PatternKind::Bind(name) = &lhs.kind else {
            todo!();
        };

        if let Some(entry) = self
            .elaborated_types
            .nominals
            .get(&name.symbol())
            .map(|n| n.ty.clone())
            .or_else(|| self.elaborated_types.globals.get(&name.symbol()).cloned())
        {
            if let Some(rhs) = rhs {
                self.check_expr(rhs, entry._as_ty(), level, wants);
            }

            self.session.insert_term(name.symbol(), entry);

            return InferTy::Void;
        };

        match (&type_annotation, &rhs) {
            (None, None) => (),
            (None, Some(rhs)) => {
                let rhs_ty = self.infer_node(rhs, level.next(), wants);
                self.session.insert_mono(name.symbol(), rhs_ty);
            }
            (Some(anno), None) => {
                let rhs_ty = self.infer_type_annotation(&anno.kind, level.next(), wants);
                self.session.insert_mono(name.symbol(), rhs_ty);
            }
            (Some(_), Some(_)) => todo!(),
        }

        InferTy::Void
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, wants))]
    fn infer_type_annotation(
        &mut self,
        kind: &TypeAnnotationKind,
        level: Level,
        wants: &mut Wants,
    ) -> InferTy {
        todo!()
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, wants))]
    fn infer_func(&mut self, func: &Func, level: Level, wants: &mut Wants) -> InferTy {
        InferTy::Void
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, wants))]
    fn infer_parameter(&mut self, decl: &Parameter, level: Level, wants: &mut Wants) -> InferTy {
        InferTy::Void
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, wants, stmt), fields(stmt.kind = ?stmt.kind))]
    fn infer_stmt(&mut self, stmt: &Stmt, level: Level, wants: &mut Wants) -> InferTy {
        match &stmt.kind {
            StmtKind::Expr(expr) => self.infer_expr(expr, level, wants),
            StmtKind::If(expr, block, block1) => todo!(),
            StmtKind::Return(expr) => todo!(),
            StmtKind::Break => todo!(),
            StmtKind::Assignment(expr, expr1) => todo!(),
            StmtKind::Loop(expr, block) => todo!(),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, wants, expr), fields(expr.kind = ?expr.kind))]
    fn infer_expr(&mut self, expr: &Expr, level: Level, wants: &mut Wants) -> InferTy {
        match &expr.kind {
            ExprKind::Incomplete(incomplete_expr) => todo!(),
            ExprKind::LiteralArray(exprs) => todo!(),
            ExprKind::LiteralInt(_) => InferTy::Int,
            ExprKind::LiteralFloat(_) => InferTy::Float,
            ExprKind::LiteralFalse | ExprKind::LiteralTrue => InferTy::Bool,
            ExprKind::LiteralString(_) => InferTy::String(),
            ExprKind::Unary(token_kind, expr) => todo!(),
            ExprKind::Binary(expr, token_kind, expr1) => todo!(),
            ExprKind::Tuple(exprs) => todo!(),
            ExprKind::Block(block) => todo!(),
            ExprKind::Call {
                callee,
                type_args,
                args,
            } => todo!(),
            ExprKind::Member(expr, label, span) => todo!(),
            ExprKind::Func(func) => self.infer_func(func, level, wants),
            ExprKind::Variable(name) => self.session.lookup(&name.symbol()).unwrap().instantiate(
                expr.id,
                self.session,
                level,
                wants,
                expr.span,
            ),
            ExprKind::Constructor(name) => todo!(),
            ExprKind::If(expr, block, block1) => todo!(),
            ExprKind::Match(expr, match_arms) => todo!(),
            ExprKind::RecordLiteral { fields, spread } => todo!(),
            ExprKind::RowVariable(name) => todo!(),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, wants))]
    fn infer_block(&mut self, expr: &Block, level: Level, wants: &mut Wants) -> InferTy {
        InferTy::Void
    }

    // Checks
    fn check_func(&mut self, func: &Func, expected: InferTy, level: Level, wants: &mut Wants) {
        let InferTy::Func(param, box ret) = expected else {
            panic!("can't check func against non-func expected ty: {expected:?}");
        };

        self.check_body(&func.body, ret.clone(), level, wants);
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, wants, block), fields(block.id = ?block.id))]
    fn check_body(&mut self, block: &Block, expected: InferTy, level: Level, wants: &mut Wants) {
        let mut actual_ret = InferTy::Void;

        for node in block.body.iter() {
            actual_ret = self.infer_node(node, level, wants);
        }

        wants.equals(
            expected,
            actual_ret.clone(),
            ConstraintCause::Internal,
            block.span,
        );
    }
}

#[cfg(test)]
pub mod tests {
    use crate::{
        compiling::{
            driver::{Driver, Source},
            module::ModuleId,
        },
        types::{
            infer_ty::InferTy, passes::elaboration_pass::ElaborationPass, type_session::TypeSession,
        },
    };

    use super::*;

    struct InferResult {
        session: TypeSession,
        asts: Vec<AST<NameResolved>>,
    }

    impl InferResult {
        fn nth(&self, i: usize) -> InferTy {
            let node = &self.asts[0].roots[i];
            self.session.types_by_node[&node.node_id()].clone()
        }
    }

    fn infer(code: &'static str) -> InferResult {
        let driver = Driver::new_bare(vec![Source::from(code)], Default::default());
        let resolved = driver.parse().unwrap().resolve_names().unwrap();
        let mut session = TypeSession::new(ModuleId::Current, Default::default());
        let mut asts: Vec<_> = resolved.phase.asts.into_values().collect();
        let elaborated_types = ElaborationPass::drive(asts.as_slice(), &mut session);
        InferencePass::drive(asts.as_mut_slice(), &mut session, elaborated_types);
        InferResult { session, asts }
    }

    #[test]
    fn infers_simple_func() {
        let typed = infer("func fizz() { 123 }; fizz");
        assert_eq!(
            typed.nth(1),
            InferTy::Func(InferTy::Void.into(), InferTy::Int.into())
        );
    }
}
