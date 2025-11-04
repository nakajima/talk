use itertools::Itertools;
use rustc_hash::FxHashMap;
use tracing::instrument;

use crate::{
    ast::AST,
    label::Label,
    name::Name,
    name_resolution::{name_resolver::NameResolved, scc_graph::BindingGroup, symbol::Symbol},
    node::Node,
    node_kinds::{
        block::Block,
        body::Body,
        call_arg::CallArg,
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        func::Func,
        generic_decl::GenericDecl,
        match_arm::MatchArm,
        parameter::Parameter,
        pattern::{Pattern, PatternKind},
        stmt::{Stmt, StmtKind},
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
    types::{
        builtins::resolve_builtin_type,
        constraint_solver::ConstraintSolver,
        constraints::constraint::ConstraintCause,
        infer_row::{InferRow, RowMetaId},
        infer_ty::{InferTy, Level},
        type_operations::{apply, curry, substitute},
        type_session::{TypeDefKind, TypeSession},
        wants::Wants,
    },
};

pub struct ConstraintGenerationPass<'a> {
    ast: &'a mut AST<NameResolved>,
    session: &'a mut TypeSession,
    wants: Wants,
    canonical_rows: FxHashMap<Symbol, RowMetaId>,
}

impl<'a> ConstraintGenerationPass<'a> {
    pub fn drive(asts: &'a mut [AST<NameResolved>], session: &'a mut TypeSession) -> Wants {
        let mut result = Wants::default();

        for ast in asts.iter_mut() {
            let pass = ConstraintGenerationPass {
                ast,
                wants: Default::default(),
                session,
                canonical_rows: Default::default(),
            };

            result.extend(pass.generate());
        }

        result
    }

    fn generate(mut self) -> Wants {
        println!("GROUPS: {:?}", self.ast.phase.scc_graph.groups());

        for group in self.ast.phase.scc_graph.groups() {
            self.generate_for_group(group);
        }

        for id in self.ast.phase.unbound_nodes.clone() {
            let node = self.ast.find(id).unwrap();
            self.visit_node(&node, Level::default());
        }

        let wants = std::mem::take(&mut self.wants);
        let solver = ConstraintSolver::new(wants, Level::default(), self.session, self.ast);
        let (mut substitutions, _unsolved) = solver.solve();
        self.session.apply(&mut substitutions);
        self.wants
    }

    fn generate_for_group(&mut self, group: BindingGroup) {
        // Create placeholders
        let placeholders = group
            .binders
            .iter()
            .map(|sym| {
                let placeholder = self.session.new_ty_meta_var(group.level);
                tracing::trace!("placeholder {sym:?} = {placeholder:?}");
                self.session.insert_term(*sym, placeholder.to_entry());
                placeholder
            })
            .collect_vec();

        // Visit each binder
        for (i, binder) in group.binders.iter().enumerate() {
            let rhs_id = self.ast.phase.scc_graph.rhs_id_for(binder);
            let rhs = self.ast.find(*rhs_id).unwrap();
            let ty = self.visit_node(&rhs, group.level);
            self.wants.equals(
                ty,
                placeholders[i].clone(),
                ConstraintCause::Internal,
                rhs.span(),
            );
        }

        // Solve this group
        let wants = std::mem::take(&mut self.wants);
        let solver = ConstraintSolver::new(wants, group.level, self.session, self.ast);
        let (mut substitutions, unsolved) = solver.solve();

        // Generalize
        for (i, binder) in group.binders.iter().enumerate() {
            let ty = apply(placeholders[i].clone(), &mut substitutions);
            let entry = self.session.generalize(group.level.prev(), ty, &unsolved);
            self.session.promote(*binder, entry);
        }

        self.session.apply(&mut substitutions);
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
                generics,
                conformances,
                body,
                ..
            } => self.visit_struct(name, generics, conformances, body, level),
            DeclKind::Protocol {
                name,
                name_span,
                generics,
                body,
                conformances,
            } => todo!(),
            DeclKind::Init { name, params, body } => {
                unreachable!("inits are handled by visit_struct")
            }
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
            StmtKind::If(cond, conseq, alt) => self.visit_if_stmt(cond, conseq, alt, level),
            StmtKind::Assignment(lhs, rhs) => {
                let lhs_ty = self.visit_expr(lhs, level);
                let rhs_ty = self.visit_expr(rhs, level);
                self.wants.equals(
                    lhs_ty,
                    rhs_ty,
                    ConstraintCause::Assignment(stmt.id),
                    stmt.span,
                );
                InferTy::Void
            }
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
            ExprKind::Tuple(exprs) => InferTy::Tuple(
                exprs
                    .iter()
                    .map(|e| self.visit_expr(e, level))
                    .collect_vec(),
            ),
            ExprKind::Block(block) => todo!(),
            ExprKind::Call {
                callee,
                type_args,
                args,
            } => self.visit_call(callee, type_args, args, level),
            ExprKind::Member(receiver, label, ..) => {
                self.visit_member(expr, receiver, label, level)
            }
            ExprKind::Func(func) => self.visit_func(func, level),
            ExprKind::Variable(name) => self.visit_variable(expr, name, level),
            ExprKind::Constructor(name) => self.visit_constructor(expr, name, level),
            ExprKind::If(cond, conseq, alt) => self.infer_if_expr(cond, conseq, alt, level),
            ExprKind::Match(scrutinee, arms) => self.infer_match(scrutinee, arms, level),
            ExprKind::RecordLiteral { fields, spread } => todo!(),
            ExprKind::RowVariable(name) => todo!(),
            _ => unimplemented!(),
        };

        self.session.types_by_node.insert(expr.id, ty.clone());

        ty
    }

    fn visit_constructor(&mut self, expr: &Expr, name: &Name, level: Level) -> InferTy {
        InferTy::Constructor {
            name: name.clone(),
            params: vec![],
            ret: InferTy::Void.into(),
        }
    }

    fn visit_member(
        &mut self,
        expr: &Expr,
        receiver: &Option<Box<Expr>>,
        label: &Label,
        level: Level,
    ) -> InferTy {
        let Some(receiver) = receiver else { todo!() };

        let receiver_ty = self.visit_expr(receiver, level);
        let ret = self.session.new_ty_meta_var(level);
        self.wants.member(
            expr.id,
            receiver_ty,
            label.clone(),
            ret.clone(),
            ConstraintCause::Member(expr.id),
            expr.span,
        );

        ret
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, generics, conformances, body))]
    fn visit_struct(
        &mut self,
        name: &Name,
        generics: &[GenericDecl],
        conformances: &[TypeAnnotation],
        body: &Body,
        level: Level,
    ) -> InferTy {
        for generic in generics.iter() {
            let param_id = self.session.new_type_param_id(None);
            let skolem = self.session.new_skolem(param_id);
            self.session.insert_mono(generic.name.symbol(), skolem);
        }

        let struct_symbol = name.symbol();
        let struct_row = InferRow::Var(self.canonical_row_for(&struct_symbol, level));

        let struct_ty = InferTy::Nominal {
            symbol: name.symbol(),
            row: struct_row.clone().into(),
        };

        let mut properties = vec![];

        for decl in body.decls.iter() {
            match &decl.kind {
                DeclKind::Init { name, params, body } => {
                    self.visit_init(struct_ty.clone(), name, params, body, level.next());
                }
                DeclKind::Method { func, is_static } => todo!(),
                DeclKind::Property {
                    name,
                    is_static,
                    type_annotation,
                    default_value,
                    ..
                } => {
                    properties.push((
                        name.name_str(),
                        self.visit_property(
                            struct_symbol,
                            name,
                            *is_static,
                            type_annotation,
                            default_value,
                            level.next(),
                        ),
                    ));
                }
                _ => todo!("{:?}", decl.kind),
            }
        }

        let row =
            properties
                .iter()
                .fold(InferRow::Empty(TypeDefKind::Struct), |acc, (name, ty)| {
                    InferRow::Extend {
                        row: acc.into(),
                        label: name.into(),
                        ty: ty.clone(),
                    }
                });

        // NOTE: This is sort of a hack since we don't have a direct way to say
        // that rows should be equal.
        self.wants.equals(
            InferTy::Record(row.clone().into()),
            InferTy::Record(struct_row.into()),
            ConstraintCause::Internal,
            body.span,
        );

        InferTy::Nominal {
            symbol: struct_symbol,
            row: row.into(),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, ))]
    fn visit_property(
        &mut self,
        struct_symbol: Symbol,
        name: &Name,
        is_static: bool,
        type_annotation: &Option<TypeAnnotation>,
        default_value: &Option<Expr>,
        level: Level,
    ) -> InferTy {
        if default_value.is_some() {
            todo!()
        }

        let ty = if let Some(anno) = type_annotation {
            self.visit_type_annotation(&anno, level)
        } else {
            self.session.new_type_param(None)
        };

        if is_static {
            self.session
                .type_catalog
                .static_methods
                .entry(struct_symbol)
                .or_default()
                .insert(name.name_str().into(), name.symbol());
        } else {
            self.session
                .type_catalog
                .instance_methods
                .entry(struct_symbol)
                .or_default()
                .insert(name.name_str().into(), name.symbol());
        }

        ty
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, ))]
    fn visit_init(
        &mut self,
        struct_ty: InferTy,
        name: &Name,
        params: &[Parameter],
        body: &Block,
        level: Level,
    ) -> InferTy {
        let param_tys = self.visit_params(params, level);

        // Init blocks always return self
        _ = self.infer_block(body, level);

        let ty = curry(param_tys, struct_ty.clone());

        let InferTy::Nominal { symbol, .. } = &struct_ty else {
            unreachable!()
        };

        self.session
            .type_catalog
            .initializers
            .entry(*symbol)
            .or_default()
            .insert(Label::Named("init".into()), name.symbol());

        // TODO: This might be wrong
        self.session.insert_mono(name.symbol(), ty);

        InferTy::Void
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, scrutinee, arms))]
    fn infer_match(&mut self, scrutinee: &Expr, arms: &[MatchArm], level: Level) -> InferTy {
        let mut last_arm_ty: Option<InferTy> = None;
        let scrutinee_ty = self.visit_expr(scrutinee, level);

        for arm in arms {
            self.check_pattern(&arm.pattern, &scrutinee_ty, level);
            let arm_ty = self.infer_block(&arm.body, level);

            if let Some(last_arm_ty) = &last_arm_ty {
                self.wants.equals(
                    arm_ty.clone(),
                    last_arm_ty.clone(),
                    ConstraintCause::MatchArm(arm.id),
                    arm.span,
                );
            }

            last_arm_ty = Some(arm_ty);
        }

        last_arm_ty.unwrap_or(InferTy::Void)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn check_pattern(&mut self, pattern: &Pattern, expected: &InferTy, level: Level) {
        let Pattern { kind, .. } = &pattern;

        match kind {
            PatternKind::Bind(Name::Raw(name)) => {
                panic!("Unresolved name in pattern: {name:?}");
            }
            PatternKind::Bind(Name::Resolved(sym, _)) => {
                self.session.insert_mono(*sym, expected.clone());
            }
            PatternKind::Bind(Name::SelfType(..)) => (),
            PatternKind::LiteralInt(_) => {
                self.wants.equals(
                    expected.clone(),
                    InferTy::Int,
                    ConstraintCause::Pattern(pattern.id),
                    pattern.span,
                );
            }
            PatternKind::LiteralFloat(_) => {
                self.wants.equals(
                    expected.clone(),
                    InferTy::Float,
                    ConstraintCause::Pattern(pattern.id),
                    pattern.span,
                );
            }
            PatternKind::LiteralFalse | PatternKind::LiteralTrue => {
                self.wants.equals(
                    expected.clone(),
                    InferTy::Bool,
                    ConstraintCause::Pattern(pattern.id),
                    pattern.span,
                );
            }
            PatternKind::Tuple(patterns) => {
                let metas: Vec<InferTy> = (0..patterns.len())
                    .map(|_| self.session.new_ty_meta_var(level))
                    .collect();

                self.wants.equals(
                    expected.clone(),
                    InferTy::Tuple(metas.clone()),
                    ConstraintCause::Pattern(pattern.id),
                    pattern.span,
                );

                for (pi, bi) in patterns.iter().zip(metas) {
                    self.check_pattern(pi, &bi, level);
                }
            }
            PatternKind::Record { fields } => {
                todo!()
            }
            PatternKind::Variant {
                enum_name: _,
                variant_name,
                fields,
                ..
            } => {
                let field_metas: Vec<InferTy> = fields
                    .iter()
                    .map(|_| self.session.new_ty_meta_var(level))
                    .collect();
                let payload = if fields.is_empty() {
                    expected.clone()
                } else if fields.len() == 1 {
                    InferTy::Func(field_metas[0].clone().into(), expected.clone().into())
                } else {
                    curry(field_metas.clone(), expected.clone())
                };

                self.wants.member(
                    pattern.id,
                    expected.clone(),
                    variant_name.into(),
                    payload,
                    ConstraintCause::Pattern(pattern.id),
                    pattern.span,
                );

                // Recursively check each field pattern
                for (field_pattern, field_ty) in fields.iter().zip(field_metas) {
                    self.check_pattern(field_pattern, &field_ty, level);
                }
            }
            PatternKind::Wildcard => (),
            PatternKind::Struct { .. } => todo!(),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, cond, conseq, alt))]
    fn infer_if_expr(&mut self, cond: &Expr, conseq: &Block, alt: &Block, level: Level) -> InferTy {
        let cond_ty = self.visit_expr(cond, level);
        self.wants.equals(
            cond_ty,
            InferTy::Bool,
            ConstraintCause::Condition(cond.id),
            cond.span,
        );

        let conseq_ty = self.infer_block(conseq, level);
        let alt_ty = self.infer_block(alt, level);
        self.wants.equals(
            conseq_ty.clone(),
            alt_ty,
            ConstraintCause::Internal,
            alt.span,
        );

        conseq_ty
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, cond, conseq, alt))]
    fn visit_if_stmt(
        &mut self,
        cond: &Expr,
        conseq: &Block,
        alt: &Option<Block>,
        level: Level,
    ) -> InferTy {
        let cond_ty = self.visit_expr(cond, level);
        self.wants.equals(
            cond_ty,
            InferTy::Bool,
            ConstraintCause::Condition(cond.id),
            cond.span,
        );

        let conseq_ty = self.infer_block(conseq, level);

        if let Some(alt) = alt {
            let alt_ty = self.infer_block(alt, level);
            self.wants.equals(
                conseq_ty.clone(),
                alt_ty,
                ConstraintCause::Internal,
                alt.span,
            );
        }

        conseq_ty
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, block))]
    fn infer_block(&mut self, block: &Block, level: Level) -> InferTy {
        let mut ret = InferTy::Void;
        for node in block.body.iter() {
            ret = self.visit_node(node, level);
        }
        ret
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, expr))]
    fn visit_variable(&mut self, expr: &Expr, name: &Name, level: Level) -> InferTy {
        self.session.lookup(&name.symbol()).unwrap().instantiate(
            expr.id,
            self.session,
            level,
            &mut self.wants,
            expr.span,
        )
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn visit_call(
        &mut self,
        callee: &Expr,
        type_args: &[TypeAnnotation],
        args: &[CallArg],
        level: Level,
    ) -> InferTy {
        let mut arg_tys = args
            .iter()
            .map(|a| self.visit_expr(&a.value, level))
            .collect_vec();
        let type_args = type_args
            .iter()
            .map(|a| self.visit_type_annotation(&a, level))
            .collect_vec();
        let callee_ty = self.visit_expr(callee, level);
        let ret = self.session.new_ty_meta_var(level);

        if matches!(callee_ty, InferTy::Constructor { .. }) {
            arg_tys.insert(0, ret.clone());
        }

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

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn visit_func(&mut self, func: &Func, level: Level) -> InferTy {
        for generic in func.generics.iter() {
            let param_id = self.session.new_type_param_id(None);
            let skolem = self.session.new_skolem(param_id);
            self.session.insert_mono(generic.name.symbol(), skolem);
        }

        let mut params = self.visit_params(&func.params, level);

        let ret = if let Some(ret) = &func.ret {
            self.visit_type_annotation(ret, level)
        } else {
            self.session.new_ty_meta_var(level)
        };

        self.check_block(&func.body, ret.clone(), level);

        if params.is_empty() {
            // Otherwise curry gets confused. TODO: just fix curry?
            params.push(InferTy::Void);
        }

        let func_ty = curry(params, ret);
        substitute(func_ty, &self.session.skolem_map) // Deskolemize
    }

    fn visit_params(&mut self, params: &[Parameter], level: Level) -> Vec<InferTy> {
        params
            .iter()
            .map(|param| {
                if let Some(existing) = self.session.lookup(&param.name.symbol()) {
                    return existing._as_ty();
                }

                let ty = if let Some(type_annotation) = &param.type_annotation {
                    self.visit_type_annotation(type_annotation, level)
                } else {
                    self.session.new_ty_meta_var(level)
                };

                self.session
                    .insert_term(param.name.symbol(), ty.clone().to_entry());

                ty
            })
            .collect_vec()
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, block))]
    fn check_block(&mut self, block: &Block, expected: InferTy, level: Level) {
        let mut ret = InferTy::Void;
        for node in &block.body {
            ret = self.visit_node(node, level);
        }
        self.wants
            .equals(ret, expected, ConstraintCause::Internal, block.span);
    }

    // Checks
    #[allow(clippy::too_many_arguments)]
    #[instrument(skip(self, body))]
    fn check_func(
        &mut self,
        params: &[Parameter],
        ret: &Option<TypeAnnotation>,
        body: &Block,
        expected_params: Vec<InferTy>,
        expected_ret: InferTy,
        level: Level,
    ) {
        for (param, expected_param_ty) in params.iter().zip(expected_params) {
            self.session
                .insert_mono(param.name.symbol(), expected_param_ty);
        }

        if let Some(ret) = ret {
            let ret_ty = self.visit_type_annotation(&ret, level);
            self.wants.equals(
                ret_ty,
                expected_ret.clone(),
                ConstraintCause::Annotation(ret.id),
                ret.span,
            );
        }

        println!("expected ret: {expected_ret:?}");

        self.check_block(body, expected_ret.clone(), level);
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn visit_type_annotation(&mut self, type_annotation: &TypeAnnotation, level: Level) -> InferTy {
        match &type_annotation.kind {
            TypeAnnotationKind::Nominal { name, generics, .. } => {
                if matches!(name.symbol(), Symbol::Builtin(..)) {
                    return resolve_builtin_type(&name.symbol()).0;
                }

                // Do we know about this already? Cool.
                if let Some(entry) = self.session.lookup(&name.symbol()) {
                    return entry.instantiate(
                        type_annotation.id,
                        self.session,
                        level,
                        &mut self.wants,
                        type_annotation.span,
                    );
                } else {
                    tracing::info!("nope, did not find anything in the env for {name:?}");
                }

                if matches!(name.symbol(), Symbol::TypeParameter(..)) {
                    return self.session.lookup(&name.symbol()).unwrap()._as_ty();
                }

                if !generics.is_empty() {
                    todo!()
                }

                let row = InferRow::Var(self.canonical_row_for(&name.symbol(), level));

                InferTy::Nominal {
                    symbol: name.symbol(),
                    row: Box::new(row),
                }
            }
            TypeAnnotationKind::SelfType(name) => {
                self.session.lookup(&name.symbol()).unwrap().instantiate(
                    type_annotation.id,
                    self.session,
                    level,
                    &mut self.wants,
                    type_annotation.span,
                )
            }
            _ => todo!(),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
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

    fn canonical_row_for(&mut self, symbol: &Symbol, level: Level) -> RowMetaId {
        if let Some(existing) = self.canonical_rows.get(symbol).copied() {
            return existing;
        }

        let id = self.session.new_row_meta_var_id(level);
        self.canonical_rows.insert(*symbol, id);
        id
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
        let wants = ConstraintGenerationPass::drive(&mut vec![resolved], &mut session);
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
