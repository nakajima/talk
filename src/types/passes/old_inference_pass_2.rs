use itertools::Itertools;
use tracing::instrument;

use crate::{
    ast::AST,
    diagnostic::{AnyDiagnostic, Diagnostic},
    label::Label,
    name::Name,
    name_resolution::{name_resolver::NameResolved, symbol::Symbol},
    node::Node,
    node_id::{FileID, NodeID},
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
        pattern::{Pattern, PatternKind, RecordFieldPatternKind},
        record_field::RecordField,
        stmt::{Stmt, StmtKind},
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
    span::Span,
    types::{
        builtins::resolve_builtin_type,
        constraints::constraint::{Constraint, ConstraintCause},
        infer_row::InferRow,
        infer_ty::{InferTy, Level},
        passes::elaboration_pass::{ElaboratedTypes, ElaborationPass, RegisteredNames, SCCGraph},
        scheme::Scheme,
        term_environment::EnvEntry,
        type_operations::{UnificationSubstitutions, apply, curry, unify},
        type_session::{TypeDefKind, TypeSession},
        wants::Wants,
    },
};

pub struct InferencePass<'a> {
    session: &'a mut TypeSession,
    asts: &'a mut [AST<NameResolved>],
    unsolved_constraints: Vec<Constraint>,
    substitutions: UnificationSubstitutions,
}

#[allow(unused_variables)]
impl<'a> InferencePass<'a> {
    pub fn drive(asts: &'a mut [AST<NameResolved>], session: &'a mut TypeSession) {
        let substitutions = UnificationSubstitutions::new(session.meta_levels.clone());
        let mut pass = InferencePass {
            asts,
            session,
            unsolved_constraints: Default::default(),
            substitutions,
        };

        let graph = pass.session.elaborated_types.scc_graph.clone();

        let level = Level::default();
        pass.infer_scc_graph(level.next(), &graph);
        pass.final_pass(level);
        pass.apply_substitutions();
    }

    fn final_pass(&mut self, level: Level) {
        let mut wants = Wants::default();
        for i in 0..self.asts.len() {
            let roots = self.asts[i].roots.clone(); // TODO: It'd be nice to avoid this clone.
            self.infer_nodes(&roots, level.next(), &mut wants);
        }
        self.solve(wants, level);
    }

    fn apply_substitutions(&mut self) {
        self.session.apply(&mut self.substitutions);
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, wants))]
    fn solve(
        &mut self,
        mut wants: Wants,
        level: Level,
    ) -> (Vec<Constraint>, UnificationSubstitutions) {
        let mut substitutions = UnificationSubstitutions::new(self.session.meta_levels.clone());
        let mut unsolved = vec![];

        // Add our current unsolved constraints to the end of the list of wants to see if any of the new
        // information we've collected can satisfy them.
        wants
            .defer
            .extend(std::mem::take(&mut self.unsolved_constraints));

        // TODO: Move to a more sophisticated system than just a limit on solve attempts.
        let mut remaining_attempts = 5;
        while remaining_attempts >= 0 {
            let mut next_wants = Wants::default();
            while let Some(want) = wants.pop() {
                let constraint = want.apply(&mut substitutions);
                let solution = match constraint {
                    Constraint::Equals(ref equals) => {
                        unify(&equals.lhs, &equals.rhs, &mut substitutions, self.session)
                    }
                    Constraint::Call(ref call) => {
                        call.solve(self.session, &mut next_wants, &mut substitutions)
                    }
                    Constraint::HasField(ref has_field) => {
                        has_field.solve(self.session, level, &mut next_wants, &mut substitutions)
                    }
                    Constraint::Member(ref member) => {
                        member.solve(self.session, level, &mut next_wants, &mut substitutions)
                    }
                    Constraint::Construction(construction) => todo!(),
                    Constraint::Conforms(ref conforms) => {
                        conforms.solve(self.session, &mut next_wants, &mut substitutions)
                    }
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
                        let file_id = if self.asts.len() >= constraint.span().file_id.0 as usize {
                            constraint.span().file_id.0 as usize
                        } else {
                            self.asts.len() - 1
                        };
                        let diagnostic = AnyDiagnostic::Typing(Diagnostic {
                            span: constraint.span(),
                            kind: e,
                        });
                        if !self.asts[file_id].diagnostics.contains(&diagnostic) {
                            self.asts[file_id].diagnostics.push(diagnostic);
                        }
                    }
                }

                // Add any new constraints generated during solving
            }
            wants.extend(next_wants);
            remaining_attempts -= 1;
        }

        // Stash our unsolved constraints for later
        self.unsolved_constraints.extend(unsolved.clone());
        self.substitutions.extend(&substitutions);
        self.session.apply(&mut substitutions);

        (unsolved, substitutions)
    }

    fn infer_scc_graph(&mut self, level: Level, graph: &SCCGraph) {
        let groups = graph.groups();
        for group in groups {
            self.infer_group(&group.binders, group.level, graph);
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, group, graph))]
    fn infer_group(&mut self, group: &[Symbol], level: Level, graph: &SCCGraph) {
        let mut wants = Wants::default();

        let mut placeholders = vec![];
        for symbol in group {
            if self.session.lookup(symbol).is_none() {
                let ty = self.session.new_ty_meta_var(level.next());
                placeholders.push(ty.clone());
                self.session.insert_mono(*symbol, ty);
            }
        }

        for (binder, placeholder) in group.iter().zip(placeholders) {
            let rhs_id = graph.rhs_id_for(binder);
            let ast = &self.asts[rhs_id.0.0 as usize];
            let rhs = ast.find(*rhs_id).unwrap();

            let ty = self.infer_node(&rhs, level.next(), &mut wants);
            wants.equals(
                placeholder,
                ty.clone(),
                ConstraintCause::Internal,
                rhs.span(),
            );

            if self.session.lookup(&binder).is_none() {
                self.session.insert_mono(*binder, ty);
            }
        }

        let (predicates, mut substitutions) = self.solve(wants, level);

        for sym in group {
            match self.session.lookup(sym) {
                Some(EnvEntry::Mono(ty)) => {
                    let applied = apply(ty, &mut substitutions);
                    let scheme = self.session.generalize(level, applied, &predicates);
                    self.session.promote(*sym, scheme);
                }
                Some(entry @ EnvEntry::Scheme(_)) => {
                    let applied_entry = entry.apply(&mut substitutions);
                    self.session.promote(*sym, applied_entry);
                }
                None => panic!("didn't find {sym:?} in term env"),
            }
        }
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

        tracing::trace!("infer_node {node:?}");

        if let Some(known) = self.session.types_by_node.get(&node.node_id()) {
            return known.clone();
        }

        let ty = match node {
            Node::Attribute(..) => todo!(),
            Node::Decl(ref decl) => self.infer_decl(decl, level, wants),
            Node::Func(ref func) => self.infer_func(func, level, wants),
            Node::Parameter(ref parameter) => self.infer_parameter(parameter, level, wants),
            Node::Stmt(ref stmt) => self.infer_stmt(stmt, level, wants),
            Node::Expr(ref expr) => self.infer_expr(expr, level, wants),
            Node::Body(ref body) => self.infer_body(body, level, wants),
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

    #[instrument(level = tracing::Level::TRACE, skip(self, wants, expr))]
    fn infer_body(&mut self, expr: &Body, level: Level, wants: &mut Wants) -> InferTy {
        let graph = self.collect_scc_graph(&expr.decls);
        self.infer_scc_graph(level, &graph);

        let mut ret = InferTy::Void;
        for node in &expr.decls {
            ret = self.infer_node(node, level, wants);
        }
        ret
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
            } => self.infer_nominal(name, generics, conformances, body, level, wants),
            DeclKind::Enum {
                name,
                name_span,
                conformances,
                generics,
                body,
            } => self.infer_nominal(name, generics, conformances, body, level, wants),
            DeclKind::Protocol {
                name,
                name_span,
                generics,
                body,
                conformances,
            } => self.infer_protocol(name, generics, conformances, body, level, wants),
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
            } => InferTy::Void,
            DeclKind::EnumVariant(name, span, type_annotations) => todo!(),
            DeclKind::FuncSignature(func_signature) => todo!(),
            DeclKind::MethodRequirement(func_signature) => todo!(),
            DeclKind::TypeAlias(type_annotation, type_annotation1) => todo!(),
            DeclKind::Import(_) => InferTy::Void,
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, wants, generics, conformances, body, ))]
    fn infer_protocol(
        &mut self,
        name: &Name,
        generics: &[GenericDecl],
        conformances: &[TypeAnnotation],
        body: &Body,
        level: Level,
        wants: &mut Wants,
    ) -> InferTy {
        // TODO: check methods

        InferTy::Void
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, wants, generics, conformances, body))]
    fn infer_nominal(
        &mut self,
        name: &Name,
        generics: &[GenericDecl],
        conformances: &[TypeAnnotation],
        body: &Body,
        level: Level,
        wants: &mut Wants,
    ) -> InferTy {
        // let entry = self.session.lookup(&name.symbol()).unwrap();
        let entry = self
            .session
            .elaborated_types
            .nominals
            .get(&name.symbol())
            .unwrap();
        let entry = self
            .session
            .materialize_entry(entry.ty.clone(), level, wants);

        for decl in &body.decls {
            match &decl.kind {
                DeclKind::Struct {
                    name,
                    generics,
                    conformances,
                    body,
                    ..
                } => {
                    self.infer_nominal(name, generics, conformances, body, level, wants);
                }
                DeclKind::Protocol {
                    name,
                    name_span,
                    generics,
                    body,
                    conformances,
                } => todo!(),
                DeclKind::Init {
                    name: init_name,
                    params,
                    body,
                } => {
                    let expected_entry = self
                        .session
                        .elaborated_types
                        .nominals
                        .get(&name.symbol())
                        .unwrap()
                        .members
                        .initializers
                        .get(&Label::Named("init".into()))
                        .unwrap();
                    let expected_entry =
                        self.session
                            .materialize_entry(expected_entry.clone(), level, wants);
                    let expected =
                        expected_entry.instantiate(decl.id, self.session, level, wants, decl.span);
                    let (expected_params, expected_ret) = uncurry_function(expected);
                    self.check_func(
                        params,
                        &None,
                        body,
                        expected_params,
                        InferTy::Void,
                        level,
                        wants,
                    );
                }
                DeclKind::EnumVariant(variant_name, span, type_annotations) => {
                    // Should something be happening here? Unclear.
                    let expected_entry = self.session.lookup(&variant_name.symbol()).unwrap();
                    self.session
                        .insert_term(variant_name.symbol(), expected_entry.clone());
                }
                DeclKind::Property {
                    name: property_name,
                    default_value,
                    ..
                } => {
                    let entry = self
                        .session
                        .elaborated_types
                        .nominals
                        .get(&name.symbol())
                        .unwrap()
                        .members
                        .properties
                        .get(&Label::Named(property_name.name_str()))
                        .unwrap();
                    let entry = self.session.materialize_entry(entry.clone(), level, wants);
                    let mono_ty = entry._as_ty();
                    if let Some(val) = default_value {
                        let default_value_ty = self.infer_node(val, level, wants);
                        wants.equals(
                            mono_ty,
                            default_value_ty,
                            ConstraintCause::Literal(val.id),
                            val.span,
                        );
                    }
                }
                DeclKind::Method { func, is_static } => {
                    let expected_entry = self
                        .session
                        .elaborated_types
                        .nominals
                        .get(&name.symbol())
                        .unwrap()
                        .members
                        .methods
                        .get(&Label::Named(func.name.name_str()))
                        .unwrap();
                    let expected_entry =
                        self.session
                            .materialize_entry(expected_entry.clone(), level, wants);
                    let skolemized = self.session.skolemize(&expected_entry);
                    let (expected_params, expected_ret) = uncurry_function(skolemized);
                    self.check_func(
                        &func.params,
                        &func.ret,
                        &func.body,
                        expected_params,
                        expected_ret,
                        level,
                        wants,
                    );
                }
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
                DeclKind::FuncSignature(func_signature) => todo!(),
                DeclKind::MethodRequirement(func_signature) => todo!(),
                DeclKind::TypeAlias(type_annotation, type_annotation1) => todo!(),
                _ => (),
            }
        }

        InferTy::Void
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

        if let Some(entry) = self.session.lookup(&name.symbol()) {
            // This name was already inferred (e.g., by the SCC pass). Do not re-check RHS
            // against a skolemized type; just expose the known entry for downstream uses.
            self.session.insert_term(name.symbol(), entry.clone());
            return entry._as_ty();
        }

        if let Some(entry) = self.session.lookup(&name.symbol()) {
            let skolemized = self.session.skolemize(&entry);
            if let Some(rhs) = rhs {
                self.check_expr(rhs, skolemized.clone(), level, wants);
            }

            self.session.insert_term(name.symbol(), entry.clone());
            return skolemized;
        };

        let ty = match (&type_annotation, &rhs) {
            (None, None) => self.session.new_ty_meta_var(level),
            (None, Some(rhs)) => self.infer_node(rhs, level.next(), wants),
            (Some(anno), None) => self.infer_type_annotation(&anno.kind, level.next(), wants),
            (Some(anno), Some(rhs)) => {
                let rhs_ty = self.infer_node(rhs, level.next(), wants);
                let anno_ty = self.infer_type_annotation(&anno.kind, level.next(), wants);
                wants.equals(
                    rhs_ty,
                    anno_ty.clone(),
                    ConstraintCause::Annotation(anno.id),
                    anno.span,
                );

                anno_ty
            }
        };

        if self.session.lookup(&name.symbol()).is_none() {
            self.session.insert_mono(name.symbol(), ty);
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
        match kind {
            TypeAnnotationKind::SelfType(name) | TypeAnnotationKind::Nominal { name, .. } => {
                match name.symbol() {
                    Symbol::Struct(..) | Symbol::Enum(..) => {
                        let Some(nominal) = self.session.lookup(&name.symbol()) else {
                            panic!("did not find nominal named {name:?}");
                        };

                        nominal._as_ty()
                    }
                    Symbol::TypeParameter(..) => {
                        let id = self
                            .session
                            .elaborated_types
                            .canonical_type_params
                            .get(&name.symbol())
                            .unwrap();
                        InferTy::Param(*id)
                    }
                    Symbol::Builtin(..) => resolve_builtin_type(&name.symbol()).0,
                    _ => panic!("not sure how to handle {name:?} type annotation"),
                }
            }
            _ => todo!("{kind:?}"),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, wants, func), fields(func.name = ?func.name))]
    fn infer_func(&mut self, func: &Func, level: Level, wants: &mut Wants) -> InferTy {
        let mut param_tys = vec![];
        for param in func.params.iter() {
            let meta = if let Some(existing) = self.session.lookup(&param.name.symbol()) {
                existing._as_ty()
            } else if let Some(anno) = &param.type_annotation {
                let param_id = self
                    .session
                    .elaborated_types
                    .canonical_type_params
                    .get(&anno.symbol())
                    .cloned()
                    .unwrap();
                self.session
                    .insert_mono(param.name.symbol(), InferTy::Param(param_id));
                InferTy::Param(param_id)
            } else {
                let meta = self.session.new_ty_meta_var(level);
                self.session.insert_mono(param.name.symbol(), meta.clone());
                meta
            };

            param_tys.push(meta);
        }

        if param_tys.is_empty() {
            param_tys.push(InferTy::Void);
        }

        let ret = self.infer_block(&func.body, level, wants);

        curry(param_tys, ret)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, wants))]
    fn infer_parameter(&mut self, decl: &Parameter, level: Level, wants: &mut Wants) -> InferTy {
        InferTy::Void
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, wants, stmt), fields(stmt.kind = ?stmt.kind))]
    fn infer_stmt(&mut self, stmt: &Stmt, level: Level, wants: &mut Wants) -> InferTy {
        match &stmt.kind {
            StmtKind::Expr(expr) => self.infer_expr(expr, level, wants),
            StmtKind::If(cond, conseq, alt) => {
                let cond_ty = self.infer_node(cond, level, wants);
                wants.equals(
                    cond_ty,
                    InferTy::Bool,
                    ConstraintCause::Condition(cond.id),
                    cond.span,
                );

                let ret = self.infer_node(conseq, level, wants);
                if let Some(alt) = alt {
                    self.infer_node(alt, level, wants);
                }

                ret // TODO: This is sort of a hack around the fact that if exprs are parsed as statements at times.
            }
            StmtKind::Return(expr) => todo!(),
            StmtKind::Break => todo!(),
            StmtKind::Assignment(lhs, rhs) => {
                let lhs_ty = self.infer_expr(lhs, level, wants);
                let rhs_ty = self.infer_expr(rhs, level, wants);
                wants.equals(
                    lhs_ty,
                    rhs_ty,
                    ConstraintCause::Assignment(stmt.id),
                    stmt.span,
                );
                InferTy::Void
            }
            StmtKind::Loop(cond, block) => {
                if let Some(cond) = cond {
                    let cond_ty = self.infer_expr(cond, level, wants);
                    wants.equals(
                        cond_ty,
                        InferTy::Bool,
                        ConstraintCause::Condition(cond.id),
                        cond.span,
                    );
                }

                self.infer_block(block, level, wants);

                InferTy::Void
            }
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
            ExprKind::Tuple(exprs) => InferTy::Tuple(
                exprs
                    .iter()
                    .map(|e| self.infer_expr(e, level, wants))
                    .collect(),
            ),
            ExprKind::Block(block) => todo!(),
            ExprKind::Call {
                callee,
                type_args,
                args,
            } => self.infer_call(expr.id, callee, type_args, args, level, wants),
            ExprKind::Member(receiver, label, span) => {
                self.infer_member(expr.id, receiver, label, level, wants)
            }
            ExprKind::Func(func) => self.infer_func(func, level, wants),
            ExprKind::Variable(name) => self
                .session
                .lookup(&name.symbol())
                .unwrap_or_else(|| panic!("did not find entry for {name:?}"))
                .instantiate(expr.id, self.session, level, wants, expr.span),
            ExprKind::Constructor(name) => self.infer_constructor(expr, name, level, wants),
            ExprKind::If(cond, conseq, alt) => self.infer_if_expr(cond, conseq, alt, level, wants),
            ExprKind::Match(scrutinee, arms) => self.infer_match(scrutinee, arms, level, wants),
            ExprKind::RecordLiteral { fields, spread } => {
                self.infer_record_literal(fields, spread, level, wants)
            }
            ExprKind::RowVariable(name) => todo!(),
        }
    }

    fn infer_constructor(
        &mut self,
        expr: &Expr,
        name: &Name,
        level: Level,
        wants: &mut Wants,
    ) -> InferTy {
        match name.symbol() {
            Symbol::Struct(..) => {
                let entry = self
                    .session
                    .elaborated_types
                    .nominals
                    .get(&name.symbol())
                    .unwrap()
                    .members
                    .initializers
                    .get(&Label::Named("init".into()))
                    .unwrap();
                let entry = self.session.materialize_entry(entry.clone(), level, wants);
                entry.instantiate(expr.id, self.session, level, wants, expr.span)
            }
            Symbol::Enum(..) => self.session.lookup(&name.symbol()).unwrap().instantiate(
                expr.id,
                self.session,
                level,
                wants,
                expr.span,
            ),
            _ => panic!("cannot have a constructor for {name:?}"),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, wants))]
    fn infer_member(
        &mut self,
        id: NodeID,
        receiver: &Option<Box<Expr>>,
        label: &Label,
        level: Level,
        wants: &mut Wants,
    ) -> InferTy {
        let receiver_ty = if let Some(receiver) = &receiver {
            self.infer_expr(receiver, level, wants)
        } else {
            self.session.new_ty_meta_var(level)
        };

        let member_ty = self.session.new_ty_meta_var(level);

        wants.member(
            id,
            receiver_ty,
            label.clone(),
            member_ty.clone(),
            ConstraintCause::Member(id),
            receiver.as_ref().map(|r| r.span).unwrap_or(Span {
                file_id: FileID(0),
                start: 0,
                end: 0,
            }),
        );

        member_ty
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn infer_match(
        &mut self,
        scrutinee: &Expr,
        arms: &[MatchArm],
        level: Level,
        wants: &mut Wants,
    ) -> InferTy {
        let mut last_arm_ty: Option<InferTy> = None;
        let scrutinee_ty = self.infer_expr(scrutinee, level, wants);

        for arm in arms {
            self.check_pattern(&arm.pattern, &scrutinee_ty, level, wants);
            let arm_ty = self.infer_block(&arm.body, level, wants);

            if let Some(last_arm_ty) = &last_arm_ty {
                wants.equals(
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
    fn infer_record_literal(
        &mut self,
        fields: &[RecordField],
        spread: &Option<Box<Expr>>,
        level: Level,
        wants: &mut Wants,
    ) -> InferTy {
        let mut row = InferRow::Empty(TypeDefKind::Struct);
        for field in fields.iter().rev() {
            row = InferRow::Extend {
                row: Box::new(row),
                label: field.label.name_str().into(),
                ty: self.infer_expr(&field.value, level, wants),
            };
        }

        InferTy::Record(Box::new(row))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, cond, conseq, alt, wants))]
    fn infer_if_expr(
        &mut self,
        cond: &Expr,
        conseq: &Block,
        alt: &Block,
        level: Level,
        wants: &mut Wants,
    ) -> InferTy {
        let cond_ty = self.infer_expr(cond, level, wants);
        wants.equals(
            cond_ty,
            InferTy::Bool,
            ConstraintCause::Condition(cond.id),
            cond.span,
        );

        let conseq_ty = self.infer_block(conseq, level, wants);
        let alt_ty = self.infer_block(alt, level, wants);
        wants.equals(
            conseq_ty.clone(),
            alt_ty,
            ConstraintCause::Condition(alt.id),
            alt.span,
        );

        conseq_ty
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, wants))]
    fn infer_call(
        &mut self,
        id: NodeID,
        callee: &Expr,
        type_args: &[TypeAnnotation],
        args: &[CallArg],
        level: Level,
        wants: &mut Wants,
    ) -> InferTy {
        let returns = self.session.new_ty_meta_var(level);
        let callee_ty = if !type_args.is_empty()
            && let Some(scheme) = self.lookup_named_scheme(callee)
        {
            let type_args_tys: Vec<(InferTy, NodeID)> = type_args
                .iter()
                .map(|arg| (self.infer_type_annotation(&arg.kind, level, wants), arg.id))
                .collect();
            scheme.instantiate_with_args(
                callee.id,
                &type_args_tys,
                self.session,
                level,
                wants,
                callee.span,
            )
        } else {
            self.infer_expr(callee, level, wants)
        };

        let mut arg_tys = args
            .iter()
            .map(|a| self.infer_expr(&a.value, level, wants))
            .collect_vec();

        // If we're calling a constructor, it needs to take `self` as its first arg.
        if matches!(&callee.kind, ExprKind::Constructor(..)) {
            arg_tys.insert(0, returns.clone());
        }

        let type_arg_tys = type_args
            .iter()
            .map(|t| self.infer_type_annotation(&t.kind, level, wants))
            .collect();

        wants.call(
            callee.id,
            callee_ty,
            arg_tys,
            type_arg_tys,
            returns.clone(),
            None,
            ConstraintCause::Call(id),
            callee.span,
        );
        returns
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, wants, expr))]
    fn infer_block(&mut self, expr: &Block, level: Level, wants: &mut Wants) -> InferTy {
        let graph = self.collect_scc_graph(
            &expr
                .body
                .iter()
                .filter_map(|n| {
                    if let Node::Decl(decl) = n {
                        Some(decl.clone())
                    } else {
                        None
                    }
                })
                .collect_vec(),
        );
        self.infer_scc_graph(level, &graph);

        let mut ret = InferTy::Void;
        for node in &expr.body {
            ret = self.infer_node(node, level, wants);
        }
        ret
    }

    // Checks
    #[allow(clippy::too_many_arguments)]
    #[instrument(skip(self, wants, body))]
    fn check_func(
        &mut self,
        params: &[Parameter],
        ret: &Option<TypeAnnotation>,
        body: &Block,
        expected_params: Vec<InferTy>,
        expected_ret: InferTy,
        level: Level,
        wants: &mut Wants,
    ) {
        for (param, expected_param_ty) in params.iter().zip(expected_params) {
            self.session
                .insert_mono(param.name.symbol(), expected_param_ty);
        }

        if let Some(ret) = ret {
            let ret_ty = self.infer_type_annotation(&ret.kind, level, wants);
            wants.equals(
                ret_ty,
                expected_ret.clone(),
                ConstraintCause::Annotation(ret.id),
                ret.span,
            );
        }

        self.check_body(body, expected_ret.clone(), level, wants);
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
                let (params, ret) = uncurry_function(expected);
                self.check_func(
                    &func.params,
                    &func.ret,
                    &func.body,
                    params,
                    ret,
                    level,
                    wants,
                );
            }
            _ => todo!(),
        }
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

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn check_pattern(
        &mut self,
        pattern: &Pattern,
        expected: &InferTy,
        level: Level,
        wants: &mut Wants,
    ) {
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
                wants.equals(
                    expected.clone(),
                    InferTy::Int,
                    ConstraintCause::Pattern(pattern.id),
                    pattern.span,
                );
            }
            PatternKind::LiteralFloat(_) => {
                wants.equals(
                    expected.clone(),
                    InferTy::Float,
                    ConstraintCause::Pattern(pattern.id),
                    pattern.span,
                );
            }
            PatternKind::LiteralFalse | PatternKind::LiteralTrue => {
                wants.equals(
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

                wants.equals(
                    expected.clone(),
                    InferTy::Tuple(metas.clone()),
                    ConstraintCause::Pattern(pattern.id),
                    pattern.span,
                );

                for (pi, bi) in patterns.iter().zip(metas) {
                    self.check_pattern(pi, &bi, level, wants);
                }
            }
            PatternKind::Record { fields } => {
                let expected_row =
                    self.ensure_row_record(pattern.id, pattern.span, expected, level, wants);
                for field in fields {
                    match &field.kind {
                        RecordFieldPatternKind::Bind(name) => {
                            // fresh meta for the field type
                            let field_ty = self.session.new_ty_meta_var(level);

                            // bind the pattern name
                            self.session.insert_mono(name.symbol(), field_ty.clone());

                            // ONE RowHas per field, all referring to the same row
                            wants._has_field(
                                expected_row.clone(),
                                name.name_str().into(),
                                field_ty,
                                ConstraintCause::Pattern(field.id),
                                pattern.span,
                            );
                        }
                        RecordFieldPatternKind::Equals { name, value, .. } => {
                            // optional: pattern field = subpattern; same RowHas then recurse on value
                            let field_ty = self.session.new_ty_meta_var(level);
                            wants._has_field(
                                expected_row.clone(),
                                name.name_str().into(),
                                field_ty.clone(),
                                ConstraintCause::Pattern(field.id),
                                pattern.span,
                            );
                            self.check_pattern(value, &field_ty, level, wants);
                        }
                        RecordFieldPatternKind::Rest => {}
                    }
                }
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

                wants.member(
                    pattern.id,
                    expected.clone(),
                    variant_name.into(),
                    payload,
                    ConstraintCause::Pattern(pattern.id),
                    pattern.span,
                );

                // Recursively check each field pattern
                for (field_pattern, field_ty) in fields.iter().zip(field_metas) {
                    self.check_pattern(field_pattern, &field_ty, level, wants);
                }
            }
            PatternKind::Wildcard => (),
            PatternKind::Struct { .. } => todo!(),
        }
    }

    fn ensure_row_record(
        &mut self,
        id: NodeID,
        span: Span,
        expected: &InferTy,
        level: Level,
        wants: &mut Wants,
    ) -> InferRow {
        match expected {
            InferTy::Record(box row) => row.clone(),
            _ => {
                let row = self.session.new_row_meta_var(level);
                wants.equals(
                    expected.clone(),
                    InferTy::Record(Box::new(row.clone())),
                    ConstraintCause::Member(id),
                    span,
                );
                row
            }
        }
    }

    pub fn collect_scc_graph(&mut self, nodes: &[Decl]) -> SCCGraph {
        let mut pass = ElaborationPass {
            canonical_row_vars: self.session.elaborated_types.canonical_row_vars.clone(),
            canonical_type_params: self.session.elaborated_types.canonical_type_params.clone(),
            type_param_conformances: self
                .session
                .elaborated_types
                .type_param_conformances
                .clone(),

            session: self.session,
        };

        let types = ElaboratedTypes::<RegisteredNames>::default();
        let types_registered =
            pass.register_type_names(types, nodes.iter(), &mut Default::default());

        let elaborated_infer_tys = pass.elaborate_to_infer_tys(types_registered, nodes.iter());
        let elaborated_schemes = pass.elaborate_to_schemes(elaborated_infer_tys, nodes.iter());

        elaborated_schemes.scc_graph
    }

    fn lookup_named_scheme(&mut self, expr: &Expr) -> Option<Scheme<InferTy>> {
        if let ExprKind::Variable(Name::Resolved(sym, _)) = &expr.kind
            && let Some(EnvEntry::Scheme(scheme)) = self.session.lookup(sym)
        {
            return Some(scheme.clone());
        }

        None
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
        ElaborationPass::drive(asts.as_slice(), &mut session);
        InferencePass::drive(asts.as_mut_slice(), &mut session);
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
