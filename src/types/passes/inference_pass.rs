use crate::types::type_session::TypeDef;
use crate::types::wants::Wants;
use crate::{
    ast::{AST, ASTPhase},
    diagnostic::Diagnostic,
    label::Label,
    name::Name,
    name_resolution::{
        name_resolver::NameResolved,
        symbol::{Symbol, TypeId},
    },
    node::Node,
    node_id::NodeID,
    node_kinds::{
        block::Block,
        call_arg::CallArg,
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        func::Func,
        match_arm::MatchArm,
        pattern::{Pattern, PatternKind, RecordFieldPatternKind},
        record_field::RecordField,
        stmt::{Stmt, StmtKind},
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
    span::Span,
    types::{
        constraints::constraint::{Constraint, ConstraintCause},
        passes::dependencies_pass::{Binder, SCCResolved},
        row::{Row, RowMetaId},
        scheme::Scheme,
        term_environment::{EnvEntry, TermEnv},
        ty::{Level, Ty, UnificationVarId},
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, apply, substitute, unify},
        type_session::{TypeDefKind, TypeSession, TypingPhase},
        type_snapshot::TypeSnapshot,
    },
};
use derive_visitor::{Drive, Visitor};
use petgraph::algo::kosaraju_scc;
use rustc_hash::{FxHashMap, FxHashSet};
use tracing::instrument;

#[derive(Debug, PartialEq, Clone)]
pub struct Inferenced {
    pub types_by_node: FxHashMap<NodeID, Ty>,
}

impl TypingPhase for Inferenced {
    type Next = Inferenced;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Meta {
    Ty(UnificationVarId),
    Row(RowMetaId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct MetaTag {
    pub id: UnificationVarId,
    pub level: Level,
}

#[derive(Debug)]
pub struct BindingGroup {
    binders: Vec<Binder>,
    level: Level,
}

#[derive(Debug)]
pub struct InferenceSolution {
    pub diagnostics: Vec<Diagnostic<TypeError>>,
    pub types_by_node: FxHashMap<NodeID, Ty>,
}

/// Perform the rest of type inference for this AST. By now we shouldn't care about
/// scope stacks since everything should already be in the flat term env.
#[derive(Debug)]
pub struct InferencePass<'a> {
    ast: &'a mut AST<NameResolved>,
    types_by_node: FxHashMap<NodeID, Ty>,
    snapshots: Vec<TypeSnapshot>,
    #[allow(dead_code)]
    protocols: FxHashMap<TypeId, TypeDef<Ty>>,

    pub(crate) session: TypeSession<SCCResolved>,
}

impl<'a> InferencePass<'a> {
    pub fn perform(
        session: TypeSession<SCCResolved>,
        ast: &'a mut AST<NameResolved>,
    ) -> TypeSession<Inferenced> {
        let groups = kosaraju_scc(&session.phase.graph);
        let mut pass = InferencePass {
            ast,
            types_by_node: Default::default(),
            session,
            snapshots: Default::default(),
            protocols: Default::default(),
        };

        // Handle binders
        for binders in groups {
            let globals: Vec<_> = binders
                .into_iter()
                .filter(|b| {
                    matches!(
                        b,
                        Binder::Global(_) | Binder::InstanceMethod(..) | Binder::StaticMethod(..)
                    )
                })
                .collect();
            if globals.is_empty() {
                continue;
            }

            let group = BindingGroup {
                binders: globals,
                level: Level(1),
            };

            let wants = pass.infer_group(&group);
            let (mut subs, unsolved) = pass.solve(Level(1), wants);
            pass.promote_group(&group, &mut subs, unsolved);
            pass.apply_to_self(&mut subs);
        }

        let roots = pass.ast.roots.clone();

        for root in roots.iter() {
            if !matches!(root, Node::Stmt(_)) {
                continue;
            }

            let mut wants = Wants::default();
            let ty = pass.infer_node(root, Level(1), &mut wants);
            pass.types_by_node.insert(root.node_id(), ty);
            let (mut subs, _) = pass.solve(Level(1), wants);
            pass.apply_to_self(&mut subs);
        }

        _ = std::mem::replace(&mut pass.ast.roots, roots);

        pass.annotate_uses_after_inference();

        let phase = Inferenced {
            types_by_node: pass.types_by_node,
        };

        pass.session.advance(phase)
    }

    #[instrument(skip(self))]
    fn infer_group(&mut self, group: &BindingGroup) -> Wants {
        let mut wants = Wants::default();
        let inner_level = group.level.next();

        for &binder in &group.binders {
            let symbol = Symbol::from(binder);

            if self.session.term_env.lookup(&symbol).is_none() {
                let ty = self.session.new_ty_meta_var(inner_level);
                self.session.term_env.insert_mono(symbol, ty);
            }
        }

        for &binder in &group.binders {
            let symbol = Symbol::from(binder);
            let Some(rhs_expr_id) = self.session.phase.rhs_map.get(&binder).copied() else {
                continue;
            };

            let rhs_expr = self.ast.find(rhs_expr_id).clone().unwrap();
            let got = self.infer_node(&rhs_expr, inner_level, &mut wants);
            self.types_by_node.insert(rhs_expr_id, got.clone());

            let tv = match self.session.term_env.lookup(&symbol).cloned() {
                Some(EnvEntry::Mono(t)) => t.clone(),
                Some(EnvEntry::Scheme(scheme)) => scheme.ty,
                _ => unreachable!(
                    "no env entry found for {symbol:?} {:#?}",
                    self.session.term_env
                ),
            };

            if let Some(annotation_id) = self.session.phase.annotation_map.get(&binder).cloned() {
                let Some(Node::TypeAnnotation(annotation)) = self.ast.find(annotation_id) else {
                    panic!("didn't find type annotation for annotation id");
                };

                let annotation_ty =
                    self.infer_type_annotation(&annotation, inner_level, &mut wants);
                wants.equals(
                    got.clone(),
                    annotation_ty,
                    ConstraintCause::Annotation(annotation_id),
                    annotation.span,
                );
            }

            wants.equals(got, tv, ConstraintCause::Internal, rhs_expr.span());
        }

        wants
    }

    #[instrument(skip(self))]
    pub(crate) fn infer_type_annotation(
        &mut self,
        annotation: &TypeAnnotation,
        level: Level,
        wants: &mut Wants,
    ) -> Ty {
        match &annotation.kind {
            TypeAnnotationKind::Func { .. } => todo!(),
            TypeAnnotationKind::Tuple(..) => todo!(),
            TypeAnnotationKind::Nominal {
                name: Name::Resolved(sym, _),
                ..
            }
            | TypeAnnotationKind::SelfType(Name::Resolved(sym, _)) => {
                match self.session.term_env.lookup(sym).unwrap().clone() {
                    EnvEntry::Mono(ty) => ty.clone(),
                    EnvEntry::Scheme(scheme) => {
                        scheme
                            .inference_instantiate(&mut self.session, level, wants, annotation.span)
                            .0
                    }
                }
            }
            TypeAnnotationKind::Record { fields } => {
                let mut row = Row::Empty(TypeDefKind::Struct);
                for field in fields.iter().rev() {
                    row = Row::Extend {
                        row: Box::new(row),
                        label: field.label.name_str().into(),
                        ty: self.infer_type_annotation(&field.value, level, wants),
                    };
                }

                Ty::Record(Box::new(row))
            }
            _ => unreachable!(),
        }
    }

    #[instrument(skip(self), level = tracing::Level::TRACE)]
    fn apply_to_self(&mut self, substitutions: &mut UnificationSubstitutions) {
        for (_, ty) in self.types_by_node.iter_mut() {
            if matches!(ty, Ty::Primitive(_)) {
                continue;
            }

            *ty = apply(ty.clone(), substitutions);
        }
    }

    #[instrument(skip(self))]
    fn solve(
        &mut self,
        level: Level,
        mut wants: Wants,
    ) -> (UnificationSubstitutions, Vec<Constraint>) {
        let mut substitutions = UnificationSubstitutions::new(self.session.meta_levels.clone());
        let mut unsolved = vec![];
        loop {
            let mut made_progress = false;
            let mut next_wants = Wants::default();
            while let Some(want) = wants.pop() {
                let want = want.apply(&mut substitutions);
                tracing::trace!("solving {want:?}");

                let solution = match want {
                    Constraint::Construction(ref construction) => construction.solve(
                        &mut self.session,
                        level,
                        &mut next_wants,
                        &mut substitutions,
                    ),
                    Constraint::Equals(ref equals) => unify(
                        &equals.lhs,
                        &equals.rhs,
                        &mut substitutions,
                        &mut self.session.vars,
                    ),
                    Constraint::Call(ref call) => {
                        call.solve(&mut self.session, &mut next_wants, &mut substitutions)
                    }
                    Constraint::Member(ref member) => member.solve(
                        &mut self.session,
                        level,
                        &mut next_wants,
                        &mut substitutions,
                    ),
                    Constraint::HasField(ref has_field) => has_field.solve(
                        &mut self.session,
                        level,
                        &mut next_wants,
                        &mut substitutions,
                    ),
                };

                match solution {
                    Ok(did_make_progress) => {
                        made_progress |= did_make_progress;
                    }
                    Err(e) => {
                        self.ast
                            .diagnostics
                            .push(crate::diagnostic::AnyDiagnostic::Typing(Diagnostic {
                                path: self.ast.path.clone(),
                                span: want.span(),
                                kind: e,
                            }));
                        made_progress = false;
                    }
                }
            }

            if !made_progress || next_wants.is_empty() {
                unsolved.extend(next_wants.to_vec());
                break;
            }

            wants = next_wants;
        }

        self.apply_to_self(&mut substitutions);

        // Apply our substitutions to the unsolved constraints
        let unsolved = unsolved
            .into_iter()
            .map(|c| c.apply(&mut substitutions))
            .collect();

        #[cfg(debug_assertions)]
        {
            let snapshot = TypeSnapshot {
                generation: self.snapshots.len() + 1,
                ast: self.ast.clone(),
                substitutions: substitutions.clone(),
                types_by_node: self.types_by_node.clone(),
            };

            tracing::trace!("{snapshot:?}");
            self.snapshots.push(snapshot);
        }

        (substitutions, unsolved)
    }

    #[instrument(skip(self))]
    fn annotate_uses_after_inference(&mut self) {
        let mut visitor = AnnotateUsesAfterInferenceVisitor {
            term_env: &mut self.session.term_env,
            types_by_node: &mut self.types_by_node,
        };

        for root in &self.ast.roots {
            root.drive(&mut visitor);
        }
    }

    #[instrument(skip(self))]
    fn promote_group(
        &mut self,
        group: &BindingGroup,
        subs: &mut UnificationSubstitutions,
        predicates: Vec<Constraint>,
    ) {
        for &binder in &group.binders {
            let sym = Symbol::from(binder);

            match self.session.term_env.lookup(&sym).cloned() {
                Some(EnvEntry::Mono(ty)) => {
                    let applied = apply(ty, subs);
                    let scheme = self.session.generalize(group.level, applied, &predicates);
                    self.session.term_env.promote(sym, scheme);
                }
                Some(EnvEntry::Scheme(_scheme)) => {}
                None => panic!("didn't find {sym:?} in term env"),
            }
        }
    }

    #[instrument(skip(self))]
    fn infer_node(&mut self, node: &Node, level: Level, wants: &mut Wants) -> Ty {
        match node {
            Node::Expr(expr) => self.infer_expr(expr, level, wants),
            Node::Stmt(stmt) => self.infer_stmt(stmt, level, wants),
            Node::Decl(decl) => self.infer_decl(decl, level, wants),
            Node::Block(block) => self.infer_block(block, level, wants),
            _ => todo!("don't know how to handle {node:?}"),
        }
    }

    #[instrument(skip(self))]
    fn infer_decl(&mut self, decl: &Decl, level: Level, wants: &mut Wants) -> Ty {
        match &decl.kind {
            DeclKind::Let {
                lhs,
                value,
                type_annotation: _,
            } => {
                let ty = self.session.new_ty_meta_var(level);
                self.check_pattern(lhs, &ty, level, wants);

                let mut rhs_wants = Wants::default();
                if let Some(expr) = value {
                    let rhs_ty = self.infer_expr(expr, level.next(), &mut rhs_wants);
                    rhs_wants.equals(
                        ty.clone(),
                        rhs_ty,
                        ConstraintCause::Assignment(decl.id),
                        expr.span,
                    );
                }

                let (mut subs, unsolved) = self.solve(level, rhs_wants);
                let applied_ty = apply(ty.clone(), &mut subs);

                if let PatternKind::Bind(Name::Resolved(sym, _)) = lhs.kind {
                    let scheme = self
                        .session
                        .generalize(level, applied_ty.clone(), &unsolved);
                    self.session.term_env.promote(sym, scheme);
                }

                ty
            }
            DeclKind::Method { func, .. } => {
                let func_ty = self.infer_func(func, level, wants);
                let entry = self.session.generalize(level, func_ty.clone(), &[]);
                self.session
                    .term_env
                    .promote(func.name.symbol().unwrap(), entry);
                func_ty
            }
            DeclKind::Struct { body, .. } => self.infer_block(body, level, wants),
            DeclKind::Property { .. } => Ty::Void,

            _ => todo!("unhandled: {decl:?}"),
        }
    }

    #[instrument(skip(self))]
    fn check_pattern(&mut self, pattern: &Pattern, expected: &Ty, level: Level, wants: &mut Wants) {
        let Pattern { kind, .. } = &pattern;

        match kind {
            PatternKind::Bind(Name::Raw(name)) => {
                panic!("Unresolved name in pattern: {name:?}");
            }
            PatternKind::Bind(Name::Resolved(sym, _)) => {
                self.session.term_env.insert_mono(*sym, expected.clone());
            }
            PatternKind::Bind(Name::SelfType) => {
                todo!()
            }
            PatternKind::LiteralInt(_) => {
                wants.equals(
                    expected.clone(),
                    Ty::Int,
                    ConstraintCause::Pattern(pattern.id),
                    pattern.span,
                );
            }
            PatternKind::LiteralFloat(_) => {
                wants.equals(
                    expected.clone(),
                    Ty::Float,
                    ConstraintCause::Pattern(pattern.id),
                    pattern.span,
                );
            }
            PatternKind::LiteralFalse | PatternKind::LiteralTrue => {
                wants.equals(
                    expected.clone(),
                    Ty::Bool,
                    ConstraintCause::Pattern(pattern.id),
                    pattern.span,
                );
            }
            PatternKind::Tuple(patterns) => {
                let metas: Vec<Ty> = (0..patterns.len())
                    .map(|_| self.session.new_ty_meta_var(level))
                    .collect();

                wants.equals(
                    expected.clone(),
                    Ty::Tuple(metas.clone()),
                    ConstraintCause::Pattern(pattern.id),
                    pattern.span,
                );

                for (pi, bi) in patterns.iter().zip(metas) {
                    self.check_pattern(pi, &bi, level, wants);
                }
            }
            PatternKind::Record { fields } => {
                let expected_row = self.ensure_row_record(
                    pattern.id,
                    pattern.span,
                    expected,
                    level,
                    wants,
                    TypeDefKind::Struct,
                );
                for field in fields {
                    match &field.kind {
                        RecordFieldPatternKind::Bind(name) => {
                            // fresh meta for the field type
                            let field_ty = self.session.new_ty_meta_var(level);

                            // bind the pattern name
                            self.session.term_env.insert_mono(
                                name.symbol().expect("did not resolve name"),
                                field_ty.clone(),
                            );

                            // ONE RowHas per field, all referring to the same row
                            wants._has_field(
                                expected_row.clone(),
                                name.name_str().into(),
                                field_ty,
                                ConstraintCause::Pattern(field.id),
                                pattern.span,
                            );
                        }
                        RecordFieldPatternKind::Equals { name, value } => {
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
                let field_metas: Vec<Ty> = fields
                    .iter()
                    .map(|_| self.session.new_ty_meta_var(level))
                    .collect();
                let payload = if fields.is_empty() {
                    expected.clone()
                } else if fields.len() == 1 {
                    Ty::Func(field_metas[0].clone().into(), expected.clone().into())
                } else {
                    curry(field_metas.clone(), expected.clone())
                };

                wants.member(
                    expected.clone(),
                    variant_name.into(),
                    payload,
                    ConstraintCause::Pattern(pattern.id),
                    pattern.span,
                );

                // wants._has_field(*row.clone(), variant_name.into(), payload);

                // Recursively check each field pattern
                for (field_pattern, field_ty) in fields.iter().zip(field_metas) {
                    self.check_pattern(field_pattern, &field_ty, level, wants);
                }
            }
            PatternKind::Wildcard => todo!(),
            PatternKind::Struct { .. } => todo!(),
        }
    }

    #[instrument(skip(self), ret)]
    fn ensure_row_record(
        &mut self,
        id: NodeID,
        span: Span,
        expected: &Ty,
        level: Level,
        wants: &mut Wants,
        kind: TypeDefKind,
    ) -> Row {
        match expected {
            Ty::Record(box row) => row.clone(),
            _ => {
                let row = self.session.new_row_meta_var(level);
                wants.equals(
                    expected.clone(),
                    Ty::Record(Box::new(row.clone())),
                    ConstraintCause::Member(id),
                    span,
                );
                row
            }
        }
    }

    #[instrument(skip(self))]
    fn infer_block(&mut self, block: &Block, level: Level, wants: &mut Wants) -> Ty {
        // Very simple semantics: return the type of the last expression statement, else Void.
        // TODO: Handle explicit returns
        let mut last_ty = Ty::Void;
        for node in &block.body {
            match node {
                Node::Stmt(stmt) => {
                    last_ty = self.infer_stmt(stmt, level, wants);
                }
                Node::Decl(decl) => {
                    self.infer_decl(decl, level, wants);
                }
                _ => unreachable!("no {node:?} allowed in block body"),
            }
        }
        last_ty
    }

    #[instrument(skip(self))]
    fn lookup_named_scheme(&self, expr: &Expr) -> Option<Scheme> {
        if let ExprKind::Variable(Name::Resolved(sym, _)) = &expr.kind
            && let Some(EnvEntry::Scheme(scheme)) = self.session.term_env.lookup(sym)
        {
            return Some(scheme.clone());
        }

        None
    }

    #[instrument(skip(self))]
    fn infer_expr(&mut self, expr: &Expr, level: Level, wants: &mut Wants) -> Ty {
        let ty = match &expr.kind {
            ExprKind::Incomplete(..) => Ty::Void,
            ExprKind::LiteralArray(..) => todo!(),
            ExprKind::LiteralInt(_) => Ty::Int,
            ExprKind::LiteralFloat(_) => Ty::Float,
            ExprKind::LiteralTrue => Ty::Bool,
            ExprKind::LiteralFalse => Ty::Bool,
            ExprKind::Variable(Name::Resolved(sym, _)) => {
                match self.session.term_env.lookup(sym).cloned() {
                    Some(EnvEntry::Scheme(scheme)) => {
                        scheme
                            .inference_instantiate(&mut self.session, level, wants, expr.span)
                            .0
                    } // or pass through
                    Some(EnvEntry::Mono(t)) => t.clone(),
                    None => {
                        panic!(
                            "variable not found in term env: {:?}, {:?}",
                            sym, self.session.term_env
                        )
                    }
                }
            }
            ExprKind::LiteralString(_) => todo!(),
            ExprKind::Unary(..) => todo!(),
            ExprKind::Binary(..) => todo!(),
            ExprKind::Tuple(items) => Ty::Tuple(
                items
                    .iter()
                    .map(|t| self.infer_expr(t, level, wants))
                    .collect(),
            ),
            ExprKind::Block(block) => self.infer_block(block, level, wants),
            ExprKind::Call {
                callee,
                type_args,
                args,
            } => self.infer_call(callee, type_args, args, level, wants),
            ExprKind::Member(receiver, label) => {
                self.infer_member(expr.id, receiver, label, level, wants)
            }
            ExprKind::Func(func) => self.infer_func(func, level, wants),
            ExprKind::If(box cond, conseq, alt) => {
                let cond_ty = self.infer_expr(cond, level, wants);
                wants.equals(
                    cond_ty,
                    Ty::Bool,
                    ConstraintCause::Condition(cond.id),
                    cond.span,
                );

                let conseq_ty = self.infer_block(conseq, level, wants);
                let alt_ty = self.infer_block(alt, level, wants);

                wants.equals(
                    conseq_ty.clone(),
                    alt_ty,
                    ConstraintCause::Condition(alt.id),
                    conseq.span,
                );
                conseq_ty
            }
            ExprKind::Match(scrutinee, arms) => self.infer_match(scrutinee, arms, level, wants),
            ExprKind::RecordLiteral { fields, spread } => {
                self.infer_record_literal(fields, spread, level, wants)
            }
            ExprKind::Constructor(Name::Resolved(Symbol::Type(id), _)) => Ty::Constructor {
                type_id: *id,
                params: vec![],
                ret: Ty::Void.into(),
            },
            ExprKind::RowVariable(..) => todo!(),

            _ => todo!(),
        };

        // // record the type for this expression node
        self.types_by_node.insert(expr.id, ty.clone());
        ty
    }

    #[instrument(skip(self))]
    fn infer_member(
        &mut self,
        id: NodeID,
        receiver: &Option<Box<Expr>>,
        label: &Label,
        level: Level,
        wants: &mut Wants,
    ) -> Ty {
        let receiver_ty = if let Some(receiver) = &receiver {
            self.infer_expr(receiver, level, wants)
        } else {
            self.session.new_ty_meta_var(level)
        };

        let member_ty = self.session.new_ty_meta_var(level);

        wants.member(
            receiver_ty,
            label.clone(),
            member_ty.clone(),
            ConstraintCause::Member(id),
            receiver
                .as_ref()
                .map(|r| r.span)
                .unwrap_or(Span { start: 0, end: 0 }),
        );

        member_ty
    }

    #[instrument(skip(self))]
    fn infer_record_literal(
        &mut self,
        fields: &[RecordField],
        spread: &Option<Box<Expr>>,
        level: Level,
        wants: &mut Wants,
    ) -> Ty {
        let mut row = Row::Empty(TypeDefKind::Struct);
        for field in fields.iter().rev() {
            row = Row::Extend {
                row: Box::new(row),
                label: field.label.name_str().into(),
                ty: self.infer_expr(&field.value, level, wants),
            };
        }

        Ty::Record(Box::new(row))
    }

    #[instrument(skip(self))]
    fn infer_match(
        &mut self,
        scrutinee: &Expr,
        arms: &[MatchArm],
        level: Level,
        wants: &mut Wants,
    ) -> Ty {
        let mut last_arm_ty: Option<Ty> = None;
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

        last_arm_ty.unwrap_or(Ty::Void)
    }

    #[instrument(skip(self))]
    fn infer_call(
        &mut self,
        callee: &Expr,
        type_args: &[TypeAnnotation],
        args: &[CallArg],
        level: Level,
        wants: &mut Wants,
    ) -> Ty {
        let callee_ty = if !type_args.is_empty()
            && let Some(scheme) = self.lookup_named_scheme(callee)
        {
            let type_args_tys: Vec<(Ty, NodeID)> = type_args
                .iter()
                .map(|arg| (self.infer_type_annotation(arg, level, wants), arg.id))
                .collect();
            scheme.instantiate_with_args(
                &type_args_tys,
                &mut self.session,
                level,
                wants,
                callee.span,
            )
        } else {
            self.infer_expr(callee, level, wants)
        };

        let mut arg_tys = Vec::with_capacity(args.len() + 1);

        for arg in args {
            arg_tys.push(self.infer_expr(&arg.value, level, wants));
        }

        let returns = self.session.new_ty_meta_var(level);
        let receiver = if let Expr {
            kind: ExprKind::Member(receiver, _),
            ..
        } = &callee
        {
            let receiver_ty = if let Some(receiver) = receiver {
                self.infer_expr(receiver, level, wants)
            } else {
                self.session.new_ty_meta_var(level)
            };

            Some(receiver_ty)
        } else {
            None
        };

        if let ExprKind::Constructor(Name::Resolved(sym, _)) = &callee.kind {
            wants.construction(
                callee_ty,
                arg_tys,
                returns.clone(),
                *sym,
                ConstraintCause::Call(callee.id),
                callee.span,
            );
        } else {
            wants.call(
                callee_ty,
                arg_tys,
                returns.clone(),
                receiver,
                ConstraintCause::Call(callee.id),
                callee.span,
            );
        }

        returns
    }

    #[instrument(skip(self))]
    fn infer_func(&mut self, func: &Func, level: Level, wants: &mut Wants) -> Ty {
        let mut skolem_map = FxHashMap::default();
        for generic in func.generics.iter() {
            let skolem_id = self.session.vars.skolems.next_id();
            let param_id = self.session.vars.type_params.next_id();
            skolem_map.insert(Ty::Rigid(skolem_id), Ty::Param(param_id));

            self.session.term_env.insert_mono(
                generic.name.symbol().expect("did not get symbol"),
                Ty::Rigid(skolem_id),
            );

            for conf in &generic.conformances {
                use crate::name::Name;
                use crate::name_resolution::symbol::Symbol;
                use crate::node_kinds::type_annotation::TypeAnnotationKind;

                let Some(proto_id) = (match &conf.kind {
                    TypeAnnotationKind::Nominal {
                        name: Name::Resolved(Symbol::Type(id), _),
                        ..
                    } => Some(*id),
                    _ => None,
                }) else {
                    continue;
                };

                let Some(protocol) = self.session.phase.type_catalog.protocols.get(&proto_id)
                else {
                    continue;
                };

                for (label, req_sym) in &protocol.method_requirements {
                    // requirement result type from env (e.g., Int for `func getCount() -> Int`)
                    let req_ret = match self.session.term_env.lookup(req_sym).cloned() {
                        Some(EnvEntry::Mono(t)) => t,
                        Some(EnvEntry::Scheme(s)) => s.ty,
                        None => continue,
                    };

                    // instance method on the generic: (T) -> ReqRet
                    let method_ty = Ty::Func(Box::new(Ty::Rigid(skolem_id)), Box::new(req_ret));

                    // tell the solver: a T that conforms to this protocol has that member with that type
                    wants.member(
                        Ty::Rigid(skolem_id),
                        label.clone(),
                        method_ty,
                        ConstraintCause::Internal,
                        generic.span,
                    );
                }
            }
        }

        let mut param_tys: Vec<Ty> = Vec::with_capacity(func.params.len());
        for param in &func.params {
            let ty = if let Some(type_annotation) = &param.type_annotation {
                self.infer_type_annotation(type_annotation, level, wants)
            } else {
                self.session.new_ty_meta_var(level)
            };

            param_tys.push(ty);
        }

        for (p, ty) in func.params.iter().zip(param_tys.iter()) {
            let Name::Resolved(sym, _) = &p.name else {
                panic!("unresolved param");
            };
            tracing::info!("inserting mono: {sym:?} : {ty:?}");
            self.session.term_env.insert_mono(*sym, ty.clone());
        }

        let body_ty = self.infer_block(&func.body, level, wants);
        let ret_ty = if let Some(ret) = &func.ret {
            let annotated_ty = self.infer_type_annotation(ret, level, wants);
            wants.equals(
                body_ty,
                annotated_ty.clone(),
                ConstraintCause::Internal,
                ret.span,
            );
            annotated_ty
        } else {
            body_ty
        };

        // Build function type
        let func_ty = if param_tys.is_empty() {
            // zero-arg: Unit -> ret_ty
            Ty::Func(
                Box::new(Ty::Void /* or Ty::Unit */),
                Box::new(ret_ty.clone()),
            )
        } else {
            curry(param_tys, ret_ty.clone())
        };

        substitute(func_ty, &skolem_map)
    }

    #[instrument(skip(self))]
    fn infer_stmt(&mut self, stmt: &Stmt, level: Level, wants: &mut Wants) -> Ty {
        match &stmt.kind {
            StmtKind::Expr(expr) => self.infer_expr(expr, level, wants),
            StmtKind::If(cond, conseq, alt) => {
                self.infer_if_stmt(stmt.id, cond, conseq, alt, level, wants)
            }
            StmtKind::Return(..) => todo!(),
            StmtKind::Break => Ty::Void,
            StmtKind::Assignment(lhs, rhs) => {
                let lhs_ty = self.infer_expr(lhs, level, wants);
                let rhs_ty = self.infer_expr(rhs, level, wants);
                wants.equals(
                    lhs_ty.clone(),
                    rhs_ty,
                    ConstraintCause::Assignment(stmt.id),
                    lhs.span,
                );
                lhs_ty
            }
            StmtKind::Loop(cond, body) => {
                if let Some(cond) = cond {
                    let cond_ty = self.infer_expr(cond, level, wants);
                    wants.equals(
                        cond_ty,
                        Ty::Bool,
                        ConstraintCause::Condition(cond.id),
                        cond.span,
                    );
                }

                self.infer_block(body, level, wants);

                Ty::Void
            }
        }
    }

    fn infer_if_stmt(
        &mut self,
        id: NodeID,
        cond: &Expr,
        conseq: &Block,
        alt: &Option<Block>,
        level: Level,
        wants: &mut Wants,
    ) -> Ty {
        let cond_ty = self.infer_expr(cond, level, wants);
        wants.equals(
            cond_ty,
            Ty::Bool,
            ConstraintCause::Condition(cond.id),
            cond.span,
        );

        let conseq_ty = self.infer_block(conseq, level, wants);
        if let Some(alt) = alt {
            let alt_ty = self.infer_block(alt, level, wants);
            // If both branches exist, unify their types and return the result
            wants.equals(
                conseq_ty.clone(),
                alt_ty,
                ConstraintCause::Condition(id),
                conseq.span,
            );
            conseq_ty
        } else {
            // If no else branch, it's a statement that returns void
            Ty::Void
        }
    }
}

pub fn curry<I: IntoIterator<Item = Ty>>(params: I, ret: Ty) -> Ty {
    params
        .into_iter()
        .collect::<Vec<_>>()
        .into_iter()
        .rfold(ret, |acc, p| Ty::Func(Box::new(p), Box::new(acc)))
}

pub fn collect_meta(ty: &Ty, out: &mut FxHashSet<Ty>) {
    match ty {
        Ty::Param(_) => {
            out.insert(ty.clone());
        }
        Ty::UnificationVar { .. } => {
            out.insert(ty.clone());
        }
        Ty::Func(dom, codom) => {
            collect_meta(dom, out);
            collect_meta(codom, out);
        }
        Ty::Tuple(items) => {
            for item in items {
                collect_meta(item, out);
            }
        }
        Ty::Record(box row) => match row {
            Row::Empty(..) => (),
            Row::Var(..) => {
                out.insert(ty.clone());
            }
            Row::Param(..) => (),
            Row::Extend { row, ty, .. } => {
                collect_meta(ty, out);
                collect_meta(&Ty::Record(row.clone()), out);
            }
        },
        Ty::Nominal { .. } => (),
        Ty::Constructor { params, .. } => {
            for param in params {
                collect_meta(param, out);
            }
        }
        Ty::Primitive(_) | Ty::Rigid(_) | Ty::Hole(_) => {}
    }
}

#[derive(Visitor)]
#[visitor(Expr(enter))]
struct AnnotateUsesAfterInferenceVisitor<'a> {
    term_env: &'a TermEnv,
    types_by_node: &'a mut FxHashMap<NodeID, Ty>,
}
impl<'a> AnnotateUsesAfterInferenceVisitor<'a> {
    fn enter_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Variable(Name::Resolved(name, _)) => match self.term_env.lookup(name) {
                Some(EnvEntry::Mono(ty)) => {
                    tracing::trace!("annotating {name:?}");
                    self.types_by_node.insert(expr.id, ty.clone());
                }
                Some(EnvEntry::Scheme(scheme)) => {
                    tracing::trace!("annotating {name:?}");
                    self.types_by_node.insert(expr.id, scheme.ty.clone());
                }
                _ => tracing::warn!("no type found for use of {:?}", expr),
            },
            ExprKind::Block(..) => todo!(),
            _ => (),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Typed {
    _types_by_node: FxHashMap<NodeID, Ty>,
}
impl ASTPhase for Typed {}

pub struct InferenceResult {
    pub ast: AST<Typed>,
    pub diagnostics: Vec<Diagnostic<TypeError>>,
}
