use derive_visitor::{Drive, Visitor};
use petgraph::algo::kosaraju_scc;
use rustc_hash::{FxHashMap, FxHashSet};
use tracing::instrument;

use crate::{
    ast::{AST, ASTPhase},
    diagnostic::{AnyDiagnostic, Diagnostic},
    id_generator::IDGenerator,
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
        constraints::{Constraint, ConstraintCause, Equals, HasField},
        fields::TypeFields,
        passes::dependencies_pass::{Binder, SCCResolved},
        row::{Row, RowMetaId},
        scheme::{ForAll, Scheme},
        term_environment::{EnvEntry, TermEnv},
        ty::{Level, Ty, TyMetaId},
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, apply, apply_row, substitute, unify},
        type_session::{TypeDef, TypeSession, TypingPhase},
    },
};

#[derive(Debug, PartialEq, Clone)]
pub struct Inferenced {
    pub type_constructors: FxHashMap<TypeId, TypeDef<Ty>>,
    pub protocols: FxHashMap<TypeId, TypeDef<Ty>>,
    pub types_by_node: FxHashMap<NodeID, Ty>,
}

impl TypingPhase for Inferenced {
    type Next = Inferenced;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Meta {
    Ty(TyMetaId),
    Row(RowMetaId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct MetaTag {
    pub id: TyMetaId,
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

#[derive(Debug)]
pub struct InferencePass<'a> {
    ast: &'a mut AST<NameResolved>,
    types_by_node: FxHashMap<NodeID, Ty>,
    metavars: IDGenerator,
    skolems: IDGenerator,
    type_params: IDGenerator,
    row_params: IDGenerator,
    pub(crate) row_meta_generator: IDGenerator,
    term_env: TermEnv,
    session: TypeSession<SCCResolved>,
    meta_levels: FxHashMap<Meta, Level>,
}

#[derive(Debug)]
pub struct Wants(Vec<Constraint>);
impl Wants {
    pub fn push(&mut self, constraint: Constraint) {
        self.0.push(constraint)
    }

    pub fn equals(&mut self, lhs: Ty, rhs: Ty, cause: ConstraintCause) {
        self.0.push(Constraint::Equals(Equals { lhs, rhs, cause }));
    }

    pub fn has_field(
        &mut self,
        row: Row,
        label: Label,
        ty: Ty,
        cause: ConstraintCause,
        span: Span,
    ) {
        self.0.push(Constraint::HasField(HasField {
            row,
            label,
            ty,
            cause,
            span,
        }))
    }
}

impl<'a> InferencePass<'a> {
    pub fn perform(
        session: TypeSession<SCCResolved>,
        ast: &'a mut AST<NameResolved>,
    ) -> TypeSession<Inferenced> {
        let groups = kosaraju_scc(&session.phase.graph);
        let term_env = TermEnv::new();
        let mut pass = InferencePass {
            term_env,
            ast,
            types_by_node: Default::default(),
            metavars: Default::default(),
            skolems: Default::default(),
            type_params: Default::default(),
            row_params: Default::default(),
            row_meta_generator: Default::default(),
            session,
            meta_levels: Default::default(),
        };

        let type_ids: Vec<TypeId> = pass
            .session
            .phase
            .type_constructors
            .keys()
            .copied()
            .collect();
        for id in type_ids {
            pass.define_type(id);
        }

        // Handle binders
        for binders in groups {
            let globals: Vec<_> = binders
                .into_iter()
                .filter(|b| matches!(b, Binder::Global(_)))
                .collect();
            if globals.is_empty() {
                continue;
            }

            let group = BindingGroup {
                binders: globals,
                level: Level(1),
            };

            let wants = pass.infer_group(&group);
            let (mut subs, unsolved) = pass.solve(wants);
            pass.promote_group(&group, &mut subs, unsolved);
            pass.apply_to_self(&mut subs);
        }

        let roots = std::mem::take(&mut pass.ast.roots);

        for root in roots.iter() {
            if !matches!(root, Node::Stmt(_)) {
                continue;
            }

            let mut wants = Wants(vec![]);
            let ty = pass.infer_node(root, Level(1), &mut wants);
            pass.types_by_node.insert(root.node_id(), ty);
            let (mut subs, _) = pass.solve(wants);
            pass.apply_to_self(&mut subs);
        }

        _ = std::mem::replace(&mut pass.ast.roots, roots);

        pass.annotate_uses_after_inference();

        let type_constructors = std::mem::take(&mut pass.session.phase.type_constructors);
        let protocols = std::mem::take(&mut pass.session.phase.protocols);

        let phase = Inferenced {
            type_constructors,
            protocols,
            types_by_node: pass.types_by_node,
        };

        pass.session.advance(phase)
    }

    #[instrument(skip(self))]
    fn define_type(&mut self, type_id: TypeId) {
        let type_def = self
            .session
            .phase
            .type_constructors
            .get(&type_id)
            .expect("didn't find type for type id");

        match &type_def.fields {
            TypeFields::Struct { properties, .. } => {
                let row = properties
                    .iter()
                    .fold(Row::Empty, |mut acc, (label, property)| {
                        acc = Row::Extend {
                            row: Box::new(acc),
                            label: label.clone(),
                            ty: property.ty_repr.clone(),
                        };
                        acc
                    });
                let scheme = Scheme::new(
                    vec![],
                    vec![],
                    Ty::Struct(type_def.name.clone(), Box::new(row)),
                );

                self.term_env
                    .promote(Symbol::Type(type_id), EnvEntry::Scheme(scheme));
            }
            _ => unimplemented!(),
        }
    }

    #[instrument(skip(self))]
    fn infer_group(&mut self, group: &BindingGroup) -> Wants {
        let mut wants = Wants(Default::default());
        let inner_level = group.level.next();

        for &binder in &group.binders {
            let symbol = Symbol::from(binder);
            let ty = self.new_ty_meta_var(inner_level);
            self.term_env.insert_mono(symbol, ty);
        }

        for &binder in &group.binders {
            let symbol = Symbol::from(binder);
            let Some(rhs_expr_id) = self.session.phase.rhs_map.get(&binder).copied() else {
                continue;
            };

            let rhs_expr = self.ast.find(rhs_expr_id).clone();

            let got = self.infer_node(&rhs_expr.unwrap(), inner_level, &mut wants);
            self.types_by_node.insert(rhs_expr_id, got.clone());

            let tv = match self.term_env.lookup(&symbol) {
                Some(EnvEntry::Mono(t)) => t.clone(),
                _ => unreachable!("no env entry found for {symbol:?} {:#?}", self.term_env),
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
                );
            }

            wants.equals(got, tv, ConstraintCause::Internal);
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
            } => match self.term_env.lookup(sym).unwrap().clone() {
                EnvEntry::Mono(ty) => ty.clone(),
                EnvEntry::Scheme(scheme) => scheme.instantiate(self, level, wants, annotation.span),
            },
            TypeAnnotationKind::Record { fields } => {
                let mut row = Row::Empty;
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

    #[instrument(skip(self))]
    fn apply_to_self(&mut self, substitutions: &mut UnificationSubstitutions) {
        for (_, ty) in self.types_by_node.iter_mut() {
            if matches!(ty, Ty::Primitive(_)) {
                continue;
            }

            *ty = apply(ty.clone(), substitutions);
        }
    }

    #[instrument(skip(self))]
    fn solve(&mut self, mut wants: Wants) -> (UnificationSubstitutions, Vec<Constraint>) {
        let mut substitutions = UnificationSubstitutions::new(self.meta_levels.clone());
        let mut unsolved = vec![];
        loop {
            let mut made_progress = false;
            let mut next_wants = Wants(vec![]);
            for want in wants.0.drain(..) {
                tracing::trace!("solving {want:?}");

                let solution = match want {
                    Constraint::Equals(equals) => unify(
                        &equals.lhs,
                        &equals.rhs,
                        &mut substitutions,
                        &mut self.row_meta_generator,
                    ),
                    Constraint::HasField(has_field) => {
                        let row = apply_row(has_field.row.clone(), &mut substitutions);
                        match row {
                            Row::Empty => {
                                self.ast.diagnostics.push(AnyDiagnostic::Typing(Diagnostic {
                                    path: self.ast.path.clone(),
                                    span: has_field.span,
                                    kind: TypeError::MemberNotFound(
                                        Ty::Record(Box::new(has_field.row)),
                                        has_field.label.to_string(),
                                    ),
                                }));
                                Ok(false)
                            }
                            Row::Param(..) => {
                                self.ast.diagnostics.push(AnyDiagnostic::Typing(Diagnostic {
                                    path: self.ast.path.clone(),
                                    span: has_field.span,
                                    kind: TypeError::MemberNotFound(
                                        Ty::Record(Box::new(has_field.row)),
                                        has_field.label.to_string(),
                                    ),
                                }));
                                Ok(false)
                            }
                            Row::Var(..) => {
                                // Keep the constraint for the next iteration with the applied row
                                next_wants.has_field(
                                    row,
                                    has_field.label,
                                    has_field.ty,
                                    ConstraintCause::Internal,
                                    has_field.span,
                                );
                                Ok(false)
                            }
                            Row::Extend { row, label, ty } => {
                                if has_field.label == label {
                                    next_wants.equals(has_field.ty, ty, ConstraintCause::Internal);
                                    tracing::trace!("found match for {label:?}");
                                    Ok(true)
                                } else {
                                    next_wants.has_field(
                                        *row,
                                        has_field.label,
                                        has_field.ty,
                                        ConstraintCause::Internal,
                                        has_field.span,
                                    );

                                    Ok(true)
                                }
                            }
                        }
                    }
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
                                span: Span { start: 0, end: 0 },
                                kind: e,
                            }));
                        made_progress = false;
                    }
                }
            }

            if !made_progress || next_wants.0.is_empty() {
                unsolved.extend(next_wants.0);
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

        (substitutions, unsolved)
    }

    #[instrument(skip(self))]
    fn annotate_uses_after_inference(&mut self) {
        let mut visitor = AnnotateUsesAfterInferenceVisitor {
            term_env: &mut self.term_env,
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

            match self.term_env.lookup(&sym).cloned() {
                Some(EnvEntry::Mono(ty)) => {
                    let applied = apply(ty, subs);
                    let scheme = self.generalize(group.level, applied, &predicates);
                    self.term_env.promote(sym, scheme);
                }
                Some(EnvEntry::Scheme(_scheme)) => {}
                None => panic!("didn't find {sym:?} in term env"),
            }
        }
    }

    #[instrument(skip(self))]
    fn generalize(&mut self, inner: Level, ty: Ty, unsolved: &[Constraint]) -> EnvEntry {
        // collect metas in ty
        let mut metas = FxHashSet::default();
        collect_meta(&ty, &mut metas);

        // keep only metas born at or above inner
        let mut foralls = vec![];
        let mut substitutions = UnificationSubstitutions::new(self.meta_levels.clone());
        for m in &metas {
            match m {
                Ty::Param(p) => {
                    // No substitution needed (the ty already contains Ty::Param(p)),
                    // but we must record it in `foralls`, so instantiate() knows what to replace.
                    if !foralls
                        .iter()
                        .any(|fa| matches!(fa, ForAll::Ty(q) if *q == *p))
                    {
                        foralls.push(ForAll::Ty(*p));
                    }
                }

                Ty::MetaVar { level, id } => {
                    if *level <= inner {
                        tracing::trace!("discarding {m:?} due to level ({level:?} < {inner:?})");
                        continue;
                    }

                    let param_id = self.type_params.next_id();
                    tracing::trace!("generalizing {m:?} to {param_id:?}");
                    foralls.push(ForAll::Ty(param_id));
                    substitutions.ty.insert(*id, Ty::Param(param_id));
                }
                Ty::Record(box Row::Var(id)) => {
                    let level = self
                        .meta_levels
                        .get(&Meta::Row(*id))
                        .expect("didn't get level for row meta");
                    if *level <= inner {
                        tracing::trace!("discarding {m:?} due to level ({level:?} < {inner:?})");
                        continue;
                    }

                    let param_id = self.row_params.next_id();
                    tracing::trace!("generalizing {m:?} to {param_id:?}");
                    foralls.push(ForAll::Row(param_id));
                    substitutions.row.insert(*id, Row::Param(param_id));
                }
                _ => {
                    tracing::warn!("got {m:?} for var while generalizing")
                }
            }
        }

        let ty = apply(ty, &mut substitutions);

        if foralls.is_empty() {
            return EnvEntry::Mono(ty);
        }

        let predicates = unsolved
            .iter()
            .map(|c| c.into_predicate(&mut substitutions))
            .collect();

        EnvEntry::Scheme(Scheme::new(foralls, predicates, ty))
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
                let ty = self.new_ty_meta_var(level);
                self.check_pattern(lhs, &ty, level, wants);

                let mut rhs_wants = Wants(vec![]);
                if let Some(expr) = value {
                    let rhs_ty = self.infer_expr(expr, level.next(), &mut rhs_wants);
                    rhs_wants.equals(ty.clone(), rhs_ty, ConstraintCause::Assignment(decl.id));
                }

                let (mut subs, unsolved) = self.solve(rhs_wants);
                let applied_ty = apply(ty.clone(), &mut subs);

                if let PatternKind::Bind(Name::Resolved(sym, _)) = lhs.kind {
                    let scheme = self.generalize(level, applied_ty.clone(), &unsolved);
                    self.term_env.promote(sym, scheme);
                }

                ty
            }
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
                self.term_env.insert_mono(*sym, expected.clone());
            }
            PatternKind::Bind(Name::_Self | Name::SelfType) => {
                todo!()
            }
            PatternKind::LiteralInt(_) => {
                wants.equals(
                    expected.clone(),
                    Ty::Int,
                    ConstraintCause::Pattern(pattern.id),
                );
            }
            PatternKind::LiteralFloat(_) => {
                wants.equals(
                    expected.clone(),
                    Ty::Float,
                    ConstraintCause::Pattern(pattern.id),
                );
            }
            PatternKind::LiteralFalse | PatternKind::LiteralTrue => {
                wants.equals(
                    expected.clone(),
                    Ty::Bool,
                    ConstraintCause::Pattern(pattern.id),
                );
            }
            PatternKind::Tuple(patterns) => {
                let metas: Vec<Ty> = (0..patterns.len())
                    .map(|_| self.new_ty_meta_var(level))
                    .collect();

                wants.equals(
                    expected.clone(),
                    Ty::Tuple(metas.clone()),
                    ConstraintCause::Pattern(pattern.id),
                );

                for (pi, bi) in patterns.iter().zip(metas) {
                    self.check_pattern(pi, &bi, level, wants);
                }
            }
            PatternKind::Record { fields } => {
                let expected_row = self.ensure_row(pattern.id, expected, level, wants);
                for field in fields {
                    match &field.kind {
                        RecordFieldPatternKind::Bind(name) => {
                            // fresh meta for the field type
                            let field_ty = self.new_ty_meta_var(level);

                            // bind the pattern name
                            self.term_env.insert_mono(
                                name.symbol().expect("did not resolve name"),
                                field_ty.clone(),
                            );

                            // ONE RowHas per field, all referring to the same row
                            wants.has_field(
                                expected_row.clone(),
                                name.name_str().into(),
                                field_ty,
                                ConstraintCause::Pattern(field.id),
                                pattern.span,
                            );
                        }
                        RecordFieldPatternKind::Equals { name, value } => {
                            // optional: pattern field = subpattern; same RowHas then recurse on value
                            let field_ty = self.new_ty_meta_var(level);
                            wants.has_field(
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
            PatternKind::Wildcard => todo!(),
            PatternKind::Variant { .. } => todo!(),
            PatternKind::Struct { .. } => todo!(),
        }
    }

    /// Ensure we have a row to talk about for `expected`.
    /// If `expected` is Ty::Record(row), return that row.
    /// Otherwise create a fresh row var row_var and add Eq(expected, Record(row_var)).
    #[instrument(skip(self), ret)]
    fn ensure_row(&mut self, id: NodeID, expected: &Ty, level: Level, wants: &mut Wants) -> Row {
        match expected {
            Ty::Record(box row) => row.clone(),
            _ => {
                let rho = self.new_row_meta_var(level);
                wants.equals(expected.clone(), rho.clone(), ConstraintCause::Pattern(id));
                let Ty::Record(row) = rho else { unreachable!() };
                *row
            }
        }
    }

    #[instrument(skip(self))]
    fn infer_block(&mut self, block: &Block, level: Level, wants: &mut Wants) -> Ty {
        // Very simple semantics: return the type of the last expression statement, else Void.
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
            && let Some(EnvEntry::Scheme(scheme)) = self.term_env.lookup(sym)
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
                match self.term_env.lookup(sym).cloned() {
                    Some(EnvEntry::Scheme(scheme)) => {
                        scheme.instantiate(self, level, wants, expr.span)
                    } // or pass through
                    Some(EnvEntry::Mono(t)) => t.clone(),
                    None => {
                        panic!(
                            "variable not found in term env: {:?}, {:?}",
                            sym, self.term_env
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
                wants.equals(cond_ty, Ty::Bool, ConstraintCause::Condition(cond.id));

                let conseq_ty = self.infer_block(conseq, level, wants);
                let alt_ty = self.infer_block(alt, level, wants);

                wants.equals(
                    conseq_ty.clone(),
                    alt_ty,
                    ConstraintCause::Condition(alt.id),
                );
                conseq_ty
            }
            ExprKind::Match(scrutinee, arms) => self.infer_match(scrutinee, arms, level, wants),
            ExprKind::RecordLiteral { fields, spread } => {
                self.infer_record_literal(fields, spread, level, wants)
            }
            ExprKind::Constructor(Name::Resolved(sym @ Symbol::Type(id), _)) => {
                let entry = self
                    .term_env
                    .lookup(sym)
                    .cloned()
                    .expect("did not find type for sym in env");

                let ty = match entry {
                    EnvEntry::Mono(ty) => ty.clone(),
                    EnvEntry::Scheme(scheme) => scheme.instantiate(self, level, wants, expr.span),
                };

                let type_def = self
                    .session
                    .phase
                    .type_constructors
                    .get(id)
                    .expect("didn't get type def");

                let TypeFields::Struct { initializers, .. } = &type_def.fields else {
                    panic!("didn't get struct type def for constructor");
                };

                // TODO: handle multiple initializers
                let (_, initializer) = initializers.first().expect("no initializer found");

                curry(initializer.params.clone(), ty)
            }
            ExprKind::RowVariable(..) => todo!(),

            _ => todo!(),
        };

        // record the type for this expression node
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
        let (receiver_row, span) = if let Some(receiver) = receiver {
            let receiver_ty = self.infer_expr(receiver, level, wants);
            match receiver_ty {
                Ty::Record(box row) => (row, receiver.span),
                Ty::MetaVar { .. } => {
                    // Add a constraint saying that receiver needs to be a row
                    let row = self.new_row_meta_var(level);
                    wants.equals(
                        receiver_ty.clone(),
                        row.clone(),
                        ConstraintCause::Member(id),
                    );

                    let Ty::Record(row) = row else {
                        unreachable!();
                    };

                    (*row, receiver.span)
                }
                ty => {
                    self.ast
                        .diagnostics
                        .push(crate::diagnostic::AnyDiagnostic::Typing(Diagnostic {
                            path: self.ast.path.clone(),
                            span: receiver.span,
                            kind: TypeError::ExpectedRow(ty),
                        }));
                    return Ty::Void;
                }
            }
        } else {
            let Ty::Record(box row) = self.new_row_meta_var(level) else {
                unreachable!()
            };

            (row, Span { start: 0, end: 0 })
        };

        let member_ty = self.new_ty_meta_var(level);

        wants.has_field(
            receiver_row,
            label.clone(),
            member_ty.clone(),
            ConstraintCause::Member(id),
            span,
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
        let mut row = Row::Empty;
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
            scheme.instantiate_with_args(type_args, self, level, wants, callee.span)
        } else {
            self.infer_expr(callee, level, wants)
        };

        let mut arg_tys = Vec::with_capacity(args.len());

        for _ in args {
            arg_tys.push(self.new_ty_meta_var(level));
        }

        tracing::trace!("adding returns meta");
        let returns = self.new_ty_meta_var(level);

        if args.is_empty() {
            // zero-arg call: callee must be Unit -> returns
            let expected = Ty::Func(Box::new(Ty::Void /* or Unit */), Box::new(returns.clone()));
            wants.equals(callee_ty, expected, ConstraintCause::Call(callee.id));
            return returns;
        }

        wants.equals(
            callee_ty,
            curry(arg_tys.clone(), returns.clone()),
            ConstraintCause::Call(callee.id),
        );

        for (a, aty) in args.iter().zip(arg_tys) {
            let got = self.infer_expr(&a.value, level, wants);
            wants.equals(got, aty, ConstraintCause::Internal);
        }

        returns
    }

    #[instrument(skip(self))]
    fn infer_func(&mut self, func: &Func, level: Level, wants: &mut Wants) -> Ty {
        let mut skolem_map = FxHashMap::default();
        for generic in func.generics.iter() {
            let skolem_id = self.skolems.next_id();
            let param_id = self.type_params.next_id();
            skolem_map.insert(Ty::Rigid(skolem_id), Ty::Param(param_id));
            self.term_env.insert_mono(
                generic.name.symbol().expect("did not get symbol"),
                Ty::Rigid(skolem_id),
            );
        }

        let mut param_tys: Vec<Ty> = Vec::with_capacity(func.params.len());
        for param in &func.params {
            let ty = if let Some(type_annotation) = &param.type_annotation {
                self.infer_type_annotation(type_annotation, level, wants)
            } else {
                self.new_ty_meta_var(level)
            };

            param_tys.push(ty);
        }

        let ret_ty = if let Some(ret) = &func.ret {
            self.infer_type_annotation(ret, level, wants)
        } else {
            self.new_ty_meta_var(level)
        };

        for (p, ty) in func.params.iter().zip(param_tys.iter()) {
            let Name::Resolved(sym, _) = &p.name else {
                panic!("unresolved param");
            };
            tracing::info!("inserting mono: {sym:?} : {ty:?}");
            self.term_env.insert_mono(*sym, ty.clone());
        }

        let body_ty = self.infer_block(&func.body, level, wants);

        wants.equals(body_ty, ret_ty.clone(), ConstraintCause::Internal);

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
                let cond_ty = self.infer_expr(cond, level, wants);
                wants.equals(cond_ty, Ty::Bool, ConstraintCause::Condition(cond.id));

                let conseq_ty = self.infer_block(conseq, level, wants);
                if let Some(alt) = alt {
                    let alt_ty = self.infer_block(alt, level, wants);
                    // If both branches exist, unify their types and return the result
                    wants.equals(
                        conseq_ty.clone(),
                        alt_ty,
                        ConstraintCause::Condition(stmt.id),
                    );
                    conseq_ty
                } else {
                    // If no else branch, it's a statement that returns void
                    Ty::Void
                }
            }
            StmtKind::Return(..) => todo!(),
            StmtKind::Break => Ty::Void,
            StmtKind::Assignment(lhs, rhs) => {
                let lhs_ty = self.infer_expr(lhs, level, wants);
                let rhs_ty = self.infer_expr(rhs, level, wants);
                wants.equals(lhs_ty.clone(), rhs_ty, ConstraintCause::Assignment(stmt.id));
                lhs_ty
            }
            StmtKind::Loop(cond, body) => {
                if let Some(cond) = cond {
                    let cond_ty = self.infer_expr(cond, level, wants);
                    wants.equals(cond_ty, Ty::Bool, ConstraintCause::Condition(cond.id));
                }

                self.infer_block(body, level, wants);

                Ty::Void
            }
        }
    }

    pub(crate) fn new_ty_meta_var(&mut self, level: Level) -> Ty {
        let id = self.metavars.next_id();
        self.meta_levels.insert(Meta::Ty(id), level);
        tracing::trace!("Fresh {id:?}");
        Ty::MetaVar { id, level }
    }

    pub(crate) fn new_row_meta_var(&mut self, level: Level) -> Ty {
        let id = self.row_meta_generator.next_id();
        self.meta_levels.insert(Meta::Row(id), level);
        tracing::trace!("Fresh {id:?}");
        Ty::Record(Box::new(Row::Var(id)))
    }
}

fn curry<I: IntoIterator<Item = Ty>>(params: I, ret: Ty) -> Ty {
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
        Ty::MetaVar { .. } => {
            out.insert(ty.clone());
        }
        Ty::Func(dom, codom) => {
            collect_meta(dom, out);
            collect_meta(codom, out);
        }
        Ty::TypeApplication(fun, arg) => {
            collect_meta(fun, out);
            collect_meta(arg, out);
        }
        Ty::Tuple(items) => {
            for item in items {
                collect_meta(item, out);
            }
        }
        Ty::Record(box row) => match row {
            Row::Empty => (),
            Row::Var(..) => {
                out.insert(ty.clone());
            }
            Row::Param(..) => (),
            Row::Extend { row, ty, .. } => {
                collect_meta(ty, out);
                collect_meta(&Ty::Record(row.clone()), out);
            }
        },
        Ty::Struct(_, box row) => match row {
            Row::Empty => (),
            Row::Var(..) => {
                out.insert(ty.clone());
            }
            Row::Param(..) => (),
            Row::Extend { row, ty, .. } => {
                collect_meta(ty, out);
                collect_meta(&Ty::Record(row.clone()), out);
            }
        },
        Ty::Primitive(_) | Ty::Rigid(_) | Ty::Hole(_) | Ty::TypeConstructor { .. } => {}
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

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::types::passes::dependencies_pass::tests::resolve_dependencies;

    fn typecheck(code: &'static str) -> (AST<NameResolved>, TypeSession<Inferenced>) {
        let (ast, session) = typecheck_err(code);
        assert!(
            ast.diagnostics.is_empty(),
            "diagnostics not empty: {:?}",
            ast.diagnostics
        );
        (ast, session)
    }

    fn typecheck_err(code: &'static str) -> (AST<NameResolved>, TypeSession<Inferenced>) {
        let (mut ast, session) = resolve_dependencies(code);
        let session = InferencePass::perform(session, &mut ast);
        (ast, session)
    }

    fn ty(i: usize, ast: &AST<NameResolved>, session: &TypeSession<Inferenced>) -> Ty {
        session
            .phase
            .types_by_node
            .get(&ast.roots[i].as_stmt().clone().as_expr().id)
            .unwrap()
            .clone()
    }

    #[test]
    fn types_int_literal() {
        let (ast, session) = typecheck("123");
        assert_eq!(ty(0, &ast, &session), Ty::Int);
    }

    #[test]
    fn types_int() {
        let (ast, session) = typecheck("let a = 123; a");
        assert_eq!(ty(1, &ast, &session), Ty::Int);
    }

    #[test]
    fn types_float() {
        let (ast, session) = typecheck("let a = 1.23; a");
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Float
        );
    }

    #[test]
    fn types_bool() {
        let (ast, session) = typecheck("let a = true; a ; let b = false ; b");
        assert_eq!(ty(1, &ast, &session), Ty::Bool);
        assert_eq!(ty(3, &ast, &session), Ty::Bool);
    }

    #[test]
    fn monomorphic_let_annotation() {
        let (ast, session) = typecheck(
            r#"
        let a: Int = 123
        a
    "#,
        );
        assert_eq!(ty(1, &ast, &session), Ty::Int);
    }

    #[test]
    fn monomorphic_let_annotation_mismatch() {
        let (ast, _session) = typecheck_err(
            r#"
        let a: Bool = 123
        a
    "#,
        );
        assert_eq!(ast.diagnostics.len(), 1);
    }

    #[test]
    fn types_identity() {
        let (ast, session) = typecheck(
            "
        func identity(x) { x }
        identity(123)
        identity(true)
        ",
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Int
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[2].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Bool
        );
    }

    #[test]
    fn types_nested_func() {
        let (ast, session) = typecheck(
            r#"
        func fizz(x) {
            func buzz() { x }
            buzz()
        }

        fizz(123)
        "#,
        );

        assert_eq!(ty(1, &ast, &session), Ty::Int);
    }

    #[test]
    fn explicit_generic_function_instantiates() {
        let (ast, session) = typecheck(
            r#"
        func id<T>(x: T) -> T { x }
        id(123)
        id(true)
    "#,
        );

        let call1 = ast.roots[1].as_stmt().clone().as_expr().id;
        let call2 = ast.roots[2].as_stmt().clone().as_expr().id;

        assert_eq!(*session.phase.types_by_node.get(&call1).unwrap(), Ty::Int);
        assert_eq!(*session.phase.types_by_node.get(&call2).unwrap(), Ty::Bool);
    }

    #[test]
    fn generic_function_body_must_respect_its_own_type_vars() {
        let (ast, _session) = typecheck_err(
            r#"
        func bad<T>(x: T) -> T { 0 } // 0 == Int != T
        bad(true)
    "#,
        );
        assert_eq!(
            ast.diagnostics.len(),
            1,
            "didn't get correct diagnostic: {:?}",
            ast.diagnostics
        );
    }

    #[test]
    fn generalizes_locals() {
        let (ast, session) = typecheck(
            "
        func outer() {
            func id(x) { x }
            (id(123), id(true))
        }

        outer()
        ",
        );

        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Tuple(vec![Ty::Int, Ty::Bool])
        );
    }

    #[test]
    fn types_call_let() {
        let (ast, session) = typecheck(
            "
        func id(x) { x }
        let a = id(123)
        let b = id(1.23)
        a
        b
        ",
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[3].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Int
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[4].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Float
        );
    }

    #[test]
    fn types_nested_identity() {
        let (ast, session) = typecheck(
            "
        func identity(x) { x }
        identity(identity(123))
        identity(identity(true))
        ",
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Int
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[2].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Bool
        );
    }

    #[test]
    fn types_multiple_args() {
        let (ast, session) = typecheck(
            "
        func makeTuple(x, y) {
            (x, y)
        }

        makeTuple(123, true)
            ",
        );

        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Tuple(vec![Ty::Int, Ty::Bool])
        );
    }

    #[test]
    fn types_tuple_value() {
        let (ast, session) = typecheck(
            "
        let z = (123, true)
        z
        ",
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Tuple(vec![Ty::Int, Ty::Bool])
        );
    }

    #[test]
    #[ignore = "waiting on rows"]
    fn types_tuple_assignment() {
        let (ast, session) = typecheck(
            "
        let z = (123, 1.23)
        let (x, y) = z
        ",
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Int
        );
    }

    #[test]
    fn types_if_expr() {
        let (ast, session) = typecheck(
            "
        let z = if true { 123 } else { 456 }
        z
        ",
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Int
        );
    }

    #[test]
    fn requires_if_expr_cond_to_be_bool() {
        let (ast, _session) = typecheck_err(
            "
        let z = if 123 { 123 } else { 456 }
        z
        ",
        );

        assert_eq!(ast.diagnostics.len(), 1);
    }

    #[test]
    fn requires_if_expr_arms_to_match() {
        let (ast, _session) = typecheck_err(
            "
        let z = if true { 123 } else { false }
        z
        ",
        );

        assert_eq!(ast.diagnostics.len(), 1);
    }

    #[test]
    fn requires_if_stmt_cond_to_be_bool() {
        let (ast, _session) = typecheck_err(
            "
        if 123 { 123 } 
        ",
        );

        assert_eq!(ast.diagnostics.len(), 1);
    }

    #[test]
    fn types_match() {
        let (ast, session) = typecheck(
            "
        match 123 {
            123 -> true,
            456 -> false
        }
        ",
        );

        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[0].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Bool
        );
    }

    #[test]
    fn types_match_binding() {
        let (ast, session) = typecheck(
            "
        match 123 {
            a -> a,
        }
        ",
        );

        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[0].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Int
        );
    }

    #[test]
    fn checks_match_pattern_type() {
        assert_eq!(
            typecheck_err(
                "
        match 123 {
            true -> false,
        }
        ",
            )
            .0
            .diagnostics
            .len(),
            1
        );
        assert_eq!(
            typecheck_err(
                "
        match 1.23 {
            123 -> false,
        }
        ",
            )
            .0
            .diagnostics
            .len(),
            1
        );
    }

    #[test]
    fn checks_tuple_match() {
        let (ast, session) = typecheck(
            "
        match (123, true) {
            (a, b) -> (b, a),
        }
        ",
        );

        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[0].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Tuple(vec![Ty::Bool, Ty::Int])
        );
    }

    #[test]
    fn checks_loop_cond_is_bool() {
        assert_eq!(
            typecheck_err(
                "
        loop 123 {}
        ",
            )
            .0
            .diagnostics
            .len(),
            1
        );
    }

    #[test]
    fn checks_assignment() {
        assert_eq!(
            typecheck_err(
                "
        let bool = true
        bool = 123
        ",
            )
            .0
            .diagnostics
            .len(),
            1
        );
    }

    #[test]
    fn call_time_type_args_are_checked() {
        // Should be a type error because <Bool> contradicts the actual arg 123.
        let (ast, _session) = typecheck_err(
            r#"
        func id<T>(x: T) -> T { x }
        id<Bool>(123)
    "#,
        );
        assert_eq!(ast.diagnostics.len(), 1, "expected 1 diagnostic");
    }

    #[test]
    fn match_arms_must_agree_on_result_type() {
        // Arms return Int vs Bool → should be an error.
        let (ast, _session) = typecheck_err(
            r#"
        match 123 {
            123 -> 1,
            456 -> true,
        }
    "#,
        );
        assert_eq!(
            ast.diagnostics.len(),
            1,
            "match arms not constrained to same type"
        );
    }

    #[test]
    fn param_annotation_is_enforced_at_call() {
        let (ast, _session) = typecheck_err(
            r#"
        func f(x: Int) -> Int { x }
        f(true)
    "#,
        );
        assert_eq!(ast.diagnostics.len(), 1);
    }

    #[test]
    fn return_annotation_is_enforced_in_body() {
        let (ast, _session) = typecheck_err(
            r#"
        func f(x: Int) -> Int { true }
        f(1)
    "#,
        );
        assert_eq!(ast.diagnostics.len(), 1);
    }

    #[test]
    fn types_recursive_func() {
        let (ast, session) = typecheck(
            "
        func fizz(n) {
            if true {
                123
            } else {
                fizz(n)
            }
        }

        fizz(456)
        ",
        );

        assert_eq!(ty(1, &ast, &session), Ty::Int);
    }

    #[test]
    fn recursion_is_monomorphic_within_binding_group() {
        // Polymorphic recursion should NOT be inferred.
        let (ast, _session) = typecheck_err(
            r#"
        func g(x) { 
            // Force a shape change on the recursive call to try to “polymorphically” recurse.
            g( (x, x) ) 
        }
        g(1)
    "#,
        );

        // We expect either an occurs check error or an invalid unification error
        // Both indicate that polymorphic recursion is not allowed
        assert!(
            !ast.diagnostics.is_empty(),
            "expected errors for polymorphic recursion"
        );

        // Check that we have the expected error types
        let has_occurs_check = ast.diagnostics.iter().any(|d| {
            matches!(
                d,
                crate::diagnostic::AnyDiagnostic::Typing(Diagnostic {
                    kind: TypeError::OccursCheck(_),
                    ..
                })
            )
        });

        let has_invalid_unification = ast.diagnostics.iter().any(|d| {
            matches!(
                d,
                crate::diagnostic::AnyDiagnostic::Typing(Diagnostic {
                    kind: TypeError::InvalidUnification(_, _),
                    ..
                })
            )
        });

        assert!(
            has_occurs_check || has_invalid_unification,
            "expected OccursCheck or InvalidUnification error for polymorphic recursion, got {:?}",
            ast.diagnostics
        );
    }

    #[test]
    #[ignore = "TypeAnnotationKind::Func not implemented"]
    fn func_type_annotation_on_let_is_honored() {
        // Once Func annotations work, this should typecheck and instantiate.
        let (ast, session) = typecheck(
            r#"
        let id: func<T>(T) -> T = func(x) { x }
        (id(123), id(true))
    "#,
        );
        let pair = ast.roots[1].as_stmt().clone().as_expr().id;
        assert_eq!(
            *session.phase.types_by_node.get(&pair).unwrap(),
            Ty::Tuple(vec![Ty::Int, Ty::Bool])
        );
    }

    #[test]
    #[ignore = "TypeAnnotationKind::Tuple not implemented"]
    fn tuple_type_annotation_on_let_is_honored() {
        let (ast, session) = typecheck(
            r#"
        let z: (Int, Bool) = (123, true)
        z
    "#,
        );
        let use_id = ast.roots[1].as_stmt().clone().as_expr().id;
        assert_eq!(
            *session.phase.types_by_node.get(&use_id).unwrap(),
            Ty::Tuple(vec![Ty::Int, Ty::Bool])
        );
    }

    #[test]
    fn let_generalization_for_value_bindings() {
        let (ast, session) = typecheck(
            r#"
        let id = func(x) { x }
        (id(123), id(true))
    "#,
        );
        let pair = ast.roots[1].as_stmt().clone().as_expr().id;
        assert_eq!(
            *session.phase.types_by_node.get(&pair).unwrap(),
            Ty::Tuple(vec![Ty::Int, Ty::Bool])
        );
    }

    #[test]
    fn types_record_literal() {
        let (ast, session) = typecheck(
            r#"
        let rec = { a: true, b: 123, c: 1.23 }
        rec
        "#,
        );

        let Ty::Record(row) = ty(1, &ast, &session) else {
            panic!("did not get record");
        };

        assert_eq!(
            row.close(),
            [
                ("a".into(), Ty::Bool),
                ("b".into(), Ty::Int),
                ("c".into(), Ty::Float),
            ]
            .into()
        );
    }

    #[test]
    fn types_record_type_out_of_order() {
        // shouldn't blow up
        let (ast, session) = typecheck(
            "
        let x: { a: Int, b: Bool } = { b: true, a: 1 }
        x
        ",
        );

        let Ty::Record(row) = ty(1, &ast, &session) else {
            panic!("Didn't get row");
        };

        assert_eq!(
            row.close(),
            [("a".into(), Ty::Int), ("b".into(), Ty::Bool)].into()
        )
    }

    #[test]
    fn types_record_member() {
        let (ast, session) = typecheck(
            r#"
        let rec = { a: true, b: 123, c: 1.23 }
        rec.a
        rec.b
        rec.c
        "#,
        );

        assert_eq!(ty(1, &ast, &session), Ty::Bool);
        assert_eq!(ty(2, &ast, &session), Ty::Int);
        assert_eq!(ty(3, &ast, &session), Ty::Float);
    }

    #[test]
    fn types_nested_record() {
        let (ast, session) = typecheck(
            r#"
        let rec = { a: { b: { c: 1.23 } } }
        rec.a.b.c
        "#,
        );

        assert_eq!(ty(1, &ast, &session), Ty::Float);
    }

    #[test]
    fn types_record_pattern_out_of_order() {
        let (ast, session) = typecheck(
            r#"
        let rec = { a: 123, b: true }
        match rec {
            { b, a } -> (a, b)
        }
        "#,
        );

        assert_eq!(ty(1, &ast, &session), Ty::Tuple(vec![Ty::Int, Ty::Bool]));
    }

    #[test]
    fn types_record_pattern_with_equalities() {
        let (ast, session) = typecheck(
            r#"
        let rec = { a: 123, b: true }
        match rec {
            { a: 123, b } -> b
        }
        "#,
        );

        assert_eq!(ty(1, &ast, &session), Ty::Bool);
    }

    #[test]
    fn checks_fields_exist() {
        let (ast, _session) = typecheck_err(
            r#"
        let rec = { a: 123, b: true }
        match rec {
            { a, c } -> (a, c)
        }
        "#,
        );

        assert_eq!(
            ast.diagnostics.len(),
            1,
            "did not get diagnostic: {:?}",
            ast.diagnostics
        );
    }

    #[test]
    fn checks_field_types() {
        let (ast, _session) = typecheck_err(
            r#"
        let rec = { a: 123 }
        match rec {
            { a: true } -> ()
        }
        "#,
        );

        assert_eq!(
            ast.diagnostics.len(),
            1,
            "did not get diagnostic: {:?}",
            ast.diagnostics
        );
    }

    /// id over rows should generalize the *row tail* and instantiate independently.
    #[test]
    fn row_id_generalizes_and_instantiates() {
        let (ast, session) = typecheck(
            r#"
        let id = func id(r) { r }
        // project different fields from differently-shaped records
        (id({ a: 1 }).a, id({ b: true }).b)
    "#,
        );

        assert_eq!(ty(1, &ast, &session), Ty::Tuple(vec![Ty::Int, Ty::Bool]));
    }

    /// Simple polymorphic projection: fstA extracts `a` from any record that has it.
    #[test]
    fn row_projection_polymorphic() {
        let (ast, session) = typecheck(
            r#"
        func fstA(r) { r.a }
        (fstA({ a: 1 }), fstA({ a: 2, b: true }))
    "#,
        );

        assert_eq!(ty(1, &ast, &session), Ty::Tuple(vec![Ty::Int, Ty::Int]));
    }

    /// Local `let` that returns an *env row* must NOT generalize its tail.
    /// Matching on a field that isn't known in the env row should fail inside `outer`.
    #[test]
    fn row_env_tail_not_generalized_in_local_let() {
        let (ast, _session) = typecheck_err(
            r#"
        func outer(r) {
            let _x = r.a;               // forces r to have field `a`
            let k  = func() { r };      // returns the *same* env row (no row-generalization)
            match k() {
                { c } -> c              // `c` is not known; should produce one error
            }
        }
        outer({ a: 1 })
    "#,
        );

        // exactly one "missing field" diagnostic
        assert_eq!(ast.diagnostics.len(), 1, "{:?}", ast.diagnostics);
    }

    /// Local `let` with a fresh row in RHS should generalize its row tail.
    /// Using it twice with different shapes must type independently.
    #[test]
    fn row_generalizes_in_local_let_when_fresh() {
        let (ast, session) = typecheck(
            r#"
        func outer() {
            let id = func(r) { r };     // fresh row metas -> generalize to a row param
            (id({ a: 1 }).a, id({ b: true }).b)
        }
        outer()
    "#,
        );

        assert_eq!(ty(1, &ast, &session), Ty::Tuple(vec![Ty::Int, Ty::Bool]));
    }

    /// Instantiation stability: once a row param is instantiated at a call site,
    /// subsequent projections line up with the instantiated fields.
    #[test]
    fn row_instantiation_stability_across_uses() {
        let (ast, session) = typecheck(
            r#"
        let id = func id(r) { r }
        let x  = id({ a: 1, b: true });
        (x.a, x.b)
    "#,
        );

        assert_eq!(ty(2, &ast, &session), Ty::Tuple(vec![Ty::Int, Ty::Bool]));
    }

    /// Polymorphic consumer: a function requiring presence of `a` should accept any record
    /// with `a`, regardless of extra fields.
    #[test]
    fn row_presence_constraint_is_polymorphic() {
        let (ast, session) = typecheck(
            r#"
        func useA(r) { r.a } // imposes HasField(row_var, "a", Int)
        (useA({ a: 1 }), useA({ a: 2, c: true }))
    "#,
        );

        assert_eq!(ty(1, &ast, &session), Ty::Tuple(vec![Ty::Int, Ty::Int]));
    }

    #[test]
    fn row_meta_levels_prevent_leak() {
        // Outer forces r to be an open record { a: Int | row_var } by projecting r.a.
        // Then local let k = func(){ r } must NOT generalize row_var; match should fail on { c }.
        let (ast, _session) = typecheck_err(
            r#"
        func outer(r) {
            let x = r.a; // creates an internal Row::Var tail for r's row (your ensure_row/projection does this)
            let k = func() { r } // local let; do NOT generalize the outer row var into a Row::Param
            match k() {
                { c } -> c // should be a missing-field error (no 'c' in r)
            }
        }
        outer({ a: 1 })
    "#,
        );
        assert_eq!(ast.diagnostics.len(), 1);
    }

    #[test]
    fn types_row_type_as_params() {
        let (ast, session) = typecheck(
            "
        func foo(x: { y: Int, z: Bool }) {
            (x.y, x.z)
        }

        foo({ y: 123, z: true })
        ",
        );

        assert_eq!(ty(1, &ast, &session), Ty::Tuple(vec![Ty::Int, Ty::Bool]));
    }

    #[test]
    fn enforces_row_type_as_params() {
        let (ast, _session) = typecheck_err(
            "
        func foo(x: { y: Int, z: Bool }) {
            (x.y, x.z)
        }

        foo({ y: 123 })
        ",
        );

        assert_eq!(
            ast.diagnostics.len(),
            1,
            "diagnostics: {:?}",
            ast.diagnostics
        );
    }

    #[test]
    fn types_struct_constructor() {
        let (ast, session) = typecheck(
            "
        struct Person {
            let age: Int
            let height: Float
        }

        Person(age: 123, height: 1.23)
        ",
        );

        let Ty::Struct(Name::Resolved(..), row) = ty(1, &ast, &session) else {
            panic!("didn't get struct");
        };

        assert_eq!(
            row.close(),
            [("age".into(), Ty::Int), ("height".into(), Ty::Float)].into()
        );
    }
}
