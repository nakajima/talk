use derive_visitor::{Drive, Visitor};
use petgraph::algo::kosaraju_scc;
use rustc_hash::{FxHashMap, FxHashSet};
use tracing::instrument;

use crate::{
    ast::{AST, ASTPhase},
    diagnostic::{AnyDiagnostic, Diagnostic},
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
        constraint::{Constraint, ConstraintCause, Equals, HasField},
        constraints::{call::Call, member::Member},
        fields::TypeFields,
        passes::dependencies_pass::{Binder, SCCResolved},
        row::{Row, RowMetaId},
        scheme::{ForAll, Scheme},
        term_environment::{EnvEntry, TermEnv},
        ty::{Level, Ty, UnificationVarId},
        type_error::TypeError,
        type_operations::{
            UnificationSubstitutions, apply, apply_row, instantiate_ty, substitute, unify,
        },
        type_session::{ASTTyRepr, TypeDefKind, TypeSession, TypingPhase},
        type_snapshot::TypeSnapshot,
    },
};

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

#[derive(Debug)]
pub struct InferencePass<'a> {
    ast: &'a mut AST<NameResolved>,
    types_by_node: FxHashMap<NodeID, Ty>,
    meta_levels: FxHashMap<Meta, Level>,
    snapshots: Vec<TypeSnapshot>,

    pub(crate) term_env: TermEnv,
    pub(crate) session: TypeSession<SCCResolved>,
}

#[derive(Debug, Default)]
pub struct Wants(Vec<Constraint>);
impl Wants {
    pub fn push(&mut self, constraint: Constraint) {
        tracing::debug!("constraining {constraint:?}");
        self.0.push(constraint)
    }

    pub fn call(
        &mut self,
        callee: Ty,
        args: Vec<Ty>,
        returns: Ty,
        receiver: Option<Ty>,
        cause: ConstraintCause,
        span: Span,
    ) {
        tracing::debug!("constraining call {callee:?}({args:?}) = {returns:?}");
        self.0.push(Constraint::Call(Call {
            callee,
            args,
            returns,
            receiver,
            cause,
            span,
        }))
    }

    pub fn equals(&mut self, lhs: Ty, rhs: Ty, cause: ConstraintCause, span: Span) {
        tracing::debug!("constraining equals {lhs:?} = {rhs:?}");
        self.0.push(Constraint::Equals(Equals {
            lhs,
            rhs,
            cause,
            span,
        }));
    }

    pub fn member(
        &mut self,
        receiver: Ty,
        label: Label,
        ty: Ty,
        cause: ConstraintCause,
        span: Span,
    ) {
        tracing::debug!("constraining member {receiver:?}.{label:?} <> {ty:?}");
        self.0.push(Constraint::Member(Member {
            receiver,
            label,
            ty,
            cause,
            span,
        }))
    }

    pub fn _has_field(
        &mut self,
        row: Row,
        label: Label,
        ty: Ty,
        cause: ConstraintCause,
        span: Span,
    ) {
        tracing::debug!("constraining has_field {row:?}.{label:?} <> {ty:?}");
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
            session,
            meta_levels: Default::default(),
            snapshots: Default::default(),
        };

        let type_ids: Vec<TypeId> = pass
            .session
            .phase
            .type_constructors
            .keys()
            .copied()
            .collect();
        for id in type_ids {
            let mut wants = Wants(vec![]);
            pass.define_type(id, Level(1), &mut wants);
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

        let roots = pass.ast.roots.clone();

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

        let phase = Inferenced {
            types_by_node: pass.types_by_node,
        };

        pass.session.advance(phase)
    }

    pub(crate) fn infer_ast_ty_repr(
        &mut self,
        ty_repr: &ASTTyRepr,
        level: Level,
        wants: &mut Wants,
    ) -> Ty {
        match &ty_repr {
            ASTTyRepr::Annotated(annotation) => {
                self.infer_type_annotation(annotation, level, wants)
            }
            ASTTyRepr::SelfType(name, _, _) => {
                let Name::Resolved(Symbol::Type(type_id), _) = name else {
                    panic!("didn't get type id");
                };
                // For self parameters in methods, look up the struct type from the environment
                // The struct type should be in the environment by now
                let entry = self.term_env.lookup(&Symbol::Type(*type_id)).cloned();
                match entry {
                    Some(EnvEntry::Mono(ty)) => ty,
                    Some(EnvEntry::Scheme(scheme)) => scheme.ty.clone(),
                    None => unreachable!("define_type didn't work"),
                }
            }
            ASTTyRepr::Hole(..) => Ty::Param(self.session.vars.type_params.next_id()),
            ASTTyRepr::Generic(decl) => {
                let ty = Ty::Param(self.session.vars.type_params.next_id());
                self.term_env.promote(
                    decl.name
                        .symbol()
                        .expect("didn't resolve name of generic param"),
                    EnvEntry::Mono(ty.clone()),
                );
                ty
            }
        }
    }

    #[instrument(skip(self))]
    fn define_type(&mut self, type_id: TypeId, level: Level, wants: &mut Wants) {
        let mut type_def = self
            .session
            .phase
            .type_constructors
            .remove(&type_id)
            .expect("didn't find type for type id");

        let foralls = type_def
            .generics
            .iter()
            .map(|(_, g)| {
                let Ty::Param(id) = self.infer_ast_ty_repr(g, level, wants) else {
                    unreachable!();
                };

                ForAll::Ty(id)
            })
            .collect();

        let methods = match &mut type_def.fields {
            TypeFields::Struct {
                properties,
                methods,
                ..
            } => {
                // Build the struct row first
                let row = properties.iter().fold(
                    Row::Empty(TypeDefKind::Struct),
                    |mut acc, (label, property)| {
                        acc = Row::Extend {
                            row: Box::new(acc),
                            label: label.clone(),
                            ty: self.infer_ast_ty_repr(&property.ty_repr, level, wants),
                        };
                        acc
                    },
                );

                let struct_ty = Ty::Struct(Some(type_def.name.clone()), Box::new(row.clone()));
                let scheme = Scheme::new(foralls, vec![], struct_ty);
                self.term_env
                    .promote(Symbol::Type(type_id), EnvEntry::Scheme(scheme));

                methods
            }
            TypeFields::Enum {
                variants, methods, ..
            } => {
                // CLOSED row: label -> payload(Params). No row meta, no HasField predicates.
                let row =
                    variants
                        .iter()
                        .fold(Row::Empty(TypeDefKind::Enum), |acc, (label, variant)| {
                            let payload = if variant.fields.is_empty() {
                                Ty::Void
                            } else if variant.fields.len() == 1 {
                                self.infer_ast_ty_repr(&variant.fields[0], level, wants)
                            } else {
                                Ty::Tuple(
                                    variant
                                        .fields
                                        .iter()
                                        .map(|f| self.infer_ast_ty_repr(f, level, wants))
                                        .collect(),
                                )
                            };
                            Row::Extend {
                                row: Box::new(acc),
                                label: label.clone(),
                                ty: payload,
                            }
                        });

                let sum_ty = Ty::Sum(Some(type_def.name.clone()), Box::new(row.clone()));

                // Export the nominal enum type scheme: ∀… . Opt<…>
                self.term_env.promote(
                    Symbol::Type(type_id),
                    EnvEntry::Scheme(Scheme::new(foralls.clone(), vec![], sum_ty.clone())),
                );

                methods
            }

            _ => unimplemented!(),
        };

        for method in methods.values_mut() {
            let mut params = vec![];
            for param in method.params.iter() {
                let param_ty = self.infer_ast_ty_repr(param, level, wants);
                params.push(param_ty)
            }

            // Fill in holes with meta vars
            let ret = self.infer_ast_ty_repr(&method.ret, level.next(), wants);
            // Don't generalize yet - let the method body inference determine the actual return type
            let method_ty = curry(params, ret);
            let entry = EnvEntry::Mono(method_ty);

            self.term_env.promote(method.symbol, entry);
        }

        self.session
            .phase
            .type_constructors
            .insert(type_id, type_def);
    }

    #[instrument(skip(self))]
    fn infer_group(&mut self, group: &BindingGroup) -> Wants {
        let mut wants = Wants(Default::default());
        let inner_level = group.level.next();

        for &binder in &group.binders {
            let symbol = Symbol::from(binder);

            if self.term_env.lookup(&symbol).is_none() {
                let ty = self.new_ty_meta_var(inner_level);
                self.term_env.insert_mono(symbol, ty);
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

            let tv = match self.term_env.lookup(&symbol).cloned() {
                Some(EnvEntry::Mono(t)) => t.clone(),
                Some(EnvEntry::Scheme(scheme)) => scheme.ty,
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
            } => match self.term_env.lookup(sym).unwrap().clone() {
                EnvEntry::Mono(ty) => ty.clone(),
                EnvEntry::Scheme(scheme) => {
                    scheme
                        .inference_instantiate(self, level, wants, annotation.span)
                        .0
                }
            },
            TypeAnnotationKind::Record { fields } => {
                let mut row = Row::Empty(TypeDefKind::Struct);
                for field in fields.iter().rev() {
                    row = Row::Extend {
                        row: Box::new(row),
                        label: field.label.name_str().into(),
                        ty: self.infer_type_annotation(&field.value, level, wants),
                    };
                }

                Ty::Struct(None, Box::new(row))
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
    fn solve(&mut self, mut wants: Wants) -> (UnificationSubstitutions, Vec<Constraint>) {
        let mut substitutions = UnificationSubstitutions::new(self.meta_levels.clone());
        let mut unsolved = vec![];
        loop {
            let mut made_progress = false;
            let mut next_wants = Wants(vec![]);
            for want in wants.0.drain(..) {
                tracing::trace!("solving {want:?}");

                let solution = match want {
                    Constraint::Equals(ref equals) => unify(
                        &equals.lhs,
                        &equals.rhs,
                        &mut substitutions,
                        &mut self.session.vars,
                    ),
                    Constraint::Call(ref call) => {
                        call.solve(self, &mut next_wants, &mut substitutions)
                    }
                    Constraint::Member(ref member) => {
                        member.solve(self, &mut next_wants, &mut substitutions)
                    }
                    Constraint::HasField(ref has_field) => {
                        let row = apply_row(has_field.row.clone(), &mut substitutions);
                        match row {
                            Row::Empty(kind) => {
                                self.ast.diagnostics.push(AnyDiagnostic::Typing(Diagnostic {
                                    path: self.ast.path.clone(),
                                    span: has_field.span,
                                    kind: TypeError::MemberNotFound(
                                        if kind == TypeDefKind::Struct {
                                            Ty::Struct(None, Box::new(has_field.row.clone()))
                                        } else {
                                            Ty::Sum(None, Box::new(has_field.row.clone()))
                                        },
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
                                        Ty::Struct(None, Box::new(has_field.row.clone())),
                                        has_field.label.to_string(),
                                    ),
                                }));
                                Ok(false)
                            }
                            Row::Var(..) => {
                                // Keep the constraint for the next iteration with the applied row
                                next_wants._has_field(
                                    row,
                                    has_field.label.clone(),
                                    has_field.ty.clone(),
                                    ConstraintCause::Internal,
                                    has_field.span,
                                );
                                Ok(false)
                            }
                            Row::Extend { row, label, ty } => {
                                if has_field.label == label {
                                    next_wants.equals(
                                        has_field.ty.clone(),
                                        ty,
                                        ConstraintCause::Internal,
                                        want.span(),
                                    );
                                    tracing::trace!("found match for {label:?}");
                                    Ok(true)
                                } else {
                                    next_wants._has_field(
                                        *row,
                                        has_field.label.clone(),
                                        has_field.ty.clone(),
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
                                span: want.span(),
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

                Ty::UnificationVar { level, id } => {
                    if *level <= inner {
                        tracing::warn!("discarding {m:?} due to level ({level:?} < {inner:?})");
                        continue;
                    }

                    let param_id = self.session.vars.type_params.next_id();
                    tracing::trace!("generalizing {m:?} to {param_id:?}");
                    foralls.push(ForAll::Ty(param_id));
                    substitutions.ty.insert(*id, Ty::Param(param_id));
                }
                Ty::Struct(None, box Row::Var(id)) => {
                    let level = self
                        .meta_levels
                        .get(&Meta::Row(*id))
                        .expect("didn't get level for row meta");
                    if *level <= inner {
                        tracing::trace!("discarding {m:?} due to level ({level:?} < {inner:?})");
                        continue;
                    }

                    let param_id = self.session.vars.row_params.next_id();
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
                    rhs_wants.equals(
                        ty.clone(),
                        rhs_ty,
                        ConstraintCause::Assignment(decl.id),
                        expr.span,
                    );
                }

                let (mut subs, unsolved) = self.solve(rhs_wants);
                let applied_ty = apply(ty.clone(), &mut subs);

                if let PatternKind::Bind(Name::Resolved(sym, _)) = lhs.kind {
                    let scheme = self.generalize(level, applied_ty.clone(), &unsolved);
                    self.term_env.promote(sym, scheme);
                }

                ty
            }
            DeclKind::Method { func, .. } => {
                // Type the method body just like a regular function
                // This ensures the body type is constrained to match the return type
                let Name::Resolved(func_sym, _) = func.name else {
                    unreachable!("didn't get method name");
                };

                let ty = self.infer_func(func, level, wants);
                self.term_env.promote(func_sym, EnvEntry::Mono(ty.clone()));
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
                    .map(|_| self.new_ty_meta_var(level))
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
                let expected_row = self.ensure_row(
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
                            let field_ty = self.new_ty_meta_var(level);

                            // bind the pattern name
                            self.term_env.insert_mono(
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
                            let field_ty = self.new_ty_meta_var(level);
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
                enum_name,
                variant_name,
                fields,
            } => {
                let receiver = if let Some(enum_name) = enum_name {
                    let entry = self
                        .term_env
                        .lookup(&enum_name.symbol().unwrap())
                        .cloned()
                        .expect("didn't get enum for name");

                    entry.inference_instantiate(self, level, wants, pattern.span)
                } else {
                    self.new_ty_meta_var(level)
                };

                wants.equals(
                    expected.clone(),
                    receiver.clone(),
                    ConstraintCause::Pattern(pattern.id),
                    pattern.span,
                );

                let field_metas: Vec<Ty> =
                    fields.iter().map(|_| self.new_ty_meta_var(level)).collect();
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

    /// Ensure we have a row to talk about for `expected`.
    /// If `expected` is Ty::Record(row), return that row.
    /// Otherwise create a fresh row var row_var and add Eq(expected, Record(row_var)).
    #[instrument(skip(self), ret)]
    fn ensure_row(
        &mut self,
        id: NodeID,
        span: Span,
        expected: &Ty,
        level: Level,
        wants: &mut Wants,
        kind: TypeDefKind,
    ) -> Row {
        match expected {
            Ty::Struct(_, box row) => row.clone(),
            Ty::Sum(_, box row) => row.clone(),
            _ => {
                let row = Box::new(self.new_row_meta_var(level));
                let rho = if kind == TypeDefKind::Struct {
                    Ty::Struct(None, row)
                } else {
                    Ty::Sum(None, row)
                };

                wants.equals(
                    expected.clone(),
                    rho.clone(),
                    ConstraintCause::Pattern(id),
                    span,
                );

                let (Ty::Struct(_, row) | Ty::Sum(_, row)) = rho else {
                    unreachable!()
                };

                *row
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
                        scheme
                            .inference_instantiate(self, level, wants, expr.span)
                            .0
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
            ExprKind::Constructor(Name::Resolved(sym @ Symbol::Type(id), _)) => {
                let entry = self
                    .term_env
                    .lookup(sym)
                    .cloned()
                    .expect("did not find type for sym in env");

                let (ty, substitutions) = match &entry {
                    EnvEntry::Mono(ty) => (ty.clone(), Default::default()),
                    EnvEntry::Scheme(scheme) => {
                        scheme.inference_instantiate(self, level, wants, expr.span)
                    }
                };

                let type_def = self
                    .session
                    .phase
                    .type_constructors
                    .get(id)
                    .cloned()
                    .expect("didn't get type def");

                match &type_def.fields {
                    TypeFields::Struct { initializers, .. } => {
                        // TODO: handle multiple initializers
                        let (_, initializer) = initializers.first().expect("no initializer found");

                        let params: Vec<Ty> = initializer
                            .params
                            .iter()
                            .map(|p| self.infer_ast_ty_repr(p, level, wants))
                            .collect();

                        // Apply the same substitutions to params that we applied to properties
                        let ty = params.into_iter().collect::<Vec<_>>().into_iter().rfold(
                            ty,
                            |acc, p| Ty::Constructor {
                                type_id: *id,
                                param: Box::new(p),
                                ret: Box::new(acc),
                            },
                        );

                        instantiate_ty(ty, &substitutions, level)
                    }
                    TypeFields::Enum { .. } => ty,
                    _ => todo!(),
                }
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
        // let (receiver_row, span) = if let Some(receiver) = receiver {
        //     let receiver_ty = self.infer_expr(receiver, level, wants);
        //     match receiver_ty {
        //         Ty::Struct(_, box row) => (row, receiver.span),
        //         Ty::MetaVar { .. } => {
        //             // Add a constraint saying that receiver needs to be a row
        //             let row = self.new_row_meta_var(level);
        //             wants.equals(
        //                 receiver_ty.clone(),
        //                 row.clone(),
        //                 ConstraintCause::Member(id),
        //             );

        //             let Ty::Struct(_, row) = row else {
        //                 unreachable!();
        //             };

        //             (*row, receiver.span)
        //         }
        //         ty => {
        //             self.ast
        //                 .diagnostics
        //                 .push(crate::diagnostic::AnyDiagnostic::Typing(Diagnostic {
        //                     path: self.ast.path.clone(),
        //                     span: receiver.span,
        //                     kind: TypeError::ExpectedRow(ty),
        //                 }));
        //             return Ty::Void;
        //         }
        //     }
        // } else {
        //     let Ty::Struct(_, box row) = self.new_row_meta_var(level) else {
        //         unreachable!()
        //     };

        //     (row, Span { start: 0, end: 0 })
        // };

        let receiver_ty = if let Some(receiver) = &receiver {
            self.infer_expr(receiver, level, wants)
        } else {
            todo!("unqualified members not supported yet");
        };

        let member_ty = self.new_ty_meta_var(level);

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

        Ty::Struct(None, Box::new(row))
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
            scheme.instantiate_with_args(type_args, self, level, wants, callee.span)
        } else {
            self.infer_expr(callee, level, wants)
        };

        let mut arg_tys = Vec::with_capacity(args.len() + 1);

        for arg in args {
            arg_tys.push(self.infer_expr(&arg.value, level, wants));
        }

        let returns = self.new_ty_meta_var(level);
        tracing::trace!("adding returns meta: {returns:?}");

        let receiver = if let Expr {
            kind: ExprKind::Member(receiver, _),
            ..
        } = &callee
        {
            let receiver_ty = if let Some(receiver) = receiver {
                self.infer_expr(receiver, level, wants)
            } else {
                self.new_ty_meta_var(level)
            };

            Some(receiver_ty)

            // arg_tys.insert(0, receiver_ty.clone());
        } else {
            None
        };

        wants.call(
            callee_ty,
            arg_tys,
            returns.clone(),
            receiver,
            ConstraintCause::Call(callee.id),
            callee.span,
        );

        returns
    }

    #[instrument(skip(self))]
    fn infer_func(&mut self, func: &Func, level: Level, wants: &mut Wants) -> Ty {
        let mut skolem_map = FxHashMap::default();
        for generic in func.generics.iter() {
            let skolem_id = self.session.vars.skolems.next_id();
            let param_id = self.session.vars.type_params.next_id();
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

        wants.equals(
            body_ty,
            ret_ty.clone(),
            ConstraintCause::Internal,
            func.body.span,
        );

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
                        ConstraintCause::Condition(stmt.id),
                        conseq.span,
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

    pub(crate) fn new_ty_meta_var(&mut self, level: Level) -> Ty {
        let id = self.session.vars.ty_metas.next_id();
        self.meta_levels.insert(Meta::Ty(id), level);
        tracing::trace!("Fresh {id:?}");
        Ty::UnificationVar { id, level }
    }

    pub(crate) fn new_row_meta_var(&mut self, level: Level) -> Row {
        let id = self.session.vars.row_metas.next_id();
        self.meta_levels.insert(Meta::Row(id), level);
        tracing::trace!("Fresh {id:?}");
        Row::Var(id)
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
        Ty::Struct(_, box row) | Ty::Sum(_, box row) => match row {
            Row::Empty(..) => (),
            Row::Var(..) => {
                out.insert(ty.clone());
            }
            Row::Param(..) => (),
            Row::Extend { row, ty, .. } => {
                collect_meta(ty, out);
                collect_meta(&Ty::Struct(None, row.clone()), out);
            }
        },
        Ty::Constructor { param, ret, .. } => {
            collect_meta(param, out);
            collect_meta(ret, out);
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
