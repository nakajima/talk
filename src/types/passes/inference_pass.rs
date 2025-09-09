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
        builtins::builtin_scope,
        constraints::{Constraint, ConstraintCause, Equals, HasField},
        passes::dependencies_pass::{Binder, SCCResolved},
        row::{Row, RowMetaId},
        ty::{Level, MetaId, Ty, TypeParamId},
        type_error::TypeError,
        type_operations::{apply, apply_row, substitute, unify},
        type_session::{TypeDef, TypeSession, TypingPhase},
    },
};

#[derive(Debug, Clone, Default)]
pub struct Substitutions {
    pub row: FxHashMap<RowMetaId, Row>,
    pub ty: FxHashMap<MetaId, Ty>,
}

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
pub struct MetaTag {
    pub id: MetaId,
    pub level: Level,
}

#[derive(Debug)]
pub struct BindingGroup {
    binders: Vec<Binder>,
    level: Level,
}

#[derive(Debug, Clone)]
pub struct Scheme {
    pub foralls: Vec<TypeParamId>,
    pub ty: Ty,
}

#[derive(Debug, Clone)]
pub enum EnvEntry {
    Mono(Ty),
    Scheme(Scheme),
}

#[derive(Debug)]
pub struct EnvScope {
    id: NodeID,
    parent_id: Option<NodeID>,
    entries: FxHashMap<Symbol, EnvEntry>,
}

#[derive(Debug)]
pub struct TermEnv {
    scopes: FxHashMap<NodeID, EnvScope>,
    current: NodeID,
}

impl std::fmt::Display for TermEnv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn format_scope(scope: &EnvScope, env: &TermEnv, level: usize) -> Vec<String> {
            let mut result = vec![];
            if level == 0 {
                result.push(format!("Root Scope: {scope:?}"));
            } else {
                let indent = "  ".repeat(level);
                result.push(format!("{indent}∟ {scope:?}"));
            }

            let child_scopes = env.child_scopes(scope.id);
            if !child_scopes.is_empty() {
                for scope in child_scopes {
                    result.extend(format_scope(scope, env, level + 1))
                }
            }

            result
        }

        let result = format_scope(self.scopes.get(&NodeID(0)).expect("no root scope"), self, 0);

        write!(f, "{}", result.join("\n"))
    }
}

impl Default for TermEnv {
    fn default() -> Self {
        let builtin = EnvScope {
            id: NodeID(0),
            parent_id: None,
            entries: builtin_scope(),
        };

        let mut scopes = FxHashMap::<NodeID, EnvScope>::default();
        scopes.insert(NodeID(0), builtin);

        Self {
            scopes,
            current: NodeID(0),
        }
    }
}

impl TermEnv {
    pub fn new() -> Self {
        Self::default()
    }

    fn child_scopes(&self, parent_id: NodeID) -> Vec<&EnvScope> {
        self.scopes
            .iter()
            .filter_map(|(_id, scope)| {
                if scope.parent_id == Some(parent_id) {
                    Some(scope)
                } else {
                    None
                }
            })
            .collect()
    }

    #[instrument(skip(self))]
    pub fn push(&mut self, node_id: NodeID) {
        self.scopes.insert(
            node_id,
            EnvScope {
                id: node_id,
                parent_id: Some(self.current),
                entries: Default::default(),
            },
        );

        self.current = node_id;
    }

    pub fn current_mut(&mut self) -> &mut EnvScope {
        self.scopes
            .get_mut(&self.current)
            .expect("no current scope")
    }

    pub fn current(&self) -> &EnvScope {
        self.scopes.get(&self.current).expect("no current scope")
    }

    pub fn pop(&mut self) {
        self.current = self
            .scopes
            .get(&self.current)
            .expect("no current scope to pop")
            .parent_id
            .unwrap_or(NodeID(0));
    }

    pub fn insert_mono(&mut self, sym: Symbol, ty: Ty) {
        self.current_mut().entries.insert(sym, EnvEntry::Mono(ty));
    }

    pub fn promote(&mut self, sym: Symbol, sch: Scheme) {
        // promote into the *root* frame so it’s visible everywhere (for binders)
        self.scopes
            .get_mut(&NodeID(0))
            .unwrap()
            .entries
            .insert(sym, EnvEntry::Scheme(sch));
    }

    pub fn lookup(&self, sym: &Symbol) -> Option<&EnvEntry> {
        self.lookup_in_scope(sym, self.current)
    }

    fn lookup_in_scope(&self, sym: &Symbol, scope_id: NodeID) -> Option<&EnvEntry> {
        let scope = self.scopes.get(&scope_id)?;

        if let Some(entry) = scope.entries.get(sym) {
            return Some(entry);
        }

        if let Some(parent_id) = scope.parent_id {
            return self.lookup_in_scope(sym, parent_id);
        }

        None
    }
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
    row_metas: IDGenerator,
    term_env: TermEnv,
    rhs_map: FxHashMap<Binder, NodeID>,
    annotation_map: FxHashMap<Binder, NodeID>,
}

#[derive(Debug)]
pub struct Wants(Vec<Constraint>);
impl Wants {
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
        mut session: TypeSession<SCCResolved>,
        ast: &'a mut AST<NameResolved>,
    ) -> TypeSession<Inferenced> {
        let groups = kosaraju_scc(&session.phase.graph);

        let mut pass = InferencePass {
            ast,
            types_by_node: Default::default(),
            metavars: Default::default(),
            skolems: Default::default(),
            type_params: Default::default(),
            row_metas: Default::default(),
            term_env: TermEnv::new(),
            rhs_map: session.phase.rhs_map.clone(),
            annotation_map: session.phase.annotation_map.clone(),
        };

        // Handle binders first
        for binders in groups {
            let group = BindingGroup {
                binders,
                level: Level(1),
            };

            let wants = pass.infer_group(&group);
            let subs = pass.solve(wants);
            pass.promote_group(&group, &subs);
            pass.apply_to_self(&subs);
        }

        let roots = std::mem::take(&mut pass.ast.roots);

        for root in roots.iter() {
            if !matches!(root, Node::Stmt(_)) {
                continue;
            }

            let mut wants = Wants(vec![]);
            let ty = pass.infer_node(root, Level(1), &mut wants);
            pass.types_by_node.insert(root.node_id(), ty);
            let subs = pass.solve(wants);
            pass.apply_to_self(&subs);
        }

        _ = std::mem::replace(&mut pass.ast.roots, roots);

        pass.annotate_uses_after_inference();

        let type_constructors = std::mem::take(&mut session.phase.type_constructors);
        let protocols = std::mem::take(&mut session.phase.protocols);

        let phase = Inferenced {
            type_constructors,
            protocols,
            types_by_node: pass.types_by_node,
        };

        session.advance(phase)
    }

    #[instrument(skip(self))]
    fn infer_group(&mut self, group: &BindingGroup) -> Wants {
        let mut wants = Wants(Default::default());
        let inner_level = group.level.next();

        for &binder in &group.binders {
            let m = Ty::MetaVar {
                id: self.metavars.next_id(),
                level: inner_level,
            };

            tracing::trace!("binding {binder:?} placeholder");

            self.term_env.insert_mono(binder.into(), m);
        }

        for &binder in &group.binders {
            let symbol = Symbol::from(binder);
            let Some(rhs_expr_id) = self.rhs_map.get(&binder).copied() else {
                println!("Did not get rhs for {binder:?}");
                continue;
            };

            let rhs_expr = self.ast.find(rhs_expr_id).clone();

            let got = self.infer_node(&rhs_expr.unwrap(), inner_level, &mut wants);
            self.types_by_node.insert(rhs_expr_id, got.clone());

            let tv = match self.term_env.lookup(&symbol).unwrap() {
                EnvEntry::Mono(t) => t.clone(),
                _ => unreachable!(),
            };

            if let Some(annotation_id) = self.annotation_map.get(&binder).cloned() {
                let Some(Node::TypeAnnotation(annotation)) = self.ast.find(annotation_id) else {
                    panic!("didn't find type annotation for annotation id");
                };

                let annotation_ty = self.infer_type_annotation(&annotation, inner_level);
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
    fn infer_type_annotation(&mut self, annotation: &TypeAnnotation, level: Level) -> Ty {
        match &annotation.kind {
            TypeAnnotationKind::Func { .. } => todo!(),
            TypeAnnotationKind::Tuple(..) => todo!(),
            TypeAnnotationKind::Nominal {
                name: Name::Resolved(sym, _),
                ..
            } => match self.term_env.lookup(sym).unwrap().clone() {
                EnvEntry::Mono(ty) => ty.clone(),
                EnvEntry::Scheme(scheme) => self.instantiate(&scheme, level),
            },
            _ => unreachable!(),
        }
    }

    #[instrument(skip(self))]
    fn apply_to_self(&mut self, substitutions: &Substitutions) {
        for (_, ty) in self.types_by_node.iter_mut() {
            if matches!(ty, Ty::Primitive(_)) {
                continue;
            }

            *ty = apply(ty.clone(), substitutions);
        }
    }

    #[instrument(skip(self))]
    fn solve(&mut self, mut wants: Wants) -> Substitutions {
        let mut substitutions = Substitutions::default();
        let mut made_progress = false;
        loop {
            let mut next_wants = Wants(vec![]);
            for want in wants.0.drain(..) {
                tracing::trace!("solving {want:?}");

                let solution = match want {
                    Constraint::Equals(equals) => {
                        unify(&equals.lhs, &equals.rhs, &mut substitutions)
                    }
                    Constraint::HasField(has_field) => {
                        let row = apply_row(has_field.row.clone(), &substitutions);
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
                break;
            }

            wants = next_wants;
        }

        self.apply_to_self(&substitutions);

        substitutions
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
    fn promote_group(&mut self, group: &BindingGroup, subs: &Substitutions) {
        for &binder in &group.binders {
            let sym = Symbol::from(binder);

            match self.term_env.lookup(&sym).cloned() {
                Some(EnvEntry::Mono(ty)) => {
                    let applied = apply(ty, subs);
                    let scheme = self.generalize(group.level, applied);
                    self.term_env.promote(sym, scheme);
                }
                Some(EnvEntry::Scheme(_scheme)) => {}
                None => panic!("didn't find {sym:?} in term env"),
            }
        }
    }

    #[instrument(skip(self))]
    fn generalize(&mut self, inner: Level, ty: Ty) -> Scheme {
        // collect metas in ty
        let mut metas = FxHashSet::default();
        collect_metas_and_generics(&ty, &mut metas);

        // keep only metas born at or above inner
        let mut foralls = vec![];
        let substitutions: FxHashMap<Ty, Ty> = metas
            .into_iter()
            .filter(|m| {
                if let Ty::MetaVar { level, .. } = &m {
                    *level >= inner
                } else {
                    true
                }
            })
            .map(|ty| {
                let param_id = self.type_params.next_id();
                foralls.push(param_id);
                (ty, Ty::Param(param_id))
            })
            .collect();

        let ty = substitute(ty, &substitutions);
        Scheme { foralls, ty }
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
            DeclKind::Let { lhs, .. } => self.infer_pattern(lhs, level, wants),
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
                    .map(|_| {
                        let var = self.metavars.next_id();
                        Ty::MetaVar { id: var, level }
                    })
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
                            let field_ty = Ty::MetaVar {
                                id: self.metavars.next_id(),
                                level,
                            };

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
                            let field_ty = Ty::MetaVar {
                                id: self.metavars.next_id(),
                                level,
                            };
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

    #[instrument(skip(self))]
    fn infer_pattern(&mut self, pattern: &Pattern, level: Level, wants: &mut Wants) -> Ty {
        let Pattern { id, kind, .. } = &pattern;

        match kind {
            PatternKind::Bind(Name::Resolved(sym, _)) => {
                let ty = match self.term_env.lookup(sym).unwrap() {
                    EnvEntry::Mono(ty) => ty.clone(),
                    EnvEntry::Scheme(scheme) => scheme.ty.clone(),
                };

                self.types_by_node.insert(*id, ty.clone());

                ty
            }
            _ => todo!(),
        }
    }

    /// Ensure we have a row to talk about for `expected`.
    /// If `expected` is Ty::Record(row), return that row.
    /// Otherwise create a fresh row var ρ and add Eq(expected, Record(ρ)).
    #[instrument(skip(self), ret)]
    fn ensure_row(&mut self, id: NodeID, expected: &Ty, level: Level, wants: &mut Wants) -> Row {
        match expected {
            Ty::Record(box row) => row.clone(),
            _ => {
                let rho = Row::Var(self.row_metas.next_id());
                wants.equals(
                    expected.clone(),
                    Ty::Record(Box::new(rho.clone())),
                    ConstraintCause::Pattern(id),
                );
                rho
            }
        }
    }

    #[instrument(skip(self))]
    fn infer_block(&mut self, block: &Block, level: Level, wants: &mut Wants) -> Ty {
        // Very simple semantics: return the type of the last expression statement, else Void.
        let mut last_ty = Ty::Void;
        for node in &block.body {
            if let Node::Stmt(stmt) = node {
                last_ty = self.infer_stmt(stmt, level, wants);
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
                    Some(EnvEntry::Scheme(s)) => self.instantiate(&s, level), // or pass through
                    Some(EnvEntry::Mono(t)) => t.clone(),
                    None => panic!(
                        "variable not found in term env: {:?}, {:?}",
                        sym, self.term_env
                    ),
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
                    let row = Row::Var(self.row_metas.next_id());
                    wants.equals(
                        receiver_ty.clone(),
                        Ty::Record(Box::new(row.clone())),
                        ConstraintCause::Member(id),
                    );

                    (row, receiver.span)
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
            (
                Row::Var(self.row_metas.next_id()),
                Span { start: 0, end: 0 },
            )
        };

        let member_ty = Ty::MetaVar {
            id: self.metavars.next_id(),
            level,
        };

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
            self.term_env.push(arm.id);
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
            self.term_env.pop();
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
            self.instantiate_with_args(&scheme, type_args, level, wants)
        } else {
            self.infer_expr(callee, level, wants)
        };

        let mut arg_tys = Vec::with_capacity(args.len());

        for _ in args {
            arg_tys.push(Ty::MetaVar {
                id: self.metavars.next_id(),
                level,
            });
        }
        let returns = Ty::MetaVar {
            id: self.metavars.next_id(),
            level,
        };

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
        self.term_env.push(func.id);

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
                self.infer_type_annotation(type_annotation, level)
            } else {
                Ty::MetaVar {
                    id: self.metavars.next_id(),
                    level,
                }
            };

            param_tys.push(ty);
        }

        let ret_ty = if let Some(ret) = &func.ret {
            self.infer_type_annotation(ret, level)
        } else {
            Ty::MetaVar {
                id: self.metavars.next_id(),
                level,
            }
        };

        for (p, ty) in func.params.iter().zip(param_tys.iter()) {
            let Name::Resolved(sym, _) = &p.name else {
                panic!("unresolved param");
            };
            tracing::info!("inserting mono: {sym:?} : {ty:?}");
            self.term_env.insert_mono(*sym, ty.clone());
        }

        let body_ty = self.infer_block(&func.body, level, wants);

        self.term_env.pop();

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

    #[instrument(skip(self))]
    fn instantiate(&mut self, scheme: &Scheme, level: Level) -> Ty {
        // Map each quantified meta id to a fresh meta at this use-site level
        let mut substitutions = FxHashMap::default();

        for param in &scheme.foralls {
            substitutions.insert(
                Ty::Param(*param),
                Ty::MetaVar {
                    id: self.metavars.next_id(),
                    level,
                },
            );
        }
        substitute(scheme.ty.clone(), &substitutions)
    }

    #[instrument(skip(self))]
    fn instantiate_with_args(
        &mut self,
        scheme: &Scheme,
        args: &[TypeAnnotation],
        level: Level,
        wants: &mut Wants,
    ) -> Ty {
        // Map each quantified meta id to a fresh meta at this use-site level
        let mut substitutions = FxHashMap::default();

        for (param, arg) in scheme.foralls.iter().zip(args) {
            let arg_ty = self.infer_type_annotation(arg, level);

            let meta_var = Ty::MetaVar {
                id: self.metavars.next_id(),
                level,
            };

            wants.equals(
                meta_var.clone(),
                arg_ty,
                ConstraintCause::CallTypeArg(arg.id),
            );

            substitutions.insert(Ty::Param(*param), meta_var);
        }

        substitute(scheme.ty.clone(), &substitutions)
    }
}

fn curry<I: IntoIterator<Item = Ty>>(params: I, ret: Ty) -> Ty {
    params
        .into_iter()
        .collect::<Vec<_>>()
        .into_iter()
        .rfold(ret, |acc, p| Ty::Func(Box::new(p), Box::new(acc)))
}

pub fn collect_metas_and_generics(ty: &Ty, out: &mut FxHashSet<Ty>) {
    match ty {
        Ty::Param(_) => {
            out.insert(ty.clone());
        }
        Ty::MetaVar { .. } => {
            out.insert(ty.clone());
        }
        Ty::Func(dom, codom) => {
            collect_metas_and_generics(dom, out);
            collect_metas_and_generics(codom, out);
        }
        Ty::TypeApplication(fun, arg) => {
            collect_metas_and_generics(fun, out);
            collect_metas_and_generics(arg, out);
        }
        Ty::Tuple(items) => {
            for item in items {
                collect_metas_and_generics(item, out);
            }
        }
        Ty::Record(box row) => match row {
            Row::Empty => (),
            Row::Var(_) => (),
            Row::Extend { row, ty, .. } => {
                collect_metas_and_generics(ty, out);
                collect_metas_and_generics(&Ty::Record(row.clone()), out);
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
    use crate::types::{passes::dependencies_pass::tests::resolve_dependencies, row::ClosedRow};

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
            ClosedRow {
                labels: vec!["a".into(), "b".into(), "c".into()],
                values: vec![Ty::Bool, Ty::Int, Ty::Float]
            }
        );
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
    fn types_record_pattern() {
        let (ast, session) = typecheck(
            r#"
        let rec = { a: 123, b: true }
        match rec {
            { a, b } -> (a, b)
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

    #[test]
    fn row_meta_levels_prevent_leak() {
        // Outer forces r to be an open record { a: Int | ρ } by projecting r.a.
        // Then local let k = func(){ r } must NOT generalize ρ; match should fail on { c }.
        let (ast, _session) = typecheck_err(
            r#"
        func outer(r) {
            let x = r.a;                    // creates an internal Row::Var tail for r's row (your ensure_row/projection does this)
            let k = func() { r }    // local let; do NOT generalize the outer row var into a Row::Param
            match k() {
                { c } -> c          // should be a missing-field error (no 'c' in r)
            }
        }
        outer({ a: 1 })
    "#,
        );
        assert_eq!(ast.diagnostics.len(), 1);
    }
}
