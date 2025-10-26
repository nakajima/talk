use crate::node_id::FileID;
use crate::types::builtins;
use crate::types::constraints::type_member::TypeMember;
use crate::types::wants::Wants;
use crate::{
    ast::{AST, ASTPhase},
    diagnostic::Diagnostic,
    label::Label,
    name::Name,
    name_resolution::{name_resolver::NameResolved, symbol::Symbol},
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
        infer_row::{InferRow, RowMetaId},
        infer_ty::{InferTy, Level, MetaVarId},
        passes::dependencies_pass::{Binder, SCCResolved},
        scheme::Scheme,
        term_environment::EnvEntry,
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, apply, substitute, unify},
        type_session::{TypeDefKind, TypeSession},
        type_snapshot::TypeSnapshot,
    },
};
use petgraph::algo::kosaraju_scc;
use rustc_hash::{FxHashMap, FxHashSet};
use tracing::instrument;

#[macro_export]
macro_rules! guard_found_ty {
    ($self: expr, $id: expr) => {
        if let Some(ty) = $self.session.types_by_node.get(&$id) {
            return ty.clone();
        }
    };
}

#[derive(Debug, PartialEq)]
pub struct Inferenced {}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Meta {
    Ty(MetaVarId),
    Row(RowMetaId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct MetaTag {
    pub id: MetaVarId,
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
    pub types_by_node: FxHashMap<NodeID, InferTy>,
}

/// Perform the rest of type inference for this AST. By now we shouldn't care about
/// scope stacks since everything should already be in the flat term env.
#[derive(Debug)]
pub struct OldInferencePass<'a> {
    ast: &'a mut AST<NameResolved>,
    snapshots: Vec<TypeSnapshot>,
    scc: &'a SCCResolved,
    pub(crate) session: &'a mut TypeSession,
}

impl<'a> OldInferencePass<'a> {
    pub fn perform(
        session: &'a mut TypeSession,
        scc: &'a SCCResolved,
        ast: &'a mut AST<NameResolved>,
    ) -> Inferenced {
        let groups = kosaraju_scc(&scc.graph);
        let mut pass = OldInferencePass {
            ast,
            scc,
            session,
            snapshots: Default::default(),
        };

        // Handle dependent binders first. This makes sure mutual recursion works.
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

        let mut wants = Wants::default();

        // Handle the rest of the AST
        let roots = std::mem::take(&mut pass.ast.roots);
        for root in roots.iter() {
            if !matches!(
                root,
                Node::Stmt(_)
                    | Node::Decl(Decl {
                        kind: DeclKind::Struct { .. }
                            | DeclKind::Enum { .. }
                            | DeclKind::Extend { .. }
                            | DeclKind::Protocol { .. }
                            | DeclKind::Method { .. }
                            | DeclKind::Let {
                                lhs: Pattern {
                                    // These don't get handled by the binding groups (i'm not sure if they should?)
                                    kind: PatternKind::Tuple(..) | PatternKind::Record { .. },
                                    ..
                                },
                                ..
                            },
                        ..
                    })
            ) {
                tracing::trace!("skipping decl: {root:?}");
                continue;
            }

            let ty = pass.infer_node(root, Level(1), &mut wants);
            pass.session.types_by_node.insert(root.node_id(), ty);
        }

        for conformance in pass.session.clone_conformances().values() {
            let ty = pass.session.lookup(&conformance.conforming_id).unwrap();
            wants.conforms(ty._as_ty(), conformance.protocol_id, conformance.span);
        }

        _ = std::mem::replace(&mut pass.ast.roots, roots);

        let (mut subs, unsolved) = pass.solve(Level(1), wants);
        pass.apply_to_self(&mut subs);

        for unsolved in unsolved {
            if let Constraint::Conforms(_conforms) = unsolved {
                // pass.ast
                //     .diagnostics
                //     .push(crate::diagnostic::AnyDiagnostic::Typing(Diagnostic {
                //         span: conforms.span,
                //         kind: TypeError::TypesDoesNotConform {
                //             protocol_id: conforms.protocol_id,
                //             symbol: conforms.symbol,
                //         },
                //     }))
                panic!("wip");
            }
        }

        // Move along, move along
        Inferenced {}
    }

    fn promote_pattern_bindings(
        &mut self,
        pattern: &Pattern,
        level: Level,
        unsolved: &[Constraint],
        subs: &mut UnificationSubstitutions,
    ) {
        use crate::node_kinds::pattern::{PatternKind, RecordFieldPatternKind};
        match &pattern.kind {
            PatternKind::Bind(Name::Resolved(sym, _)) => {
                if let Some(entry) = self.session.lookup(sym) {
                    let ty = match entry {
                        EnvEntry::Mono(t) => t,
                        EnvEntry::Scheme(s) => s.ty, // unlikely here, but safe
                    };
                    // Generalize with the current substitutions so metas turn into concrete types/params.
                    let scheme = self
                        .session
                        .generalize_with_substitutions(level, ty, unsolved, subs);
                    self.session.insert_term(*sym, scheme);
                }
            }
            PatternKind::Tuple(items) => {
                for p in items {
                    self.promote_pattern_bindings(p, level, unsolved, subs);
                }
            }
            PatternKind::Record { fields } => {
                for f in fields {
                    match &f.kind {
                        RecordFieldPatternKind::Bind(name) => {
                            if let Name::Resolved(sym, _) = name
                                && let Some(entry) = self.session.lookup(sym)
                            {
                                let ty = match entry {
                                    EnvEntry::Mono(t) => t,
                                    EnvEntry::Scheme(s) => s.ty,
                                };
                                let scheme = self
                                    .session
                                    .generalize_with_substitutions(level, ty, unsolved, subs);
                                self.session.insert_term(*sym, scheme);
                            }
                        }
                        RecordFieldPatternKind::Equals { value, .. } => {
                            self.promote_pattern_bindings(value, level, unsolved, subs);
                        }
                        RecordFieldPatternKind::Rest => {}
                    }
                }
            }
            // cover any other pattern forms you support
            _ => {}
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn infer_group(&mut self, group: &BindingGroup) -> Wants {
        let mut wants = Wants::default();
        let inner_level = group.level.next();

        for &binder in &group.binders {
            let symbol = Symbol::from(binder);

            if self.session.lookup(&symbol).is_none() {
                let ty = self.session.new_ty_meta_var(inner_level);
                self.session.insert_mono(symbol, ty);
            }
        }

        for &binder in &group.binders {
            let symbol = Symbol::from(binder);
            let Some(rhs_expr_id) = self.scc.rhs_map.get(&binder).copied() else {
                continue;
            };

            // Skip nodes from other ASTs - they'll be inferred when processing their own AST
            if rhs_expr_id.0 != self.ast.file_id {
                tracing::trace!("Skipping {:?} - belongs to a different file", rhs_expr_id);
                continue;
            }

            tracing::debug!(
                "Looking for rhs_expr_id: {:?} for binder {:?}",
                rhs_expr_id,
                binder
            );
            let rhs_expr = self
                .ast
                .find(rhs_expr_id)
                .clone()
                .unwrap_or_else(|| panic!("didn't find rhs_expr_id: {:?}", rhs_expr_id));
            let inferred = self.infer_node(&rhs_expr, inner_level, &mut wants);
            self.session
                .types_by_node
                .insert(rhs_expr_id, inferred.clone());

            let type_var = match self.session.lookup(&symbol) {
                Some(EnvEntry::Mono(t)) => t.clone(),
                Some(EnvEntry::Scheme(scheme)) => scheme.ty,
                _ => unreachable!("no env entry found for {symbol:?} {:#?}", self.session),
            };

            if let Some(annotation_id) = self.scc.annotation_map.get(&binder).cloned() {
                let Some(Node::TypeAnnotation(annotation)) = self.ast.find(annotation_id) else {
                    panic!("didn't find type annotation for annotation id");
                };

                let annotation_ty =
                    self.infer_type_annotation(&annotation, inner_level, &mut wants);

                wants.equals(
                    inferred.clone(),
                    annotation_ty,
                    ConstraintCause::Annotation(annotation_id),
                    annotation.span,
                );
            }

            wants.equals(
                inferred,
                type_var,
                ConstraintCause::Internal,
                rhs_expr.span(),
            );
        }

        wants
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(crate) fn infer_type_annotation(
        &mut self,
        annotation: &TypeAnnotation,
        level: Level,
        wants: &mut Wants,
    ) -> InferTy {
        guard_found_ty!(self, annotation.id);

        let ty = match &annotation.kind {
            TypeAnnotationKind::Func { .. } => todo!(),
            TypeAnnotationKind::Tuple(..) => todo!(),
            TypeAnnotationKind::Nominal {
                name: Name::Resolved(sym @ Symbol::Builtin(..), ..),
                ..
            } => builtins::resolve_builtin_type(sym).0,
            TypeAnnotationKind::Nominal {
                name: Name::Resolved(sym @ Symbol::TypeParameter(..), ..),
                name_span: _,
                generics: _,
            } => self
                .session
                .lookup(sym)
                .expect("did not get type param")
                .instantiate(annotation.id, self.session, level, wants, annotation.span),
            TypeAnnotationKind::Nominal {
                name: Name::Resolved(symbol, ..),
                ..
            } => InferTy::Nominal {
                symbol: *symbol,
                row: Box::new(self.session.new_row_meta_var(Level(1))),
            },
            TypeAnnotationKind::SelfType(Name::Resolved(sym, _)) => self
                .session
                .lookup(sym)
                .unwrap()
                .clone()
                .instantiate(annotation.id, self.session, level, wants, annotation.span),
            TypeAnnotationKind::Record { fields } => {
                let mut row = InferRow::Empty(TypeDefKind::Struct);
                for field in fields.iter().rev() {
                    row = InferRow::Extend {
                        row: Box::new(row),
                        label: field.label.name_str().into(),
                        ty: self.infer_type_annotation(&field.value, level, wants),
                    };
                }

                InferTy::Record(Box::new(row))
            }
            TypeAnnotationKind::NominalPath {
                base,
                member,
                member_span: _,
                member_generics,
            } => {
                let base = self.infer_type_annotation(base, level, wants);
                let result = self.session.new_ty_meta_var(level);
                let generics = member_generics
                    .iter()
                    .map(|g| self.infer_type_annotation(g, level, wants))
                    .collect();

                wants.push(Constraint::TypeMember(TypeMember {
                    base,
                    name: member.clone(),
                    generics,
                    result: result.clone(),
                    cause: ConstraintCause::TypeMember(annotation.id),
                    span: annotation.span,
                }));

                result
            }
            _ => unreachable!("{:?}", annotation.kind),
        };

        self.session.types_by_node.insert(annotation.id, ty.clone());

        ty
    }

    fn apply_to_self(&mut self, substitutions: &mut UnificationSubstitutions) {
        self.session.apply(substitutions);
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
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
                    Constraint::Construction(ref construction) => {
                        construction.solve(self.session, level, &mut next_wants, &mut substitutions)
                    }
                    Constraint::Equals(ref equals) => {
                        unify(&equals.lhs, &equals.rhs, &mut substitutions, self.session)
                    }
                    Constraint::Call(ref call) => {
                        call.solve(self.session, &mut next_wants, &mut substitutions)
                    }
                    Constraint::Conforms(ref conforms) => {
                        conforms.solve(self.session, &mut next_wants, &mut substitutions)
                    }
                    Constraint::Member(ref member) => {
                        member.solve(self.session, level, &mut next_wants, &mut substitutions)
                    }
                    Constraint::HasField(ref has_field) => {
                        has_field.solve(self.session, level, &mut next_wants, &mut substitutions)
                    }
                    Constraint::AssociatedEquals(ref associated_equals) => associated_equals.solve(
                        self.session,
                        level,
                        &mut next_wants,
                        &mut substitutions,
                    ),
                    Constraint::TypeMember(ref c) => {
                        c.solve(self.session, level, &mut next_wants, &mut substitutions)
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
                types_by_node: self.session.types_by_node.clone(),
            };

            // tracing::trace!("{snapshot:?}");
            self.snapshots.push(snapshot);
        }

        (substitutions, unsolved)
    }

    fn promote_group(
        &mut self,
        group: &BindingGroup,
        subs: &mut UnificationSubstitutions,
        predicates: Vec<Constraint>,
    ) {
        for &binder in &group.binders {
            let sym = Symbol::from(binder);

            match self.session.lookup(&sym) {
                Some(EnvEntry::Mono(ty)) => {
                    let applied = apply(ty, subs);
                    let scheme = self.session.generalize(group.level, applied, &predicates);
                    self.session.promote(sym, scheme);
                }
                Some(entry) => {
                    let (ty, _, _) = entry.into();
                    let applied = apply(ty, subs);
                    let scheme = self.session.generalize(group.level, applied, &predicates);
                    self.session.insert_term(sym, scheme);
                }
                None => panic!("didn't find {sym:?} in term env"),
            }
        }
    }

    fn infer_node(&mut self, node: &Node, level: Level, wants: &mut Wants) -> InferTy {
        match node {
            Node::Expr(expr) => self.infer_expr(expr, level, wants),
            Node::Stmt(stmt) => self.infer_stmt(stmt, level, wants),
            Node::Decl(decl) => self.infer_decl(decl, level, wants),
            Node::Block(block) => self.infer_block(block, level, wants),
            _ => unimplemented!(),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, decl, wants), fields(decl.id = %decl.id))]
    fn infer_decl(&mut self, decl: &Decl, level: Level, wants: &mut Wants) -> InferTy {
        let ty = match &decl.kind {
            DeclKind::Let {
                lhs,
                rhs,
                type_annotation: _,
            } => {
                guard_found_ty!(self, decl.id);
                let ty = self.session.new_ty_meta_var(level);
                let mut local_wants = Wants::default();
                self.check_pattern(lhs, &ty, level, &mut local_wants);

                if let Some(expr) = rhs {
                    let rhs_ty = self.infer_expr(expr, level.next(), &mut local_wants);
                    local_wants.equals(
                        ty.clone(),
                        rhs_ty,
                        ConstraintCause::Assignment(decl.id),
                        expr.span,
                    );
                }

                let (mut subs, unsolved) = self.solve(level, local_wants);
                let applied_ty = apply(ty.clone(), &mut subs);
                self.apply_to_self(&mut subs);

                if let PatternKind::Bind(Name::Resolved(sym, _)) = lhs.kind {
                    let scheme = self
                        .session
                        .generalize(level, applied_ty.clone(), &unsolved);
                    self.session.promote(sym, scheme);
                } else {
                    self.promote_pattern_bindings(lhs, level, &unsolved, &mut subs);
                }

                applied_ty
            }
            // DeclKind::Method { func, .. } => {
            //     tracing::info!("inferring method: {:?}", func.name);
            //     let func_ty = self.infer_func(func, level, wants);
            //     let entry = self.session.generalize(level, func_ty.clone(), &[]);
            //     self.session.promote(func.name.symbol(), entry);
            //     func_ty
            // }
            DeclKind::Method { func, .. } => {
                let method_sym = func.name.symbol();

                if let Some(EnvEntry::Scheme(scheme)) = self.session.lookup(&method_sym) {
                    tracing::debug!(
                        "skipping re-inference of {:?}: already has scheme",
                        func.name
                    );
                    return scheme.ty; // ← Return scheme's type, not Void
                }

                tracing::info!("inferring method: {:?}", func.name);
                let func_ty = self.infer_func(func, level, wants);
                let entry = self.session.generalize(level, func_ty.clone(), &[]);
                self.session.insert_term(method_sym, entry);
                func_ty
            }
            DeclKind::Init { name, params, body } => {
                guard_found_ty!(self, decl.id);
                // Look up the Init symbol's pre-computed type from type resolve pass
                let init_symbol = name.symbol();

                if let Some(entry) = self.session.lookup(&init_symbol) {
                    // Instantiate the scheme to get the function type
                    let func_ty = entry.instantiate(decl.id, self.session, level, wants, decl.span);

                    // Extract parameter types from the curried function
                    let mut param_tys = Vec::new();
                    let mut current = func_ty;
                    while let InferTy::Func(param_ty, rest) = current {
                        param_tys.push(*param_ty);
                        current = *rest;
                    }

                    // Bind parameters to their types
                    for (param, param_ty) in params.iter().zip(param_tys) {
                        self.session
                            .insert_mono(param.name.symbol(), param_ty.clone());
                        self.session.types_by_node.insert(param.id, param_ty);
                    }
                }

                _ = self.infer_block(body, level, wants);
                InferTy::Void
            }
            DeclKind::Struct {
                body,
                name: Name::Resolved(symbol, name),
                ..
            } => {
                let Some(_) = self.session.lookup_nominal(symbol) else {
                    self.ast
                        .diagnostics
                        .push(crate::diagnostic::AnyDiagnostic::Typing(Diagnostic {
                            span: decl.span,
                            kind: TypeError::TypeNotFound(name.to_string()),
                        }));

                    return InferTy::Void;
                };

                self.infer_block(body, level, wants)
            }
            DeclKind::Protocol { body, .. } => {
                // Protocols aren't nominals, they're protocols - just infer the body
                self.infer_block(body, level, wants)
            }
            DeclKind::Extend { body, .. } => {
                // Extensions can be on any type (nominals or builtins) - just infer the body
                self.infer_block(body, level, wants)
            }
            DeclKind::Property { .. } => InferTy::Void,
            DeclKind::TypeAlias(lhs, rhs) => {
                guard_found_ty!(self, decl.id);
                // If RHS is a simple nominal name, alias its EnvEntry directly.
                if let (
                    TypeAnnotationKind::Nominal {
                        name: Name::Resolved(lhs_sym, _),
                        ..
                    },
                    TypeAnnotationKind::Nominal {
                        name: Name::Resolved(rhs_sym, _),
                        ..
                    },
                ) = (&lhs.kind, &rhs.kind)
                    && let Some(entry) = self.session.lookup(rhs_sym)
                {
                    self.session.insert_term(*lhs_sym, entry);
                    return InferTy::Void;
                }

                // Otherwise, infer RHS type and GENERALIZE it before inserting.
                let level = Level(1);
                let mut wants = Wants::default();
                let rhs_ty = self.infer_type_annotation(rhs, level, &mut wants);
                let (_subs, unsolved) = (
                    UnificationSubstitutions::new(self.session.meta_levels.clone()),
                    wants.to_vec(),
                );
                let entry = self.session.generalize(level, rhs_ty, &unsolved);
                if let TypeAnnotationKind::Nominal {
                    name: Name::Resolved(lhs_sym, _),
                    ..
                } = &lhs.kind
                {
                    self.session.insert_term(*lhs_sym, entry);
                }
                InferTy::Void
            }

            _ => {
                tracing::warn!("unhandled: {decl:?}");
                InferTy::Void
            }
        };

        self.session.types_by_node.insert(decl.id, ty.clone());

        ty
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

                // wants._has_field(*row.clone(), variant_name.into(), payload);

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

    #[instrument(level = tracing::Level::TRACE, skip(self, block), fields(block.id = %block.id))]
    fn infer_block(&mut self, block: &Block, level: Level, wants: &mut Wants) -> InferTy {
        guard_found_ty!(self, block.id);

        // Very simple semantics: return the type of the last expression statement, else Void.
        // TODO: Handle explicit returns
        let mut last_ty = InferTy::Void;
        for node in &block.body {
            match node {
                Node::Stmt(stmt) => {
                    last_ty = self.infer_stmt(stmt, level, wants);
                }
                Node::Decl(decl) => {
                    self.infer_decl(decl, level, wants);
                }
                _ => continue,
            }
        }

        self.session.types_by_node.insert(block.id, last_ty.clone());

        last_ty
    }

    fn lookup_named_scheme(&mut self, expr: &Expr) -> Option<Scheme<InferTy>> {
        if let ExprKind::Variable(Name::Resolved(sym, _)) = &expr.kind
            && let Some(EnvEntry::Scheme(scheme)) = self.session.lookup(sym)
        {
            return Some(scheme.clone());
        }

        None
    }

    fn infer_expr(&mut self, expr: &Expr, level: Level, wants: &mut Wants) -> InferTy {
        guard_found_ty!(self, expr.id);

        let ty = match &expr.kind {
            ExprKind::Incomplete(..) => InferTy::Void,
            ExprKind::LiteralArray(items) => self.infer_array(items, level, wants),
            ExprKind::LiteralInt(_) => InferTy::Int,
            ExprKind::LiteralFloat(_) => InferTy::Float,
            ExprKind::LiteralTrue => InferTy::Bool,
            ExprKind::LiteralFalse => InferTy::Bool,
            ExprKind::Variable(Name::Resolved(sym, _)) => {
                match self.session.lookup(sym) {
                    Some(EnvEntry::Scheme(scheme)) => {
                        scheme
                            .instantiate(expr.id, self.session, level, wants, expr.span)
                            .0
                    } // or pass through
                    Some(EnvEntry::Mono(t)) => t.clone(),
                    None => {
                        panic!(
                            "variable not found in term env: {:?}, {:?}",
                            sym, self.session
                        )
                    }
                }
            }
            ExprKind::LiteralString(_) => InferTy::String(),
            ExprKind::Tuple(items) => InferTy::Tuple(
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
            ExprKind::Member(receiver, label, ..) => {
                self.infer_member(expr.id, receiver, label, level, wants)
            }
            ExprKind::Func(func) => self.infer_func(func, level, wants),
            ExprKind::If(box cond, conseq, alt) => {
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
                    conseq.span,
                );
                conseq_ty
            }
            ExprKind::Match(scrutinee, arms) => self.infer_match(scrutinee, arms, level, wants),
            ExprKind::RecordLiteral { fields, spread } => {
                self.infer_record_literal(fields, spread, level, wants)
            }
            ExprKind::Constructor(name) => InferTy::Constructor {
                name: name.clone(),
                params: vec![],
                ret: InferTy::Void.into(),
            },
            _ => unimplemented!(),
        };

        // // record the type for this expression node
        self.session.types_by_node.insert(expr.id, ty.clone());
        ty
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn infer_array(&mut self, items: &[Expr], level: Level, wants: &mut Wants) -> InferTy {
        // TODO: Make sure items are the same type
        let item_ty = if let Some(first) = items.first() {
            self.infer_expr(first, level, wants)
        } else {
            self.session.new_ty_meta_var(level)
        };

        InferTy::Array(item_ty)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
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

    fn infer_call(
        &mut self,
        callee: &Expr,
        type_args: &[TypeAnnotation],
        args: &[CallArg],
        level: Level,
        wants: &mut Wants,
    ) -> InferTy {
        let _s = tracing::info_span!(
            "infer_call",
            callee = format!("{callee:?}"),
            type_args = format!("{:?}", type_args),
            args = format!("{args:?}")
        )
        .entered();

        let callee_ty = if !type_args.is_empty()
            && let Some(scheme) = self.lookup_named_scheme(callee)
        {
            let type_args_tys: Vec<(InferTy, NodeID)> = type_args
                .iter()
                .map(|arg| (self.infer_type_annotation(arg, level, wants), arg.id))
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

        let mut arg_tys = Vec::with_capacity(args.len() + 1);

        for arg in args {
            arg_tys.push(self.infer_expr(&arg.value, level, wants));
        }

        let returns = self.session.new_ty_meta_var(level);
        let receiver = if let Expr {
            kind: ExprKind::Member(receiver, ..),
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
                callee.id,
                callee_ty,
                arg_tys,
                returns.clone(),
                *sym,
                ConstraintCause::Call(callee.id),
                callee.span,
            );
        } else {
            wants.call(
                callee.id,
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

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn infer_func(&mut self, func: &Func, level: Level, wants: &mut Wants) -> InferTy {
        guard_found_ty!(self, func.id);

        for generic in func.generics.iter() {
            let param_id = self.session.new_type_param_id(None);
            let skolem = self.session.new_skolem(param_id);
            self.session.insert_mono(generic.name.symbol(), skolem);
        }

        let mut param_tys: Vec<InferTy> = Vec::with_capacity(func.params.len());
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
            self.session.insert_mono(*sym, ty.clone());
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
            InferTy::Func(
                Box::new(InferTy::Void /* or Ty::Unit */),
                Box::new(ret_ty.clone()),
            )
        } else {
            curry(param_tys, ret_ty.clone())
        };

        let ty = substitute(func_ty, &self.session.skolem_map);
        self.session.types_by_node.insert(func.id, ty.clone());
        ty
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn infer_stmt(&mut self, stmt: &Stmt, level: Level, wants: &mut Wants) -> InferTy {
        guard_found_ty!(self, stmt.id);

        let ty = match &stmt.kind {
            StmtKind::Expr(expr) => self.infer_expr(expr, level, wants),
            StmtKind::If(cond, conseq, alt) => {
                self.infer_if_stmt(stmt.id, cond, conseq, alt, level, wants)
            }
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
                        InferTy::Bool,
                        ConstraintCause::Condition(cond.id),
                        cond.span,
                    );
                }

                self.infer_block(body, level, wants);

                InferTy::Void
            }
            _ => unimplemented!(),
        };

        self.session.types_by_node.insert(stmt.id, ty.clone());
        ty
    }

    fn infer_if_stmt(
        &mut self,
        id: NodeID,
        cond: &Expr,
        conseq: &Block,
        alt: &Option<Block>,
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
            InferTy::Void
        }
    }
}

pub fn curry<I: IntoIterator<Item = InferTy>>(params: I, ret: InferTy) -> InferTy {
    params
        .into_iter()
        .collect::<Vec<_>>()
        .into_iter()
        .rfold(ret, |acc, p| InferTy::Func(Box::new(p), Box::new(acc)))
}

pub fn collect_meta(ty: &InferTy, out: &mut FxHashSet<InferTy>) {
    match ty {
        InferTy::Param(_) => {
            out.insert(ty.clone());
        }
        InferTy::Var { .. } => {
            out.insert(ty.clone());
        }
        InferTy::Projection { base, .. } => {
            collect_meta(base, out);
        }
        InferTy::Func(dom, codom) => {
            collect_meta(dom, out);
            collect_meta(codom, out);
        }
        InferTy::Tuple(items) => {
            for item in items {
                collect_meta(item, out);
            }
        }
        InferTy::Record(box row) => match row {
            InferRow::Empty(..) => (),
            InferRow::Var(..) => {
                out.insert(ty.clone());
            }
            InferRow::Param(..) => (),
            InferRow::Extend { row, ty, .. } => {
                collect_meta(ty, out);
                collect_meta(&InferTy::Record(row.clone()), out);
            }
        },
        InferTy::Nominal { row, .. } => {
            collect_meta(&InferTy::Record(row.clone()), out);
        }
        InferTy::Constructor { params, .. } => {
            for param in params {
                collect_meta(param, out);
            }
        }
        InferTy::Primitive(_) | InferTy::Rigid(_) => {}
    }
}

#[derive(Clone, Debug)]
pub struct Typed {
    _types_by_node: FxHashMap<NodeID, InferTy>,
}
impl ASTPhase for Typed {}

pub struct InferenceResult {
    pub ast: AST<Typed>,
    pub diagnostics: Vec<Diagnostic<TypeError>>,
}
