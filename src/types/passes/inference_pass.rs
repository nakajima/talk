use indexmap::{IndexMap, IndexSet, indexset};
use itertools::Itertools;
use rustc_hash::FxHashMap;
use tracing::instrument;

use crate::{
    ast::AST,
    diagnostic::{AnyDiagnostic, Diagnostic},
    label::Label,
    name::Name,
    name_resolution::{
        name_resolver::NameResolved,
        scc_graph::BindingGroup,
        symbol::{ProtocolId, Symbol},
    },
    node::Node,
    node_id::NodeID,
    node_kinds::{
        block::Block,
        body::Body,
        call_arg::CallArg,
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        func::Func,
        func_signature::FuncSignature,
        generic_decl::GenericDecl,
        match_arm::MatchArm,
        parameter::Parameter,
        pattern::{Pattern, PatternKind, RecordFieldPatternKind},
        record_field::RecordField,
        stmt::{Stmt, StmtKind},
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
    span::Span,
    token_kind::TokenKind,
    types::{
        builtins::resolve_builtin_type,
        constraint_solver::ConstraintSolver,
        constraints::{
            constraint::{Constraint, ConstraintCause},
            member::consume_self,
        },
        infer_row::{InferRow, RowMetaId},
        infer_ty::{InferTy, Level, Meta, MetaVarId, TypeParamId},
        predicate::Predicate,
        scheme::{ForAll, Scheme},
        solve_context::{Solve, SolveContext, SolveContextKind},
        term_environment::EnvEntry,
        type_catalog::{Conformance, ConformanceKey, MemberWitness},
        type_error::TypeError,
        type_operations::{
            InstantiationSubstitutions, UnificationSubstitutions, apply, curry, instantiate_ty,
            substitute,
        },
        type_session::{TypeDefKind, TypeSession, collect_metas_in_constraint},
        wants::Wants,
    },
};

#[derive(Debug)]
pub enum GeneralizationBlock {
    PendingType {
        node_id: NodeID,
        span: Span,
        level: Level,
        type_symbol: Symbol,
        args: Vec<(InferTy, NodeID)>,
    },
    PatternBindLocal,
    EmptyArray,
    Placeholder,
}

pub type PendingTypeInstances =
    FxHashMap<MetaVarId, (NodeID, Span, Level, Symbol, Vec<(InferTy, NodeID)>)>;

pub struct InferencePass<'a> {
    asts: &'a mut [AST<NameResolved>],
    session: &'a mut TypeSession,
    canonical_rows: FxHashMap<Symbol, RowMetaId>,
    unsolved: IndexSet<Constraint>,
    #[allow(clippy::type_complexity)]
    instantiations: FxHashMap<NodeID, InstantiationSubstitutions>,
    substitutions: UnificationSubstitutions,
    generalization_blocks: FxHashMap<MetaVarId, GeneralizationBlock>,
}

impl<'a> InferencePass<'a> {
    pub fn drive(asts: &'a mut [AST<NameResolved>], session: &'a mut TypeSession) -> Wants {
        let result = Wants::default();
        let substitutions = UnificationSubstitutions::new(session.meta_levels.clone());
        let mut pass = InferencePass {
            asts,
            session,
            canonical_rows: Default::default(),
            instantiations: Default::default(),
            unsolved: Default::default(),
            substitutions,
            generalization_blocks: Default::default(),
        };

        pass.drive_all();

        result
    }

    fn drive_all(&mut self) {
        for i in 0..self.asts.len() {
            self.discover_protocols(i, Level::default());
            self.session.apply(&mut self.substitutions);
        }

        for i in 0..self.asts.len() {
            self.generate(i);
            self.session.apply(&mut self.substitutions);
        }

        self.check_conformances();
        self.session.apply(&mut self.substitutions);
        self.rectify_blocks();
    }

    fn discover_protocols(&mut self, idx: usize, level: Level) {
        let roots = std::mem::take(&mut self.asts[idx].roots);
        for root in roots.iter() {
            let Node::Decl(Decl {
                kind:
                    DeclKind::Protocol {
                        name: protocol_name @ Name::Resolved(Symbol::Protocol(protocol_id), ..),
                        body,
                        conformances,
                        ..
                    },
                ..
            }) = root
            else {
                continue;
            };

            for conformance in conformances {
                let Symbol::Protocol(conforms_to_id) = conformance.symbol() else {
                    tracing::error!("did not get protocol for conforms_to");
                    continue;
                };

                let key = ConformanceKey {
                    protocol_id: conforms_to_id,
                    conforming_id: protocol_name.symbol(),
                };

                self.session.type_catalog.conformances.insert(
                    key,
                    Conformance {
                        node_id: conformance.id,
                        conforming_id: protocol_name.symbol(),
                        protocol_id: conforms_to_id,
                        witnesses: Default::default(),
                        associated_types: Default::default(),
                        span: conformance.span,
                    },
                );
            }

            let protocol_self_id = self.session.new_type_param_id(None);
            let mut binders: IndexMap<Symbol, InferTy> = IndexMap::default();

            let mut context = SolveContext::new(
                self.substitutions.clone(),
                level,
                SolveContextKind::Protocol {
                    protocol_id: *protocol_id,
                    protocol_self: protocol_self_id,
                },
            );

            context.givens.insert(Predicate::Conforms {
                param: protocol_self_id,
                protocol_id: *protocol_id,
                span: root.span(),
            });
            self.session
                .type_param_bounds
                .entry(protocol_self_id)
                .or_default()
                .insert(Predicate::Conforms {
                    param: protocol_self_id,
                    protocol_id: *protocol_id,
                    span: root.span(),
                });
            self.session
                .insert(protocol_name.symbol(), InferTy::Param(protocol_self_id));

            for decl in body.decls.iter() {
                let DeclKind::Associated { generic } = &decl.kind else {
                    continue;
                };

                let ret_id = self.session.new_type_param_id(None);
                let ret = InferTy::Param(ret_id);

                #[warn(clippy::todo)]
                if !generic.conformances.is_empty() {
                    todo!("not handling associated type conformances yet");
                }

                let scheme = Scheme {
                    ty: ret.clone(),
                    foralls: indexset! { ForAll::Ty(protocol_self_id), ForAll::Ty(ret_id) },
                    predicates: vec![Predicate::Projection {
                        base: InferTy::Param(protocol_self_id),
                        label: generic.name.name_str().into(),
                        protocol_id: Some(*protocol_id),
                        returns: ret,
                    }],
                };

                self.session
                    .insert_term(generic.name.symbol(), EnvEntry::Scheme(scheme));
                self.session
                    .type_catalog
                    .associated_types
                    .entry(protocol_name.symbol())
                    .or_default()
                    .insert(generic.name.name_str().into(), generic.name.symbol());
            }

            for decl in body.decls.iter() {
                match &decl.kind {
                    DeclKind::MethodRequirement(func_signature)
                    | DeclKind::FuncSignature(func_signature) => {
                        let ty = self.visit_func_signature(
                            protocol_self_id,
                            *protocol_id,
                            func_signature,
                            &mut context,
                        );

                        binders.insert(func_signature.name.symbol(), ty.clone());

                        self.session.insert(func_signature.name.symbol(), ty);
                        self.session
                            .type_catalog
                            .method_requirements
                            .entry(protocol_name.symbol())
                            .or_default()
                            .insert(
                                func_signature.name.name_str().into(),
                                func_signature.name.symbol(),
                            );
                    }

                    DeclKind::Method { func, is_static } => {
                        let ty = self.visit_method(
                            protocol_name.symbol(),
                            func,
                            *is_static,
                            &mut context,
                        );
                        binders.insert(func.name.symbol(), ty);
                    }
                    _ => (),
                }
            }

            let (binders, placeholders) = binders.into_iter().unzip();
            self.solve(&mut context, binders, placeholders)
        }
        _ = std::mem::replace(&mut self.asts[idx].roots, roots);
    }

    #[instrument(skip(self))]
    fn check_conformances(&mut self) {
        for i in 0..self.asts.len() {
            for (key, conformance) in self.session.type_catalog.conformances.clone().iter() {
                self.check_conformance(i, key, conformance);
            }
        }
    }

    fn check_conformance(
        &mut self,
        idx: usize,
        key: &ConformanceKey,
        conformance: &Conformance<InferTy>,
    ) {
        let mut context = SolveContext::new(
            self.substitutions.clone(),
            Level::default(),
            SolveContextKind::Nominal,
        );
        let Some(protocol_self) = self.session.lookup(&Symbol::Protocol(key.protocol_id)) else {
            tracing::error!("did not get protocol_self for {key:?}");
            return;
        };

        let protocol_self_meta @ InferTy::Var { .. } = protocol_self.instantiate(
            conformance.node_id,
            &mut context,
            self.session,
            conformance.span,
        ) else {
            unreachable!();
        };

        let Some(conforming_self_entry) = self.session.lookup(&key.conforming_id) else {
            tracing::error!("Could not find conforming_self_entry for {key:?}");
            return;
        };

        let conforming_self = conforming_self_entry.instantiate(
            conformance.node_id,
            &mut context,
            self.session,
            conformance.span,
        );

        context.wants_mut().equals(
            protocol_self_meta.clone(),
            conforming_self.clone(),
            ConstraintCause::Internal,
            conformance.span,
        );

        let mut associated_substitutions = FxHashMap::<InferTy, InferTy>::default();
        for child_sym in self.asts[idx]
            .phase
            .child_types
            .get(&key.protocol_id.into())
            .cloned()
            .unwrap_or_default()
            .iter()
            .filter(|sym| matches!(sym.1, Symbol::AssociatedType(..)))
        {
            let conforming_children = self.asts[idx]
                .phase
                .child_types
                .get(&key.conforming_id)
                .cloned()
                .unwrap_or_default();
            let concrete = if let Some(conforming) = conforming_children.get(child_sym.0)
                && let Some(concrete) = self.session.lookup(conforming)
            {
                concrete.instantiate(
                    conformance.node_id,
                    &mut context,
                    self.session,
                    conformance.span,
                )
            } else {
                let Some(ty) = conformance.associated_types.get(child_sym.0).cloned() else {
                    tracing::error!("Did not get associated type {child_sym:?}");
                    continue;
                };

                ty
            };

            associated_substitutions.insert(
                InferTy::Projection {
                    base: protocol_self_meta.clone().into(),
                    associated: child_sym.0.clone(),
                    protocol_id: key.protocol_id,
                },
                concrete.clone(),
            );
            context.wants_mut().projection(
                conformance.node_id,
                conforming_self.clone(),
                child_sym.0.clone(),
                Some(key.protocol_id),
                concrete,
                ConstraintCause::Internal,
                conformance.span,
            );
        }

        let requirements = self
            .session
            .lookup_method_requirements(&key.protocol_id)
            .unwrap_or_default();

        println!("requirements: {requirements:?}");

        for (label, sym) in requirements.clone() {
            tracing::trace!("checking req {label:?} {sym:?}");
            let Some(requirement_entry) = self.session.lookup(&sym) else {
                self.asts[idx]
                    .diagnostics
                    .push(AnyDiagnostic::Typing(Diagnostic {
                        kind: TypeError::MissingConformanceRequirement(format!(
                            "{label:?} {sym:?}"
                        )),
                        span: conformance.span,
                    }));

                continue;
            };

            let Some((witness_entry_sym, _)) =
                self.session.lookup_member(&key.conforming_id, &label)
            else {
                self.asts[idx]
                    .diagnostics
                    .push(AnyDiagnostic::Typing(Diagnostic {
                        kind: TypeError::MissingConformanceRequirement(format!(
                            "{label:?} {sym:?}"
                        )),
                        span: conformance.span,
                    }));
                continue;
            };

            if !matches!(key.conforming_id, Symbol::Protocol(..))
                && matches!(witness_entry_sym, Symbol::MethodRequirement(..))
            {
                self.asts[idx]
                    .diagnostics
                    .push(AnyDiagnostic::Typing(Diagnostic {
                        kind: TypeError::MissingConformanceRequirement(format!(
                            "{label:?} {sym:?}"
                        )),
                        span: conformance.span,
                    }));
                continue;
            }

            println!("WITNESS ENTRY SYM: {witness_entry_sym:?}");

            tracing::trace!("Inserting witness {sym:?} {label:?} -> {witness_entry_sym:?}");
            self.session
                .type_catalog
                .conformances
                .entry(*key)
                .and_modify(|conformance| {
                    conformance.witnesses.insert(label, witness_entry_sym);
                });

            let Some(witness_entry) = self.session.lookup(&witness_entry_sym) else {
                tracing::error!("did not find witness entry for {witness_entry_sym:?}");
                continue;
            };
            let witness_ty = witness_entry.instantiate(
                NodeID::SYNTHESIZED,
                &mut context,
                self.session,
                conformance.span,
            );

            let requirement_ty = requirement_entry.instantiate(
                NodeID::SYNTHESIZED,
                &mut context,
                self.session,
                conformance.span,
            );

            let (req_self, requirement_ty) = consume_self(&requirement_ty);
            let (wit_self, witness_ty) = consume_self(&witness_ty);

            let requirement_ty = substitute(requirement_ty, &associated_substitutions);

            context.wants_mut().equals(
                req_self,
                wit_self,
                ConstraintCause::Internal,
                conformance.span,
            );

            context.wants_mut().equals(
                requirement_ty,
                witness_ty,
                ConstraintCause::Internal,
                conformance.span,
            );
        }

        let solver =
            ConstraintSolver::new(&mut context, self.asts, std::mem::take(&mut self.unsolved));

        solver.solve(self.session);
        self.substitutions.extend(&context.substitutions);
        self.session.apply(&mut context.substitutions);

        // Rewrite the conformance's associated_types using the solution,
        // so later Projection(Self.T) sees the *solved* witness type.
        let Some(conf_mut) = self.session.type_catalog.conformances.get_mut(key) else {
            unreachable!()
        };

        for ty in conf_mut.associated_types.values_mut() {
            *ty = apply(ty.clone(), &mut context.substitutions);
            *ty = instantiate_ty(
                conformance.node_id,
                ty.clone(),
                &context.instantiations,
                context.level(),
            );
        }
    }

    #[instrument(skip(self))]
    fn rectify_blocks(&mut self) {
        tracing::debug!(
            "Before rectify_blocks, unsolved: {} constraints",
            self.unsolved.len()
        );
        let mut context = SolveContext::new(
            self.substitutions.clone(),
            Level::default(),
            SolveContextKind::Normal,
        );
        let generalization_blocks = std::mem::take(&mut self.generalization_blocks);
        for (var_id, block) in generalization_blocks {
            tracing::debug!("rectifying generalization blocks: {var_id:?} {block:?}");
            let GeneralizationBlock::PendingType {
                node_id,
                span,
                level,
                type_symbol,
                args,
            } = &block
            else {
                self.generalization_blocks.insert(var_id, block);
                continue;
            };

            let Some(entry) = self.session.lookup(type_symbol) else {
                self.generalization_blocks.insert(var_id, block);
                continue;
            };

            let (instance, instantiations) = entry.instantiate_with_args(
                *node_id,
                args,
                self.session,
                *level,
                context.wants_mut(),
                *span,
            );

            context.instantiations_mut().ty.extend(instantiations.ty);
            context.instantiations_mut().row.extend(instantiations.row);

            self.substitutions.ty.insert(var_id, instance);
        }

        self.session.apply(&mut self.substitutions);
        context.wants_mut().apply(&mut self.substitutions);

        // Also apply substitutions to unsolved constraints so they can be retried
        // with resolved types after rectification
        let mut updated_unsolved = IndexSet::new();
        for constraint in std::mem::take(&mut self.unsolved) {
            updated_unsolved.insert(constraint.apply(&mut self.substitutions));
        }
        tracing::debug!(
            "After applying constraints in rectify_blocks, unsolved: {} constraints",
            updated_unsolved.len()
        );
        self.unsolved = updated_unsolved;
        self.solve(&mut context, vec![], vec![]);
    }

    #[instrument(skip(self))]
    fn rectify_witnesses(&mut self) {
        for (_node_id, witness) in self.session.type_catalog.member_witnesses.iter_mut() {
            if let MemberWitness::Meta { receiver, label } = witness {
                let receiver_ty = apply(receiver.clone(), &mut self.substitutions);
                let symbol = match receiver_ty {
                    InferTy::Primitive(symbol) => symbol,
                    InferTy::Nominal { symbol, .. } => symbol,
                    _ => {
                        tracing::warn!(
                            "Unable to resolve witness: {witness:?} for {receiver_ty:?} (original: {:?})",
                            receiver.clone()
                        );
                        continue;
                    }
                };

                if let Some(methods) = self.session.type_catalog.instance_methods.get(&symbol)
                    && let Some(method) = methods.get(label)
                {
                    tracing::trace!(
                        "Resolved concrete witness {receiver_ty:?}.{label:?} = {method:?}"
                    );
                    *witness = MemberWitness::Concrete(*method);
                    continue;
                }

                tracing::warn!("Unable to resolve witness: {witness:?} for {receiver_ty:?}");
            };
        }
    }

    fn generate(&mut self, idx: usize) {
        let mut groups = self.asts[idx].phase.scc_graph.groups();

        // Sort by level in descending order so inner bindings are generalized first
        // Use stable sort to preserve topological order for groups at the same level
        groups.sort_by_key(|group| std::cmp::Reverse(group.level.0));

        for group in groups {
            self.generate_for_group(idx, group);
        }

        let mut context = SolveContext::new(
            self.substitutions.clone(),
            Level::default(),
            SolveContextKind::Normal,
        );

        tracing::debug!("visiting stragglers");
        for id in self.asts[idx].phase.unbound_nodes.clone() {
            let Some(node) = self.asts.iter().find_map(|ast| ast.find(id)) else {
                tracing::error!("Did not find ast node for id: {id:?}");
                continue;
            };

            self.visit_node(&node, &mut context);
        }

        let solver =
            ConstraintSolver::new(&mut context, self.asts, std::mem::take(&mut self.unsolved));
        let unsolved = solver.solve(self.session);
        self.unsolved.extend(unsolved);
        self.substitutions.extend(&context.substitutions);

        // Apply substitutions to types_by_node for top-level expressions
        self.session.apply(&mut context.substitutions);
    }

    #[instrument(skip(self))]
    fn generate_for_group(&mut self, idx: usize, group: BindingGroup) {
        let mut context = SolveContext::new(
            self.substitutions.clone(),
            group.level,
            SolveContextKind::Normal,
        );

        // Create placeholders
        let placeholders = group
            .binders
            .iter()
            .map(|sym| {
                let placeholder_id = self.session.new_ty_meta_var_id(group.level);
                let placeholder = InferTy::Var {
                    id: placeholder_id,
                    level: context.level(),
                };
                tracing::trace!("placeholder {sym:?} = {placeholder:?}");
                self.session.insert_term(*sym, placeholder.to_entry());
                placeholder
            })
            .collect_vec();

        // Visit each binder
        for (i, binder) in group.binders.iter().enumerate() {
            if let Some(captures) = self.asts[idx].phase.captures.get(binder) {
                for capture in captures {
                    if self.session.lookup(&capture.symbol).is_none() {
                        let placeholder = self.session.new_ty_meta_var(capture.level);
                        tracing::trace!(
                            "capture placeholder {:?} = {placeholder:?}",
                            capture.symbol
                        );
                        self.session
                            .insert_term(capture.symbol, placeholder.to_entry());
                    }
                }
            }

            let Some(rhs_id) = self.asts[idx].phase.scc_graph.rhs_id_for(binder) else {
                tracing::error!("did not find rhs_id for binder: {binder:?}");
                return;
            };

            let Some(rhs) = self.asts.iter().find_map(|ast| ast.find(*rhs_id)) else {
                tracing::error!("did not find rhs for id: {rhs_id:?}, binder: {binder:?}");
                return;
            };

            let ty = self.visit_node(&rhs, &mut context);

            if let Some(existing) = self.session.lookup(binder) {
                if existing == EnvEntry::Mono(placeholders[i].clone()) {
                    context.wants_mut().equals(
                        ty,
                        placeholders[i].clone(),
                        ConstraintCause::Internal,
                        rhs.span(),
                    );
                } else {
                    context.wants_mut().equals(
                        placeholders[i].clone(),
                        existing._as_ty(),
                        ConstraintCause::Internal,
                        rhs.span(),
                    );
                }
            }
        }

        // Solve this group
        self.solve(&mut context, group.binders, placeholders)
    }

    fn solve(
        &mut self,
        context: &mut SolveContext,
        binders: Vec<Symbol>,
        placeholders: Vec<InferTy>,
    ) {
        context.substitutions_mut().extend(&self.substitutions);
        tracing::debug!(
            "After extend, context substitutions: {:?}",
            context.substitutions_mut()
        );
        let solver = ConstraintSolver::new(context, self.asts, std::mem::take(&mut self.unsolved));
        let unsolved = solver.solve(self.session);

        // Ok, hear me out. I know this is messy. We don't want to generalize metas that have pending type instances
        // and we want to hang on to constraints that contain them instead of converting them to predicates during
        // generalization. So we need to grab those and set them aside.
        let (generalizable, needs_defer): (IndexSet<_>, IndexSet<_>) =
            unsolved.into_iter().partition(|c| {
                let mut out = Default::default();
                collect_metas_in_constraint(c, &mut out);
                for ty in out {
                    let InferTy::Var { id, .. } = ty else {
                        continue;
                    };

                    if self.generalization_blocks.contains_key(&id) {
                        tracing::trace!(
                            "Deferring constraint {:?} because meta({:?}) has generalization block",
                            c,
                            id
                        );
                        return false;
                    }
                }

                tracing::trace!("Considering constraint {:?} as generalizable", c);
                true
            });

        tracing::debug!(
            "After partition: {} generalizable, {} needs_defer",
            generalizable.len(),
            needs_defer.len()
        );
        self.unsolved.extend(needs_defer);

        for (i, binder) in binders.iter().enumerate() {
            let ty = apply(placeholders[i].clone(), &mut context.substitutions);
            let entry = self.session.generalize(
                context.level(),
                ty,
                &generalizable,
                &self.generalization_blocks,
            );
            self.session.promote(*binder, entry);
        }

        self.substitutions.extend(&context.substitutions);
        self.session.apply(&mut self.substitutions);
        self.rectify_witnesses();
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, node, context), fields(node.id = ?node.node_id()))]
    fn visit_node(&mut self, node: &Node, context: &mut impl Solve) -> InferTy {
        let ty = match &node {
            Node::Decl(decl) => self.visit_decl(decl, context),
            Node::Stmt(stmt) => self.visit_stmt(stmt, context),
            Node::Expr(expr) => self.visit_expr(expr, context),
            Node::Parameter(param) => self.visit_param(param, context),
            _ => InferTy::Error(
                TypeError::TypeNotFound(format!("No type checking for {node:?}")).into(),
            ),
        };

        self.session
            .types_by_node
            .entry(node.node_id())
            .or_insert(ty.clone());

        ty
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, decl, context), fields(decl.id = ?decl.id))]
    fn visit_decl(&mut self, decl: &Decl, context: &mut impl Solve) -> InferTy {
        match &decl.kind {
            DeclKind::Let {
                lhs,
                type_annotation,
                rhs,
            } => self.visit_let(lhs, type_annotation, rhs, context),
            DeclKind::Struct {
                name,
                generics,
                conformances,
                body,
                ..
            } => self.visit_nominal(decl, name, generics, conformances, body, context),
            DeclKind::Protocol { .. } => InferTy::Void,
            DeclKind::Init { .. } => {
                unreachable!("inits are handled by visit_struct")
            }

            DeclKind::Extend {
                name,
                conformances,
                generics,
                body,
                ..
            } => self.visit_nominal(decl, name, generics, conformances, body, context),
            DeclKind::Enum {
                name,
                generics,
                conformances,
                body,
                ..
            } => self.visit_nominal(decl, name, generics, conformances, body, context),
            DeclKind::Func(..)
            | DeclKind::TypeAlias(..)
            | DeclKind::Associated { .. }
            | DeclKind::Method { .. }
            | DeclKind::Property { .. }
            | DeclKind::MethodRequirement(..)
            | DeclKind::FuncSignature(..)
            | DeclKind::EnumVariant(..) => unreachable!("handled elsewhere"),
            _ => InferTy::Void,
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, stmt, context), fields(stmt.id = ?stmt.id))]
    fn visit_stmt(&mut self, stmt: &Stmt, context: &mut impl Solve) -> InferTy {
        let ty = match &stmt.kind {
            StmtKind::Expr(expr) => self.visit_expr(expr, context),
            StmtKind::If(cond, conseq, alt) => self.visit_if_stmt(cond, conseq, alt, context),
            StmtKind::Assignment(lhs, rhs) => {
                let lhs_ty = self.visit_expr(lhs, context);
                let rhs_ty = self.visit_expr(rhs, context);
                context.wants_mut().equals(
                    lhs_ty,
                    rhs_ty,
                    ConstraintCause::Assignment(stmt.id),
                    stmt.span,
                );
                InferTy::Void
            }
            #[warn(clippy::todo)]
            StmtKind::Return(_expr) => todo!(),
            #[warn(clippy::todo)]
            StmtKind::Break => todo!(),
            StmtKind::Loop(cond, block) => {
                if let Some(cond) = cond {
                    let cond_ty = self.visit_expr(cond, context);
                    context.wants_mut().equals(
                        cond_ty,
                        InferTy::Bool,
                        ConstraintCause::Condition(cond.id),
                        cond.span,
                    );
                }

                self.infer_block(block, context);

                InferTy::Void
            }
        };

        self.session.types_by_node.insert(stmt.id, ty.clone());

        ty
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, expr, context), fields(expr.id = ?expr.id))]
    fn visit_expr(&mut self, expr: &Expr, context: &mut impl Solve) -> InferTy {
        let ty = match &expr.kind {
            ExprKind::LiteralArray(items) => self.visit_array(items, context),
            ExprKind::LiteralInt(_) => InferTy::Int,
            ExprKind::LiteralFloat(_) => InferTy::Float,
            ExprKind::LiteralTrue | ExprKind::LiteralFalse => InferTy::Bool,
            ExprKind::LiteralString(_) => InferTy::String(),
            ExprKind::Tuple(exprs) => match exprs.len() {
                0 => InferTy::Void,
                1 => self.visit_expr(&exprs[0], context),
                _ => InferTy::Tuple(
                    exprs
                        .iter()
                        .map(|e| self.visit_expr(e, context))
                        .collect_vec(),
                ),
            },
            #[warn(clippy::todo)]
            ExprKind::Block(..) => todo!(),
            ExprKind::Binary(box lhs, TokenKind::AmpAmp, box rhs) => {
                let lhs_ty = self.visit_expr(lhs, context);
                let rhs_ty = self.visit_expr(rhs, context);
                context.wants_mut().equals(
                    lhs_ty,
                    InferTy::Bool,
                    ConstraintCause::Internal,
                    lhs.span,
                );
                context.wants_mut().equals(
                    rhs_ty,
                    InferTy::Bool,
                    ConstraintCause::Internal,
                    rhs.span,
                );
                InferTy::Bool
            }
            ExprKind::Binary(box lhs, TokenKind::PipePipe, box rhs) => {
                let lhs_ty = self.visit_expr(lhs, context);
                let rhs_ty = self.visit_expr(rhs, context);
                context.wants_mut().equals(
                    lhs_ty,
                    InferTy::Bool,
                    ConstraintCause::Internal,
                    lhs.span,
                );
                context.wants_mut().equals(
                    rhs_ty,
                    InferTy::Bool,
                    ConstraintCause::Internal,
                    rhs.span,
                );
                InferTy::Bool
            }
            ExprKind::Unary(..) | ExprKind::Binary(..) => {
                unreachable!("these are lowered to calls earlier")
            }
            ExprKind::Call {
                callee,
                type_args,
                args,
            } => self.visit_call(callee, type_args, args, &mut context.next()),
            ExprKind::Member(receiver, label, ..) => {
                self.visit_member(expr, receiver, label, context)
            }
            ExprKind::Func(func) => self.visit_func(func, context),
            ExprKind::Variable(name) => self.visit_variable(expr, name, &mut context.next()),
            ExprKind::Constructor(name) => self.visit_constructor(expr, name, context),
            ExprKind::If(cond, conseq, alt) => self.infer_if_expr(cond, conseq, alt, context),
            ExprKind::Match(scrutinee, arms) => self.infer_match(scrutinee, arms, context),
            ExprKind::RecordLiteral { fields, spread } => {
                self.infer_record_literal(fields, spread, context)
            }
            #[warn(clippy::todo)]
            ExprKind::RowVariable(..) => todo!(),
            ExprKind::As(box lhs, rhs) => self.visit_as(lhs, rhs, context),
            _ => unimplemented!(),
        };

        self.session.types_by_node.insert(expr.id, ty.clone());

        ty
    }

    fn visit_as(&mut self, lhs: &Expr, rhs: &TypeAnnotation, context: &mut impl Solve) -> InferTy {
        let lhs_ty = self.visit_expr(lhs, context);
        let Symbol::Protocol(id) = rhs.symbol() else {
            return InferTy::Error(
                TypeError::MissingConformanceRequirement("not a protocol".into()).into(),
            );
        };

        context.wants_mut().conforms(lhs_ty.clone(), id, lhs.span);
        lhs_ty
    }

    fn visit_array(&mut self, items: &[Expr], context: &mut impl Solve) -> InferTy {
        let Some(first_item) = items.first() else {
            let id = self.session.new_ty_meta_var_id(context.level());
            self.generalization_blocks
                .insert(id, GeneralizationBlock::EmptyArray);
            return InferTy::Array(InferTy::Var {
                id,
                level: context.level(),
            });
        };

        let item_ty = self.visit_expr(first_item, context);

        for expr in items[1..].iter() {
            let ty = self.visit_expr(expr, context);
            context
                .wants_mut()
                .equals(item_ty.clone(), ty, ConstraintCause::Internal, expr.span);
        }

        InferTy::Array(item_ty)
    }

    fn visit_func_signature(
        &mut self,
        protocol_self_id: TypeParamId,
        protocol_id: ProtocolId,
        func_signature: &FuncSignature,
        context: &mut impl Solve,
    ) -> InferTy {
        for generic in func_signature.generics.iter() {
            let param_id = self.session.new_type_param_id(None);
            self.session
                .insert_mono(generic.name.symbol(), InferTy::Param(param_id));
        }
        let params = self.visit_params(&func_signature.params, context);
        let ret = if let Some(ret) = &func_signature.ret {
            self.visit_type_annotation(ret, context)
        } else {
            InferTy::Void
        };

        let ty = curry(params, ret);
        let mut foralls: IndexSet<_> = ty.collect_foralls().into_iter().collect();
        foralls.insert(ForAll::Ty(protocol_self_id));
        let predicates = vec![Predicate::<InferTy>::Conforms {
            param: protocol_self_id,
            protocol_id,
            span: func_signature.span,
        }];

        self.session.insert_term(
            func_signature.name.symbol(),
            EnvEntry::Scheme(Scheme {
                ty: ty.clone(),
                foralls,
                predicates,
            }),
        );

        ty
    }

    fn visit_constructor(
        &mut self,
        _expr: &Expr,
        name: &Name,
        _context: &mut impl Solve,
    ) -> InferTy {
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
        context: &mut impl Solve,
    ) -> InferTy {
        let receiver_ty = if let Some(receiver) = receiver {
            self.visit_expr(receiver, context)
        } else {
            self.session.new_ty_meta_var(context.level().next())
        };

        let ret = self.session.new_ty_meta_var(context.level().next());

        context.wants_mut().member(
            expr.id,
            receiver_ty,
            label.clone(),
            ret.clone(),
            ConstraintCause::Member(expr.id),
            expr.span,
        );

        ret
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, generics, conformances, body, context))]
    fn visit_nominal(
        &mut self,
        decl: &Decl,
        name: &Name,
        generics: &[GenericDecl],
        conformances: &[TypeAnnotation],
        body: &Body,
        context: &mut impl Solve,
    ) -> InferTy {
        for generic in generics.iter() {
            self.register_generic(generic, context);
        }

        let nominal_symbol = name.symbol();
        let row_placeholder_id = self.canonical_row_for(&nominal_symbol, context.level());
        let row_placeholder = InferRow::Var(row_placeholder_id);
        let ty = InferTy::Nominal {
            symbol: name.symbol(),
            row: row_placeholder.clone().into(),
        };

        let mut row_types = vec![];

        for decl in body.decls.iter() {
            match &decl.kind {
                DeclKind::Init { name, params, body } => {
                    self.visit_init(ty.clone(), name, params, body, &mut context.next());
                }
                DeclKind::Method { func, is_static } => {
                    self.visit_method(nominal_symbol, func, *is_static, &mut context.next());
                }
                DeclKind::EnumVariant(name, _, values) => {
                    self.session
                        .type_catalog
                        .variants
                        .entry(nominal_symbol)
                        .or_default()
                        .insert(name.name_str().into(), name.symbol());

                    let tys = values
                        .iter()
                        .map(|v| self.visit_type_annotation(v, &mut context.next()))
                        .collect_vec();

                    let values_ty = match tys.len() {
                        0 => InferTy::Void,
                        1 => tys[0].clone(),
                        _ => InferTy::Tuple(tys.to_vec()),
                    };

                    self.session.insert(name.symbol(), values_ty.clone());
                    row_types.push((name.name_str(), values_ty));
                }
                DeclKind::Property {
                    name,
                    is_static,
                    type_annotation,
                    default_value,
                    ..
                } => {
                    row_types.push((
                        name.name_str(),
                        self.visit_property(
                            nominal_symbol,
                            name,
                            *is_static,
                            type_annotation,
                            default_value,
                            context,
                        ),
                    ));
                }
                DeclKind::TypeAlias(lhs, .., rhs) => {
                    let rhs_ty = self.visit_type_annotation(rhs, context);

                    // Quantify over the enclosing nominal's generics so the alias can be
                    // instantiated at use sites (e.g., Person<A>.T = A ⇒ T specializes to α).
                    let mut foralls: IndexSet<ForAll> = IndexSet::new();
                    for g in generics {
                        if let Some(entry) = self.session.lookup(&g.name.symbol())
                            && let InferTy::Param(pid) = entry._as_ty()
                        {
                            foralls.insert(ForAll::Ty(pid));
                        }
                    }

                    let entry = if foralls.is_empty() {
                        EnvEntry::Mono(rhs_ty)
                    } else {
                        EnvEntry::Scheme(Scheme {
                            ty: rhs_ty,
                            foralls,
                            predicates: Default::default(),
                        })
                    };

                    self.session.insert_term(lhs.symbol(), entry);
                }
                _ => tracing::warn!("Unhandled nominal decl: {:?}", decl.kind),
            }
        }

        for conformance in conformances {
            self.register_conformance(
                &ty,
                nominal_symbol,
                conformance.symbol(),
                conformance.id,
                conformance.span,
                context,
            );
        }

        if !matches!(decl.kind, DeclKind::Extend { .. }) {
            let empty_kind = if matches!(nominal_symbol, Symbol::Struct(..)) {
                TypeDefKind::Struct
            } else {
                TypeDefKind::Enum
            };

            let real_row = row_types
                .iter()
                .fold(InferRow::Empty(empty_kind), |acc, (name, ty)| {
                    InferRow::Extend {
                        row: acc.into(),
                        label: name.into(),
                        ty: substitute(ty.clone(), &self.session.skolem_map),
                    }
                });

            context.wants_mut().equals(
                InferTy::Nominal {
                    symbol: nominal_symbol,
                    row: row_placeholder.into(),
                },
                InferTy::Nominal {
                    symbol: nominal_symbol,
                    row: real_row.clone().into(),
                },
                ConstraintCause::Internal,
                body.span,
            );

            // Replace all instances of the placeholder row
            let mut substitutions = UnificationSubstitutions::new(self.session.meta_levels.clone());

            substitutions
                .row
                .insert(row_placeholder_id, real_row.clone());

            let foralls: IndexSet<_> = ty.collect_foralls().into_iter().collect();
            let entry = if foralls.is_empty() {
                EnvEntry::Mono(ty.clone())
            } else {
                EnvEntry::Scheme(Scheme {
                    foralls,
                    predicates: vec![],
                    ty: ty.clone(),
                })
            };

            self.session.insert_term(nominal_symbol, entry);

            let ty = InferTy::Nominal {
                symbol: nominal_symbol,
                row: real_row.into(),
            };

            return ty;
        }

        InferTy::Void
    }

    fn register_conformance(
        &mut self,
        ty: &InferTy,
        nominal_symbol: Symbol,
        conformance_symbol: Symbol,
        conformance_node_id: NodeID,
        conformance_span: Span,
        context: &mut impl Solve,
    ) {
        let Symbol::Protocol(protocol_id) = conformance_symbol else {
            tracing::error!("didnt get protocol id for conformance: {conformance_symbol:?}");
            return;
        };

        let indirect_conformance_keys = self
            .session
            .type_catalog
            .conformances
            .keys()
            .filter(|c| c.conforming_id == conformance_symbol)
            .copied()
            .collect_vec();

        for indirect_conformance in indirect_conformance_keys {
            let (sym, node_id, span) = {
                let indirect = self
                    .session
                    .type_catalog
                    .conformances
                    .get(&indirect_conformance)
                    .unwrap_or_else(|| unreachable!());
                (
                    Symbol::Protocol(indirect.protocol_id),
                    indirect.node_id,
                    indirect.span,
                )
            };

            self.register_conformance(ty, nominal_symbol, sym, node_id, span, context);
        }

        let associated_types = self
            .session
            .type_catalog
            .associated_types
            .get(&conformance_symbol)
            .cloned()
            .unwrap_or_default()
            .iter()
            .fold(FxHashMap::default(), |mut acc, (label, _)| {
                let child_types = self
                    .asts
                    .iter()
                    .find_map(|ast| ast.phase.child_types.get(&nominal_symbol))
                    .cloned();
                let associated_ty = if let Some(child_types) = &child_types
                    && let Some(child_sym) = child_types.get(label)
                    && let Some(entry) = self.session.lookup(child_sym)
                {
                    entry._as_ty()
                } else {
                    self.session.new_ty_meta_var(context.level())
                };

                acc.insert(label.clone(), associated_ty);
                acc
            });

        self.session.type_catalog.conformances.insert(
            ConformanceKey {
                protocol_id,
                conforming_id: nominal_symbol,
            },
            Conformance {
                node_id: conformance_node_id,
                conforming_id: nominal_symbol,
                protocol_id,
                witnesses: Default::default(),
                associated_types,
                span: conformance_span,
            },
        );
        context
            .wants_mut()
            .conforms(ty.clone(), protocol_id, conformance_span);
    }

    // fn visit_extend(
    //     &mut self,
    //     name: &Name,
    //     conformances: &[TypeAnnotation],
    //     generics: &[GenericDecl],
    //     body: &Body,
    //     context: &mut impl Solve,
    // ) -> InferTy {
    //     for generic in generics.iter() {
    //         let param_id = self.session.new_type_param_id(None);
    //         self.session
    //             .insert_mono(generic.name.symbol(), InferTy::Param(param_id));
    //     }

    //     let nominal_symbol = name.symbol();
    //     let row_placeholder_id = self.canonical_row_for(&nominal_symbol, context.level());
    //     let row_placeholder = InferRow::Var(row_placeholder_id);
    //     let ty = InferTy::Nominal {
    //         symbol: name.symbol(),
    //         row: row_placeholder.clone().into(),
    //     };

    //     let mut row_types = vec![];

    //     for decl in body.decls.iter() {
    //         match &decl.kind {
    //             DeclKind::Init { name, params, body } => {
    //                 self.visit_init(ty.clone(), name, params, body, &mut context.next());
    //             }
    //             DeclKind::Method { func, is_static } => {
    //                 self.visit_method(nominal_symbol, func, *is_static, &mut context.next());
    //             }
    //             DeclKind::EnumVariant(name, _, values) => {
    //                 self.session
    //                     .type_catalog
    //                     .variants
    //                     .entry(nominal_symbol)
    //                     .or_default()
    //                     .insert(name.name_str().into(), name.symbol());

    //                 let tys = values
    //                     .iter()
    //                     .map(|v| self.visit_type_annotation(v, context))
    //                     .collect_vec();

    //                 let values_ty = match tys.len() {
    //                     0 => InferTy::Void,
    //                     1 => tys[0].clone(),
    //                     _ => InferTy::Tuple(tys.to_vec()),
    //                 };

    //                 self.session.insert(name.symbol(), values_ty.clone());
    //                 row_types.push((name.name_str(), values_ty));
    //             }
    //             DeclKind::Property {
    //                 name,
    //                 is_static,
    //                 type_annotation,
    //                 default_value,
    //                 ..
    //             } => {
    //                 row_types.push((
    //                     name.name_str(),
    //                     self.visit_property(
    //                         nominal_symbol,
    //                         name,
    //                         *is_static,
    //                         type_annotation,
    //                         default_value,
    //                         &mut context.next(),
    //                     ),
    //                 ));
    //             }
    //             DeclKind::TypeAlias(lhs, .., rhs) => {
    //                 let rhs_ty = self.visit_type_annotation(rhs, context);

    //                 // Quantify over the enclosing nominal's generics so the alias can be
    //                 // instantiated at use sites (e.g., Person<A>.T = A ⇒ T specializes to α).
    //                 let mut foralls: IndexSet<ForAll> = IndexSet::new();
    //                 for g in generics {
    //                     if let Some(entry) = self.session.lookup(&g.name.symbol())
    //                         && let InferTy::Param(pid) = entry._as_ty()
    //                     {
    //                         foralls.insert(ForAll::Ty(pid));
    //                     }
    //                 }

    //                 let entry = if foralls.is_empty() {
    //                     EnvEntry::Mono(rhs_ty)
    //                 } else {
    //                     EnvEntry::Scheme(Scheme {
    //                         ty: rhs_ty,
    //                         foralls,
    //                         predicates: Default::default(),
    //                     })
    //                 };

    //                 self.session.insert_term(lhs.symbol(), entry);
    //             }

    //             _ => tracing::warn!("Unhandled extend decl: {:?}", decl.kind),
    //         }
    //     }

    //     for conformance in conformances {
    //         let Symbol::Protocol(protocol_id) = conformance.symbol() else {
    //             unreachable!("didnt get protocol id for conformance: {conformance:?}");
    //         };

    //         let associated_types = self
    //             .session
    //             .type_catalog
    //             .associated_types
    //             .get(&conformance.symbol())
    //             .cloned()
    //             .unwrap_or_default()
    //             .iter()
    //             .fold(FxHashMap::default(), |mut acc, (label, _)| {
    //                 acc.insert(label.clone(), self.session.new_ty_meta_var(context.level()));
    //                 acc
    //             });

    //         self.session.type_catalog.conformances.insert(
    //             ConformanceKey {
    //                 protocol_id,
    //                 conforming_id: nominal_symbol,
    //             },
    //             Conformance {
    //                 node_id: conformance.id,
    //                 conforming_id: nominal_symbol,
    //                 protocol_id,
    //                 witnesses: Default::default(),
    //                 associated_types,
    //                 span: conformance.span,
    //             },
    //         );
    //         context
    //             .wants_mut()
    //             .conforms(ty.clone(), protocol_id, conformance.span);
    //     }

    //     ty
    // }

    #[instrument(level = tracing::Level::TRACE, skip(self, context))]
    fn infer_record_literal(
        &mut self,
        fields: &[RecordField],
        spread: &Option<Box<Expr>>,
        context: &mut impl Solve,
    ) -> InferTy {
        let mut row = InferRow::Empty(TypeDefKind::Struct);
        for field in fields.iter().rev() {
            row = InferRow::Extend {
                row: Box::new(row),
                label: field.label.name_str().into(),
                ty: self.visit_expr(&field.value, context),
            };
        }

        InferTy::Record(Box::new(row))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context, func))]
    fn visit_method(
        &mut self,
        owner_symbol: Symbol,
        func: &Func,
        is_static: bool,
        context: &mut impl Solve,
    ) -> InferTy {
        if is_static {
            self.session
                .type_catalog
                .static_methods
                .entry(owner_symbol)
                .or_default()
                .insert(func.name.name_str().into(), func.name.symbol());
        } else {
            self.session
                .type_catalog
                .instance_methods
                .entry(owner_symbol)
                .or_default()
                .insert(func.name.name_str().into(), func.name.symbol());
        }

        let func_ty = self.visit_func(func, context);
        self.session.insert(func.name.symbol(), func_ty.clone());

        func_ty
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context))]
    fn visit_property(
        &mut self,
        struct_symbol: Symbol,
        name: &Name,
        is_static: bool,
        type_annotation: &Option<TypeAnnotation>,
        default_value: &Option<Expr>,
        context: &mut impl Solve,
    ) -> InferTy {
        self.session
            .type_catalog
            .properties
            .entry(struct_symbol)
            .or_default()
            .insert(name.name_str().into(), name.symbol());

        let ty = if let Some(anno) = type_annotation {
            self.visit_type_annotation(anno, context)
        } else {
            self.session.new_type_param(None)
        };

        if let Some(default_value) = default_value {
            let default_ty = self.visit_expr(default_value, context);
            context.wants_mut().equals(
                default_ty,
                ty.clone(),
                ConstraintCause::Internal,
                default_value.span,
            );
        }

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
                .properties
                .entry(struct_symbol)
                .or_default()
                .insert(name.name_str().into(), name.symbol());
        }

        ty
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context))]
    fn visit_init(
        &mut self,
        struct_ty: InferTy,
        name: &Name,
        params: &[Parameter],
        body: &Block,
        context: &mut impl Solve,
    ) -> InferTy {
        let param_tys = self.visit_params(params, context);

        // Init blocks always return self
        _ = self.infer_block(body, context);

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

        let ty = substitute(ty, &self.session.skolem_map);
        let foralls: IndexSet<_> = ty.collect_foralls().into_iter().collect();
        let entry = if foralls.is_empty() {
            EnvEntry::Mono(ty)
        } else {
            EnvEntry::Scheme(Scheme {
                ty,
                foralls,
                predicates: Default::default(),
            })
        };
        self.session.insert_term(name.symbol(), entry);

        InferTy::Void
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, scrutinee, arms, context))]
    fn infer_match(
        &mut self,
        scrutinee: &Expr,
        arms: &[MatchArm],
        context: &mut impl Solve,
    ) -> InferTy {
        let mut last_arm_ty: Option<InferTy> = None;
        let scrutinee_ty = self.visit_expr(scrutinee, context);

        for arm in arms {
            self.check_pattern(&arm.pattern, &scrutinee_ty, context);
            let arm_ty = self.infer_block(&arm.body, context);

            if let Some(last_arm_ty) = &last_arm_ty {
                context.wants_mut().equals(
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

    #[instrument(level = tracing::Level::TRACE, skip(self, context))]
    fn promote_pattern_bindings(
        &mut self,
        pattern: &Pattern,
        expected: &InferTy,
        context: &mut impl Solve,
    ) -> InferTy {
        match &pattern.kind {
            PatternKind::Bind(Name::Resolved(sym, _)) => {
                if let Some(EnvEntry::Mono(existing)) = self.session.lookup(sym) {
                    context.wants_mut().equals(
                        expected.clone(),
                        existing.clone(),
                        ConstraintCause::Internal,
                        pattern.span,
                    );
                };

                self.session.insert(*sym, expected.clone());
                expected.clone()
            }
            PatternKind::Tuple(items) => {
                let ty = InferTy::Tuple(
                    items
                        .iter()
                        .map(|i| {
                            let var = self.session.new_ty_meta_var_id(context.level());
                            self.generalization_blocks
                                .insert(var, GeneralizationBlock::PatternBindLocal);
                            self.promote_pattern_bindings(
                                i,
                                &InferTy::Var {
                                    id: var,
                                    level: context.level(),
                                },
                                context,
                            )
                        })
                        .collect_vec(),
                );

                context.wants_mut().equals(
                    ty.clone(),
                    expected.clone(),
                    ConstraintCause::Internal,
                    pattern.span,
                );

                ty
            }
            PatternKind::Record { fields } => {
                let mut row = InferRow::Empty(TypeDefKind::Struct);
                for field in fields {
                    match &field.kind {
                        RecordFieldPatternKind::Bind(name) => {
                            let var = self.session.new_ty_meta_var_id(context.level());
                            self.generalization_blocks
                                .insert(var, GeneralizationBlock::PatternBindLocal);
                            let ty = InferTy::Var {
                                id: var,
                                level: context.level(),
                            };

                            self.session.insert(name.symbol(), ty.clone());
                            row = InferRow::Extend {
                                row: row.into(),
                                label: name.name_str().into(),
                                ty,
                            };
                        }
                        RecordFieldPatternKind::Equals { name, value, .. } => {
                            let ty = if let Some(existing) = self.session.lookup(&name.symbol()) {
                                existing._as_ty()
                            } else {
                                let var = self.session.new_ty_meta_var_id(context.level());
                                self.generalization_blocks
                                    .insert(var, GeneralizationBlock::PatternBindLocal);
                                InferTy::Var {
                                    id: var,
                                    level: context.level(),
                                }
                            };
                            let ty = self.promote_pattern_bindings(value, &ty, context);
                            row = InferRow::Extend {
                                row: row.into(),
                                label: name.name_str().into(),
                                ty,
                            };
                        }
                        RecordFieldPatternKind::Rest => {}
                    }
                }

                let ty = InferTy::Record(row.into());
                context.wants_mut().equals(
                    ty.clone(),
                    expected.clone(),
                    ConstraintCause::Internal,
                    pattern.span,
                );

                ty
            }
            // cover any other pattern forms you support
            _ => InferTy::Void,
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context))]
    fn check_pattern(&mut self, pattern: &Pattern, expected: &InferTy, context: &mut impl Solve) {
        let Pattern { kind, .. } = &pattern;

        match kind {
            PatternKind::Bind(Name::Raw(name)) => {
                context.wants_mut().equals(
                    expected.clone(),
                    InferTy::Error(TypeError::NameNotResolved(name.clone().into()).into()),
                    ConstraintCause::Internal,
                    pattern.span,
                );
            }
            PatternKind::Bind(Name::Resolved(sym, _)) => {
                self.session.insert_mono(*sym, expected.clone());
            }
            PatternKind::Bind(Name::SelfType(..)) => (),
            PatternKind::LiteralInt(_) => {
                context.wants_mut().equals(
                    expected.clone(),
                    InferTy::Int,
                    ConstraintCause::Pattern(pattern.id),
                    pattern.span,
                );
            }
            PatternKind::LiteralFloat(_) => {
                context.wants_mut().equals(
                    expected.clone(),
                    InferTy::Float,
                    ConstraintCause::Pattern(pattern.id),
                    pattern.span,
                );
            }
            PatternKind::LiteralFalse | PatternKind::LiteralTrue => {
                context.wants_mut().equals(
                    expected.clone(),
                    InferTy::Bool,
                    ConstraintCause::Pattern(pattern.id),
                    pattern.span,
                );
            }
            PatternKind::Tuple(patterns) => {
                let metas: Vec<InferTy> = (0..patterns.len())
                    .map(|_| self.session.new_ty_meta_var(context.level()))
                    .collect();

                context.wants_mut().equals(
                    expected.clone(),
                    InferTy::Tuple(metas.clone()),
                    ConstraintCause::Pattern(pattern.id),
                    pattern.span,
                );

                for (pi, bi) in patterns.iter().zip(metas) {
                    self.check_pattern(pi, &bi, context);
                }
            }
            PatternKind::Record { fields } => {
                let expected_row =
                    self.ensure_row_record(pattern.id, pattern.span, expected, context);
                for field in fields {
                    match &field.kind {
                        RecordFieldPatternKind::Bind(name) => {
                            // fresh meta for the field type
                            let field_ty = self.session.new_ty_meta_var(context.level());

                            // bind the pattern name
                            self.session.insert_mono(name.symbol(), field_ty.clone());

                            // ONE RowHas per field, all referring to the same row
                            context.wants_mut()._has_field(
                                expected_row.clone(),
                                name.name_str().into(),
                                field_ty,
                                ConstraintCause::Pattern(field.id),
                                pattern.span,
                            );
                        }
                        RecordFieldPatternKind::Equals { name, value, .. } => {
                            // optional: pattern field = subpattern; same RowHas then recurse on value
                            let field_ty = self.session.new_ty_meta_var(context.level());
                            context.wants_mut()._has_field(
                                expected_row.clone(),
                                name.name_str().into(),
                                field_ty.clone(),
                                ConstraintCause::Pattern(field.id),
                                pattern.span,
                            );
                            self.check_pattern(value, &field_ty, context);
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
                    .map(|_| {
                        let var_id = self.session.new_ty_meta_var_id(context.level());
                        self.generalization_blocks
                            .insert(var_id, GeneralizationBlock::PatternBindLocal);

                        InferTy::Var {
                            id: var_id,
                            level: context.level(),
                        }
                    })
                    .collect();
                let payload = if fields.is_empty() {
                    expected.clone()
                } else if fields.len() == 1 {
                    InferTy::Func(field_metas[0].clone().into(), expected.clone().into())
                } else {
                    curry(field_metas.clone(), expected.clone())
                };

                context.wants_mut().member(
                    pattern.id,
                    expected.clone(),
                    variant_name.into(),
                    payload,
                    ConstraintCause::Pattern(pattern.id),
                    pattern.span,
                );

                // Recursively check each field pattern
                for (field_pattern, field_ty) in fields.iter().zip(field_metas) {
                    self.check_pattern(field_pattern, &field_ty, context);
                }
            }
            PatternKind::Wildcard => (),
            #[warn(clippy::todo)]
            PatternKind::Struct { .. } => todo!(),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, cond, conseq, alt, context))]
    fn infer_if_expr(
        &mut self,
        cond: &Expr,
        conseq: &Block,
        alt: &Block,
        context: &mut impl Solve,
    ) -> InferTy {
        let cond_ty = self.visit_expr(cond, context);
        context.wants_mut().equals(
            cond_ty,
            InferTy::Bool,
            ConstraintCause::Condition(cond.id),
            cond.span,
        );

        let conseq_ty = self.infer_block(conseq, context);
        let alt_ty = self.infer_block(alt, context);
        context.wants_mut().equals(
            conseq_ty.clone(),
            alt_ty,
            ConstraintCause::Internal,
            alt.span,
        );

        conseq_ty
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, cond, conseq, alt, context))]
    fn visit_if_stmt(
        &mut self,
        cond: &Expr,
        conseq: &Block,
        alt: &Option<Block>,
        context: &mut impl Solve,
    ) -> InferTy {
        let cond_ty = self.visit_expr(cond, context);
        context.wants_mut().equals(
            cond_ty,
            InferTy::Bool,
            ConstraintCause::Condition(cond.id),
            cond.span,
        );

        let conseq_ty = self.infer_block(conseq, context);

        if let Some(alt) = alt {
            let alt_ty = self.infer_block(alt, context);
            context.wants_mut().equals(
                conseq_ty.clone(),
                alt_ty,
                ConstraintCause::Internal,
                alt.span,
            );
        }

        conseq_ty
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, block, context))]
    fn infer_block(&mut self, block: &Block, context: &mut impl Solve) -> InferTy {
        let mut ret = InferTy::Void;
        for node in block.body.iter() {
            ret = self.visit_node(node, context);
        }

        self.session.types_by_node.insert(block.id, ret.clone());

        ret
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, expr, context))]
    fn visit_variable(&mut self, expr: &Expr, name: &Name, context: &mut impl Solve) -> InferTy {
        let Some(entry) = self.session.lookup(&name.symbol()) else {
            return InferTy::Error(TypeError::NameNotResolved(name.clone()).into());
        };

        let ty = entry.instantiate(expr.id, context, self.session, expr.span);

        self.instantiations
            .insert(expr.id, context.instantiations_mut().clone());

        ty
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context))]
    fn visit_call(
        &mut self,
        callee: &Expr,
        type_args: &[TypeAnnotation],
        args: &[CallArg],
        context: &mut impl Solve,
    ) -> InferTy {
        let callee_ty = self.visit_expr(callee, context);
        let receiver_ty = match &callee.kind {
            ExprKind::Member(Some(rcv), ..) => {
                // Reuse the already-computed type if available; otherwise visit.
                Some(
                    self.session
                        .types_by_node
                        .get(&rcv.id)
                        .cloned()
                        .unwrap_or_else(|| self.visit_expr(rcv, context)),
                )
            }
            ExprKind::Member(None, ..) => Some(self.session.new_ty_meta_var(context.level())),
            _ => None,
        };

        let arg_tys = args
            .iter()
            .map(|a| self.visit_expr(&a.value, context))
            .collect_vec();
        let type_args = type_args
            .iter()
            .map(|a| self.visit_type_annotation(a, context))
            .collect_vec();

        let ret = self.session.new_ty_meta_var(context.level());
        let instantiations = self
            .instantiations
            .get(&callee.id)
            .cloned()
            .unwrap_or_default();
        for (type_arg, instantiated) in type_args
            .iter()
            .zip(instantiations.ty_mappings(&callee.id).values())
        {
            context.wants_mut().equals(
                type_arg.clone(),
                InferTy::Var {
                    id: *instantiated,
                    level: self
                        .session
                        .meta_levels
                        .borrow()
                        .get(&Meta::Ty(*instantiated))
                        .copied()
                        .unwrap_or_default(),
                },
                ConstraintCause::Internal,
                callee.span,
            );
        }

        // if matches!(callee_ty, InferTy::Constructor { .. }) {
        //     arg_tys.insert(0, ret.clone());
        // }

        let level = context.level();
        context.wants_mut().call(
            callee.id,
            callee_ty,
            arg_tys,
            type_args,
            ret.clone(),
            receiver_ty,
            level,
            ConstraintCause::Call(callee.id),
            callee.span,
        );
        ret
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context))]
    fn visit_func(&mut self, func: &Func, context: &mut impl Solve) -> InferTy {
        for generic in func.generics.iter() {
            self.register_generic(generic, context);
        }

        let mut params = self.visit_params(&func.params, context);

        let ret = if let Some(ret) = &func.ret {
            let ret = self.visit_type_annotation(ret, context);
            self.check_block(&func.body, ret.clone(), &mut context.next());
            ret
        } else {
            self.infer_block(&func.body, &mut context.next())
        };

        if params.is_empty() {
            // Otherwise curry gets confused. TODO: just fix curry?
            params.push(InferTy::Void);
        }

        let func_ty = curry(params, ret);
        substitute(func_ty, &self.session.skolem_map) // Deskolemize
    }

    fn visit_params(&mut self, params: &[Parameter], context: &mut impl Solve) -> Vec<InferTy> {
        params
            .iter()
            .map(|param| self.visit_param(param, context))
            .collect_vec()
    }

    fn visit_param(&mut self, param: &Parameter, context: &mut impl Solve) -> InferTy {
        if let Some(existing) = self.session.lookup(&param.name.symbol()) {
            return existing._as_ty();
        }

        let ty = if let Some(type_annotation) = &param.type_annotation {
            self.visit_type_annotation(type_annotation, context)
        } else {
            self.session.new_ty_meta_var(context.level())
        };

        self.session
            .insert_term(param.name.symbol(), ty.clone().to_entry());

        ty
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, block, context))]
    fn check_block(&mut self, block: &Block, expected: InferTy, context: &mut impl Solve) {
        let mut ret = InferTy::Void;
        for node in &block.body {
            ret = self.visit_node(node, context);
        }
        context
            .wants_mut()
            .equals(ret, expected, ConstraintCause::Internal, block.span);
    }

    // Checks
    #[allow(clippy::too_many_arguments)]
    #[allow(dead_code)]
    #[instrument(skip(self, body, context))]
    fn check_func(
        &mut self,
        params: &[Parameter],
        ret: &Option<TypeAnnotation>,
        body: &Block,
        expected_params: Vec<InferTy>,
        expected_ret: InferTy,
        context: &mut impl Solve,
    ) {
        for (param, expected_param_ty) in params.iter().zip(expected_params) {
            self.session
                .insert_mono(param.name.symbol(), expected_param_ty);
        }

        if let Some(ret) = ret {
            let ret_ty = self.visit_type_annotation(ret, context);
            context.wants_mut().equals(
                ret_ty,
                expected_ret.clone(),
                ConstraintCause::Annotation(ret.id),
                ret.span,
            );
        }

        self.check_block(body, expected_ret.clone(), context);
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context))]
    fn visit_type_annotation(
        &mut self,
        type_annotation: &TypeAnnotation,
        context: &mut impl Solve,
    ) -> InferTy {
        match &type_annotation.kind {
            TypeAnnotationKind::Nominal { name, generics, .. } => {
                if let (
                    SolveContextKind::Protocol {
                        protocol_self,
                        protocol_id,
                    },
                    Symbol::AssociatedType(..),
                ) = (context.kind(), name.symbol())
                {
                    // Evaluate generic arguments (if any) the usual way (often empty for assoc types)
                    let _generic_args = generics
                        .iter()
                        .map(|g| (self.visit_type_annotation(g, context), g.id))
                        .collect_vec();

                    // Fresh variable for the associated type's value in this position.
                    let result = self.session.new_ty_meta_var(context.level());

                    // Base is the protocol "Self" variable in this requirement.
                    let base = InferTy::Param(protocol_self);

                    context.wants_mut().projection(
                        type_annotation.id,
                        base,
                        name.name_str().into(), // "T"
                        Some(protocol_id),
                        result.clone(),
                        ConstraintCause::Annotation(type_annotation.id),
                        type_annotation.span,
                    );

                    // NOTE: we intentionally DO NOT instantiate the env entry for @AssociatedType here.
                    // That entry encodes the *law* (`projection(Self.T) -> α`) but instantiating it would
                    // re-introduce a pathy return type. The constraint above is sufficient.
                    return result;
                }

                if matches!(name.symbol(), Symbol::Builtin(..)) {
                    return resolve_builtin_type(&name.symbol()).0;
                }

                let generic_args = generics
                    .iter()
                    .map(|g| (self.visit_type_annotation(g, context), g.id))
                    .collect_vec();

                // Do we know about this already? Cool.
                if let Some(entry) = self.session.lookup(&name.symbol()) {
                    let (ty, subsitutions) = entry.instantiate_with_args(
                        type_annotation.id,
                        &generic_args,
                        self.session,
                        context.level(),
                        context.wants_mut(),
                        type_annotation.span,
                    );

                    self.instantiations.insert(type_annotation.id, subsitutions);

                    return ty;
                } else {
                    tracing::warn!("nope, did not find anything in the env for {name:?}");
                }

                let var_id = self.session.new_ty_meta_var_id(context.level());

                self.generalization_blocks.insert(
                    var_id,
                    GeneralizationBlock::PendingType {
                        node_id: type_annotation.id,
                        span: type_annotation.span,
                        level: context.level(),
                        type_symbol: name.symbol(),
                        args: generic_args,
                    },
                );

                InferTy::Var {
                    id: var_id,
                    level: context.level(),
                }
            }
            TypeAnnotationKind::SelfType(name) => {
                if matches!(name.symbol(), Symbol::Builtin(..)) {
                    return resolve_builtin_type(&name.symbol()).0;
                }

                if let SolveContextKind::Protocol { protocol_self, .. } = context.kind() {
                    return InferTy::Param(protocol_self);
                }

                let Some(entry) = self.session.lookup(&name.symbol()) else {
                    return InferTy::Error(TypeError::TypeNotFound(format!("{name:?}")).into());
                };

                let ty = entry.instantiate(
                    type_annotation.id,
                    context,
                    self.session,
                    type_annotation.span,
                );

                self.instantiations
                    .insert(type_annotation.id, context.instantiations_mut().clone());

                ty
            }
            TypeAnnotationKind::Record { fields } => {
                let mut row = InferRow::Empty(TypeDefKind::Struct);
                for field in fields.iter().rev() {
                    row = InferRow::Extend {
                        row: Box::new(row),
                        label: field.label.name_str().into(),
                        ty: self.visit_type_annotation(&field.value, context),
                    };
                }

                InferTy::Record(Box::new(row))
            }
            TypeAnnotationKind::NominalPath {
                base,
                member,
                member_generics,
                ..
            } => {
                let base_ty = self.visit_type_annotation(base, context);
                let generics = member_generics
                    .iter()
                    .map(|t| self.visit_type_annotation(t, context))
                    .collect_vec();
                let ret = self.session.new_ty_meta_var(context.level());

                if matches!(base.symbol(), Symbol::TypeParameter(..)) {
                    context.wants_mut().projection(
                        type_annotation.id,
                        base_ty,
                        member.clone(),
                        None,
                        ret.clone(),
                        ConstraintCause::Annotation(type_annotation.id),
                        type_annotation.span,
                    );
                } else {
                    context.wants_mut().type_member(
                        base_ty,
                        member.clone(),
                        generics,
                        ret.clone(),
                        type_annotation.id,
                        type_annotation.span,
                    );
                }

                ret
            }
            _ => InferTy::Error(TypeError::TypeNotFound(format!("{type_annotation:?}")).into()),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context))]
    fn visit_let(
        &mut self,
        lhs: &Pattern,
        type_annotation: &Option<TypeAnnotation>,
        rhs: &Option<Expr>,
        context: &mut impl Solve,
    ) -> InferTy {
        let ty = match (&type_annotation, &rhs) {
            (None, Some(expr)) => self.visit_expr(expr, context),
            (Some(annotation), None) => self.visit_type_annotation(annotation, context),
            (Some(annotation), Some(rhs)) => {
                let annotated_ty = self.visit_type_annotation(annotation, context);
                let rhs_ty = self.visit_expr(rhs, context);
                context.wants_mut().equals(
                    annotated_ty.clone(),
                    rhs_ty,
                    ConstraintCause::Annotation(annotation.id),
                    annotation.span,
                );
                annotated_ty
            }
            (None, None) => {
                let id = self.session.new_ty_meta_var_id(context.level().next());
                self.generalization_blocks
                    .insert(id, GeneralizationBlock::PatternBindLocal);
                InferTy::Var {
                    id,
                    level: context.level().next(),
                }
            }
        };

        self.promote_pattern_bindings(lhs, &ty, &mut context.next())
    }

    fn canonical_row_for(&mut self, symbol: &Symbol, level: Level) -> RowMetaId {
        if let Some(existing) = self.canonical_rows.get(symbol).copied() {
            return existing;
        }

        let id = self.session.new_row_meta_var_id(level);
        self.canonical_rows.insert(*symbol, id);
        id
    }

    fn ensure_row_record(
        &mut self,
        id: NodeID,
        span: Span,
        expected: &InferTy,
        context: &mut impl Solve,
    ) -> InferRow {
        match expected {
            InferTy::Record(box row) => row.clone(),
            _ => {
                let row = self.session.new_row_meta_var(context.level());
                context.wants_mut().equals(
                    expected.clone(),
                    InferTy::Record(Box::new(row.clone())),
                    ConstraintCause::Member(id),
                    span,
                );
                row
            }
        }
    }

    fn register_generic(&mut self, generic: &GenericDecl, context: &mut impl Solve) -> TypeParamId {
        let param_id = self.session.new_type_param_id(None);

        for conformance in generic.conformances.iter() {
            let Symbol::Protocol(protocol_id) = conformance.symbol() else {
                tracing::warn!("could not determine conformance: {conformance:?}");
                continue;
            };

            let predicate = Predicate::Conforms {
                param: param_id,
                protocol_id,
                span: conformance.span,
            };

            context.givens_mut().insert(predicate.clone());
            self.session
                .type_param_bounds
                .entry(param_id)
                .or_default()
                .insert(predicate);
        }

        self.session
            .insert_mono(generic.name.symbol(), InferTy::Param(param_id));

        param_id
    }
}
