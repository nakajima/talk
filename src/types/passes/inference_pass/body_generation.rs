use tracing::instrument;

use super::InferencePass;
use crate::{
    diagnostic::{AnyDiagnostic, Diagnostic, Severity},
    name_resolution::{scc_graph::BindingGroup, symbol::Symbol},
    node_id::NodeID,
    types::{
        constraints::store::GroupId,
        infer_ty::{Level, Ty},
        solve_context::{SolveContext, SolveContextKind},
        term_environment::EnvEntry,
        type_error::TypeError,
        typed_ast::{TypedDecl, TypedNode, TypedStmt},
    },
};

#[derive(Clone, Debug)]
struct DeferredBinder {
    binder: Symbol,
    rhs_id: NodeID,
    level: Level,
    group_id: GroupId,
    is_top_level: bool,
}

impl InferencePass<'_> {
    pub(super) fn generate(&mut self) {
        if self.asts.is_empty() {
            return;
        }

        let mut groups = self.session.resolved_names.scc_graph.groups();
        groups.sort_by_key(|group| group.id.0);
        let mut deferred = vec![];

        for group in groups {
            let is_top_level = group.is_top_level;

            // Skip groups that capture a self parameter (ParamLocal named "self").
            // These are DeclaredLocals inside struct methods that will be visited as
            // part of their containing struct, where current_self_ty is properly set.
            // Processing them separately would generate Member constraints without the
            // correct self type constraint.
            let captures_self = group.binders.iter().any(|b| {
                self.session
                    .resolved_names
                    .captures
                    .get(b)
                    .map(|caps| {
                        caps.iter().any(|c| {
                            matches!(c.symbol, Symbol::ParamLocal(..))
                                && self.session.resolved_names.symbol_names.get(&c.symbol)
                                    == Some(&"self".to_string())
                        })
                    })
                    .unwrap_or(false)
            });

            if captures_self && !is_top_level {
                continue;
            }

            let nominal_member_group = !is_top_level
                && group.binders.iter().all(|binder| {
                    matches!(
                        binder,
                        Symbol::InstanceMethod(..)
                            | Symbol::StaticMethod(..)
                            | Symbol::Initializer(..)
                    )
                });
            if nominal_member_group {
                continue;
            }

            let (new_decls, new_stmts, mut group_deferred) = self.generate_for_group(group);
            deferred.append(&mut group_deferred);

            if is_top_level {
                self.root_decls.extend(new_decls);
                self.root_stmts.extend(new_stmts);
            }
        }

        self.process_deferred_binders(deferred);

        let mut context = SolveContext::new(
            self.substitutions.clone(),
            Level::default(),
            Default::default(),
            SolveContextKind::Normal,
        );

        tracing::debug!("visiting stragglers");
        for id in self.session.resolved_names.unbound_nodes.clone() {
            let Some(node) = self.asts.iter().find_map(|ast| ast.find(id)) else {
                continue;
            };

            match self.visit_node(&node, &mut context) {
                Ok(typed_node) => match typed_node {
                    TypedNode::Decl(typed_decl) => {
                        self.root_decls.push(typed_decl);
                    }
                    TypedNode::Stmt(typed_stmt) => self.root_stmts.push(typed_stmt),
                    _ => {
                        continue;
                    }
                },
                Err(e) => {
                    tracing::error!("{e:?}");
                    self.diagnostics.insert(AnyDiagnostic::Typing(Diagnostic {
                        id: node.node_id(),
                        severity: Severity::Error,
                        kind: e,
                    }));
                }
            }
        }

        // Retry deferred constraints now that all extend blocks (stragglers)
        // have been processed and their methods are available.
        self.constraints.retry_all_deferred();

        self.solve(&mut context, Default::default(), Default::default());

        // Apply substitutions to types_by_node for top-level expressions
        self.session.apply_all(&mut context.substitutions_mut());
    }

    fn should_defer_missing_global(&self, binder: &Symbol, error: &TypeError) -> bool {
        matches!(binder, Symbol::Global(..))
            && matches!(
                error,
                TypeError::TypeNotFound(message)
                if message.starts_with("Entry not found for variable ")
            )
    }

    fn is_missing_variable_entry_error(&self, error: &TypeError) -> bool {
        matches!(
            error,
            TypeError::TypeNotFound(message)
            if message.starts_with("Entry not found for variable ")
        )
    }

    fn skip_redundant_member_binder(&self, binder: &Symbol, group_has_nominal: bool) -> bool {
        group_has_nominal
            && matches!(
                binder,
                Symbol::InstanceMethod(..) | Symbol::StaticMethod(..) | Symbol::Initializer(..)
            )
    }

    fn process_deferred_binders(&mut self, mut deferred: Vec<DeferredBinder>) {
        while !deferred.is_empty() {
            let mut next = vec![];
            let mut progressed = false;

            for binder in deferred {
                let Some(rhs) = self.asts.iter().find_map(|ast| ast.find(binder.rhs_id)) else {
                    continue;
                };

                let mut context = SolveContext::new(
                    self.substitutions.clone(),
                    binder.level,
                    binder.group_id,
                    SolveContextKind::Normal,
                );

                let node = match self.visit_node(&rhs, &mut context) {
                    Ok(node) => node,
                    Err(e) => {
                        if self.should_defer_missing_global(&binder.binder, &e) {
                            next.push(binder);
                        } else {
                            tracing::error!("{e:?}");
                            self.diagnostics.insert(AnyDiagnostic::Typing(Diagnostic {
                                id: rhs.node_id(),
                                severity: Severity::Error,
                                kind: e,
                            }));
                        }
                        continue;
                    }
                };

                progressed = true;

                if binder.is_top_level {
                    match &node {
                        TypedNode::Decl(decl) => self.root_decls.push(decl.clone()),
                        TypedNode::Stmt(stmt) => self.root_stmts.push(stmt.clone()),
                        TypedNode::Expr(_) => {}
                    }
                }

                let Some(existing) = self.session.lookup(&binder.binder) else {
                    continue;
                };
                let placeholder = existing._as_ty();

                self.constraints.wants_equals_at(
                    binder.rhs_id,
                    node.ty(),
                    placeholder.clone(),
                    &context.group_info(),
                );

                self.solve(&mut context, vec![binder.binder], vec![placeholder]);
            }

            if !progressed {
                for binder in next {
                    let Some(rhs) = self.asts.iter().find_map(|ast| ast.find(binder.rhs_id)) else {
                        continue;
                    };

                    let mut context = SolveContext::new(
                        self.substitutions.clone(),
                        binder.level,
                        binder.group_id,
                        SolveContextKind::Normal,
                    );

                    match self.visit_node(&rhs, &mut context) {
                        Ok(node) => {
                            if binder.is_top_level {
                                match &node {
                                    TypedNode::Decl(decl) => self.root_decls.push(decl.clone()),
                                    TypedNode::Stmt(stmt) => self.root_stmts.push(stmt.clone()),
                                    TypedNode::Expr(_) => {}
                                }
                            }

                            if let Some(existing) = self.session.lookup(&binder.binder) {
                                let placeholder = existing._as_ty();
                                self.constraints.wants_equals_at(
                                    binder.rhs_id,
                                    node.ty(),
                                    placeholder.clone(),
                                    &context.group_info(),
                                );
                                self.solve(&mut context, vec![binder.binder], vec![placeholder]);
                            }
                        }
                        Err(e) => {
                            tracing::error!("{e:?}");
                            self.diagnostics.insert(AnyDiagnostic::Typing(Diagnostic {
                                id: rhs.node_id(),
                                severity: Severity::Error,
                                kind: e,
                            }));
                        }
                    }
                }
                return;
            }

            deferred = next;
        }
    }

    #[instrument(skip(self))]
    fn generate_for_group(
        &mut self,
        group: BindingGroup,
    ) -> (Vec<TypedDecl>, Vec<TypedStmt>, Vec<DeferredBinder>) {
        let mut decls = vec![];
        let mut stmts = vec![];
        let mut deferred = vec![];
        let mut solved_binders = vec![];
        let mut solved_placeholders = vec![];

        let mut context = SolveContext::new(
            self.substitutions.clone(),
            group.level,
            group.id,
            SolveContextKind::Normal,
        );

        let group_has_nominal = group.binders.iter().any(|binder| {
            matches!(
                binder,
                Symbol::Struct(..) | Symbol::Enum(..) | Symbol::Protocol(..)
            )
        });

        // Create placeholders for binders that are actively solved in this pass.
        let placeholders: Vec<Option<Ty>> = group
            .binders
            .iter()
            .map(|sym| {
                if self.skip_redundant_member_binder(sym, group_has_nominal) {
                    return None;
                }

                let placeholder_id = self.session.new_ty_meta_var_id(group.level);
                let placeholder = Ty::Var {
                    id: placeholder_id,
                    level: context.level(),
                };
                tracing::trace!("placeholder {sym:?} = {placeholder:?}");
                self.session
                    .insert_term(*sym, placeholder.to_entry(), &mut self.constraints);
                Some(placeholder)
            })
            .collect();

        // Visit each binder
        for (i, binder) in group.binders.iter().enumerate() {
            let Some(placeholder) = placeholders[i].clone() else {
                continue;
            };

            if let Some(captures) = self.session.resolved_names.captures.get(binder).cloned() {
                for capture in captures {
                    if self.session.lookup(&capture.symbol).is_none()
                        && !matches!(capture.symbol, Symbol::Global(_))
                    {
                        let placeholder = self.session.new_ty_meta_var(capture.level);
                        tracing::trace!(
                            "capture placeholder {:?} = {placeholder:?}",
                            capture.symbol
                        );
                        self.session.insert_term(
                            capture.symbol,
                            placeholder.to_entry(),
                            &mut self.constraints,
                        );
                    }
                }
            }
            // Search all ASTs for the rhs_id - cross-file dependencies within a module
            // may have the definition in a different file's SCC graph
            let Some(rhs_id) = self
                .session
                .resolved_names
                .scc_graph
                .rhs_id_for(binder)
                .copied()
            else {
                tracing::error!("did not find rhs_id for binder: {binder:?}");
                return (decls, stmts, deferred);
            };

            let Some(rhs) = self.asts.iter().find_map(|ast| ast.find(rhs_id)) else {
                tracing::error!("did not find rhs for id: {rhs_id:?}, binder: {binder:?}");
                return (decls, stmts, deferred);
            };

            let node = match self.visit_node(&rhs, &mut context) {
                Ok(node) => node,
                Err(e) => {
                    if self.should_defer_missing_global(binder, &e) {
                        deferred.push(DeferredBinder {
                            binder: *binder,
                            rhs_id,
                            level: group.level,
                            group_id: group.id,
                            is_top_level: group.is_top_level,
                        });
                        continue;
                    }

                    if self.is_missing_variable_entry_error(&e) {
                        tracing::debug!("{e:?}");
                        continue;
                    }

                    tracing::error!("{e:?}");
                    continue;
                }
            };

            match &node {
                TypedNode::Decl(decl) => decls.push(decl.clone()),
                TypedNode::Stmt(stmt) => stmts.push(stmt.clone()),
                _ => unreachable!(),
            }

            if let Some(existing) = self.session.lookup(binder) {
                if existing == EnvEntry::Mono(placeholder.clone()) {
                    self.constraints.wants_equals_at(
                        rhs_id,
                        node.ty(),
                        placeholder.clone(),
                        &context.group_info(),
                    );
                } else {
                    self.constraints.wants_equals_at(
                        rhs_id,
                        placeholder.clone(),
                        existing._as_ty(),
                        &context.group_info(),
                    );
                }
            }

            solved_binders.push(*binder);
            solved_placeholders.push(placeholder);
        }

        // Solve this group
        if !solved_binders.is_empty() {
            self.solve(&mut context, solved_binders, solved_placeholders);
        }

        (decls, stmts, deferred)
    }
}
