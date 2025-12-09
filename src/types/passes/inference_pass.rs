use indexmap::{IndexMap, IndexSet, indexset};
use itertools::Itertools;
use rustc_hash::FxHashMap;
use tracing::instrument;

use crate::{
    ast::AST,
    diagnostic::{AnyDiagnostic, Diagnostic},
    formatter,
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
        inline_ir_instruction::InlineIRInstruction,
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
        conformance::{Conformance, ConformanceKey, Witnesses},
        constraint_solver::ConstraintSolver,
        constraints::store::ConstraintStore,
        infer_row::InferRow,
        infer_ty::{InferTy, Level, Meta, MetaVarId, TypeParamId},
        predicate::Predicate,
        scheme::{ForAll, Scheme},
        solve_context::{Solve, SolveContext, SolveContextKind},
        term_environment::EnvEntry,
        type_catalog::MemberWitness,
        type_error::TypeError,
        type_operations::{
            InstantiationSubstitutions, UnificationSubstitutions, curry, substitute,
        },
        type_session::{TypeDefKind, TypeSession},
        typed_ast::{
            TypedAST, TypedBlock, TypedDecl, TypedDeclKind, TypedExpr, TypedExprKind, TypedFunc,
            TypedMatchArm, TypedNode, TypedParameter, TypedPattern, TypedRecordField, TypedStmt,
            TypedStmtKind,
        },
    },
};

type TypedRet<T> = Result<T, TypeError>;

#[must_use]
struct ReturnToken {}

pub type PendingTypeInstances =
    FxHashMap<MetaVarId, (NodeID, Span, Level, Symbol, Vec<(InferTy, NodeID)>)>;

pub struct InferencePass<'a> {
    asts: &'a mut [AST<NameResolved>],
    session: &'a mut TypeSession,
    constraints: ConstraintStore,
    instantiations: FxHashMap<NodeID, InstantiationSubstitutions>,
    substitutions: UnificationSubstitutions,
    tracked_returns: Vec<IndexSet<(Span, InferTy)>>,
}

impl<'a> InferencePass<'a> {
    pub fn drive(asts: &'a mut [AST<NameResolved>], session: &'a mut TypeSession) {
        let substitutions = UnificationSubstitutions::new(session.meta_levels.clone());
        let mut pass = InferencePass {
            asts,
            session,
            instantiations: Default::default(),
            constraints: Default::default(),
            substitutions,
            tracked_returns: Default::default(),
        };

        pass.drive_all();
    }

    fn drive_all(&mut self) {
        // Register extension conformances first, so they're available when processing protocol default methods
        for i in 0..self.asts.len() {
            self.discover_conformances(i);
        }

        for i in 0..self.asts.len() {
            self.discover_protocols(i, Level::default());
            self.session.apply_all(&mut self.substitutions);
        }

        for i in 0..self.asts.len() {
            self.generate(i);
            self.session.apply_all(&mut self.substitutions);
        }

        // Transfer child_types from AST phases to the catalog for module export
        for ast in self.asts.iter() {
            for (sym, entries) in ast.phase.child_types.iter() {
                self.session
                    .type_catalog
                    .child_types
                    .entry(*sym)
                    .or_default()
                    .extend(entries.iter().map(|(k, v)| (k.to_string(), *v)));
            }
        }
    }

    /// Pre-register extension conformances so they're available when processing protocol default methods.
    /// This ensures that when `Comparable` uses `!` operator on Bool, the `Bool: Not` conformance is known.
    fn discover_conformances(&mut self, idx: usize) {
        for root in self.asts[idx].roots.iter() {
            let Node::Decl(Decl {
                kind:
                    DeclKind::Extend {
                        name, conformances, ..
                    },
                ..
            }) = root
            else {
                continue;
            };

            let Ok(nominal_symbol) = name.symbol() else {
                continue;
            };

            for conformance in conformances {
                let Ok(Symbol::Protocol(protocol_id)) = conformance.symbol() else {
                    continue;
                };

                let key = ConformanceKey {
                    protocol_id,
                    conforming_id: nominal_symbol,
                };

                // Only insert if not already present (e.g. from imports)
                self.session
                    .type_catalog
                    .conformances
                    .entry(key)
                    .or_insert_with(|| Conformance {
                        node_id: conformance.id,
                        conforming_id: nominal_symbol,
                        protocol_id,
                        witnesses: Default::default(),
                        span: conformance.span,
                    });
            }
        }
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

            let Ok(protocol_sym) = protocol_name.symbol() else {
                self.asts[idx]
                    .diagnostics
                    .push(AnyDiagnostic::Typing(Diagnostic {
                        id: root.node_id(),
                        kind: TypeError::NameNotResolved(protocol_name.clone()),
                    }));
                continue;
            };

            for conformance in conformances {
                let Ok(Symbol::Protocol(conforms_to_id)) = conformance.symbol() else {
                    tracing::error!("did not get protocol for conforms_to");
                    continue;
                };

                let key = ConformanceKey {
                    protocol_id: conforms_to_id,
                    conforming_id: protocol_sym,
                };

                self.session.type_catalog.conformances.insert(
                    key,
                    Conformance {
                        node_id: conformance.id,
                        conforming_id: protocol_sym,
                        protocol_id: conforms_to_id,
                        witnesses: Default::default(),
                        span: conformance.span,
                    },
                );
            }

            let protocol_self_id = self.session.new_type_param_id(None);
            let mut binders: IndexMap<Symbol, InferTy> = IndexMap::default();

            let mut context = SolveContext::new(
                self.substitutions.clone(),
                level,
                Default::default(),
                SolveContextKind::Protocol {
                    protocol_id: *protocol_id,
                    protocol_self: protocol_self_id,
                },
            );

            context.givens.insert(Predicate::Conforms {
                param: protocol_self_id,
                protocol_id: *protocol_id,
            });
            self.session
                .type_param_bounds
                .entry(protocol_self_id)
                .or_default()
                .insert(Predicate::Conforms {
                    param: protocol_self_id,
                    protocol_id: *protocol_id,
                });
            self.session.insert(
                protocol_sym,
                InferTy::Param(protocol_self_id),
                &mut self.constraints,
            );

            // Process associated types
            for decl in body.decls.iter() {
                let DeclKind::Associated { generic } = &decl.kind else {
                    continue;
                };

                let ret_id = self.session.new_type_param_id(None);
                let ret = InferTy::Param(ret_id);

                if !generic.conformances.is_empty() {
                    unimplemented!("not handling associated type conformances yet");
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

                let Ok(generic_sym) = generic.name.symbol() else {
                    self.asts[idx]
                        .diagnostics
                        .push(AnyDiagnostic::Typing(Diagnostic {
                            id: root.node_id(),
                            kind: TypeError::NameNotResolved(generic.name.clone()),
                        }));
                    continue;
                };

                self.session.insert_term(
                    generic_sym,
                    EnvEntry::Scheme(scheme),
                    &mut self.constraints,
                );
                self.session
                    .type_catalog
                    .associated_types
                    .entry(protocol_sym)
                    .or_default()
                    .insert(generic.name.name_str().into(), generic_sym);
            }

            for decl in body.decls.iter() {
                match &decl.kind {
                    DeclKind::MethodRequirement(func_signature)
                    | DeclKind::FuncSignature(func_signature) => {
                        let ty = self
                            .visit_func_signature(
                                protocol_self_id,
                                *protocol_id,
                                func_signature,
                                &mut context,
                            )
                            .unwrap_or_else(|_| unimplemented!());

                        let Ok(func_sym) = func_signature.name.symbol() else {
                            self.asts[idx]
                                .diagnostics
                                .push(AnyDiagnostic::Typing(Diagnostic {
                                    id: root.node_id(),
                                    kind: TypeError::NameNotResolved(func_signature.name.clone()),
                                }));
                            continue;
                        };

                        binders.insert(func_sym, ty.clone());

                        self.session.insert(func_sym, ty, &mut self.constraints);
                        self.session
                            .type_catalog
                            .method_requirements
                            .entry(protocol_sym)
                            .or_default()
                            .insert(func_signature.name.name_str().into(), func_sym);
                    }

                    DeclKind::Method { func, is_static } => {
                        let Ok(func_sym) = func.name.symbol() else {
                            self.asts[idx]
                                .diagnostics
                                .push(AnyDiagnostic::Typing(Diagnostic {
                                    id: root.node_id(),
                                    kind: TypeError::NameNotResolved(func.name.clone()),
                                }));
                            continue;
                        };
                        let ty = self
                            .visit_method(protocol_sym, func, *is_static, &mut context)
                            .unwrap_or_else(|_| unimplemented!());
                        binders.insert(func_sym, ty.ret.clone());
                    }
                    _ => (),
                }
            }

            if let Some(child_types) = self.asts[idx].phase.child_types.get(&protocol_sym) {
                self.session
                    .type_catalog
                    .associated_types
                    .entry(protocol_sym)
                    .or_default()
                    .extend(child_types.clone());
            }

            let (binders, placeholders) = binders.into_iter().unzip();
            self.solve(&mut context, binders, placeholders)
        }
        _ = std::mem::replace(&mut self.asts[idx].roots, roots);
    }

    #[instrument(skip(self))]
    fn rectify_witnesses(&mut self) {
        for (witness_id, witness) in self
            .session
            .type_catalog
            .member_witnesses
            .iter()
            .map(|(k, v)| (*k, v.clone()))
            .collect_vec()
        {
            match &witness {
                MemberWitness::Meta { receiver, label } => {
                    self.resolve_witness_to_concrete(witness_id, receiver, label);
                }
                MemberWitness::Requirement(method_req, receiver) => {
                    // Get the method label from the requirement symbol
                    let Some(label) = self
                        .session
                        .type_catalog
                        .method_requirement_label(method_req)
                    else {
                        continue;
                    };
                    self.resolve_witness_to_concrete(witness_id, receiver, &label);
                }
                _ => {}
            }
        }
    }

    fn resolve_witness_to_concrete(
        &mut self,
        witness_id: NodeID,
        receiver: &InferTy,
        label: &Label,
    ) {
        let receiver_ty = self
            .session
            .apply(receiver.clone(), &mut self.substitutions);
        let symbol = match receiver_ty {
            InferTy::Primitive(symbol) => symbol,
            InferTy::Nominal { symbol, .. } => symbol,
            _ => {
                tracing::warn!("Unable to resolve witness for {receiver_ty:?}.{label:?}");
                return;
            }
        };

        // Use lookup_member which checks instance_methods, conformances, and modules
        if let Some((method, _source)) = self.session.lookup_member(&symbol, label)
            && matches!(method, Symbol::InstanceMethod(..))
        {
            tracing::trace!("Resolved concrete witness {receiver_ty:?}.{label:?} = {method:?}");
            self.session
                .type_catalog
                .member_witnesses
                .insert(witness_id, MemberWitness::Concrete(method));
        }
    }

    fn generate(&mut self, idx: usize) -> TypedAST<InferTy> {
        let mut decls = vec![];
        let mut stmts = vec![];
        let mut context = SolveContext::new(
            self.substitutions.clone(),
            Level::default(),
            Default::default(),
            SolveContextKind::Normal,
        );

        let roots = std::mem::take(&mut self.asts[idx].roots);
        for root in roots.iter() {
            match self.visit_node(root, &mut context) {
                Ok(typed_node) => match typed_node {
                    TypedNode::Decl(decl) => decls.push(decl),
                    TypedNode::Stmt(stmt) => stmts.push(stmt),
                    TypedNode::Expr(_) => unreachable!(),
                },
                Err(e) => {
                    self.asts[idx]
                        .diagnostics
                        .push(AnyDiagnostic::Typing(Diagnostic {
                            id: root.node_id(),
                            kind: e,
                        }));
                }
            }
        }
        _ = std::mem::replace(&mut self.asts[idx].roots, roots);

        // let mut groups = self.asts[idx].phase.scc_graph.groups();

        // // Process groups in topological order (dependencies first).
        // // Kosaraju returns reverse topological order, so we reverse it.
        // groups.sort_by_key(|group| group.id.0);

        // for group in groups {
        //     self.generate_for_group(idx, group);
        // }

        // let mut context = SolveContext::new(
        //     self.substitutions.clone(),
        //     Level::default(),
        //     Default::default(),
        //     SolveContextKind::Normal,
        // );

        // tracing::debug!("visiting stragglers");
        // for id in self.asts[idx].phase.unbound_nodes.clone() {
        //     let Some(node) = self.asts.iter().find_map(|ast| ast.find(id)) else {
        //         tracing::error!("Did not find ast node for id: {id:?}");
        //         continue;
        //     };

        //     self.visit_node(&node, &mut context);
        // }

        let level = context.level();
        let solver = ConstraintSolver::new(&mut context, self.asts);
        solver.solve(
            level,
            &mut self.constraints,
            self.session,
            self.substitutions.clone(),
        );
        self.substitutions.extend(&context.substitutions);

        // Apply substitutions to types_by_node for top-level expressions
        self.session.apply_all(&mut context.substitutions);

        // Rectify witnesses for stragglers (top-level expressions like protocol method calls)
        self.rectify_witnesses();

        TypedAST { decls, stmts }
    }

    #[instrument(skip(self))]
    fn _generate_for_group(&mut self, idx: usize, group: BindingGroup) {
        let mut context = SolveContext::new(
            self.substitutions.clone(),
            group.level,
            group.id,
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
                self.session
                    .insert_term(*sym, placeholder.to_entry(), &mut self.constraints);
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
                .asts
                .iter()
                .find_map(|ast| ast.phase.scc_graph.rhs_id_for(binder))
            else {
                tracing::error!("did not find rhs_id for binder: {binder:?}");
                return;
            };

            let Some(rhs) = self.asts.iter().find_map(|ast| ast.find(*rhs_id)) else {
                tracing::error!("did not find rhs for id: {rhs_id:?}, binder: {binder:?}");
                return;
            };

            let expr = self
                .visit_expr(&rhs.as_expr(), &mut context)
                .unwrap_or_else(|_| unimplemented!());

            if let Some(existing) = self.session.lookup(binder) {
                if existing == EnvEntry::Mono(placeholders[i].clone()) {
                    self.constraints
                        .wants_equals(expr.ty, placeholders[i].clone());
                } else {
                    self.constraints
                        .wants_equals(placeholders[i].clone(), existing._as_ty());
                }
            }
        }

        // Solve this group
        self.solve(&mut context, group.binders.clone(), placeholders)
    }

    fn solve(
        &mut self,
        context: &mut SolveContext,
        binders: Vec<Symbol>,
        placeholders: Vec<InferTy>,
    ) {
        context.substitutions_mut().extend(&self.substitutions);

        let level = context.level();
        let solver = ConstraintSolver::new(context, self.asts);
        solver.solve(
            level,
            &mut self.constraints,
            self.session,
            self.substitutions.clone(),
        );

        let generalizable = self.constraints.generalizable_for(context);

        for (i, binder) in binders.iter().enumerate() {
            let ty = self
                .session
                .apply(placeholders[i].clone(), &mut context.substitutions);
            let entry = self.session.generalize(ty, context, &generalizable);
            self.session.promote(*binder, entry, &mut self.constraints);
        }

        self.substitutions.extend(&context.substitutions);
        self.session.apply_all(&mut self.substitutions);
        self.rectify_witnesses();
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, node, context), fields(node.id = ?node.node_id()))]
    fn visit_node(
        &mut self,
        node: &Node,
        context: &mut impl Solve,
    ) -> TypedRet<TypedNode<InferTy>> {
        match &node {
            Node::Decl(decl) => Ok(TypedNode::Decl(self.visit_decl(decl, context)?)),
            Node::Stmt(stmt) => Ok(TypedNode::Stmt(self.visit_stmt(stmt, context)?)),
            Node::Expr(expr) => Ok(TypedNode::Expr(self.visit_expr(expr, context)?)),
            _ => Err(TypeError::TypeNotFound(format!(
                "No type checking for {node:?}"
            ))),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, decl, context), fields(decl.id = ?decl.id))]
    fn visit_decl(
        &mut self,
        decl: &Decl,
        context: &mut impl Solve,
    ) -> TypedRet<TypedDecl<InferTy>> {
        match &decl.kind {
            DeclKind::Let {
                lhs,
                type_annotation,
                rhs,
            } => self.visit_let(decl.id, lhs, type_annotation, rhs, context),
            DeclKind::Struct {
                name,
                generics,
                conformances,
                body,
                ..
            } => self.visit_nominal(decl, name, generics, conformances, body, context),
            DeclKind::Protocol {
                name,
                generics,
                body,
                conformances,
                ..
            } => self.visit_protocol(decl, name, generics, conformances, body, context),
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
            DeclKind::Import(_) => unimplemented!(),
            DeclKind::Func(..)
            | DeclKind::Init { .. }
            | DeclKind::TypeAlias(..)
            | DeclKind::Associated { .. }
            | DeclKind::Method { .. }
            | DeclKind::Property { .. }
            | DeclKind::MethodRequirement(..)
            | DeclKind::FuncSignature(..)
            | DeclKind::EnumVariant(..) => unreachable!("handled elsewhere"),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, stmt, context), fields(stmt.id = ?stmt.id))]
    fn visit_stmt(
        &mut self,
        stmt: &Stmt,
        context: &mut impl Solve,
    ) -> TypedRet<TypedStmt<InferTy>> {
        let ty = match &stmt.kind {
            StmtKind::Expr(expr) => TypedStmt {
                id: stmt.id,
                kind: TypedStmtKind::Expr(self.visit_expr(expr, context)?),
            },
            StmtKind::If(cond, conseq, alt) => {
                self.visit_if_stmt(stmt.id, cond, conseq, alt, context)?
            }
            StmtKind::Assignment(lhs, rhs) => {
                let lhs_ty = self.visit_expr(lhs, context)?;
                let rhs_ty = self.visit_expr(rhs, context)?;
                self.constraints
                    .wants_equals(lhs_ty.ty.clone(), rhs_ty.ty.clone());
                TypedStmt {
                    id: stmt.id,
                    kind: TypedStmtKind::Assignment(lhs_ty, rhs_ty),
                }
            }
            StmtKind::Return(expr) => self.visit_return(stmt, expr, context)?,
            StmtKind::Break => TypedStmt {
                id: stmt.id,
                kind: TypedStmtKind::Break,
            },
            StmtKind::Loop(cond, block) => {
                let cond_ty = if let Some(cond) = cond {
                    let cond_ty = self.visit_expr(cond, context)?;
                    self.constraints
                        .wants_equals(cond_ty.ty.clone(), InferTy::Bool);
                    cond_ty
                } else {
                    TypedExpr {
                        id: stmt.id,
                        ty: InferTy::Bool,
                        kind: TypedExprKind::LiteralTrue,
                    }
                };

                let block = self.infer_block(block, context)?;

                TypedStmt {
                    id: stmt.id,
                    kind: TypedStmtKind::Loop(cond_ty, block),
                }
            }
        };

        Ok(ty)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, expr, context), fields(expr.id = ?expr.id, expr = formatter::format_node(&expr.into(), &self.asts[0].meta)))]
    fn visit_expr(
        &mut self,
        expr: &Expr,
        context: &mut impl Solve,
    ) -> TypedRet<TypedExpr<InferTy>> {
        let expr = match &expr.kind {
            ExprKind::Incomplete(..) => TypedExpr {
                id: expr.id,
                ty: self.session.new_ty_meta_var(context.level()),
                kind: TypedExprKind::Hole,
            },
            ExprKind::LiteralArray(items) => self.visit_array(expr, items, context)?,
            ExprKind::LiteralInt(v) => TypedExpr {
                id: expr.id,
                ty: InferTy::Int,
                kind: TypedExprKind::LiteralInt(v.to_string()),
            },
            ExprKind::LiteralFloat(v) => TypedExpr {
                id: expr.id,
                ty: InferTy::Float,
                kind: TypedExprKind::LiteralFloat(v.to_string()),
            },
            ExprKind::LiteralTrue => TypedExpr {
                id: expr.id,
                ty: InferTy::Bool,
                kind: TypedExprKind::LiteralTrue,
            },
            ExprKind::LiteralFalse => TypedExpr {
                id: expr.id,
                ty: InferTy::Bool,
                kind: TypedExprKind::LiteralFalse,
            },
            ExprKind::LiteralString(val) => TypedExpr {
                id: expr.id,
                ty: InferTy::String(),
                kind: TypedExprKind::LiteralString(val.to_string()),
            },
            ExprKind::Tuple(exprs) => match exprs.len() {
                0 => TypedExpr {
                    id: expr.id,
                    ty: InferTy::Void,
                    kind: TypedExprKind::Tuple(Default::default()),
                },
                1 => self.visit_expr(&exprs[0], context)?,
                _ => {
                    let typed_exprs: Vec<_> = exprs
                        .iter()
                        .map(|e| self.visit_expr(e, context))
                        .try_collect()?;
                    TypedExpr {
                        id: expr.id,
                        ty: InferTy::Tuple(typed_exprs.iter().map(|t| t.ty.clone()).collect_vec()),
                        kind: TypedExprKind::Tuple(typed_exprs),
                    }
                }
            },
            ExprKind::Block(block) => {
                let typed_block = self.infer_block(block, context)?;
                TypedExpr {
                    id: expr.id,
                    ty: typed_block.ret.clone(),
                    kind: TypedExprKind::Block(typed_block),
                }
            }
            ExprKind::Unary(..) | ExprKind::Binary(..) => {
                unreachable!("these are lowered to calls earlier")
            }
            ExprKind::Call {
                callee,
                type_args,
                args,
            } => self.visit_call(expr.id, callee, type_args, args, &mut context.next())?,
            ExprKind::Member(receiver, label, ..) => {
                self.visit_member(expr, receiver, label, context)?
            }
            ExprKind::Func(func) => {
                let func = self.visit_func(func, context)?;
                TypedExpr {
                    id: expr.id,
                    ty: curry(func.params.iter().map(|p| p.ty.clone()), func.ret.clone()),
                    kind: TypedExprKind::Func(func),
                }
            }
            ExprKind::Variable(name) => self.visit_variable(expr, name, &mut context.next())?,
            ExprKind::Constructor(name) => self.visit_constructor(expr, name, context)?,
            ExprKind::If(cond, conseq, alt) => {
                self.infer_if_expr(expr.id, cond, conseq, alt, context)?
            }
            ExprKind::Match(scrutinee, arms) => {
                self.infer_match(expr.id, scrutinee, arms, context)?
            }
            ExprKind::RecordLiteral { fields, spread } => {
                self.infer_record_literal(expr.id, fields, spread, context)?
            }
            #[allow(clippy::todo)]
            ExprKind::RowVariable(..) => todo!(),
            ExprKind::As(box lhs, rhs) => self.visit_as(lhs, rhs, context)?,
            ExprKind::InlineIR(instr) => self.visit_inline_ir(instr, context)?,
        };

        self.session.types_by_node.insert(expr.id, expr.ty.clone());

        Ok(expr)
    }

    fn visit_inline_ir(
        &mut self,
        instr: &InlineIRInstruction,
        context: &mut impl Solve,
    ) -> TypedRet<TypedExpr<InferTy>> {
        for bind in instr.binds.iter() {
            self.visit_expr(bind, context)?;
        }

        let ty = self.session.new_ty_meta_var(context.level());

        Ok(TypedExpr {
            id: instr.id,
            ty,
            kind: TypedExprKind::InlineIR(instr.clone().into()),
        })
    }

    fn visit_return(
        &mut self,
        stmt: &Stmt,
        expr: &Option<Expr>,
        context: &mut impl Solve,
    ) -> TypedRet<TypedStmt<InferTy>> {
        let ty_expr = if let Some(expr) = expr {
            Some(self.visit_expr(expr, context)?)
        } else {
            None
        };

        if let Some(returns) = self.tracked_returns.last_mut()
            && let Some(ty_expr) = &ty_expr
        {
            returns.insert((stmt.span, ty_expr.ty.clone()));
        }

        Ok(TypedStmt {
            id: stmt.id,
            kind: TypedStmtKind::Return(ty_expr),
        })
    }

    fn visit_as(
        &mut self,
        lhs: &Expr,
        rhs: &TypeAnnotation,
        context: &mut impl Solve,
    ) -> TypedRet<TypedExpr<InferTy>> {
        let lhs_ty = self.visit_expr(lhs, context)?;
        let Ok(Symbol::Protocol(id)) = rhs.symbol() else {
            return Err(TypeError::MissingConformanceRequirement(format!(
                "Protocol not found: {rhs:?}"
            )));
        };

        self.constraints.wants_conforms(lhs_ty.ty.clone(), id);
        Ok(lhs_ty)
    }

    fn visit_array(
        &mut self,
        expr: &Expr,
        items: &[Expr],
        context: &mut impl Solve,
    ) -> TypedRet<TypedExpr<InferTy>> {
        let Some(first_item) = items.first() else {
            let id = self.session.new_ty_meta_var_id(context.level());

            return Ok(TypedExpr {
                id: expr.id,
                ty: InferTy::Array(InferTy::Var {
                    id,
                    level: context.level(),
                }),
                kind: TypedExprKind::LiteralArray(vec![]),
            });
        };

        let item_ty = self.visit_expr(first_item, context)?;

        let mut typed_items = vec![];
        for expr in items[1..].iter() {
            let ty = self.visit_expr(expr, context)?;
            self.constraints
                .wants_equals(item_ty.ty.clone(), ty.ty.clone());
            typed_items.push(ty);
        }

        Ok(TypedExpr {
            id: expr.id,
            ty: InferTy::Array(item_ty.ty),
            kind: TypedExprKind::LiteralArray(typed_items),
        })
    }

    fn visit_func_signature(
        &mut self,
        protocol_self_id: TypeParamId,
        protocol_id: ProtocolId,
        func_signature: &FuncSignature,
        context: &mut impl Solve,
    ) -> TypedRet<InferTy> {
        for generic in func_signature.generics.iter() {
            let param_id = self.session.new_type_param_id(None);

            let Ok(name_sym) = generic.name.symbol() else {
                return Err(TypeError::NameNotResolved(generic.name.clone()));
            };

            self.session
                .insert_mono(name_sym, InferTy::Param(param_id), &mut self.constraints);
        }
        let params = self.visit_params(&func_signature.params, context)?;
        let ret = if let Some(ret) = &func_signature.ret {
            self.visit_type_annotation(ret, context)?
        } else {
            InferTy::Void
        };

        let ty = curry(params.iter().map(|p| p.ty.clone()), ret);
        let mut foralls: IndexSet<_> = ty.collect_foralls().into_iter().collect();
        foralls.insert(ForAll::Ty(protocol_self_id));
        let predicates = vec![Predicate::<InferTy>::Conforms {
            param: protocol_self_id,
            protocol_id,
        }];

        self.session.insert_term(
            func_signature
                .name
                .symbol()
                .unwrap_or_else(|_| unreachable!()),
            EnvEntry::Scheme(Scheme {
                ty: ty.clone(),
                foralls,
                predicates,
            }),
            &mut self.constraints,
        );

        Ok(ty)
    }

    fn visit_constructor(
        &mut self,
        expr: &Expr,
        name: &Name,
        _context: &mut impl Solve,
    ) -> TypedRet<TypedExpr<InferTy>> {
        let symbol = name
            .symbol()
            .map_err(|_| TypeError::NameNotResolved(name.clone()))?;

        let ty = InferTy::Constructor {
            name: name.clone(),
            params: vec![],
            ret: InferTy::Void.into(),
        };

        Ok(TypedExpr {
            id: expr.id,
            ty,
            kind: TypedExprKind::Constructor(symbol, vec![]),
        })
    }

    fn visit_member(
        &mut self,
        expr: &Expr,
        receiver: &Option<Box<Expr>>,
        label: &Label,
        context: &mut impl Solve,
    ) -> TypedRet<TypedExpr<InferTy>> {
        let receiver_ty = if let Some(receiver) = receiver {
            self.visit_expr(receiver, context)?
        } else {
            TypedExpr {
                id: expr.id,
                ty: self.session.new_ty_meta_var(context.level().next()),
                kind: TypedExprKind::Hole,
            }
        };

        let ret = self.session.new_ty_meta_var(context.level().next());

        self.constraints.wants_member(
            expr.id,
            receiver_ty.ty.clone(),
            label.clone(),
            ret.clone(),
            &context.group_info(),
        );

        Ok(TypedExpr {
            id: expr.id,
            ty: ret,
            kind: TypedExprKind::Member(Box::new(receiver_ty), label.clone()),
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, decl, generics, conformances, body, context))]
    fn visit_protocol(
        &mut self,
        decl: &Decl,
        name: &Name,
        generics: &[GenericDecl],
        conformances: &[TypeAnnotation],
        body: &Body,
        context: &mut impl Solve,
    ) -> TypedRet<TypedDecl<InferTy>> {
        let Ok(symbol) = name.symbol() else {
            return Err(TypeError::NameNotResolved(name.clone()));
        };

        let mut instance_methods = IndexMap::default();
        let mut instance_method_requirements = IndexMap::default();
        let mut associated_types = IndexMap::default();

        for decl in &body.decls {
            match &decl.kind {
                DeclKind::Method {
                    func,
                    is_static: false,
                } => {
                    instance_methods
                        .insert(func.name.name_str().into(), self.visit_func(func, context)?);
                }
                DeclKind::Associated { generic } => {
                    let id = self.register_generic(generic, context);
                    associated_types.insert(generic.name.name_str().into(), InferTy::Param(id));
                }
                DeclKind::MethodRequirement(func_signature)
                | DeclKind::FuncSignature(func_signature) => {
                    let params = self
                        .visit_params(&func_signature.params, context)?
                        .into_iter()
                        .map(|p| p.ty)
                        .collect_vec();
                    let ret = func_signature
                        .ret
                        .as_ref()
                        .map(|ret| self.visit_type_annotation(ret, context))
                        .transpose()?
                        .unwrap_or(InferTy::Void);
                    instance_method_requirements
                        .insert(func_signature.name.name_str().into(), curry(params, ret));
                }
                _ => {
                    tracing::error!("unhandled decl: {decl:?}");
                    continue;
                }
            }
        }

        Ok(TypedDecl {
            id: decl.id,
            kind: TypedDeclKind::ProtocolDef {
                symbol,
                instance_methods,
                instance_method_requirements,
                typealiases: Default::default(),
                associated_types,
            },
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, decl, generics, conformances, body, context))]
    fn visit_nominal(
        &mut self,
        decl: &Decl,
        name: &Name,
        generics: &[GenericDecl],
        conformances: &[TypeAnnotation],
        body: &Body,
        context: &mut impl Solve,
    ) -> TypedRet<TypedDecl<InferTy>> {
        let mut type_params = vec![];
        for generic in generics.iter() {
            type_params.push(InferTy::Param(self.register_generic(generic, context)));
        }

        let Ok(nominal_symbol) = name.symbol() else {
            return Err(TypeError::NameNotResolved(name.clone()));
        };

        let ty = InferTy::Nominal {
            symbol: nominal_symbol,
            type_args: type_params.clone(),
        };

        if !matches!(decl.kind, DeclKind::Extend { .. })
            && !self
                .session
                .type_catalog
                .nominals
                .contains_key(&nominal_symbol)
        {
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

            self.session
                .insert_term(nominal_symbol, entry, &mut self.constraints);
        }

        let mut row_types = vec![];
        let mut instance_methods = IndexMap::<Label, TypedFunc<InferTy>>::default();
        let mut properties: IndexMap<Label, InferTy> = IndexMap::default();
        let mut variants: IndexMap<Label, Vec<InferTy>> = IndexMap::default();
        let mut typealiases: IndexMap<Label, InferTy> = IndexMap::default();
        let mut nominal_conformances: Vec<Conformance<InferTy>> = vec![];

        for decl in body.decls.iter() {
            match &decl.kind {
                DeclKind::Init { name, params, body } => {
                    self.visit_init(decl, ty.clone(), name, params, body, &mut context.next());
                }
                DeclKind::Method { func, is_static } => {
                    let func =
                        self.visit_method(nominal_symbol, func, *is_static, &mut context.next())?;
                    instance_methods.insert(func.name.to_string().into(), func);
                }
                DeclKind::EnumVariant(name @ Name::Resolved(sym, name_str), _, values) => {
                    self.session
                        .type_catalog
                        .variants
                        .entry(nominal_symbol)
                        .or_default()
                        .insert(name_str.into(), *sym);

                    let tys: Vec<_> = values
                        .iter()
                        .map(|v| self.visit_type_annotation(v, &mut context.next()))
                        .try_collect()?;

                    variants.insert(name.name_str().into(), tys.clone());

                    let values_ty = match tys.len() {
                        0 => InferTy::Void,
                        1 => tys[0].clone(),
                        _ => InferTy::Tuple(tys.to_vec()),
                    };

                    self.session
                        .insert(*sym, values_ty.clone(), &mut self.constraints);
                    row_types.push((name.name_str(), values_ty));
                }
                DeclKind::Property {
                    name,
                    is_static,
                    type_annotation,
                    default_value,
                    ..
                } => {
                    properties.insert(
                        name.name_str().into(),
                        self.visit_property(
                            decl,
                            nominal_symbol,
                            name,
                            *is_static,
                            type_annotation,
                            default_value,
                            context,
                        )?,
                    );
                }
                DeclKind::TypeAlias(lhs, .., rhs) => {
                    let rhs_ty = self.visit_type_annotation(rhs, context)?;

                    // Quantify over the enclosing nominal's generics so the alias can be
                    // instantiated at use sites (e.g., Person<A>.T = A ⇒ T specializes to α).
                    let mut foralls: IndexSet<ForAll> = IndexSet::new();
                    for g in generics {
                        if let Ok(sym) = g.name.symbol()
                            && let Some(entry) = self.session.lookup(&sym)
                            && let InferTy::Param(pid) = entry._as_ty()
                        {
                            foralls.insert(ForAll::Ty(pid));
                        }
                    }

                    typealiases.insert(lhs.name_str().into(), rhs_ty.clone());

                    let Ok(lhs_sym) = lhs.symbol() else {
                        return Err(TypeError::NameNotResolved(lhs.clone()));
                    };

                    self.session
                        .type_catalog
                        .child_types
                        .entry(nominal_symbol)
                        .or_default()
                        .insert(lhs.name_str(), lhs_sym);

                    self.session.insert(lhs_sym, rhs_ty, &mut self.constraints);
                }
                _ => tracing::warn!("Unhandled nominal decl: {:?}", decl.kind),
            }
        }

        for conformance in conformances {
            let Ok(sym) = conformance.symbol() else {
                tracing::error!("skipping {conformance:?} due to unresolved name");
                continue;
            };

            self.register_conformance(
                &ty,
                nominal_symbol,
                sym,
                conformance.id,
                conformance.span,
                context,
            );
        }

        let kind = match &decl.kind {
            DeclKind::Struct { .. } => TypedDeclKind::StructDef {
                symbol: nominal_symbol,
                properties,
                instance_methods,
                typealiases,
                conformances: nominal_conformances,
            },
            DeclKind::Enum { .. } => TypedDeclKind::EnumDef {
                symbol: nominal_symbol,
                variants,
                instance_methods,
                typealiases,
                conformances: nominal_conformances,
            },
            DeclKind::Extend { .. } => TypedDeclKind::Extend {
                symbol: nominal_symbol,
                instance_methods,
                typealiases,
                conformances: nominal_conformances,
            },
            _ => unreachable!(),
        };

        Ok(TypedDecl { id: decl.id, kind })
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

        let transitive_conformance_keys = self
            .session
            .type_catalog
            .conformances
            .keys()
            .filter(|c| c.conforming_id == conformance_symbol)
            .copied()
            .collect_vec();

        for indirect_conformance in transitive_conformance_keys {
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

        // Get the protocol's associated type declarations
        // First try ASTs (for locally defined protocols), then type_catalog (for imported protocols)
        let protocol_associated_types = self
            .asts
            .iter()
            .find_map(|ast| ast.phase.child_types.get(&conformance_symbol))
            .cloned()
            .or_else(|| {
                self.session
                    .type_catalog
                    .associated_types
                    .get(&conformance_symbol)
                    .cloned()
            })
            .unwrap_or_default();

        let associated_types = protocol_associated_types
            .iter()
            .filter(|(_, sym)| matches!(sym, Symbol::AssociatedType(_)))
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

                tracing::debug!(
                    "  label={:?}, child_types={:?}, associated_ty={:?}",
                    label,
                    child_types,
                    associated_ty
                );
                acc.insert(label.clone(), associated_ty);
                acc
            });

        tracing::debug!("  final associated_types={:?}", associated_types);

        let key = ConformanceKey {
            protocol_id,
            conforming_id: nominal_symbol,
        };

        let mut conformance = self
            .session
            .type_catalog
            .conformances
            .remove(&key)
            .unwrap_or_else(|| Conformance {
                node_id: conformance_node_id,
                conforming_id: nominal_symbol,
                protocol_id,
                witnesses: Witnesses::default(),
                span: conformance_span,
            });

        conformance
            .witnesses
            .associated_types
            .extend(associated_types);

        self.session
            .type_catalog
            .conformances
            .insert(key, conformance);

        self.constraints.wants_conforms(ty.clone(), protocol_id);
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context))]
    fn infer_record_literal(
        &mut self,
        id: NodeID,
        fields: &[RecordField],
        spread: &Option<Box<Expr>>,
        context: &mut impl Solve,
    ) -> TypedRet<TypedExpr<InferTy>> {
        let mut row = InferRow::Empty(TypeDefKind::Struct);
        let mut typed_fields = vec![];
        for field in fields.iter().rev() {
            let typed_field = self.visit_expr(&field.value, context)?;
            row = InferRow::Extend {
                row: Box::new(row),
                label: field.label.name_str().into(),
                ty: typed_field.ty.clone(),
            };

            typed_fields.push(TypedRecordField {
                name: field.label.name_str().into(),
                value: typed_field,
            });
        }

        Ok(TypedExpr {
            id,
            ty: InferTy::Record(Box::new(row)),
            kind: TypedExprKind::RecordLiteral {
                fields: typed_fields,
            },
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context, func))]
    fn visit_method(
        &mut self,
        owner_symbol: Symbol,
        func: &Func,
        is_static: bool,
        context: &mut impl Solve,
    ) -> TypedRet<TypedFunc<InferTy>> {
        let Ok(func_sym) = func.name.symbol() else {
            return Err(TypeError::NameNotResolved(func.name.clone()));
        };

        if is_static {
            self.session
                .type_catalog
                .static_methods
                .entry(owner_symbol)
                .or_default()
                .insert(func.name.name_str().into(), func_sym);
        } else {
            self.session
                .type_catalog
                .instance_methods
                .entry(owner_symbol)
                .or_default()
                .insert(func.name.name_str().into(), func_sym);
        }

        let func_ty = self.visit_func(func, context)?;
        self.session.insert(
            func_sym,
            curry(
                func_ty.params.iter().map(|p| p.ty.clone()),
                func_ty.ret.clone(),
            ),
            &mut self.constraints,
        );

        Ok(func_ty)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context))]
    #[allow(clippy::too_many_arguments)]
    fn visit_property(
        &mut self,
        decl: &Decl,
        struct_symbol: Symbol,
        name: &Name,
        is_static: bool,
        type_annotation: &Option<TypeAnnotation>,
        default_value: &Option<Expr>,
        context: &mut impl Solve,
    ) -> TypedRet<InferTy> {
        let Ok(sym) = name.symbol() else {
            return Err(TypeError::NameNotResolved(name.clone()));
        };

        self.session
            .type_catalog
            .properties
            .entry(struct_symbol)
            .or_default()
            .insert(name.name_str().into(), sym);

        let ty = if let Some(anno) = type_annotation {
            self.visit_type_annotation(anno, context)?
        } else {
            self.session.new_type_param(None)
        };

        if let Some(default_value) = default_value {
            let default_ty = self.visit_expr(default_value, context)?;
            self.constraints
                .wants_equals(default_ty.ty.clone(), ty.clone());
        }

        if is_static {
            self.session
                .type_catalog
                .static_methods
                .entry(struct_symbol)
                .or_default()
                .insert(name.name_str().into(), sym);
        } else {
            self.session
                .type_catalog
                .properties
                .entry(struct_symbol)
                .or_default()
                .insert(name.name_str().into(), sym);
        }

        Ok(ty)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context, decl))]
    fn visit_init(
        &mut self,
        decl: &Decl,
        struct_ty: InferTy,
        name: &Name,
        params: &[Parameter],
        body: &Block,
        context: &mut impl Solve,
    ) -> TypedRet<TypedFunc<InferTy>> {
        let Ok(sym) = name.symbol() else {
            return Err(TypeError::NameNotResolved(name.clone()));
        };

        // Handle self param directly with struct_ty - don't instantiate!
        let params = self.visit_params(params, context)?;

        // Init blocks always return self
        let block = self.infer_block(body, context)?;

        let ty = curry(params.iter().map(|p| p.ty.clone()), struct_ty.clone());

        let InferTy::Nominal { symbol, .. } = &struct_ty else {
            unreachable!()
        };

        self.session
            .type_catalog
            .initializers
            .entry(*symbol)
            .or_default()
            .insert(Label::Named("init".into()), sym);

        let ty = substitute(ty, &self.session.skolem_map);
        self.session.insert(sym, ty, &mut self.constraints);

        Ok(TypedFunc {
            name: sym,
            params,
            body: block,
            ret: struct_ty,
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, scrutinee, arms, context))]
    fn infer_match(
        &mut self,
        id: NodeID,
        scrutinee: &Expr,
        arms: &[MatchArm],
        context: &mut impl Solve,
    ) -> TypedRet<TypedExpr<InferTy>> {
        let mut last_arm_ty: Option<InferTy> = None;
        let scrutinee_ty = self.visit_expr(scrutinee, context)?;
        let mut typed_arms = vec![];

        for arm in arms {
            let pattern = self.check_pattern(&arm.pattern, &scrutinee_ty.ty.clone(), context);
            let arm_ty = self.infer_block(&arm.body, context)?;

            if let Some(last_arm_ty) = &last_arm_ty {
                self.constraints
                    .wants_equals(arm_ty.ret.clone(), last_arm_ty.clone());
            }

            last_arm_ty = Some(arm_ty.ret.clone());
            typed_arms.push(TypedMatchArm {
                pattern,
                body: arm_ty,
            });
        }

        let ty = last_arm_ty.unwrap_or(InferTy::Void);

        Ok(TypedExpr {
            id,
            ty,
            kind: TypedExprKind::Match(Box::new(scrutinee_ty), typed_arms),
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context))]
    fn _promote_pattern_bindings(
        &mut self,
        pattern: &Pattern,
        expected: &InferTy,
        context: &mut impl Solve,
    ) -> InferTy {
        match &pattern.kind {
            PatternKind::Bind(Name::Resolved(sym, _)) => {
                if let Some(EnvEntry::Mono(existing)) = self.session.lookup(sym) {
                    self.constraints
                        .wants_equals(expected.clone(), existing.clone());
                };

                self.session
                    .insert(*sym, expected.clone(), &mut self.constraints);
                expected.clone()
            }
            PatternKind::Tuple(items) => {
                let ty = InferTy::Tuple(
                    items
                        .iter()
                        .map(|i| {
                            let var = self.session.new_ty_meta_var_id(context.level());

                            self._promote_pattern_bindings(
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

                self.constraints.wants_equals(ty.clone(), expected.clone());

                ty
            }
            PatternKind::Record { fields } => {
                let mut row = InferRow::Empty(TypeDefKind::Struct);
                for field in fields {
                    match &field.kind {
                        RecordFieldPatternKind::Bind(name) => {
                            let Ok(sym) = name.symbol() else {
                                self.asts[field.id.0.0 as usize].diagnostics.push(
                                    AnyDiagnostic::Typing(Diagnostic {
                                        id: field.id,
                                        kind: TypeError::NameNotResolved(name.clone()),
                                    }),
                                );
                                return InferTy::Error(
                                    TypeError::NameNotResolved(name.clone()).into(),
                                );
                            };

                            let var = self.session.new_ty_meta_var_id(context.level());
                            let ty = InferTy::Var {
                                id: var,
                                level: context.level(),
                            };

                            self.session.insert(sym, ty.clone(), &mut self.constraints);
                            row = InferRow::Extend {
                                row: row.into(),
                                label: name.name_str().into(),
                                ty,
                            };
                        }
                        RecordFieldPatternKind::Equals { name, value, .. } => {
                            let Ok(sym) = name.symbol() else {
                                self.asts[field.id.0.0 as usize].diagnostics.push(
                                    AnyDiagnostic::Typing(Diagnostic {
                                        id: field.id,
                                        kind: TypeError::NameNotResolved(name.clone()),
                                    }),
                                );
                                return InferTy::Error(
                                    TypeError::NameNotResolved(name.clone()).into(),
                                );
                            };

                            let ty = if let Some(existing) = self.session.lookup(&sym) {
                                existing._as_ty()
                            } else {
                                let var = self.session.new_ty_meta_var_id(context.level());

                                InferTy::Var {
                                    id: var,
                                    level: context.level(),
                                }
                            };
                            let ty = self._promote_pattern_bindings(value, &ty, context);
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
                self.constraints.wants_equals(ty.clone(), expected.clone());

                ty
            }
            // cover any other pattern forms you support
            _ => InferTy::Void,
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context))]
    fn check_pattern(
        &mut self,
        pattern: &Pattern,
        expected: &InferTy,
        context: &mut impl Solve,
    ) -> TypedPattern<InferTy> {
        let Pattern { kind, .. } = &pattern;

        match kind {
            PatternKind::Bind(Name::Raw(name)) => {
                self.constraints.wants_equals(
                    expected.clone(),
                    InferTy::Error(TypeError::NameNotResolved(name.clone().into()).into()),
                );
            }
            PatternKind::Bind(Name::Resolved(sym, _)) => {
                self.session
                    .insert_mono(*sym, expected.clone(), &mut self.constraints);
            }
            PatternKind::Bind(Name::SelfType(..)) => (),
            PatternKind::LiteralInt(_) => {
                self.constraints
                    .wants_equals(expected.clone(), InferTy::Int);
            }
            PatternKind::LiteralFloat(_) => {
                self.constraints
                    .wants_equals(expected.clone(), InferTy::Float);
            }
            PatternKind::LiteralFalse | PatternKind::LiteralTrue => {
                self.constraints
                    .wants_equals(expected.clone(), InferTy::Bool);
            }
            PatternKind::Tuple(patterns) => {
                let metas: Vec<InferTy> = (0..patterns.len())
                    .map(|_| self.session.new_ty_meta_var(context.level()))
                    .collect();

                self.constraints
                    .wants_equals(expected.clone(), InferTy::Tuple(metas.clone()));

                for (pi, bi) in patterns.iter().zip(metas) {
                    self.check_pattern(pi, &bi, context);
                }
            }
            PatternKind::Record { fields } => {
                let expected_row = self.ensure_row_record(expected, context);
                for field in fields {
                    match &field.kind {
                        RecordFieldPatternKind::Bind(name) => {
                            let Ok(sym) = name.symbol() else {
                                self.asts[field.id.0.0 as usize].diagnostics.push(
                                    AnyDiagnostic::Typing(Diagnostic {
                                        id: field.id,
                                        kind: TypeError::NameNotResolved(name.clone()),
                                    }),
                                );
                                continue;
                            };

                            // fresh meta for the field type
                            let field_ty = self.session.new_ty_meta_var(context.level());

                            // bind the pattern name
                            self.session
                                .insert_mono(sym, field_ty.clone(), &mut self.constraints);

                            // ONE RowHas per field, all referring to the same row
                            self.constraints._has_field(
                                expected_row.clone(),
                                name.name_str().into(),
                                field_ty,
                                &context.group_info(),
                            );
                        }
                        RecordFieldPatternKind::Equals { name, value, .. } => {
                            // optional: pattern field = subpattern; same RowHas then recurse on value
                            let field_ty = self.session.new_ty_meta_var(context.level());
                            self.constraints._has_field(
                                expected_row.clone(),
                                name.name_str().into(),
                                field_ty.clone(),
                                &context.group_info(),
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

                self.constraints.wants_member(
                    pattern.id,
                    expected.clone(),
                    variant_name.into(),
                    payload,
                    &context.group_info(),
                );

                // Recursively check each field pattern
                for (field_pattern, field_ty) in fields.iter().zip(field_metas) {
                    self.check_pattern(field_pattern, &field_ty, context);
                }
            }
            PatternKind::Wildcard => (),
            #[allow(clippy::todo)]
            PatternKind::Struct { .. } => todo!(),
        }

        TypedPattern {
            id: pattern.id,
            ty: expected.clone(),
            kind: kind.clone(),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, cond, conseq, alt, context))]
    fn infer_if_expr(
        &mut self,
        id: NodeID,
        cond: &Expr,
        conseq: &Block,
        alt: &Block,
        context: &mut impl Solve,
    ) -> TypedRet<TypedExpr<InferTy>> {
        let cond_ty = self.visit_expr(cond, context)?;
        self.constraints
            .wants_equals(cond_ty.ty.clone(), InferTy::Bool);

        let conseq_ty = self.infer_block(conseq, context)?;
        let alt_ty = self.infer_block(alt, context)?;
        self.constraints
            .wants_equals(conseq_ty.ret.clone(), alt_ty.ret.clone());

        Ok(TypedExpr {
            id,
            ty: conseq_ty.ret.clone(),
            kind: TypedExprKind::If(cond_ty.into(), conseq_ty, alt_ty),
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, cond, conseq, alt, context))]
    fn visit_if_stmt(
        &mut self,
        id: NodeID,
        cond: &Expr,
        conseq: &Block,
        alt: &Option<Block>,
        context: &mut impl Solve,
    ) -> TypedRet<TypedStmt<InferTy>> {
        let cond_ty = self.visit_expr(cond, context)?;
        self.constraints
            .wants_equals(cond_ty.ty.clone(), InferTy::Bool);

        let conseq_ty = self.infer_block(conseq, context)?;

        let alt_ty = if let Some(alt) = alt {
            self.infer_block(alt, context)?
        } else {
            TypedBlock {
                id: NodeID(id.0, self.asts[id.0.0 as usize].node_ids.next_id()),
                body: vec![],
                ret: InferTy::Void,
            }
        };

        Ok(TypedStmt {
            id,
            kind: TypedStmtKind::Expr(TypedExpr {
                id,
                ty: InferTy::Void,
                kind: TypedExprKind::If(cond_ty.into(), conseq_ty, alt_ty),
            }),
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, block, context))]
    fn infer_block(
        &mut self,
        block: &Block,
        context: &mut impl Solve,
    ) -> TypedRet<TypedBlock<InferTy>> {
        let mut ret = InferTy::Void;

        let mut nodes = vec![];
        for node in block.body.iter() {
            let typed_node = self.visit_node(node, context)?;
            ret = typed_node.ty();
            nodes.push(typed_node);
        }

        Ok(TypedBlock {
            id: block.id,
            body: nodes,
            ret,
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, block, context))]
    fn infer_block_with_returns(
        &mut self,
        block: &Block,
        context: &mut impl Solve,
    ) -> TypedRet<TypedBlock<InferTy>> {
        let tok = self.tracking_returns();
        let block = self.infer_block(block, context)?;
        self.verify_returns(tok, block.ret.clone());
        Ok(block)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, expr, context))]
    fn visit_variable(
        &mut self,
        expr: &Expr,
        name: &Name,
        context: &mut impl Solve,
    ) -> TypedRet<TypedExpr<InferTy>> {
        let Ok(sym) = name.symbol() else {
            return Err(TypeError::NameNotResolved(name.clone()));
        };

        let Some(entry) = self.session.lookup(&sym) else {
            return Err(TypeError::TypeNotFound(format!(
                "Entry not found for variable {:?}",
                name
            )));
        };

        let ty = entry.instantiate(expr.id, &mut self.constraints, context, self.session);

        self.instantiations
            .insert(expr.id, context.instantiations_mut().clone());

        Ok(TypedExpr {
            id: expr.id,
            ty,
            kind: TypedExprKind::Variable(sym),
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context, ))]
    fn visit_call(
        &mut self,
        id: NodeID,
        callee: &Expr,
        type_args: &[TypeAnnotation],
        args: &[CallArg],
        context: &mut impl Solve,
    ) -> TypedRet<TypedExpr<InferTy>> {
        let callee_ty = self.visit_expr(callee, context)?;

        let arg_tys: Vec<_> = args
            .iter()
            .map(|a| self.visit_expr(&a.value, context))
            .try_collect()?;
        let type_args: Vec<_> = type_args
            .iter()
            .map(|a| self.visit_type_annotation(a, context))
            .try_collect()?;

        let receiver = match &callee.kind {
            ExprKind::Member(Some(rcv), ..) => {
                if let ExprKind::Constructor(Name::Resolved(Symbol::Protocol(protocol_id), ..)) =
                    &rcv.kind
                    && let Some(first_arg) = arg_tys.first()
                {
                    self.constraints
                        .wants_conforms(first_arg.ty.clone(), *protocol_id);
                }

                Some(self.visit_expr(rcv, context)?)
            }
            ExprKind::Member(None, ..) => Some(TypedExpr {
                id: callee.id,
                ty: self.session.new_ty_meta_var(context.level()),
                kind: TypedExprKind::Hole,
            }),
            _ => None,
        };

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
            self.constraints.wants_equals(
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
            );
        }

        // if matches!(callee_ty, InferTy::Constructor { .. }) {
        //     arg_tys.insert(0, ret.clone());
        // }

        self.constraints.wants_call(
            callee.id,
            callee_ty.ty.clone(),
            arg_tys.iter().map(|a| a.ty.clone()).collect_vec(),
            type_args.clone(),
            ret.clone(),
            receiver.map(|r| r.ty.clone()),
            &context.group_info(),
        );

        Ok(TypedExpr {
            id,
            ty: ret,
            kind: TypedExprKind::Call {
                callee: callee_ty.into(),
                type_args,
                args: arg_tys,
            },
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context, func), fields(func.name = ?func.name))]
    fn visit_func(
        &mut self,
        func: &Func,
        context: &mut impl Solve,
    ) -> TypedRet<TypedFunc<InferTy>> {
        for generic in func.generics.iter() {
            self.register_generic(generic, context);
        }

        let params = self.visit_params(&func.params, context)?;

        let body = if let Some(ret) = &func.ret {
            let ret = self.visit_type_annotation(ret, context)?;
            self.check_block(&func.body, ret.clone(), &mut context.next())?
        } else {
            self.infer_block_with_returns(&func.body, &mut context.next())?
        };

        Ok(TypedFunc {
            name: func.name.symbol().unwrap_or_else(|_| unimplemented!()),
            params: params
                .iter()
                .map(|t| TypedParameter {
                    name: t.name,
                    ty: substitute(t.ty.clone(), &self.session.skolem_map),
                })
                .collect(),
            ret: substitute(body.ret.clone(), &self.session.skolem_map),
            body,
        })
    }

    fn visit_params(
        &mut self,
        params: &[Parameter],
        context: &mut impl Solve,
    ) -> TypedRet<Vec<TypedParameter<InferTy>>> {
        params
            .iter()
            .map(|param| self.visit_param(param, context))
            .try_collect()
    }

    fn visit_param(
        &mut self,
        param: &Parameter,
        context: &mut impl Solve,
    ) -> TypedRet<TypedParameter<InferTy>> {
        let Ok(sym) = param.name.symbol() else {
            unreachable!()
        };

        // If there's an existing entry (e.g., from capture placeholder), get its type
        // so we can unify with it if we have a type annotation
        let existing_ty = self.session.lookup(&sym).map(|e| e._as_ty());

        let ty = if let Some(type_annotation) = &param.type_annotation {
            let annotation_ty = self.visit_type_annotation(type_annotation, context)?;
            // If there was a placeholder, unify it with the annotated type
            if let Some(existing) = existing_ty {
                self.constraints
                    .wants_equals(existing, annotation_ty.clone());
            }
            annotation_ty
        } else if let Some(existing) = existing_ty {
            // No annotation but have existing - use it
            return Ok(TypedParameter {
                name: sym,
                ty: existing,
            });
        } else {
            self.session.new_ty_meta_var(context.level())
        };

        // I feel like params are always monotypes? But tests were failing when we
        // made them all mono..., i dont know
        if param.name.name_str() == "self" {
            self.session
                .insert_mono(sym, ty.clone(), &mut self.constraints);
        } else {
            self.session.insert(sym, ty.clone(), &mut self.constraints);
        }

        Ok(TypedParameter { name: sym, ty })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, block, context))]
    fn check_block(
        &mut self,
        block: &Block,
        expected: InferTy,
        context: &mut impl Solve,
    ) -> TypedRet<TypedBlock<InferTy>> {
        let tok = self.tracking_returns();
        let ret = self.infer_block(block, context)?;
        self.verify_returns(tok, ret.ret.clone());
        self.constraints.wants_equals(ret.ret.clone(), expected);
        Ok(ret)
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
    ) -> TypedRet<()> {
        for (param, expected_param_ty) in params.iter().zip(expected_params) {
            let Ok(sym) = param.name.symbol() else {
                self.asts[param.id.0.0 as usize]
                    .diagnostics
                    .push(AnyDiagnostic::Typing(Diagnostic {
                        id: param.id,
                        kind: TypeError::NameNotResolved(param.name.clone()),
                    }));
                continue;
            };

            self.session
                .insert_mono(sym, expected_param_ty, &mut self.constraints);
        }

        if let Some(ret) = ret {
            let ret_ty = self.visit_type_annotation(ret, context)?;
            self.constraints.wants_equals(ret_ty, expected_ret.clone());
        }

        self.check_block(body, expected_ret.clone(), context)?;

        Ok(())
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context))]
    fn visit_type_annotation(
        &mut self,
        type_annotation: &TypeAnnotation,
        context: &mut impl Solve,
    ) -> TypedRet<InferTy> {
        match &type_annotation.kind {
            TypeAnnotationKind::Nominal { name, generics, .. } => {
                let Ok(sym) = name.symbol() else {
                    return Err(TypeError::NameNotResolved(name.clone()));
                };

                let generic_args: Vec<_> = generics
                    .iter()
                    .map(|g| self.visit_type_annotation(g, context))
                    .try_collect::<InferTy, Vec<_>, TypeError>()?
                    .into_iter()
                    .zip(generics.iter().map(|g| g.id))
                    .collect();

                if let (
                    SolveContextKind::Protocol {
                        protocol_self,
                        protocol_id,
                    },
                    Symbol::AssociatedType(..),
                ) = (context.kind(), sym)
                {
                    // Fresh variable for the associated type's value in this position.
                    let result = self.session.new_ty_meta_var(context.level());

                    // Base is the protocol "Self" variable in this requirement.
                    let base = InferTy::Param(protocol_self);

                    self.constraints.wants_projection(
                        type_annotation.id,
                        base,
                        name.name_str().into(), // "T"
                        Some(protocol_id),
                        result.clone(),
                        &context.group_info(),
                    );

                    return Ok(result);
                }

                if matches!(name.symbol(), Ok(Symbol::Builtin(..))) {
                    return Ok(resolve_builtin_type(
                        &name.symbol().unwrap_or_else(|_| unreachable!()),
                    )
                    .0);
                }

                // Do we know about this already? Cool.
                if let Some(entry) = self.session.lookup(&sym) {
                    let (ty, subsitutions) = entry.instantiate_with_args(
                        type_annotation.id,
                        &generic_args,
                        self.session,
                        context,
                        &mut self.constraints,
                    );

                    self.instantiations.insert(type_annotation.id, subsitutions);

                    return Ok(ty);
                } else {
                    tracing::warn!("nope, did not find anything in the env for {name:?}");
                }

                Ok(InferTy::Nominal {
                    symbol: sym,
                    type_args: generic_args.into_iter().map(|a| a.0).collect(),
                })
            }
            TypeAnnotationKind::SelfType(name) => {
                let Ok(sym) = name.symbol() else {
                    self.asts[type_annotation.id.0.0 as usize].diagnostics.push(
                        AnyDiagnostic::Typing(Diagnostic {
                            id: type_annotation.id,
                            kind: TypeError::NameNotResolved(name.clone()),
                        }),
                    );
                    return Err(TypeError::NameNotResolved(name.clone()));
                };

                if matches!(name.symbol(), Ok(Symbol::Builtin(..))) {
                    return Ok(resolve_builtin_type(&sym).0);
                }

                if let SolveContextKind::Protocol { protocol_self, .. } = context.kind() {
                    return Ok(InferTy::Param(protocol_self));
                }

                if self.session.lookup_nominal(&sym).is_some() {
                    return Ok(InferTy::Nominal {
                        symbol: sym,
                        type_args: vec![],
                    });
                }

                let Some(entry) = self.session.lookup(&sym) else {
                    return Err(TypeError::TypeNotFound(format!(
                        "Type annotation entry not found {name:?}"
                    )));
                };

                Ok(entry._as_ty())
            }
            TypeAnnotationKind::Record { fields } => {
                let mut row = InferRow::Empty(TypeDefKind::Struct);
                for field in fields.iter().rev() {
                    row = InferRow::Extend {
                        row: Box::new(row),
                        label: field.label.name_str().into(),
                        ty: self.visit_type_annotation(&field.value, context)?,
                    };
                }

                Ok(InferTy::Record(Box::new(row)))
            }
            TypeAnnotationKind::NominalPath {
                base,
                member,
                member_generics,
                ..
            } => {
                let base_ty = self.visit_type_annotation(base, context)?;
                let generics = member_generics
                    .iter()
                    .map(|t| self.visit_type_annotation(t, context))
                    .try_collect()?;
                let ret = self.session.new_ty_meta_var(context.level());

                if matches!(base.symbol(), Ok(Symbol::TypeParameter(..))) {
                    self.constraints.wants_projection(
                        type_annotation.id,
                        base_ty,
                        member.clone(),
                        None,
                        ret.clone(),
                        &context.group_info(),
                    );
                } else {
                    self.constraints.wants_type_member(
                        base_ty,
                        member.clone(),
                        generics,
                        ret.clone(),
                        type_annotation.id,
                        &context.group_info(),
                    );
                }

                Ok(ret)
            }
            _ => Err(TypeError::TypeNotFound(format!(
                "Type annotation unable to be determined {type_annotation:?}"
            ))),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context, rhs))]
    fn visit_let(
        &mut self,
        id: NodeID,
        lhs: &Pattern,
        type_annotation: &Option<TypeAnnotation>,
        rhs: &Option<Expr>,
        context: &mut impl Solve,
    ) -> TypedRet<TypedDecl<InferTy>> {
        let ty = match (&type_annotation, &rhs) {
            (None, Some(expr)) => self.visit_expr(expr, context)?.ty,
            (Some(annotation), None) => self.visit_type_annotation(annotation, context)?,
            (Some(annotation), Some(rhs)) => {
                let annotated_ty = self.visit_type_annotation(annotation, context)?;
                let rhs_ty = self.visit_expr(rhs, context)?;
                self.constraints
                    .wants_equals(annotated_ty.clone(), rhs_ty.ty);
                annotated_ty
            }
            (None, None) => self.session.new_ty_meta_var(context.level().next()),
        };

        let typed_pattern = self.check_pattern(lhs, &ty, context);

        Ok(TypedDecl {
            id,
            kind: TypedDeclKind::Let {
                pattern: typed_pattern,
                ty,
            },
        })
    }

    fn tracking_returns(&mut self) -> ReturnToken {
        self.tracked_returns.push(Default::default());
        ReturnToken {}
    }

    fn verify_returns(&mut self, _tok: ReturnToken, ret: InferTy) {
        for tracked_ret in self.tracked_returns.pop().unwrap_or_else(|| unreachable!()) {
            self.constraints.wants_equals(tracked_ret.1, ret.clone());
        }
    }

    fn ensure_row_record(&mut self, expected: &InferTy, context: &mut impl Solve) -> InferRow {
        match expected {
            InferTy::Record(box row) => row.clone(),
            _ => {
                let row = self.session.new_row_meta_var(context.level());
                self.constraints
                    .wants_equals(expected.clone(), InferTy::Record(Box::new(row.clone())));
                row
            }
        }
    }

    fn register_generic(&mut self, generic: &GenericDecl, context: &mut impl Solve) -> TypeParamId {
        let param_id = self.session.new_type_param_id(None);

        for conformance in generic.conformances.iter() {
            let Ok(Symbol::Protocol(protocol_id)) = conformance.symbol() else {
                tracing::warn!("could not determine conformance: {conformance:?}");
                continue;
            };

            let predicate = Predicate::Conforms {
                param: param_id,
                protocol_id,
            };

            context.givens_mut().insert(predicate.clone());
            self.session
                .type_param_bounds
                .entry(param_id)
                .or_default()
                .insert(predicate);
        }

        let Ok(sym) = generic.name.symbol() else {
            self.asts[generic.id.0.0 as usize]
                .diagnostics
                .push(AnyDiagnostic::Typing(Diagnostic {
                    id: generic.id,
                    kind: TypeError::NameNotResolved(generic.name.clone()),
                }));
            return 0.into();
        };

        self.session
            .insert_mono(sym, InferTy::Param(param_id), &mut self.constraints);

        param_id
    }
}
