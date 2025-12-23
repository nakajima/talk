use indexmap::{IndexMap, IndexSet, indexset};
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use tracing::instrument;

use crate::{
    ast::{AST, NameResolved},
    compiling::module::ModuleId,
    diagnostic::{AnyDiagnostic, Diagnostic, Severity},
    formatter,
    label::Label,
    name::Name,
    name_resolution::{
        scc_graph::BindingGroup,
        symbol::{ProtocolId, Symbol, set_symbol_names},
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
        inline_ir_instruction::{InlineIRInstruction, TypedInlineIRInstruction},
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
        constraints::{
            constraint::Constraint,
            store::{ConstraintStore, GroupId},
        },
        infer_row::InferRow,
        infer_ty::{InferTy, Level, Meta, MetaVarId, TypeParamId},
        predicate::Predicate,
        scheme::{ForAll, Scheme},
        solve_context::{Solve, SolveContext, SolveContextKind},
        term_environment::EnvEntry,
        ty::Ty,
        type_catalog::Nominal,
        type_error::TypeError,
        type_operations::{
            InstantiationSubstitutions, UnificationSubstitutions, curry, substitute,
        },
        type_session::{TypeDefKind, TypeSession},
        typed_ast::{
            TypedAST, TypedBlock, TypedDecl, TypedDeclKind, TypedExpr, TypedExprKind, TypedFunc,
            TypedMatchArm, TypedNode, TypedParameter, TypedPattern, TypedPatternKind,
            TypedRecordField, TypedRecordFieldPattern, TypedRecordFieldPatternKind, TypedStmt,
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
    asts: &'a mut [&'a mut AST<NameResolved>],
    session: &'a mut TypeSession,
    constraints: ConstraintStore,
    instantiations: FxHashMap<NodeID, InstantiationSubstitutions>,
    substitutions: UnificationSubstitutions,
    tracked_returns: Vec<IndexSet<(NodeID, InferTy)>>,
    nominal_placeholders: FxHashMap<Symbol, (MetaVarId, Level)>,
    or_binders: Vec<FxHashMap<Symbol, InferTy>>,
    diagnostics: IndexSet<AnyDiagnostic>,
    root_decls: Vec<TypedDecl<InferTy>>,
    root_stmts: Vec<TypedStmt<InferTy>>,
}

impl<'a> InferencePass<'a> {
    pub fn drive(
        asts: &'a mut [&'a mut AST<NameResolved>],
        session: &'a mut TypeSession,
    ) -> (TypedAST<Ty>, Vec<AnyDiagnostic>) {
        let substitutions = UnificationSubstitutions::new(session.meta_levels.clone());
        let pass = InferencePass {
            asts,
            session,
            instantiations: Default::default(),
            constraints: Default::default(),
            substitutions,
            tracked_returns: Default::default(),
            diagnostics: Default::default(),
            nominal_placeholders: Default::default(),
            or_binders: Default::default(),
            root_decls: Default::default(),
            root_stmts: Default::default(),
        };

        pass.drive_all()
    }

    fn drive_all(mut self) -> (TypedAST<Ty>, Vec<AnyDiagnostic>) {
        let _s = set_symbol_names(self.session.resolved_names.symbol_names.clone());

        // Register extension conformances first, so they're available when processing protocol default methods
        for i in 0..self.asts.len() {
            self.discover_conformances(i);
        }

        for i in 0..self.asts.len() {
            self.discover_protocols(i, Level::default());
            self.session.apply_all(&mut self.substitutions);
        }

        self.generate();
        self.session.apply_all(&mut self.substitutions);

        // Transfer child_types from AST phases to the catalog for module export
        for (sym, entries) in self.session.resolved_names.child_types.iter() {
            self.session
                .type_catalog
                .child_types
                .entry(*sym)
                .or_default()
                .extend(entries.iter().map(|(k, v)| (k.clone(), *v)));
        }

        // At this point, any unsolved constraints are errors
        for constraint in self.constraints.unsolved() {
            match constraint {
                Constraint::Call(..) => (),
                Constraint::Equals(..) => (),
                Constraint::HasField(..) => (),
                Constraint::Member(..) => (),
                Constraint::Conforms(conforms) => {
                    match &conforms.ty {
                        InferTy::Nominal { symbol, .. } | InferTy::Primitive(symbol) => {
                            self.diagnostics.insert(AnyDiagnostic::Typing(Diagnostic {
                                id: conforms.conformance_node_id,
                                severity: Severity::Error,
                                kind: TypeError::TypeDoesNotConform {
                                    symbol: *symbol,
                                    protocol_id: conforms.protocol_id,
                                },
                            }));
                        }
                        InferTy::Constructor { name, .. } => {
                            self.diagnostics.insert(AnyDiagnostic::Typing(Diagnostic {
                                id: conforms.conformance_node_id,
                                severity: Severity::Error,
                                kind: TypeError::TypeDoesNotConform {
                                    symbol: name
                                        .symbol()
                                        .unwrap_or_else(|_| unreachable!("did not resolve name")),
                                    protocol_id: conforms.protocol_id,
                                },
                            }));
                        }
                        ty => {
                            tracing::error!("did not solve {conforms:?}");
                            self.diagnostics.insert(AnyDiagnostic::Typing(Diagnostic {
                                id: conforms.conformance_node_id,
                                severity: Severity::Error,
                                kind: TypeError::TypeCannotConform {
                                    ty: ty.clone(),
                                    protocol_id: conforms.protocol_id,
                                },
                            }));
                        }
                    };
                }
                Constraint::TypeMember(..) => (),
                Constraint::Projection(..) => (),
            }
        }

        let typed_ast = TypedAST {
            decls: self.root_decls,
            stmts: self.root_stmts,
        };

        let ast = typed_ast
            .apply(&mut self.substitutions, self.session)
            .finalize(
                self.session,
                &self.session.protocol_member_witnesses.clone(),
            );

        (ast, self.diagnostics.into_iter().collect())
    }

    fn discover_conformances(&mut self, idx: usize) {
        let roots = std::mem::take(&mut self.asts[idx].roots);
        for root in roots.iter() {
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

                let protocol_symbol = Symbol::Protocol(protocol_id);
                let Some(conforming_id) = name.symbol().ok() else {
                    tracing::error!("did not resolve {name:?}");
                    continue;
                };

                self.register_conformance(
                    conforming_id,
                    protocol_symbol,
                    conformance.id,
                    conformance.span,
                    &mut SolveContext::new(
                        UnificationSubstitutions::new(self.session.meta_levels.clone()),
                        Level::default(),
                        GroupId(u32::MAX),
                        SolveContextKind::Nominal,
                    ),
                )
                .ok();

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
        _ = std::mem::replace(&mut self.asts[idx].roots, roots);
    }

    fn discover_protocols(&mut self, idx: usize, level: Level) {
        let mut result = vec![];
        let roots = std::mem::take(&mut self.asts[idx].roots);
        for root in roots.iter() {
            let Node::Decl(
                decl @ Decl {
                    kind:
                        DeclKind::Protocol {
                            name: protocol_name @ Name::Resolved(Symbol::Protocol(protocol_id), ..),
                            generics,
                            conformances,
                            body,
                            ..
                        },
                    ..
                },
            ) = root
            else {
                continue;
            };

            let Ok(protocol_sym) = protocol_name.symbol() else {
                self.diagnostics.insert(AnyDiagnostic::Typing(Diagnostic {
                    id: root.node_id(),
                    severity: Severity::Error,
                    kind: TypeError::NameNotResolved(protocol_name.clone()),
                }));
                continue;
            };

            let protocol_self_id = self.session.new_type_param_id(None);
            self.session.insert(
                protocol_sym,
                InferTy::Param(protocol_self_id),
                &mut self.constraints,
            );

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

            let mut binders = IndexMap::<Symbol, InferTy>::default();

            match self.visit_protocol(
                decl,
                protocol_name,
                generics,
                conformances,
                body,
                &mut context,
            ) {
                Ok((decl, new_binders)) => {
                    result.push(decl);
                    binders.extend(new_binders)
                }
                Err(e) => {
                    self.diagnostics.insert(AnyDiagnostic::Typing(Diagnostic {
                        id: decl.id,
                        severity: Severity::Error,
                        kind: e,
                    }));
                }
            }

            let (binders, placeholders) = binders.into_iter().unzip();
            self.solve(&mut context, binders, placeholders)
        }
        _ = std::mem::replace(&mut self.asts[idx].roots, roots);

        self.root_decls.extend(result);
    }

    fn visit_associated_type(
        &mut self,
        generic: &GenericDecl,
        protocol_self_id: TypeParamId,
        protocol_symbol: Symbol,
    ) -> TypedRet<InferTy> {
        let Symbol::Protocol(protocol_id) = protocol_symbol else {
            unreachable!()
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
                protocol_id: Some(protocol_id),
                returns: ret.clone(),
            }],
        };

        let Ok(generic_sym) = generic.name.symbol() else {
            self.diagnostics.insert(AnyDiagnostic::Typing(Diagnostic {
                id: generic.id,
                severity: Severity::Error,
                kind: TypeError::NameNotResolved(generic.name.clone()),
            }));
            return Err(TypeError::NameNotResolved(generic.name.clone()));
        };

        self.session
            .insert_term(generic_sym, EnvEntry::Scheme(scheme), &mut self.constraints);
        self.session
            .type_catalog
            .associated_types
            .entry(protocol_symbol)
            .or_default()
            .insert(generic.name.name_str().into(), generic_sym);

        Ok(ret)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, decl, _generics, conformances, body, context))]
    fn visit_protocol(
        &mut self,
        decl: &Decl,
        name: &Name,
        _generics: &[GenericDecl],
        conformances: &[TypeAnnotation],
        body: &Body,
        context: &mut impl Solve,
    ) -> TypedRet<(TypedDecl<InferTy>, IndexMap<Symbol, InferTy>)> {
        let Ok(protocol_symbol @ Symbol::Protocol(protocol_id)) = name.symbol() else {
            return Err(TypeError::NameNotResolved(name.clone()));
        };

        let Some(InferTy::Param(protocol_self_id)) =
            self.session.lookup(&protocol_symbol).map(|s| s._as_ty())
        else {
            return Err(TypeError::TypeNotFound(
                "Didn't get self id for {protocol_symbol:?}".into(),
            ));
        };

        let mut binders: IndexMap<Symbol, InferTy> = IndexMap::default();

        for conformance in conformances {
            let Ok(Symbol::Protocol(conforms_to_id)) = conformance.symbol() else {
                tracing::error!("did not get protocol for conforms_to");
                continue;
            };

            let key = ConformanceKey {
                protocol_id: conforms_to_id,
                conforming_id: protocol_symbol,
            };

            self.register_conformance(
                protocol_symbol,
                conforms_to_id.into(),
                conformance.id,
                conformance.span,
                context,
            )
            .ok();

            self.session.type_catalog.conformances.insert(
                key,
                Conformance {
                    node_id: conformance.id,
                    conforming_id: protocol_symbol,
                    protocol_id: conforms_to_id,
                    witnesses: Default::default(),
                    span: conformance.span,
                },
            );
        }

        context.givens_mut().insert(Predicate::Conforms {
            param: protocol_self_id,
            protocol_id,
        });

        self.session
            .type_param_bounds
            .entry(protocol_self_id)
            .or_default()
            .insert(Predicate::Conforms {
                param: protocol_self_id,
                protocol_id,
            });
        self.session.insert(
            protocol_symbol,
            InferTy::Param(protocol_self_id),
            &mut self.constraints,
        );

        let mut instance_methods = IndexMap::default();
        let mut instance_method_requirements = IndexMap::default();
        let mut associated_types = IndexMap::default();

        for decl in &body.decls {
            match &decl.kind {
                DeclKind::Method {
                    func,
                    is_static: false,
                } => {
                    let func_sym = func
                        .name
                        .symbol()
                        .map_err(|_| TypeError::NameNotResolved(func.name.clone()))?;

                    self.session
                        .type_catalog
                        .instance_methods
                        .entry(protocol_symbol)
                        .or_default()
                        .insert(
                            func.name.name_str().into(),
                            func.name
                                .symbol()
                                .map_err(|_| TypeError::NameNotResolved(name.clone()))?,
                        );

                    let typed_func = self.visit_func(func, context)?;
                    let func_ty = curry(
                        typed_func.params.iter().map(|p| p.ty.clone()),
                        typed_func.ret.clone(),
                    );

                    // We want to override the func to include the self predicate
                    let foralls = func_ty.collect_foralls();
                    let entry = EnvEntry::Scheme(Scheme {
                        foralls,
                        predicates: vec![Predicate::Conforms {
                            param: protocol_self_id,
                            protocol_id,
                        }],
                        ty: func_ty.clone(),
                    });

                    self.session.promote(func_sym, entry, &mut self.constraints);

                    instance_methods.insert(func.name.name_str().into(), typed_func.clone());

                    binders.insert(func_sym, func_ty);
                }
                DeclKind::Associated { generic } => {
                    if let Ok(ty) =
                        self.visit_associated_type(generic, protocol_self_id, protocol_symbol)
                    {
                        associated_types.insert(generic.name.name_str().into(), ty);
                    }
                }
                DeclKind::MethodRequirement(func_signature)
                | DeclKind::FuncSignature(func_signature) => {
                    let ty = self.visit_func_signature(
                        protocol_self_id,
                        protocol_id,
                        func_signature,
                        context,
                    )?;
                    binders.insert(
                        func_signature
                            .name
                            .symbol()
                            .map_err(|_| TypeError::NameNotResolved(func_signature.name.clone()))?,
                        ty.clone(),
                    );
                    instance_method_requirements.insert(func_signature.name.name_str().into(), ty);
                }
                _ => {
                    tracing::error!("unhandled decl: {decl:?}");
                    continue;
                }
            }
        }

        if let Some(child_types) = self
            .session
            .resolved_names
            .child_types
            .get(&protocol_symbol)
        {
            self.session
                .type_catalog
                .associated_types
                .entry(protocol_symbol)
                .or_default()
                .extend(child_types.clone());
        }

        Ok((
            TypedDecl {
                id: decl.id,
                ty: self
                    .session
                    .lookup(&protocol_symbol)
                    .unwrap_or_else(|| unreachable!("did not find ty for {protocol_symbol:?}"))
                    ._as_ty(),
                kind: TypedDeclKind::ProtocolDef {
                    symbol: protocol_symbol,
                    instance_methods,
                    instance_method_requirements,
                    typealiases: Default::default(),
                    associated_types,
                },
            },
            binders,
        ))
    }

    fn generate(&mut self) {
        if self.asts.is_empty() {
            return;
        }

        let mut groups = self.session.resolved_names.scc_graph.groups();
        groups.sort_by_key(|group| group.id.0);

        for group in groups {
            let is_top_level = group.is_top_level;
            let (new_decls, new_stmts) = self.generate_for_group(group.clone());

            if is_top_level {
                self.root_decls.extend(new_decls);
                self.root_stmts.extend(new_stmts);
            }
        }

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

        self.solve(&mut context, Default::default(), Default::default());

        // Apply substitutions to types_by_node for top-level expressions
        self.session.apply_all(&mut context.substitutions);
    }

    #[instrument(skip(self))]
    fn generate_for_group(
        &mut self,
        group: BindingGroup,
    ) -> (Vec<TypedDecl<InferTy>>, Vec<TypedStmt<InferTy>>) {
        let mut decls = vec![];
        let mut stmts = vec![];

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
            if let Some(captures) = self.session.resolved_names.captures.get(binder).cloned() {
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
                .session
                .resolved_names
                .scc_graph
                .rhs_id_for(binder)
                .copied()
            else {
                tracing::error!("did not find rhs_id for binder: {binder:?}");
                return (decls, stmts);
            };

            let Some(rhs) = self.asts.iter().find_map(|ast| ast.find(rhs_id)) else {
                tracing::error!("did not find rhs for id: {rhs_id:?}, binder: {binder:?}");
                return (decls, stmts);
            };

            let node = match self.visit_node(&rhs, &mut context) {
                Ok(node) => node,
                Err(e) => {
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
                if existing == EnvEntry::Mono(placeholders[i].clone()) {
                    self.constraints.wants_equals_at(
                        rhs_id,
                        node.ty(),
                        placeholders[i].clone(),
                        &context.group_info(),
                    );
                } else {
                    self.constraints.wants_equals_at(
                        rhs_id,
                        placeholders[i].clone(),
                        existing._as_ty(),
                        &context.group_info(),
                    );
                }
            }
        }

        // Solve this group
        self.solve(&mut context, group.binders.clone(), placeholders);
        (decls, stmts)
    }

    fn solve(
        &mut self,
        context: &mut SolveContext,
        binders: Vec<Symbol>,
        placeholders: Vec<InferTy>,
    ) {
        context.substitutions_mut().extend(&self.substitutions);

        let level = context.level();
        let solver = ConstraintSolver::new(context);
        let diagnostics = solver.solve(
            level,
            &mut self.constraints,
            self.session,
            self.substitutions.clone(),
        );

        self.diagnostics.extend(diagnostics);

        let generalizable = self.constraints.generalizable_for(context);

        for (i, binder) in binders.iter().enumerate() {
            let ty = self
                .session
                .apply(placeholders[i].clone(), &mut context.substitutions);
            let entry = self
                .session
                .generalize(ty, context, &generalizable, &mut self.constraints);
            self.session.promote(*binder, entry, &mut self.constraints);
        }

        self.substitutions.extend(&context.substitutions);
        self.session.apply_all(&mut self.substitutions);
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
                body,
                ..
            } => self.visit_nominal(decl, name, generics, Default::default(), body, context),
            DeclKind::Protocol {
                name,
                generics,
                body,
                conformances,
                ..
            } => Ok(self
                .visit_protocol(decl, name, generics, conformances, body, context)?
                .0),
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
                body,
                ..
            } => self.visit_nominal(decl, name, generics, Default::default(), body, context),
            DeclKind::Import(_) => unimplemented!(),
            DeclKind::Func(..)
            | DeclKind::Init { .. }
            | DeclKind::TypeAlias(..)
            | DeclKind::Associated { .. }
            | DeclKind::Method { .. }
            | DeclKind::Property { .. }
            | DeclKind::MethodRequirement(..)
            | DeclKind::FuncSignature(..)
            | DeclKind::EnumVariant(..) => unreachable!("skipped: {decl:?}"),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, stmt, context), fields(stmt.id = ?stmt.id))]
    fn visit_stmt(
        &mut self,
        stmt: &Stmt,
        context: &mut impl Solve,
    ) -> TypedRet<TypedStmt<InferTy>> {
        let ty = match &stmt.kind {
            StmtKind::Expr(expr) => {
                let typed_expr = self.visit_expr(expr, context)?;
                TypedStmt {
                    id: stmt.id,
                    ty: typed_expr.ty.clone(),
                    kind: TypedStmtKind::Expr(typed_expr),
                }
            }
            StmtKind::If(cond, conseq, alt) => {
                self.visit_if_stmt(stmt.id, cond, conseq, alt, context)?
            }
            StmtKind::Assignment(lhs, rhs) => {
                let lhs_ty = self.visit_expr(lhs, context)?;
                let rhs_ty = self.visit_expr(rhs, context)?;
                self.constraints.wants_equals_at(
                    stmt.id,
                    lhs_ty.ty.clone(),
                    rhs_ty.ty.clone(),
                    &context.group_info(),
                );
                TypedStmt {
                    id: stmt.id,
                    ty: lhs_ty.ty.clone(),
                    kind: TypedStmtKind::Assignment(lhs_ty, rhs_ty),
                }
            }
            StmtKind::Return(expr) => self.visit_return(stmt, expr, context)?,
            StmtKind::Break => TypedStmt {
                id: stmt.id,
                ty: InferTy::Void,
                kind: TypedStmtKind::Break,
            },
            StmtKind::Loop(cond, block) => {
                let cond_ty = if let Some(cond) = cond {
                    let cond_ty = self.visit_expr(cond, context)?;
                    self.constraints.wants_equals_at(
                        cond.id,
                        cond_ty.ty.clone(),
                        InferTy::Bool,
                        &context.group_info(),
                    );
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
                    ty: InferTy::Void,
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
            ExprKind::Incomplete(incomplete) => {
                use crate::node_kinds::incomplete_expr::IncompleteExpr;
                match incomplete {
                    IncompleteExpr::Member(Some(receiver)) => {
                        let _ = self.visit_expr(receiver, context)?;
                    }
                    IncompleteExpr::Member(None) => {}
                    IncompleteExpr::Func { .. } => {}
                }

                TypedExpr {
                    id: expr.id,
                    ty: InferTy::Void,
                    kind: TypedExprKind::Hole,
                }
            }
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
            kind: TypedExprKind::InlineIR(
                TypedInlineIRInstruction {
                    id: instr.id,
                    span: instr.span,
                    binds: instr
                        .binds
                        .iter()
                        .map(|e| self.visit_expr(e, context))
                        .try_collect()?,
                    instr_name_span: instr.instr_name_span,
                    kind: instr.kind.clone(),
                }
                .into(),
            ),
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
            returns.insert((stmt.id, ty_expr.ty.clone()));
        }

        Ok(TypedStmt {
            id: stmt.id,
            ty: ty_expr
                .as_ref()
                .map(|t| t.ty.clone())
                .unwrap_or(InferTy::Void),
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

        self.constraints
            .wants_conforms(lhs.id, lhs_ty.ty.clone(), id, &context.group_info());

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

        let mut typed_items = vec![item_ty.clone()];
        for expr in items[1..].iter() {
            let ty = self.visit_expr(expr, context)?;
            self.constraints.wants_equals_at(
                expr.id,
                item_ty.ty.clone(),
                ty.ty.clone(),
                &context.group_info(),
            );
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

        self.session
            .type_catalog
            .method_requirements
            .entry(protocol_id.into())
            .or_default()
            .insert(
                func_signature.name.name_str().into(),
                func_signature.name.symbol().map_err(|_| {
                    TypeError::NameNotResolved(Name::Raw(format!("{protocol_id}")).clone())
                })?,
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
            kind: TypedExprKind::Member {
                receiver: Box::new(receiver_ty),
                label: label.clone(),
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
        let Ok(nominal_symbol) = name.symbol() else {
            return Err(TypeError::NameNotResolved(name.clone()));
        };

        let mut type_params = vec![];
        for generic in generics.iter() {
            let id = self.register_generic(generic, context);
            type_params.push(InferTy::Param(id));
            let name = generic
                .name
                .symbol()
                .map_err(|_| TypeError::NameNotResolved(generic.name.clone()))?;
            self.session
                .type_catalog
                .child_types
                .entry(nominal_symbol)
                .or_default()
                .insert(generic.name.name_str().into(), name);
        }

        let ty = if matches!(nominal_symbol, Symbol::Builtin(..)) {
            InferTy::Primitive(nominal_symbol)
        } else {
            InferTy::Nominal {
                symbol: nominal_symbol,
                type_args: type_params.clone(),
            }
        };

        if !matches!(decl.kind, DeclKind::Extend { .. })
            && !self
                .session
                .type_catalog
                .nominals
                .contains_key(&nominal_symbol)
        {
            self.session
                .insert(nominal_symbol, ty.clone(), &mut self.constraints);
        }

        let mut row_types = vec![];
        let mut initializers = IndexMap::<Label, TypedFunc<InferTy>>::default();
        let mut instance_methods = IndexMap::<Label, TypedFunc<InferTy>>::default();
        let mut properties: IndexMap<Label, InferTy> = IndexMap::default();
        let mut variants: IndexMap<Label, Vec<InferTy>> = IndexMap::default();
        let mut typealiases: IndexMap<Label, InferTy> = IndexMap::default();

        for decl in body.decls.iter() {
            match &decl.kind {
                DeclKind::Init { name, params, body } => {
                    let func =
                        self.visit_init(decl, ty.clone(), name, params, body, &mut context.next())?;
                    initializers.insert("init".into(), func);
                    self.session
                        .type_catalog
                        .initializers
                        .entry(nominal_symbol)
                        .or_default()
                        .insert(
                            name.name_str().into(),
                            name.symbol()
                                .map_err(|_| TypeError::NameNotResolved(name.clone()))?,
                        );
                }
                DeclKind::Method { func, is_static } => {
                    let func_name = &func.name;
                    let func =
                        self.visit_method(nominal_symbol, func, *is_static, &mut context.next())?;
                    instance_methods.insert(func.name.to_string().into(), func);

                    self.session
                        .type_catalog
                        .instance_methods
                        .entry(nominal_symbol)
                        .or_default()
                        .insert(
                            func_name.name_str().into(),
                            func_name
                                .symbol()
                                .map_err(|_| TypeError::NameNotResolved(name.clone()))?,
                        );
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
                    self.session
                        .type_catalog
                        .variants
                        .entry(nominal_symbol)
                        .or_default()
                        .insert(
                            name.name_str().into(),
                            name.symbol()
                                .map_err(|_| TypeError::NameNotResolved(name.clone()))?,
                        );
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
                        .insert(lhs.name_str().into(), lhs_sym);

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

            let Symbol::Protocol(protocol_id) = sym else {
                continue;
            };

            // self.register_conformance(
            //     &ty,
            //     nominal_symbol,
            //     sym,
            //     conformance.id,
            //     conformance.span,
            //     context,
            // )?;

            self.constraints.wants_conforms(
                conformance.id,
                ty.clone(),
                protocol_id,
                &context.group_info(),
            );
        }

        let kind = match &decl.kind {
            DeclKind::Struct { .. } => TypedDeclKind::StructDef {
                initializers,
                symbol: nominal_symbol,
                properties: properties.clone(),
                instance_methods,
                typealiases,
            },
            DeclKind::Enum { .. } => TypedDeclKind::EnumDef {
                symbol: nominal_symbol,
                variants: variants.clone(),
                instance_methods,
                typealiases,
            },
            DeclKind::Extend { .. } => TypedDeclKind::Extend {
                symbol: nominal_symbol,
                instance_methods,
                typealiases,
            },
            _ => unreachable!(),
        };

        if !matches!(decl.kind, DeclKind::Extend { .. }) {
            self.session.type_catalog.nominals.insert(
                nominal_symbol,
                Nominal {
                    properties,
                    variants,
                    type_params,
                },
            );

            if let Some((id, level)) = self.nominal_placeholders.remove(&nominal_symbol) {
                self.constraints.wants_equals_at(
                    decl.id,
                    ty.clone(),
                    InferTy::Var { id, level },
                    &context.group_info(),
                );
            }
        }

        Ok(TypedDecl {
            id: decl.id,
            ty,
            kind,
        })
    }

    fn register_conformance(
        &mut self,
        conforming_symbol: Symbol,
        protocol_symbol: Symbol,
        conformance_node_id: NodeID,
        conformance_span: Span,
        context: &mut impl Solve,
    ) -> TypedRet<()> {
        let _s = set_symbol_names(self.session.resolved_names.symbol_names.clone());

        let Symbol::Protocol(protocol_id) = protocol_symbol else {
            tracing::error!("didnt get protocol id for conformance: {protocol_symbol:?}");
            return Err(TypeError::NameNotResolved(Name::Resolved(
                protocol_symbol,
                "".into(),
            )));
        };

        let transitive_conformance_keys = self
            .session
            .type_catalog
            .conformances
            .keys()
            .filter(|c| c.conforming_id == protocol_symbol)
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

            self.register_conformance(conforming_symbol, sym, node_id, span, context)?;
        }

        // Get the protocol's associated type declarations
        // First try ASTs (for locally defined protocols), then type_catalog (for imported protocols)
        let protocol_associated_types = self
            .session
            .resolved_names
            .child_types
            .get(&protocol_symbol)
            .cloned()
            .or_else(|| self.session.lookup_associated_types(protocol_symbol))
            .unwrap_or_default();

        let associated_types =
            protocol_associated_types
                .iter()
                .fold(FxHashMap::default(), |mut acc, (label, _)| {
                    let child_types = self
                        .session
                        .resolved_names
                        .child_types
                        .get(&conforming_symbol)
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
            conforming_id: conforming_symbol,
        };

        let mut conformance = self
            .session
            .type_catalog
            .conformances
            .swap_remove(&key)
            .unwrap_or_else(|| Conformance {
                node_id: conformance_node_id,
                conforming_id: conforming_symbol,
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
            .insert(key, conformance.clone());

        self.constraints.wake_conformances(&[key]);

        Ok(())
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
        // We iterate `fields` in reverse to build a row whose closed order matches the source
        // order, but we still want to evaluate and lower the record fields in source order.
        typed_fields.reverse();

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
            self.constraints.wants_equals_at(
                default_value.id,
                default_ty.ty.clone(),
                ty.clone(),
                &context.group_info(),
            );
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

    #[instrument(level = tracing::Level::TRACE, skip(self, context, _decl))]
    fn visit_init(
        &mut self,
        _decl: &Decl,
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

        let foralls = ty.collect_foralls();
        let ty = substitute(ty, &self.session.skolem_map);
        self.session.insert(sym, ty, &mut self.constraints);

        Ok(TypedFunc {
            name: sym,
            params,
            body: block,
            foralls,
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
            let pattern = self.check_pattern(&arm.pattern, &scrutinee_ty.ty.clone(), context)?;
            let arm_ty = self.infer_block(&arm.body, context)?;

            if let Some(last_arm_ty) = &last_arm_ty {
                self.constraints.wants_equals_at(
                    arm.id,
                    arm_ty.ret.clone(),
                    last_arm_ty.clone(),
                    &context.group_info(),
                );
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
                    self.constraints.wants_equals_at(
                        pattern.id,
                        expected.clone(),
                        existing.clone(),
                        &context.group_info(),
                    );
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

                self.constraints.wants_equals_at(
                    pattern.id,
                    ty.clone(),
                    expected.clone(),
                    &context.group_info(),
                );

                ty
            }
            PatternKind::Record { fields } => {
                let mut row = InferRow::Empty(TypeDefKind::Struct);
                for field in fields {
                    match &field.kind {
                        RecordFieldPatternKind::Bind(name) => {
                            let Ok(sym) = name.symbol() else {
                                self.diagnostics.insert(AnyDiagnostic::Typing(Diagnostic {
                                    id: field.id,
                                    severity: Severity::Error,
                                    kind: TypeError::NameNotResolved(name.clone()),
                                }));
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
                                self.diagnostics.insert(AnyDiagnostic::Typing(Diagnostic {
                                    id: field.id,
                                    severity: Severity::Error,
                                    kind: TypeError::NameNotResolved(name.clone()),
                                }));
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
                self.constraints.wants_equals_at(
                    pattern.id,
                    ty.clone(),
                    expected.clone(),
                    &context.group_info(),
                );

                ty
            }
            // cover any other pattern forms you support
            _ => InferTy::Void,
        }
    }

    fn lookup_or_binder(&self, sym: Symbol) -> Option<InferTy> {
        for binders in self.or_binders.iter().rev() {
            if let Some(ty) = binders.get(&sym) {
                return Some(ty.clone());
            }
        }
        None
    }

    fn prepare_or_binders(
        &mut self,
        pattern_id: NodeID,
        patterns: &[Pattern],
        context: &mut impl Solve,
    ) -> FxHashMap<Symbol, InferTy> {
        let mut sets = vec![];
        for pattern in patterns {
            let mut set = FxHashSet::default();
            for (_, sym) in pattern.collect_binders() {
                set.insert(sym);
            }
            sets.push(set);
        }

        let baseline = sets.first().cloned().unwrap_or_default();
        if sets.iter().skip(1).any(|set| *set != baseline) {
            self.diagnostics.insert(AnyDiagnostic::Typing(Diagnostic {
                id: pattern_id,
                severity: Severity::Error,
                kind: TypeError::OrPatternBinderMismatch,
            }));
        }

        let mut binders = FxHashMap::default();
        for sym in baseline {
            let canonical = self.session.new_ty_meta_var(context.level());
            if let Some(existing) = self.session.lookup(&sym) {
                self.constraints.wants_equals_at(
                    pattern_id,
                    existing._as_ty(),
                    canonical.clone(),
                    &context.group_info(),
                );
            }

            self.session
                .insert_mono(sym, canonical.clone(), &mut self.constraints);
            binders.insert(sym, canonical);
        }

        binders
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context))]
    fn check_pattern(
        &mut self,
        pattern: &Pattern,
        expected: &InferTy,
        context: &mut impl Solve,
    ) -> TypedRet<TypedPattern<InferTy>> {
        let Pattern { kind, .. } = &pattern;

        let typed_kind = match kind {
            PatternKind::Or(patterns) => {
                let binders = self.prepare_or_binders(pattern.id, patterns, context);
                self.or_binders.push(binders);
                let typed_patterns = patterns
                    .iter()
                    .map(|pattern| self.check_pattern(pattern, expected, context))
                    .try_collect();
                self.or_binders.pop();
                TypedPatternKind::Or(typed_patterns?)
            }
            PatternKind::Bind(Name::Raw(name)) => {
                self.constraints.wants_equals_at(
                    pattern.id,
                    expected.clone(),
                    InferTy::Error(TypeError::NameNotResolved(name.clone().into()).into()),
                    &context.group_info(),
                );
                TypedPatternKind::Bind(Symbol::Synthesized(
                    self.session.symbols.next_synthesized(ModuleId::Current),
                ))
            }
            PatternKind::Bind(Name::Resolved(sym, _)) => {
                if let Some(ty) = self.lookup_or_binder(*sym) {
                    self.constraints.wants_equals_at(
                        pattern.id,
                        expected.clone(),
                        ty,
                        &context.group_info(),
                    );
                } else {
                    self.session
                        .insert_mono(*sym, expected.clone(), &mut self.constraints);
                }
                TypedPatternKind::Bind(*sym)
            }
            PatternKind::Bind(Name::SelfType(..)) => TypedPatternKind::Bind(Symbol::Synthesized(
                self.session.symbols.next_synthesized(ModuleId::Current),
            )),
            PatternKind::LiteralInt(val) => {
                self.constraints.wants_equals_at(
                    pattern.id,
                    expected.clone(),
                    InferTy::Int,
                    &context.group_info(),
                );

                TypedPatternKind::LiteralInt(val.clone())
            }
            PatternKind::LiteralFloat(val) => {
                self.constraints.wants_equals_at(
                    pattern.id,
                    expected.clone(),
                    InferTy::Float,
                    &context.group_info(),
                );

                TypedPatternKind::LiteralFloat(val.clone())
            }
            PatternKind::LiteralFalse => {
                self.constraints.wants_equals_at(
                    pattern.id,
                    expected.clone(),
                    InferTy::Bool,
                    &context.group_info(),
                );

                TypedPatternKind::LiteralFalse
            }
            PatternKind::LiteralTrue => {
                self.constraints.wants_equals_at(
                    pattern.id,
                    expected.clone(),
                    InferTy::Bool,
                    &context.group_info(),
                );

                TypedPatternKind::LiteralTrue
            }
            PatternKind::Tuple(patterns) => {
                let metas: Vec<InferTy> = (0..patterns.len())
                    .map(|_| self.session.new_ty_meta_var(context.level()))
                    .collect();

                self.constraints.wants_equals_at(
                    pattern.id,
                    expected.clone(),
                    InferTy::Tuple(metas.clone()),
                    &context.group_info(),
                );

                TypedPatternKind::Tuple(
                    patterns
                        .iter()
                        .zip(metas)
                        .map(|(pi, bi)| self.check_pattern(pi, &bi, context))
                        .try_collect()?,
                )
            }
            PatternKind::Record { fields } => {
                let expected_row = self.ensure_row_record(expected, pattern.id, context);
                let mut typed_fields = vec![];
                for field in fields {
                    match &field.kind {
                        RecordFieldPatternKind::Bind(name) => {
                            let Ok(sym) = name.symbol() else {
                                self.diagnostics.insert(AnyDiagnostic::Typing(Diagnostic {
                                    id: field.id,
                                    severity: Severity::Error,
                                    kind: TypeError::NameNotResolved(name.clone()),
                                }));
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
                                Some(field.id),
                                &context.group_info(),
                            );

                            typed_fields.push(TypedRecordFieldPattern {
                                id: field.id,
                                kind: TypedRecordFieldPatternKind::Bind(sym),
                            });
                        }
                        RecordFieldPatternKind::Equals { name, value, .. } => {
                            // optional: pattern field = subpattern; same RowHas then recurse on value
                            let field_ty = self.session.new_ty_meta_var(context.level());
                            self.constraints._has_field(
                                expected_row.clone(),
                                name.name_str().into(),
                                field_ty.clone(),
                                Some(field.id),
                                &context.group_info(),
                            );

                            typed_fields.push(TypedRecordFieldPattern {
                                id: field.id,
                                kind: TypedRecordFieldPatternKind::Equals {
                                    name: name
                                        .symbol()
                                        .map_err(|_| TypeError::NameNotResolved(name.clone()))?,
                                    value: self.check_pattern(value, &field_ty, context)?,
                                },
                            });
                        }
                        RecordFieldPatternKind::Rest => {
                            typed_fields.push(TypedRecordFieldPattern {
                                id: field.id,
                                kind: TypedRecordFieldPatternKind::Rest,
                            })
                        }
                    }
                }

                TypedPatternKind::Record {
                    fields: typed_fields,
                }
            }
            PatternKind::Variant {
                enum_name,
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
                TypedPatternKind::Variant {
                    enum_name: enum_name
                        .clone()
                        .map(|s| {
                            s.symbol()
                                .map_err(|_| TypeError::NameNotResolved(s.clone()))
                        })
                        .transpose()?,
                    variant_name: variant_name.clone(),
                    fields: fields
                        .iter()
                        .zip(field_metas)
                        .map(|(field_pattern, field_ty)| {
                            self.check_pattern(field_pattern, &field_ty, context)
                        })
                        .try_collect()?,
                }
            }
            PatternKind::Wildcard => TypedPatternKind::Wildcard,
            #[allow(clippy::todo)]
            PatternKind::Struct { .. } => todo!(),
        };

        Ok(TypedPattern {
            id: pattern.id,
            ty: expected.clone(),
            kind: typed_kind,
        })
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
        self.constraints.wants_equals_at(
            cond.id,
            cond_ty.ty.clone(),
            InferTy::Bool,
            &context.group_info(),
        );

        let conseq_ty = self.infer_block(conseq, context)?;
        let alt_ty = self.infer_block(alt, context)?;
        self.constraints.wants_equals_at(
            id,
            conseq_ty.ret.clone(),
            alt_ty.ret.clone(),
            &context.group_info(),
        );

        Ok(TypedExpr {
            id,
            ty: conseq_ty.ret.clone(),
            kind: TypedExprKind::If(cond_ty.into(), conseq_ty, alt_ty),
        })
    }

    // TODO: We should be smarter about whether we've got an if stmt vs an if expr
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
        self.constraints.wants_equals_at(
            cond.id,
            cond_ty.ty.clone(),
            InferTy::Bool,
            &context.group_info(),
        );

        let conseq_ty = self.infer_block(conseq, context)?;

        let (alt_ty, result_ty) = if let Some(alt) = alt {
            let alt_ty = self.infer_block(alt, context)?;
            self.constraints.wants_equals_at(
                id,
                conseq_ty.ret.clone(),
                alt_ty.ret.clone(),
                &context.group_info(),
            );
            (alt_ty, conseq_ty.ret.clone())
        } else {
            (
                TypedBlock {
                    id: NodeID(id.0, self.asts[id.0.0 as usize].node_ids.next_id()),
                    body: vec![],
                    ret: InferTy::Void,
                },
                InferTy::Void,
            )
        };

        Ok(TypedStmt {
            id,
            ty: result_ty.clone(),
            kind: TypedStmtKind::Expr(TypedExpr {
                id,
                ty: result_ty,
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
        self.verify_returns(tok, block.ret.clone(), context);
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
        let type_arg_tys: Vec<_> = type_args
            .iter()
            .map(|a| self.visit_type_annotation(a, context))
            .try_collect()?;

        let receiver = match &callee.kind {
            ExprKind::Member(Some(rcv), ..) => {
                if let ExprKind::Constructor(Name::Resolved(Symbol::Protocol(protocol_id), ..)) =
                    &rcv.kind
                    && let Some(first_arg) = arg_tys.first()
                {
                    self.constraints.wants_conforms(
                        rcv.id,
                        first_arg.ty.clone(),
                        *protocol_id,
                        &context.group_info(),
                    );
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
        for ((type_arg, type_arg_ty), instantiated) in type_args
            .iter()
            .zip(type_arg_tys.iter())
            .zip(instantiations.ty_mappings(&callee.id).values())
        {
            self.constraints.wants_equals_at(
                type_arg.id,
                type_arg_ty.clone(),
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
                &context.group_info(),
            );
        }

        // if matches!(callee_ty, InferTy::Constructor { .. }) {
        //     arg_tys.insert(0, ret.clone());
        // }

        self.constraints.wants_call(
            id,
            callee.id,
            callee_ty.ty.clone(),
            arg_tys.iter().map(|a| a.ty.clone()).collect_vec(),
            type_arg_tys.clone(),
            ret.clone(),
            receiver.map(|r| r.ty.clone()),
            &context.group_info(),
        );

        Ok(TypedExpr {
            id,
            ty: ret,
            kind: TypedExprKind::Call {
                callee: callee_ty.into(),
                type_args: type_arg_tys,
                args: arg_tys,
                resolved: None,
            },
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context, func), fields(func.name = ?func.name))]
    fn visit_func(
        &mut self,
        func: &Func,
        context: &mut impl Solve,
    ) -> TypedRet<TypedFunc<InferTy>> {
        let func_sym = func
            .name
            .symbol()
            .map_err(|_| TypeError::NameNotResolved(func.name.clone()))?;

        for generic in func.generics.iter() {
            self.register_generic(generic, context);
        }

        let params = self.visit_params(&func.params, context)?;

        let mut foralls = IndexSet::default();

        let body = if let Some(ret) = &func.ret {
            let ret = self.visit_type_annotation(ret, context)?;
            self.check_block(&func.body, ret.clone(), &mut context.next())?
        } else {
            self.infer_block_with_returns(&func.body, &mut context.next())?
        };

        foralls.extend(body.ret.collect_foralls());

        let params = params
            .iter()
            .map(|t| {
                let ty = substitute(t.ty.clone(), &self.session.skolem_map);
                foralls.extend(ty.collect_foralls());
                TypedParameter { name: t.name, ty }
            })
            .collect_vec();

        let ret = substitute(body.ret.clone(), &self.session.skolem_map);

        self.session.insert(
            func_sym,
            curry(params.iter().map(|t| t.ty.clone()), ret.clone()),
            &mut Default::default(),
        );

        Ok(TypedFunc {
            name: func_sym,
            params,
            foralls,
            body,
            ret,
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
                self.constraints.wants_equals_at(
                    type_annotation.id,
                    existing,
                    annotation_ty.clone(),
                    &context.group_info(),
                );
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
        self.verify_returns(tok, ret.ret.clone(), context);
        self.constraints.wants_equals_at(
            block.id,
            ret.ret.clone(),
            expected,
            &context.group_info(),
        );
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
                self.diagnostics.insert(AnyDiagnostic::Typing(Diagnostic {
                    id: param.id,
                    severity: Severity::Error,
                    kind: TypeError::NameNotResolved(param.name.clone()),
                }));
                continue;
            };

            self.session
                .insert_mono(sym, expected_param_ty, &mut self.constraints);
        }

        if let Some(ret) = ret {
            let ret_ty = self.visit_type_annotation(ret, context)?;
            self.constraints.wants_equals_at(
                ret.id,
                ret_ty,
                expected_ret.clone(),
                &context.group_info(),
            );
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
                    self.diagnostics.insert(AnyDiagnostic::Typing(Diagnostic {
                        id: type_annotation.id,
                        severity: Severity::Error,
                        kind: TypeError::NameNotResolved(name.clone()),
                    }));
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
        let (ty, initializer) = match (&type_annotation, &rhs) {
            (None, Some(expr)) => {
                let expr = self.visit_expr(expr, context)?;
                (expr.ty.clone(), Some(expr))
            }
            (Some(annotation), None) => (self.visit_type_annotation(annotation, context)?, None),
            (Some(annotation), Some(rhs)) => {
                let annotated_ty = self.visit_type_annotation(annotation, context)?;
                let rhs_ty = self.visit_expr(rhs, context)?;
                self.constraints.wants_equals_at(
                    rhs.id,
                    annotated_ty.clone(),
                    rhs_ty.ty.clone(),
                    &context.group_info(),
                );
                (annotated_ty, Some(rhs_ty))
            }
            (None, None) => (self.session.new_ty_meta_var(context.level().next()), None),
        };

        let typed_pattern = self.check_pattern(lhs, &ty, context)?;

        Ok(TypedDecl {
            id,
            ty: ty.clone(),
            kind: TypedDeclKind::Let {
                pattern: typed_pattern,
                initializer,
                ty,
            },
        })
    }

    fn tracking_returns(&mut self) -> ReturnToken {
        self.tracked_returns.push(Default::default());
        ReturnToken {}
    }

    fn verify_returns(&mut self, _tok: ReturnToken, ret: InferTy, context: &mut impl Solve) {
        for tracked_ret in self.tracked_returns.pop().unwrap_or_else(|| unreachable!()) {
            self.constraints.wants_equals_at(
                tracked_ret.0,
                tracked_ret.1,
                ret.clone(),
                &context.group_info(),
            );
        }
    }

    fn ensure_row_record(
        &mut self,
        expected: &InferTy,
        node_id: NodeID,
        context: &mut impl Solve,
    ) -> InferRow {
        match expected {
            InferTy::Record(box row) => row.clone(),
            _ => {
                let row = self.session.new_row_meta_var(context.level());
                self.constraints.wants_equals_at(
                    node_id,
                    expected.clone(),
                    InferTy::Record(Box::new(row.clone())),
                    &context.group_info(),
                );
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
            self.diagnostics.insert(AnyDiagnostic::Typing(Diagnostic {
                id: generic.id,
                severity: Severity::Error,
                kind: TypeError::NameNotResolved(generic.name.clone()),
            }));
            return 0.into();
        };

        self.session
            .insert_mono(sym, InferTy::Param(param_id), &mut self.constraints);

        param_id
    }
}
