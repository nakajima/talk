use indexmap::IndexSet;
use itertools::Itertools;
use rustc_hash::FxHashMap;
use tracing::instrument;

use crate::{
    ast::AST,
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
    types::{
        builtins::resolve_builtin_type,
        constraint_solver::ConstraintSolver,
        constraints::{constraint::ConstraintCause, member::consume_self},
        infer_row::{InferRow, RowMetaId},
        infer_ty::{InferTy, Level, Meta, MetaVarId, TypeParamId},
        predicate::Predicate,
        scheme::{ForAll, Scheme},
        term_environment::EnvEntry,
        type_catalog::{Conformance, ConformanceKey},
        type_operations::{
            InstantiationSubstitutions, UnificationSubstitutions, apply, curry, substitute,
        },
        type_session::{TypeDefKind, TypeSession},
        wants::Wants,
    },
};

#[derive(Debug, Clone, PartialEq)]
pub struct Protocol {
    name: Name,
    method_requirements: FxHashMap<Label, Symbol>,
}

impl Protocol {
    pub fn new(name: Name) -> Self {
        Self {
            name,
            method_requirements: Default::default(),
        }
    }
}

pub struct InferencePass<'a> {
    ast: &'a mut AST<NameResolved>,
    session: &'a mut TypeSession,
    wants: Wants,
    givens: IndexSet<Predicate<InferTy>>,
    canonical_rows: FxHashMap<Symbol, RowMetaId>,
    #[allow(clippy::type_complexity)]
    pending_type_instances: FxHashMap<Symbol, Vec<(MetaVarId, Vec<(InferTy, NodeID)>)>>,
    instantiations: FxHashMap<NodeID, InstantiationSubstitutions>,
    substitutions: UnificationSubstitutions,
}

impl<'a> InferencePass<'a> {
    pub fn drive(asts: &'a mut [AST<NameResolved>], session: &'a mut TypeSession) -> Wants {
        let result = Wants::default();
        let mut substitutions = UnificationSubstitutions::new(session.meta_levels.clone());

        for ast in asts.iter_mut() {
            let mut pass = InferencePass {
                ast,
                wants: Default::default(),
                givens: Default::default(),
                session,
                canonical_rows: Default::default(),
                instantiations: Default::default(),
                substitutions: UnificationSubstitutions::new(Default::default()),
                pending_type_instances: Default::default(),
            };

            let roots = std::mem::take(&mut pass.ast.roots);
            pass.discover_protocols(&roots, Level::default());
            _ = std::mem::replace(&mut pass.ast.roots, roots);

            pass.generate();
            pass.check_conformances();

            substitutions.extend(&pass.substitutions);
        }

        session.apply(&mut substitutions);

        result
    }

    #[instrument(skip(self))]
    fn check_conformances(&mut self) {
        let mut wants = Wants::default();
        println!(
            "CHECKING CONFORMANCES: {:?}",
            self.session.type_catalog.conformances
        );
        for (key, conformance) in self.session.type_catalog.conformances.clone().iter() {
            let requirements = self
                .session
                .type_catalog
                .method_requirements
                .get(&key.protocol_id.into())
                .unwrap();

            for (label, sym) in requirements.clone() {
                tracing::trace!("checking req {label:?} {sym:?}");
                let requirement_entry = self.session.lookup(&sym).unwrap();
                let witness_entry_sym = self
                    .session
                    .type_catalog
                    .instance_methods
                    .get(&key.conforming_id)
                    .unwrap()
                    .get(&label)
                    .copied()
                    .unwrap();
                let witness_entry = self.session.lookup(&witness_entry_sym).unwrap();
                let requirement_ty = requirement_entry
                    .instantiate(
                        NodeID::SYNTHESIZED,
                        self.session,
                        Level::default(),
                        &mut wants,
                        conformance.span,
                    )
                    .0;
                let witness_ty_with_self = witness_entry
                    .instantiate(
                        NodeID::SYNTHESIZED,
                        self.session,
                        Level::default(),
                        &mut wants,
                        conformance.span,
                    )
                    .0;

                let witness_ty = consume_self(&witness_ty_with_self).1;

                wants.equals(
                    requirement_ty,
                    witness_ty,
                    ConstraintCause::Internal,
                    conformance.span,
                );
            }
        }

        let solver = ConstraintSolver::new(
            wants,
            &self.givens,
            Level::default(),
            self.session,
            self.ast,
        );

        solver.solve();
    }

    fn discover_protocols(&mut self, roots: &[Node], level: Level) {
        for root in roots.iter() {
            let Node::Decl(Decl {
                kind:
                    DeclKind::Protocol {
                        name: name @ Name::Resolved(Symbol::Protocol(protocol_id), ..),
                        body,
                        ..
                    },
                ..
            }) = root
            else {
                continue;
            };

            let protocol = Protocol::new(name.clone());
            let protocol_self_id = self.session.new_type_param_id(None);
            self.givens.insert(Predicate::Conforms {
                param: protocol_self_id,
                protocol_id: *protocol_id,
                span: root.span(),
            });
            self.session
                .insert(name.symbol(), InferTy::Param(protocol_self_id));

            for decl in body.decls.iter() {
                match &decl.kind {
                    DeclKind::MethodRequirement(func_signature)
                    | DeclKind::FuncSignature(func_signature) => {
                        self.visit_func_signature(
                            protocol_self_id,
                            *protocol_id,
                            func_signature,
                            level,
                        );
                        self.session
                            .type_catalog
                            .method_requirements
                            .entry(protocol.name.symbol())
                            .or_default()
                            .insert(
                                func_signature.name.name_str().into(),
                                func_signature.name.symbol(),
                            );
                    }

                    DeclKind::Method { func, is_static } => {
                        self.visit_method(protocol.name.symbol(), func, *is_static, level);
                    }
                    _ => (),
                }
            }
        }
    }

    fn generate(&mut self) {
        for group in self.ast.phase.scc_graph.groups() {
            self.generate_for_group(group);
        }

        for id in self.ast.phase.unbound_nodes.clone() {
            let node = self.ast.find(id).unwrap();
            self.visit_node(&node, Level::default());
        }

        let wants = std::mem::take(&mut self.wants);
        let solver = ConstraintSolver::new(
            wants,
            &self.givens,
            Level::default(),
            self.session,
            self.ast,
        );
        let (mut substitutions, _unsolved) = solver.solve();
        self.substitutions.extend(&substitutions);

        // Apply substitutions to types_by_node for top-level expressions
        self.session.apply(&mut substitutions);
    }

    #[instrument(skip(self))]
    fn generate_for_group(&mut self, group: BindingGroup) {
        // Create placeholders
        let placeholders = group
            .binders
            .iter()
            .map(|sym| {
                let placeholder = self.session.new_ty_meta_var(group.level);
                tracing::trace!("placeholder {sym:?} = {placeholder:?}");
                self.session.insert_term(*sym, placeholder.to_entry());
                placeholder
            })
            .collect_vec();

        // Visit each binder
        for (i, binder) in group.binders.iter().enumerate() {
            if let Some(captures) = self.ast.phase.captures.get(binder) {
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

            let rhs_id = self.ast.phase.scc_graph.rhs_id_for(binder);
            let rhs = self.ast.find(*rhs_id).unwrap();
            let ty = self.visit_node(&rhs, group.level);
            self.wants.equals(
                ty,
                placeholders[i].clone(),
                ConstraintCause::Internal,
                rhs.span(),
            );
        }

        // Solve this group
        let wants = std::mem::take(&mut self.wants);
        let solver =
            ConstraintSolver::new(wants, &self.givens, group.level, self.session, self.ast);
        let (mut substitutions, unsolved) = solver.solve();

        // Generalize
        for (i, binder) in group.binders.iter().enumerate() {
            let ty = apply(placeholders[i].clone(), &mut substitutions);
            let entry = self.session.generalize(group.level, ty, &unsolved);
            self.session.promote(*binder, entry);
        }

        self.session.apply(&mut substitutions);
    }

    fn visit_node(&mut self, node: &Node, level: Level) -> InferTy {
        match &node {
            Node::Decl(decl) => self.visit_decl(decl, level),
            Node::Stmt(stmt) => self.visit_stmt(stmt, level),
            Node::Expr(expr) => self.visit_expr(expr, level),
            Node::Parameter(param) => self.visit_param(param, level),
            _ => todo!("{node:?}"),
        }
    }

    fn visit_decl(&mut self, decl: &Decl, level: Level) -> InferTy {
        match &decl.kind {
            DeclKind::Let {
                lhs,
                type_annotation,
                rhs,
            } => self.visit_let(lhs, type_annotation, rhs, level),
            DeclKind::Struct {
                name,
                generics,
                conformances,
                body,
                ..
            } => self.visit_nominal(name, generics, conformances, body, level),
            DeclKind::Protocol { .. } => InferTy::Void,
            DeclKind::Init { .. } => {
                unreachable!("inits are handled by visit_struct")
            }
            DeclKind::Property { .. } => todo!(),
            DeclKind::Method { .. } => todo!(),
            DeclKind::Associated { .. } => todo!(),
            DeclKind::Func(..) => todo!(),
            DeclKind::Extend {
                name,
                conformances,
                generics,
                body,
                ..
            } => self.visit_extend(name, conformances, generics, body, level),
            DeclKind::Enum {
                name,
                generics,
                conformances,
                body,
                ..
            } => self.visit_nominal(name, generics, conformances, body, level),
            DeclKind::EnumVariant(..) => todo!(),
            DeclKind::FuncSignature(..) => todo!(),
            DeclKind::MethodRequirement(..) => todo!(),
            DeclKind::TypeAlias(..) => {
                todo!()
            }
            _ => InferTy::Void,
        }
    }

    fn visit_stmt(&mut self, stmt: &Stmt, level: Level) -> InferTy {
        let ty = match &stmt.kind {
            StmtKind::Expr(expr) => self.visit_expr(expr, level),
            StmtKind::If(cond, conseq, alt) => self.visit_if_stmt(cond, conseq, alt, level),
            StmtKind::Assignment(lhs, rhs) => {
                let lhs_ty = self.visit_expr(lhs, level);
                let rhs_ty = self.visit_expr(rhs, level);
                self.wants.equals(
                    lhs_ty,
                    rhs_ty,
                    ConstraintCause::Assignment(stmt.id),
                    stmt.span,
                );
                InferTy::Void
            }
            StmtKind::Return(_expr) => todo!(),
            StmtKind::Break => todo!(),
            StmtKind::Loop(cond, block) => {
                if let Some(cond) = cond {
                    let cond_ty = self.visit_expr(cond, level);
                    self.wants.equals(
                        cond_ty,
                        InferTy::Bool,
                        ConstraintCause::Condition(cond.id),
                        cond.span,
                    );
                }

                self.infer_block(block, level);

                InferTy::Void
            }
        };

        self.session.types_by_node.insert(stmt.id, ty.clone());

        ty
    }

    fn visit_expr(&mut self, expr: &Expr, level: Level) -> InferTy {
        let ty = match &expr.kind {
            ExprKind::LiteralArray(..) => todo!(),
            ExprKind::LiteralInt(_) => InferTy::Int,
            ExprKind::LiteralFloat(_) => InferTy::Float,
            ExprKind::LiteralTrue | ExprKind::LiteralFalse => InferTy::Bool,
            ExprKind::LiteralString(_) => todo!(),
            ExprKind::Unary(..) => todo!(),
            ExprKind::Binary(..) => todo!(),
            ExprKind::Tuple(exprs) => InferTy::Tuple(
                exprs
                    .iter()
                    .map(|e| self.visit_expr(e, level))
                    .collect_vec(),
            ),
            ExprKind::Block(..) => todo!(),
            ExprKind::Call {
                callee,
                type_args,
                args,
            } => self.visit_call(callee, type_args, args, level),
            ExprKind::Member(receiver, label, ..) => {
                self.visit_member(expr, receiver, label, level)
            }
            ExprKind::Func(func) => self.visit_func(func, level),
            ExprKind::Variable(name) => self.visit_variable(expr, name, level),
            ExprKind::Constructor(name) => self.visit_constructor(expr, name, level),
            ExprKind::If(cond, conseq, alt) => self.infer_if_expr(cond, conseq, alt, level),
            ExprKind::Match(scrutinee, arms) => self.infer_match(scrutinee, arms, level),
            ExprKind::RecordLiteral { fields, spread } => {
                self.infer_record_literal(fields, spread, level)
            }
            ExprKind::RowVariable(..) => todo!(),
            _ => unimplemented!(),
        };

        self.session.types_by_node.insert(expr.id, ty.clone());

        ty
    }

    fn visit_func_signature(
        &mut self,
        protocol_self_id: TypeParamId,
        protocol_id: ProtocolId,
        func_signature: &FuncSignature,
        _level: Level,
    ) -> InferTy {
        for generic in func_signature.generics.iter() {
            let param_id = self.session.new_type_param_id(None);
            self.session
                .insert_mono(generic.name.symbol(), InferTy::Param(param_id));
        }
        let params = self.visit_params(&func_signature.params, Level::default());
        let ret = if let Some(ret) = &func_signature.ret {
            self.visit_type_annotation(ret, Level::default())
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

    fn visit_constructor(&mut self, _expr: &Expr, name: &Name, _level: Level) -> InferTy {
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
        level: Level,
    ) -> InferTy {
        let Some(receiver) = receiver else { todo!() };

        let receiver_ty = self.visit_expr(receiver, level);
        let ret = self.session.new_ty_meta_var(level);
        self.wants.member(
            expr.id,
            receiver_ty,
            label.clone(),
            ret.clone(),
            ConstraintCause::Member(expr.id),
            expr.span,
        );

        ret
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, generics, conformances, body))]
    fn visit_nominal(
        &mut self,
        name: &Name,
        generics: &[GenericDecl],
        conformances: &[TypeAnnotation],
        body: &Body,
        level: Level,
    ) -> InferTy {
        for generic in generics.iter() {
            let param_id = self.session.new_type_param_id(None);
            self.session
                .insert_mono(generic.name.symbol(), InferTy::Param(param_id));
        }

        let nominal_symbol = name.symbol();
        let row_placeholder_id = self.canonical_row_for(&nominal_symbol, level);
        let row_placeholder = InferRow::Var(row_placeholder_id);
        let ty = InferTy::Nominal {
            symbol: name.symbol(),
            row: row_placeholder.clone().into(),
        };

        let mut row_types = vec![];

        for decl in body.decls.iter() {
            match &decl.kind {
                DeclKind::Init { name, params, body } => {
                    self.visit_init(ty.clone(), name, params, body, level.next());
                }
                DeclKind::Method { func, is_static } => {
                    self.visit_method(nominal_symbol, func, *is_static, level.next());
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
                        .map(|v| self.visit_type_annotation(v, level))
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
                            level.next(),
                        ),
                    ));
                }
                _ => todo!("{:?}", decl.kind),
            }
        }

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

        // NOTE: This is sort of a hack since we don't have a direct way to say
        // that rows should be equal.
        self.wants.equals(
            InferTy::Record(row_placeholder.into()),
            InferTy::Record(real_row.clone().into()),
            ConstraintCause::Internal,
            body.span,
        );

        // Replace all instances of the placeholder row
        let mut substitutions = UnificationSubstitutions::new(self.session.meta_levels.clone());
        substitutions
            .row
            .insert(row_placeholder_id, real_row.clone());

        self.session.apply(&mut substitutions);
        self.wants.apply(&mut substitutions);

        let ty = InferTy::Nominal {
            symbol: nominal_symbol,
            row: real_row.into(),
        };

        for conformance in conformances {
            let Symbol::Protocol(protocol_id) = conformance.symbol() else {
                tracing::warn!("didnt get protocol id for conformance: {conformance:?}");
                continue;
            };

            self.session.type_catalog.conformances.insert(
                ConformanceKey {
                    protocol_id,
                    conforming_id: nominal_symbol,
                },
                Conformance {
                    conforming_id: nominal_symbol,
                    protocol_id,
                    requirements: Default::default(),
                    associated_types: Default::default(),
                    span: conformance.span,
                },
            );
            self.wants
                .conforms(ty.clone(), protocol_id, conformance.span);
        }

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

        ty
    }

    fn visit_extend(
        &mut self,
        name: &Name,
        conformances: &[TypeAnnotation],
        generics: &[GenericDecl],
        body: &Body,
        level: Level,
    ) -> InferTy {
        for generic in generics.iter() {
            let param_id = self.session.new_type_param_id(None);
            self.session
                .insert_mono(generic.name.symbol(), InferTy::Param(param_id));
        }

        let nominal_symbol = name.symbol();
        let row_placeholder_id = self.canonical_row_for(&nominal_symbol, level);
        let row_placeholder = InferRow::Var(row_placeholder_id);
        let ty = InferTy::Nominal {
            symbol: name.symbol(),
            row: row_placeholder.clone().into(),
        };

        let mut row_types = vec![];

        for decl in body.decls.iter() {
            match &decl.kind {
                DeclKind::Init { name, params, body } => {
                    self.visit_init(ty.clone(), name, params, body, level.next());
                }
                DeclKind::Method { func, is_static } => {
                    self.visit_method(nominal_symbol, func, *is_static, level.next());
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
                        .map(|v| self.visit_type_annotation(v, level))
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
                            level.next(),
                        ),
                    ));
                }
                _ => todo!("{:?}", decl.kind),
            }
        }

        for conformance in conformances {
            let Symbol::Protocol(protocol_id) = conformance.symbol() else {
                unreachable!("didnt get protocol id for conformance: {conformance:?}");
            };

            self.session.type_catalog.conformances.insert(
                ConformanceKey {
                    protocol_id,
                    conforming_id: nominal_symbol,
                },
                Conformance {
                    conforming_id: nominal_symbol,
                    protocol_id,
                    requirements: Default::default(),
                    associated_types: Default::default(),
                    span: conformance.span,
                },
            );
            self.wants
                .conforms(ty.clone(), protocol_id, conformance.span);
        }

        ty
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn infer_record_literal(
        &mut self,
        fields: &[RecordField],
        spread: &Option<Box<Expr>>,
        level: Level,
    ) -> InferTy {
        let mut row = InferRow::Empty(TypeDefKind::Struct);
        for field in fields.iter().rev() {
            row = InferRow::Extend {
                row: Box::new(row),
                label: field.label.name_str().into(),
                ty: self.visit_expr(&field.value, level),
            };
        }

        InferTy::Record(Box::new(row))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn visit_method(
        &mut self,
        owner_symbol: Symbol,
        func: &Func,
        is_static: bool,
        level: Level,
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

        let func_ty = self.visit_func(func, level);
        self.session.insert(func.name.symbol(), func_ty.clone());

        func_ty
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn visit_property(
        &mut self,
        struct_symbol: Symbol,
        name: &Name,
        is_static: bool,
        type_annotation: &Option<TypeAnnotation>,
        default_value: &Option<Expr>,
        level: Level,
    ) -> InferTy {
        if default_value.is_some() {
            todo!()
        }

        self.session
            .type_catalog
            .properties
            .entry(struct_symbol)
            .or_default()
            .insert(name.name_str().into(), name.symbol());

        let ty = if let Some(anno) = type_annotation {
            self.visit_type_annotation(anno, level)
        } else {
            self.session.new_type_param(None)
        };

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
                .instance_methods
                .entry(struct_symbol)
                .or_default()
                .insert(name.name_str().into(), name.symbol());
        }

        ty
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, ))]
    fn visit_init(
        &mut self,
        struct_ty: InferTy,
        name: &Name,
        params: &[Parameter],
        body: &Block,
        level: Level,
    ) -> InferTy {
        let param_tys = self.visit_params(params, level);

        // Init blocks always return self
        _ = self.infer_block(body, level);

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

    #[instrument(level = tracing::Level::TRACE, skip(self, scrutinee, arms))]
    fn infer_match(&mut self, scrutinee: &Expr, arms: &[MatchArm], level: Level) -> InferTy {
        let mut last_arm_ty: Option<InferTy> = None;
        let scrutinee_ty = self.visit_expr(scrutinee, level);

        for arm in arms {
            self.check_pattern(&arm.pattern, &scrutinee_ty, level);
            let arm_ty = self.infer_block(&arm.body, level);

            if let Some(last_arm_ty) = &last_arm_ty {
                self.wants.equals(
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
    fn check_pattern(&mut self, pattern: &Pattern, expected: &InferTy, level: Level) {
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
                self.wants.equals(
                    expected.clone(),
                    InferTy::Int,
                    ConstraintCause::Pattern(pattern.id),
                    pattern.span,
                );
            }
            PatternKind::LiteralFloat(_) => {
                self.wants.equals(
                    expected.clone(),
                    InferTy::Float,
                    ConstraintCause::Pattern(pattern.id),
                    pattern.span,
                );
            }
            PatternKind::LiteralFalse | PatternKind::LiteralTrue => {
                self.wants.equals(
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

                self.wants.equals(
                    expected.clone(),
                    InferTy::Tuple(metas.clone()),
                    ConstraintCause::Pattern(pattern.id),
                    pattern.span,
                );

                for (pi, bi) in patterns.iter().zip(metas) {
                    self.check_pattern(pi, &bi, level);
                }
            }
            PatternKind::Record { fields } => {
                let expected_row =
                    self.ensure_row_record(pattern.id, pattern.span, expected, level);
                for field in fields {
                    match &field.kind {
                        RecordFieldPatternKind::Bind(name) => {
                            // fresh meta for the field type
                            let field_ty = self.session.new_ty_meta_var(level);

                            // bind the pattern name
                            self.session.insert_mono(name.symbol(), field_ty.clone());

                            // ONE RowHas per field, all referring to the same row
                            self.wants._has_field(
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
                            self.wants._has_field(
                                expected_row.clone(),
                                name.name_str().into(),
                                field_ty.clone(),
                                ConstraintCause::Pattern(field.id),
                                pattern.span,
                            );
                            self.check_pattern(value, &field_ty, level);
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

                self.wants.member(
                    pattern.id,
                    expected.clone(),
                    variant_name.into(),
                    payload,
                    ConstraintCause::Pattern(pattern.id),
                    pattern.span,
                );

                // Recursively check each field pattern
                for (field_pattern, field_ty) in fields.iter().zip(field_metas) {
                    self.check_pattern(field_pattern, &field_ty, level);
                }
            }
            PatternKind::Wildcard => (),
            PatternKind::Struct { .. } => todo!(),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, cond, conseq, alt))]
    fn infer_if_expr(&mut self, cond: &Expr, conseq: &Block, alt: &Block, level: Level) -> InferTy {
        let cond_ty = self.visit_expr(cond, level);
        self.wants.equals(
            cond_ty,
            InferTy::Bool,
            ConstraintCause::Condition(cond.id),
            cond.span,
        );

        let conseq_ty = self.infer_block(conseq, level);
        let alt_ty = self.infer_block(alt, level);
        self.wants.equals(
            conseq_ty.clone(),
            alt_ty,
            ConstraintCause::Internal,
            alt.span,
        );

        conseq_ty
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, cond, conseq, alt))]
    fn visit_if_stmt(
        &mut self,
        cond: &Expr,
        conseq: &Block,
        alt: &Option<Block>,
        level: Level,
    ) -> InferTy {
        let cond_ty = self.visit_expr(cond, level);
        self.wants.equals(
            cond_ty,
            InferTy::Bool,
            ConstraintCause::Condition(cond.id),
            cond.span,
        );

        let conseq_ty = self.infer_block(conseq, level);

        if let Some(alt) = alt {
            let alt_ty = self.infer_block(alt, level);
            self.wants.equals(
                conseq_ty.clone(),
                alt_ty,
                ConstraintCause::Internal,
                alt.span,
            );
        }

        conseq_ty
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, block))]
    fn infer_block(&mut self, block: &Block, level: Level) -> InferTy {
        let mut ret = InferTy::Void;
        for node in block.body.iter() {
            ret = self.visit_node(node, level);
        }
        ret
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, expr))]
    fn visit_variable(&mut self, expr: &Expr, name: &Name, level: Level) -> InferTy {
        let (ty, substitutions) = self.session.lookup(&name.symbol()).unwrap().instantiate(
            expr.id,
            self.session,
            level,
            &mut self.wants,
            expr.span,
        );

        self.instantiations.insert(expr.id, substitutions);

        ty
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn visit_call(
        &mut self,
        callee: &Expr,
        type_args: &[TypeAnnotation],
        args: &[CallArg],
        level: Level,
    ) -> InferTy {
        let arg_tys = args
            .iter()
            .map(|a| self.visit_expr(&a.value, level))
            .collect_vec();
        let type_args = type_args
            .iter()
            .map(|a| self.visit_type_annotation(a, level))
            .collect_vec();
        let callee_ty = self.visit_expr(callee, level);
        let ret = self.session.new_ty_meta_var(level);
        let instantiations = self
            .instantiations
            .get(&callee.id)
            .cloned()
            .unwrap_or_default();
        for (type_arg, instantiated) in type_args.iter().zip(instantiations.ty.values()) {
            self.wants.equals(
                type_arg.clone(),
                InferTy::Var {
                    id: *instantiated,
                    level: *self
                        .session
                        .meta_levels
                        .borrow()
                        .get(&Meta::Ty(*instantiated))
                        .unwrap(),
                },
                ConstraintCause::Internal,
                callee.span,
            );
        }

        // if matches!(callee_ty, InferTy::Constructor { .. }) {
        //     arg_tys.insert(0, ret.clone());
        // }

        self.wants.call(
            callee.id,
            callee_ty,
            arg_tys,
            type_args,
            ret.clone(),
            None,
            level,
            ConstraintCause::Call(callee.id),
            callee.span,
        );
        ret
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn visit_func(&mut self, func: &Func, level: Level) -> InferTy {
        for generic in func.generics.iter() {
            let param_id = self.session.new_type_param_id(None);

            for conformance in generic.conformances.iter() {
                let Symbol::Protocol(protocol_id) = conformance.symbol() else {
                    tracing::warn!("could not determine conformance: {conformance:?}");
                    continue;
                };
                self.givens.insert(Predicate::Conforms {
                    param: param_id,
                    protocol_id,
                    span: conformance.span,
                });
            }

            let skolem = self.session.new_skolem(param_id);
            self.session.insert_mono(generic.name.symbol(), skolem);
        }

        let mut params = self.visit_params(&func.params, level);

        let ret = if let Some(ret) = &func.ret {
            self.visit_type_annotation(ret, level)
        } else {
            self.session.new_ty_meta_var(level)
        };

        self.check_block(&func.body, ret.clone(), level);

        if params.is_empty() {
            // Otherwise curry gets confused. TODO: just fix curry?
            params.push(InferTy::Void);
        }

        let func_ty = curry(params, ret);
        substitute(func_ty, &self.session.skolem_map) // Deskolemize
    }

    fn visit_params(&mut self, params: &[Parameter], level: Level) -> Vec<InferTy> {
        params
            .iter()
            .map(|param| self.visit_param(param, level))
            .collect_vec()
    }

    fn visit_param(&mut self, param: &Parameter, level: Level) -> InferTy {
        if let Some(existing) = self.session.lookup(&param.name.symbol()) {
            return existing._as_ty();
        }

        let ty = if let Some(type_annotation) = &param.type_annotation {
            self.visit_type_annotation(type_annotation, level)
        } else {
            self.session.new_ty_meta_var(level)
        };

        self.session
            .insert_term(param.name.symbol(), ty.clone().to_entry());

        ty
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, block))]
    fn check_block(&mut self, block: &Block, expected: InferTy, level: Level) {
        let mut ret = InferTy::Void;
        for node in &block.body {
            ret = self.visit_node(node, level);
        }
        self.wants
            .equals(ret, expected, ConstraintCause::Internal, block.span);
    }

    // Checks
    #[allow(clippy::too_many_arguments)]
    #[allow(dead_code)]
    #[instrument(skip(self, body))]
    fn check_func(
        &mut self,
        params: &[Parameter],
        ret: &Option<TypeAnnotation>,
        body: &Block,
        expected_params: Vec<InferTy>,
        expected_ret: InferTy,
        level: Level,
    ) {
        for (param, expected_param_ty) in params.iter().zip(expected_params) {
            self.session
                .insert_mono(param.name.symbol(), expected_param_ty);
        }

        if let Some(ret) = ret {
            let ret_ty = self.visit_type_annotation(ret, level);
            self.wants.equals(
                ret_ty,
                expected_ret.clone(),
                ConstraintCause::Annotation(ret.id),
                ret.span,
            );
        }

        self.check_block(body, expected_ret.clone(), level);
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn visit_type_annotation(&mut self, type_annotation: &TypeAnnotation, level: Level) -> InferTy {
        match &type_annotation.kind {
            TypeAnnotationKind::Nominal { name, generics, .. } => {
                if matches!(name.symbol(), Symbol::Builtin(..)) {
                    return resolve_builtin_type(&name.symbol()).0;
                }

                let generic_args = generics
                    .iter()
                    .map(|g| (self.visit_type_annotation(g, level), g.id))
                    .collect_vec();

                // Do we know about this already? Cool.
                if let Some(entry) = self.session.lookup(&name.symbol()) {
                    let (ty, subsitutions) = entry.instantiate_with_args(
                        type_annotation.id,
                        &generic_args,
                        self.session,
                        level,
                        &mut self.wants,
                        type_annotation.span,
                    );

                    self.instantiations.insert(type_annotation.id, subsitutions);

                    return ty;
                } else {
                    tracing::info!("nope, did not find anything in the env for {name:?}");
                }

                if matches!(name.symbol(), Symbol::TypeParameter(..)) {
                    return self.session.lookup(&name.symbol()).unwrap()._as_ty();
                }

                // We don't know about this type yet, wait until we visit it
                let var_id = self.session.new_ty_meta_var_id(level);
                self.pending_type_instances
                    .entry(name.symbol())
                    .or_default()
                    .push((var_id, generic_args));

                InferTy::Var { id: var_id, level }
            }
            TypeAnnotationKind::SelfType(name) => {
                if matches!(name.symbol(), Symbol::Builtin(..)) {
                    return resolve_builtin_type(&name.symbol()).0;
                }

                let (ty, subsitutions) = self.session.lookup(&name.symbol()).unwrap().instantiate(
                    type_annotation.id,
                    self.session,
                    level,
                    &mut self.wants,
                    type_annotation.span,
                );

                self.instantiations.insert(type_annotation.id, subsitutions);

                ty
            }
            TypeAnnotationKind::Record { fields } => {
                let mut row = InferRow::Empty(TypeDefKind::Struct);
                for field in fields.iter().rev() {
                    row = InferRow::Extend {
                        row: Box::new(row),
                        label: field.label.name_str().into(),
                        ty: self.visit_type_annotation(&field.value, level),
                    };
                }

                InferTy::Record(Box::new(row))
            }
            TypeAnnotationKind::NominalPath {
                base,
                member,
                member_span,
                member_generics,
            } => {
                todo!()
            }
            _ => todo!("{type_annotation:?}"),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn visit_let(
        &mut self,
        lhs: &Pattern,
        type_annotation: &Option<TypeAnnotation>,
        rhs: &Option<Expr>,
        level: Level,
    ) -> InferTy {
        let ty = match (&type_annotation, &rhs) {
            (None, Some(expr)) => self.visit_expr(expr, level),
            (Some(annotation), None) => self.visit_type_annotation(annotation, level),
            (Some(annotation), Some(rhs)) => {
                let annotated_ty = self.visit_type_annotation(annotation, level);
                let rhs_ty = self.visit_expr(rhs, level);
                self.wants.equals(
                    annotated_ty.clone(),
                    rhs_ty,
                    ConstraintCause::Annotation(annotation.id),
                    annotation.span,
                );
                annotated_ty
            }
            (None, None) => self.session.new_ty_meta_var(level),
        };

        match &lhs.kind {
            PatternKind::Bind(name) => {
                self.session.insert_term(name.symbol(), ty.to_entry());
            }
            PatternKind::Record { .. } => todo!(),
            _ => todo!(),
        };

        ty
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
        level: Level,
    ) -> InferRow {
        match expected {
            InferTy::Record(box row) => row.clone(),
            _ => {
                let row = self.session.new_row_meta_var(level);
                self.wants.equals(
                    expected.clone(),
                    InferTy::Record(Box::new(row.clone())),
                    ConstraintCause::Member(id),
                    span,
                );
                row
            }
        }
    }
}

#[cfg(test)]
pub mod tests {
    use crate::{
        compiling::module::ModuleId,
        name_resolution::{name_resolver_tests::tests::resolve, symbol::Symbol},
        node_id::NodeID,
        span::Span,
        types::{
            constraints::{
                constraint::{Constraint, ConstraintCause},
                equals::Equals,
            },
            infer_ty::InferTy,
            term_environment::EnvEntry,
        },
    };

    use super::*;

    fn generate(code: &'static str) -> (Wants, TypeSession) {
        let resolved = resolve(code);
        let mut session = TypeSession::new(ModuleId::Current, Default::default());
        let wants = InferencePass::drive(&mut vec![resolved], &mut session);
        (wants, session)
    }

    #[test]
    fn let_int() {
        let (wants, mut session) = generate(
            r#"
            let a = 123
            "#,
        );

        assert!(wants.is_empty(), "generated unnecessary constraint");
        assert_eq!(
            session.lookup(&Symbol::Global(1.into())).unwrap(),
            EnvEntry::Mono(InferTy::Int)
        );
    }

    #[test]
    fn let_float() {
        let (wants, mut session) = generate(
            r#"
            let a = 1.23
            "#,
        );

        assert!(wants.is_empty(), "generated unnecessary constraint");
        assert_eq!(
            session.lookup(&Symbol::Global(1.into())).unwrap(),
            EnvEntry::Mono(InferTy::Float)
        );
    }

    #[test]
    fn let_with_annotation_no_value() {
        let (wants, mut session) = generate(
            r#"
            let a: Bool
            "#,
        );

        assert!(wants.is_empty(), "generated unnecessary constraint");
        assert_eq!(
            session.lookup(&Symbol::Global(1.into())).unwrap(),
            EnvEntry::Mono(InferTy::Bool)
        );
    }

    #[test]
    fn let_with_annotation_and_value() {
        let (wants, mut session) = generate(
            r#"
            let a: Bool = 123
            "#,
        );

        assert_eq!(
            wants.all(),
            vec![Constraint::Equals(Equals {
                lhs: InferTy::Bool,
                rhs: InferTy::Int,
                cause: ConstraintCause::Annotation(NodeID::ANY),
                span: Span::ANY
            })]
        );
        assert_eq!(
            session.lookup(&Symbol::Global(1.into())).unwrap(),
            EnvEntry::Mono(InferTy::Bool)
        );
    }

    #[test]
    fn annotated_param_func_returning_monotype() {
        let (wants, mut session) = generate(
            r#"
            func foo(x: Int) { x }
            "#,
        );

        assert_eq!(
            wants.all(),
            vec![Constraint::Equals(Equals {
                lhs: InferTy::Int,
                rhs: InferTy::Var {
                    id: 1.into(),
                    level: Level(1)
                },
                cause: ConstraintCause::Internal,
                span: Span::ANY
            })]
        );
        assert_eq!(
            session.lookup(&Symbol::Global(1.into())).unwrap(),
            EnvEntry::Mono(InferTy::Func(
                InferTy::Int.into(),
                InferTy::Var {
                    id: 1.into(),
                    level: Level(1)
                }
                .into()
            ))
        );
    }

    #[test]
    fn annotated_ret_func_returning_monotype() {
        let (wants, mut session) = generate(
            r#"
            func foo(x) -> Int { x }
            "#,
        );

        assert_eq!(
            wants.all(),
            vec![Constraint::Equals(Equals {
                lhs: InferTy::Var {
                    id: 1.into(),
                    level: Level(1)
                },
                rhs: InferTy::Int,
                cause: ConstraintCause::Internal,
                span: Span::ANY
            })]
        );
        assert_eq!(
            session.lookup(&Symbol::Global(1.into())).unwrap(),
            EnvEntry::Mono(InferTy::Func(
                InferTy::Var {
                    id: 1.into(),
                    level: Level(1)
                }
                .into(),
                InferTy::Int.into(),
            ))
        );
    }

    #[test]
    fn identity() {
        let (wants, mut session) = generate(
            r#"
            func id(x) { x }
            id(123)
            id(1.23)
            "#,
        );

        assert_eq!(
            wants.all(),
            vec![Constraint::Equals(Equals {
                lhs: InferTy::Var {
                    id: 1.into(),
                    level: Level(1)
                },
                rhs: InferTy::Int,
                cause: ConstraintCause::Internal,
                span: Span::ANY
            })]
        );
        assert_eq!(
            session.lookup(&Symbol::Global(1.into())).unwrap(),
            EnvEntry::Mono(InferTy::Func(
                InferTy::Var {
                    id: 1.into(),
                    level: Level(1)
                }
                .into(),
                InferTy::Int.into(),
            ))
        );
    }
}
