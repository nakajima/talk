use indexmap::IndexMap;
use itertools::Itertools;
use rustc_hash::FxHashMap;

use crate::{
    compiling::module::{ModuleEnvironment, ModuleId},
    label::Label,
    name_resolution::{
        name_resolver::ResolvedNames,
        symbol::{Symbol, Symbols, set_symbol_names},
    },
    node_id::NodeID,
    types::{
        call_tree::{CallArgumentPlan, CallTarget, CalleeInfo, ResolvedCall},
        conformance::ConformanceKey,
        constraints::member::consume_self,
        infer_row::{Row, RowParamId, Specializations},
        infer_ty::Ty,
        scheme::ForAll,
        type_error::TypeError,
        typed_ast::{
            TypedAST, TypedBlock, TypedDecl, TypedDeclKind, TypedExpr, TypedExprKind, TypedFunc,
            TypedMatchArm, TypedNode, TypedRecordField, TypedStmt, TypedStmtKind,
        },
        types::{TypeEntry, Types},
        variational::{DimensionId, Resolution, resolve_overloads},
    },
};

#[derive(Clone, Debug, PartialEq)]
pub struct SpecializedCallee {
    pub original_symbol: Symbol,
    pub specializations: Specializations,
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct SpecializationPlan {
    specializations: FxHashMap<Symbol, Vec<Symbol>>,
    specialized_callees: FxHashMap<Symbol, SpecializedCallee>,
    /// Maps (specialized_caller, call_site_id) -> specialized_callee.
    /// Aligns with the paper's model: each call site is a dimension, resolution maps to the callee.
    call_resolutions: FxHashMap<(Symbol, NodeID), Symbol>,
}

impl SpecializationPlan {
    pub fn specializations(&self) -> &FxHashMap<Symbol, Vec<Symbol>> {
        &self.specializations
    }

    pub fn specialized_callees(&self) -> &FxHashMap<Symbol, SpecializedCallee> {
        &self.specialized_callees
    }

    pub fn call_resolutions(&self) -> &FxHashMap<(Symbol, NodeID), Symbol> {
        &self.call_resolutions
    }
}

struct CallSpecialization {
    callee_sym: Symbol,
    callee_rewrite: CallCalleeRewrite,
    argument_plan: CallArgumentPlan,
}

enum CallCalleeRewrite {
    VisitOriginal,
    Variable { symbol: Symbol, ty: Ty },
}

pub struct SpecializationPass<'a> {
    ast: TypedAST,
    symbols: Symbols,
    resolved_names: ResolvedNames,
    types: Types,
    modules: &'a ModuleEnvironment,
    module_id: ModuleId,
    plan: SpecializationPlan,
    /// Resolved overloads computed from choices and error constraints.
    resolution: Resolution,
}

impl<'a> SpecializationPass<'a> {
    pub fn new(
        ast: TypedAST,
        symbols: Symbols,
        resolved_names: ResolvedNames,
        types: Types,
        modules: &'a ModuleEnvironment,
        module_id: ModuleId,
    ) -> Self {
        // Resolve overloads using the variational type checking results
        let resolution = resolve_overloads(&types.choices, &types.error_constraints)
            .unwrap_or_else(|errors| {
                for error in &errors {
                    tracing::warn!("Resolution error: {:?}", error);
                }
                Default::default()
            });

        Self {
            ast,
            symbols,
            resolved_names,
            types,
            modules,
            module_id,
            plan: Default::default(),
            resolution,
        }
    }

    pub fn drive(
        mut self,
    ) -> Result<(TypedAST, Symbols, ResolvedNames, Types, SpecializationPlan), TypeError> {
        let stmts = std::mem::take(&mut self.ast.stmts);
        let mut specialized_stmts = vec![];
        for stmt in stmts {
            specialized_stmts.push(self.visit_stmt(stmt)?);
        }
        _ = std::mem::replace(&mut self.ast.stmts, specialized_stmts);

        // Also visit declarations to process method bodies
        let decls = std::mem::take(&mut self.ast.decls);
        let mut specialized_decls = vec![];
        for decl in decls {
            specialized_decls.push(self.visit_decl(decl)?);
        }
        _ = std::mem::replace(&mut self.ast.decls, specialized_decls);

        Ok((
            self.ast,
            self.symbols,
            self.resolved_names,
            self.types,
            self.plan,
        ))
    }

    fn visit_stmt(&mut self, mut stmt: TypedStmt) -> Result<TypedStmt, TypeError> {
        stmt.kind = match stmt.kind {
            TypedStmtKind::Expr(expr) => {
                let expr = self.visit_expr(expr)?;
                stmt.ty = expr.ty.clone();
                TypedStmtKind::Expr(expr)
            }
            TypedStmtKind::Assignment(lhs, rhs) => {
                TypedStmtKind::Assignment(self.visit_expr(lhs)?, self.visit_expr(rhs)?)
            }
            TypedStmtKind::Return(expr) => {
                TypedStmtKind::Return(expr.map(|e| self.visit_expr(e)).transpose()?)
            }
            TypedStmtKind::Continue(expr) => {
                TypedStmtKind::Continue(expr.map(|e| self.visit_expr(e)).transpose()?)
            }
            TypedStmtKind::Loop(cond, body) => {
                TypedStmtKind::Loop(self.visit_expr(cond)?, self.visit_block(body)?)
            }
            TypedStmtKind::Break => TypedStmtKind::Break,
            TypedStmtKind::Handler { effect, func } => {
                let body = self.visit_block(func.body)?;
                TypedStmtKind::Handler {
                    effect,
                    func: TypedFunc { body, ..func },
                }
            }
        };

        Ok(stmt)
    }

    fn visit_decl(&mut self, mut decl: TypedDecl) -> Result<TypedDecl, TypeError> {
        decl.kind = match decl.kind {
            TypedDeclKind::Let {
                pattern,
                ty,
                initializer,
            } => TypedDeclKind::Let {
                pattern,
                ty,
                initializer: initializer.map(|e| self.visit_expr(e)).transpose()?,
            },
            TypedDeclKind::StructDef {
                symbol,
                initializers,
                properties,
                instance_methods,
                typealiases,
            } => TypedDeclKind::StructDef {
                symbol,
                initializers: self.visit_methods(initializers)?,
                properties,
                instance_methods: self.visit_methods(instance_methods)?,
                typealiases,
            },
            TypedDeclKind::Extend {
                symbol,
                instance_methods,
                typealiases,
            } => TypedDeclKind::Extend {
                symbol,
                instance_methods: self.visit_methods(instance_methods)?,
                typealiases,
            },
            TypedDeclKind::EnumDef {
                symbol,
                variants,
                instance_methods,
                typealiases,
            } => TypedDeclKind::EnumDef {
                symbol,
                variants,
                instance_methods: self.visit_methods(instance_methods)?,
                typealiases,
            },
            TypedDeclKind::ProtocolDef {
                symbol,
                instance_methods,
                instance_method_requirements,
                typealiases,
                associated_types,
            } => TypedDeclKind::ProtocolDef {
                symbol,
                instance_methods: self.visit_methods(instance_methods)?,
                instance_method_requirements,
                typealiases,
                associated_types,
            },
            TypedDeclKind::Import => TypedDeclKind::Import,
        };
        Ok(decl)
    }

    fn visit_methods(
        &mut self,
        methods: IndexMap<Label, TypedFunc>,
    ) -> Result<IndexMap<Label, TypedFunc>, TypeError> {
        methods
            .into_iter()
            .map(|(label, func)| {
                let body = self.visit_block(func.body)?;
                Ok((label, TypedFunc { body, ..func }))
            })
            .collect()
    }

    fn visit_block(&mut self, block: TypedBlock) -> Result<TypedBlock, TypeError> {
        let body = block
            .body
            .into_iter()
            .map(|node| self.visit_node(node))
            .try_collect()?;
        Ok(TypedBlock { body, ..block })
    }

    fn visit_pattern(&mut self, pattern: &crate::types::typed_ast::TypedPattern) {
        use crate::types::typed_ast::TypedPatternKind;

        match &pattern.kind {
            TypedPatternKind::Variant { fields, .. } => {
                // Recursively visit field patterns
                for field in fields {
                    self.visit_pattern(field);
                }
            }
            TypedPatternKind::Tuple(patterns) | TypedPatternKind::Or(patterns) => {
                for p in patterns {
                    self.visit_pattern(p);
                }
            }
            TypedPatternKind::Record { fields } => {
                for field in fields {
                    if let crate::types::typed_ast::TypedRecordFieldPatternKind::Equals {
                        value,
                        ..
                    } = &field.kind
                    {
                        self.visit_pattern(value);
                    }
                }
            }
            TypedPatternKind::Struct { fields, .. } => {
                for field in fields {
                    self.visit_pattern(field);
                }
            }
            _ => {}
        }
    }

    fn visit_node(&mut self, node: TypedNode) -> Result<TypedNode, TypeError> {
        Ok(match node {
            TypedNode::Stmt(stmt) => TypedNode::Stmt(self.visit_stmt(stmt)?),
            TypedNode::Expr(expr) => TypedNode::Expr(self.visit_expr(expr)?),
            TypedNode::Decl(decl) => {
                // Also visit decls that appear inside blocks (e.g., let bindings in function bodies)
                TypedNode::Decl(self.visit_decl(decl)?)
            }
        })
    }

    fn visit_expr(&mut self, mut expr: TypedExpr) -> Result<TypedExpr, TypeError> {
        expr.kind = match expr.kind {
            TypedExprKind::LiteralArray(items) => TypedExprKind::LiteralArray(
                items
                    .into_iter()
                    .map(|i| self.visit_expr(i))
                    .try_collect()?,
            ),
            TypedExprKind::Tuple(items) => TypedExprKind::Tuple(
                items
                    .into_iter()
                    .map(|i| self.visit_expr(i))
                    .try_collect()?,
            ),
            TypedExprKind::CallEffect {
                effect,
                type_args,
                args,
            } => TypedExprKind::CallEffect {
                effect,
                type_args,
                args: args.into_iter().map(|i| self.visit_expr(i)).try_collect()?,
            },
            TypedExprKind::Constructor(name, args) => self.visit_constructor(name, args)?,
            TypedExprKind::Call { .. } => return self.visit_call(expr),
            TypedExprKind::Member {
                box receiver,
                label,
                label_span,
            } => {
                let visited_receiver = self.visit_expr(receiver)?;

                TypedExprKind::Member {
                    receiver: visited_receiver.into(),
                    label,
                    label_span,
                }
            }
            TypedExprKind::If(box cond, conseq, alt) => TypedExprKind::If(
                self.visit_expr(cond)?.into(),
                self.visit_block(conseq)?,
                self.visit_block(alt)?,
            ),
            TypedExprKind::Match(box scrutinee, arms) => {
                let new_arms = arms
                    .into_iter()
                    .map(|arm| {
                        self.visit_pattern(&arm.pattern);
                        Ok(TypedMatchArm {
                            pattern: arm.pattern,
                            body: self.visit_block(arm.body)?,
                        })
                    })
                    .collect::<Result<Vec<_>, TypeError>>()?;
                TypedExprKind::Match(self.visit_expr(scrutinee)?.into(), new_arms)
            }
            TypedExprKind::RecordLiteral { fields } => {
                let mut new_fields: Vec<_> = Default::default();
                for field in fields {
                    new_fields.push(TypedRecordField {
                        name: field.name,
                        value: self.visit_expr(field.value)?,
                    });
                }
                TypedExprKind::RecordLiteral { fields: new_fields }
            }
            TypedExprKind::Variable(name) => self.visit_variable(name)?,
            TypedExprKind::Func(func) => {
                // Visit the function body to process calls inside it
                let body = self.visit_block(func.body)?;
                TypedExprKind::Func(TypedFunc { body, ..func })
            }
            kind => kind,
        };

        Ok(expr)
    }

    fn visit_variable(&mut self, name: Symbol) -> Result<TypedExprKind, TypeError> {
        Ok(TypedExprKind::Variable(name))
    }

    fn visit_constructor(
        &mut self,
        name: Symbol,
        args: Vec<Ty>,
    ) -> Result<TypedExprKind, TypeError> {
        Ok(TypedExprKind::Constructor(name, args))
    }

    fn visit_call(&mut self, mut expr: TypedExpr) -> Result<TypedExpr, TypeError> {
        let TypedExprKind::Call {
            box callee,
            callee_ty,
            type_args,
            args,
            ..
        } = expr.kind
        else {
            unreachable!()
        };

        let is_constructor = matches!(callee.kind, TypedExprKind::Constructor(..));
        let mut specializations = if is_constructor {
            self.constructor_specializations(&callee, &expr.ty)
        } else {
            callee_ty.collect_specializations(&callee.ty)?
        };

        if let Some(ty_instantiations) = self.types.catalog.instantiations.ty.get(&callee.id) {
            for (param, ty) in ty_instantiations {
                if !matches!(ty, Ty::Param(..)) {
                    specializations.ty.insert(*param, ty.clone());
                }
            }
        }
        if let Some(row_instantiations) = self.types.catalog.instantiations.row.get(&callee.id) {
            for (param, row) in row_instantiations {
                if !matches!(row, Row::Param(..)) {
                    specializations.row.insert(*param, row.clone());
                }
            }
        }

        self.apply_explicit_type_args(&callee, &expr.ty, &type_args, &mut specializations)?;
        self.add_associated_type_specializations(&callee_ty, &mut specializations);

        if is_constructor
            && let TypedExprKind::Constructor(symbol, ..) = &callee.kind
            && let Some(specialized_init) =
                self.specialized_constructor_initializer(symbol, &specializations)
        {
            expr.kind = TypedExprKind::Call {
                callee: callee.into(),
                callee_ty,
                type_args,
                args: self.visit_call_args(args)?,
                callee_sym: Some(specialized_init),
            };
        } else if matches!(callee.kind, TypedExprKind::Call { .. }) {
            // Callee is itself a call expression (e.g., b()() where b() returns a function)
            // We can't statically specialize this - just visit the callee and args recursively
            let specialized_callee = self.visit_expr(callee)?;
            expr.kind = TypedExprKind::Call {
                callee: specialized_callee.into(),
                callee_ty,
                type_args,
                args: self.visit_call_args(args)?,
                callee_sym: None,
            };
        } else {
            let type_args = if type_args.is_empty() {
                self.inferred_type_args(&callee, &specializations)
            } else {
                type_args
            };

            let Some(specialized_call) =
                self.specialize_call_site(&callee, &expr.ty, &specializations)?
            else {
                let specialized_callee = self.visit_expr(callee.clone())?;

                expr.kind = TypedExprKind::Call {
                    callee: specialized_callee.into(),
                    callee_ty,
                    type_args,
                    args: self.visit_call_args(args)?,
                    callee_sym: None, // Will be resolved at monomorphization
                };
                return Ok(expr);
            };

            let specialized_callee =
                self.apply_call_callee_rewrite(&callee, specialized_call.callee_rewrite)?;
            let mut visited_args = Vec::new();
            if let Some(receiver) =
                self.receiver_to_prepend(&callee, &specialized_call.argument_plan)
            {
                visited_args.push(self.visit_expr(receiver)?);
            }
            visited_args.extend(self.visit_call_args(args)?);

            expr.kind = TypedExprKind::Call {
                callee: specialized_callee.into(),
                callee_ty,
                type_args,
                args: visited_args,
                callee_sym: Some(specialized_call.callee_sym),
            };
        }

        expr.ty = specializations.apply(expr.ty);
        Ok(expr)
    }

    fn specialized_constructor_initializer(
        &mut self,
        constructor: &Symbol,
        specializations: &Specializations,
    ) -> Option<Symbol> {
        let init_label = Label::Named("init".into());
        self.types
            .catalog
            .initializers
            .get(constructor)
            .and_then(|inits| inits.get(&init_label).copied())
            .or_else(|| {
                self.modules
                    .lookup_initializers(constructor)
                    .and_then(|inits| inits.get(&init_label).copied())
            })
            .map(|init_sym| self.specialize(&init_sym, specializations))
    }

    fn resolved_call_for(&self, callee_id: NodeID) -> Option<ResolvedCall> {
        self.types.resolved_calls.get(&callee_id).cloned()
    }

    fn imported_resolved_call_for(
        &self,
        caller: &Symbol,
        callee_id: NodeID,
    ) -> Option<ResolvedCall> {
        if let Some(module_id) = caller.external_module_id() {
            return self
                .modules
                .get_module(module_id)
                .and_then(|module| module.types.resolved_calls.get(&callee_id).cloned());
        }

        self.resolved_call_for(callee_id)
    }

    fn call_receiver_tys(
        &self,
        caller: Option<&Symbol>,
        callee_id: NodeID,
        specializations: &Specializations,
    ) -> Option<(Ty, Ty)> {
        let call = caller
            .and_then(|caller| self.imported_resolved_call_for(caller, callee_id))
            .or_else(|| self.resolved_call_for(callee_id))?;
        let receiver = call.receiver?;
        let raw_ty = receiver.ty;
        let concrete_ty = specializations.apply(raw_ty.clone());
        Some((raw_ty, concrete_ty))
    }

    fn inferred_type_args(&self, callee: &TypedExpr, specializations: &Specializations) -> Vec<Ty> {
        if specializations.ty.is_empty() {
            return vec![];
        }

        let Some(resolved_call) = self.resolved_call_for(callee.id) else {
            tracing::warn!(
                callee_id = ?callee.id,
                "missing resolved call target while inferring type args"
            );
            return vec![];
        };

        self.type_args_for_callee_scheme(&resolved_call.symbol(), specializations)
    }

    fn type_args_for_callee_scheme(
        &self,
        callee_sym: &Symbol,
        specializations: &Specializations,
    ) -> Vec<Ty> {
        if let Some(TypeEntry::Poly(scheme)) = self.get_type_for(callee_sym) {
            return scheme
                .foralls
                .iter()
                .filter_map(|forall| match forall {
                    ForAll::Ty(param) => specializations.ty.get(param).cloned(),
                    ForAll::Row(_) => None,
                })
                .collect();
        }

        if matches!(callee_sym, Symbol::Variant(_)) {
            return specializations.ty.values().cloned().collect();
        }

        assert!(
            specializations.ty.is_empty(),
            "missing polymorphic scheme for specialized callee {callee_sym:?}"
        );
        vec![]
    }

    fn visit_call_args(&mut self, args: Vec<TypedExpr>) -> Result<Vec<TypedExpr>, TypeError> {
        args.into_iter()
            .map(|arg| self.visit_expr(arg))
            .try_collect()
    }

    fn receiver_to_prepend(
        &self,
        callee: &TypedExpr,
        argument_plan: &CallArgumentPlan,
    ) -> Option<TypedExpr> {
        let CallArgumentPlan::PrependReceiver { id } = argument_plan else {
            return None;
        };
        let TypedExprKind::Member { receiver, .. } = &callee.kind else {
            return None;
        };
        if receiver.id == *id {
            Some(receiver.as_ref().clone())
        } else {
            None
        }
    }

    fn apply_call_callee_rewrite(
        &mut self,
        callee: &TypedExpr,
        rewrite: CallCalleeRewrite,
    ) -> Result<TypedExpr, TypeError> {
        match rewrite {
            CallCalleeRewrite::VisitOriginal => self.visit_expr(callee.clone()),
            CallCalleeRewrite::Variable { symbol, ty } => Ok(TypedExpr {
                id: callee.id,
                ty,
                kind: TypedExprKind::Variable(symbol),
            }),
        }
    }

    fn specialize_call_site(
        &mut self,
        callee: &TypedExpr,
        _call_ty: &Ty,
        specializations: &Specializations,
    ) -> Result<Option<CallSpecialization>, TypeError> {
        let mut accumulated_specs = specializations.clone();
        let Some(resolved_call) = self.resolved_call_for(callee.id) else {
            return Ok(None);
        };
        let argument_plan = resolved_call.argument_plan.clone();
        let mut caller = resolved_call.symbol();

        caller = self.resolve_member_call_callee(caller, callee.id, &mut accumulated_specs);

        let callee_sym = self.specialize(&caller, &accumulated_specs);
        self.specialize_callees(callee_sym, caller, &accumulated_specs)?;

        let mut callee_rewrite = CallCalleeRewrite::VisitOriginal;
        match &callee.kind {
            TypedExprKind::Member { .. } => {
                if !matches!(caller, Symbol::Variant(..)) {
                    callee_rewrite = CallCalleeRewrite::Variable {
                        symbol: callee_sym,
                        ty: accumulated_specs.apply(callee.ty.clone()),
                    };
                }
            }
            TypedExprKind::Variable(..) => {
                callee_rewrite = CallCalleeRewrite::Variable {
                    symbol: callee_sym,
                    ty: accumulated_specs.apply(callee.ty.clone()),
                };
            }
            _ => {}
        }

        Ok(Some(CallSpecialization {
            callee_sym,
            callee_rewrite,
            argument_plan,
        }))
    }

    fn resolve_member_call_callee(
        &self,
        mut caller: Symbol,
        call_id: NodeID,
        accumulated_specs: &mut Specializations,
    ) -> Symbol {
        if !matches!(caller, Symbol::MethodRequirement(_)) {
            return caller;
        }

        let Some((raw_receiver_ty, receiver_ty)) =
            self.call_receiver_tys(None, call_id, accumulated_specs)
        else {
            return caller;
        };

        if let Some(witness_sym) = self.resolve_witness_for_type(&caller, &receiver_ty) {
            self.add_receiver_type_args(&witness_sym, &receiver_ty, accumulated_specs);
            return witness_sym;
        }

        let dimension = DimensionId(call_id);
        if let Some(resolved_alt) = self.resolution.get(&dimension) {
            if let Some(alt) = self.types.choices.get_alternative(dimension, resolved_alt) {
                caller = alt.witness_sym;
                self.add_receiver_type_args(&caller, &receiver_ty, accumulated_specs);
            }
        } else if self.types.choices.dimension_size(&dimension) > 0
            && let Ok(receiver_sym) = self.symbol_from_ty(&receiver_ty, accumulated_specs)
            && let Some(witness_sym) = self.types.choices.resolve_for_type(dimension, receiver_sym)
        {
            caller = witness_sym;
            self.add_receiver_type_args(&caller, &receiver_ty, accumulated_specs);
        }

        if let Symbol::MethodRequirement(_) = caller
            && let Some((_, label)) = self.method_requirement_label(&caller)
            && let Some((witness_sym, concrete_ty)) =
                self.resolve_bounded_witness(&raw_receiver_ty, &label, accumulated_specs)
        {
            caller = witness_sym;
            self.add_receiver_type_args(&caller, &concrete_ty, accumulated_specs);
        }

        caller
    }

    fn lookup_witness(
        &self,
        key: &ConformanceKey,
        label: &Label,
        method_req: &Symbol,
    ) -> Option<Symbol> {
        self.types
            .lookup_witness(self.modules, key, label, method_req)
    }

    fn lookup_method_requirement(&self, protocol_sym: &Symbol, label: &Label) -> Option<Symbol> {
        self.types
            .lookup_method_requirement(self.modules, protocol_sym, label)
    }

    fn method_requirement_label(&self, method_req: &Symbol) -> Option<(Symbol, Label)> {
        self.types
            .method_requirement_label(self.modules, method_req)
    }

    fn associated_type_witnesses(&self, key: &ConformanceKey) -> Option<FxHashMap<Label, Ty>> {
        self.types.associated_type_witnesses(self.modules, key)
    }

    fn resolve_choice_for_receiver(
        &self,
        dimension: DimensionId,
        receiver_ty: &Ty,
        specializations: &Specializations,
    ) -> Option<(Symbol, Ty)> {
        let receiver_sym = self.symbol_from_ty(receiver_ty, specializations).ok()?;
        self.types
            .choices
            .resolve_for_type(dimension, receiver_sym)
            .map(|witness| (witness, receiver_ty.clone()))
    }

    fn resolve_bounded_witness(
        &self,
        receiver_ty: &Ty,
        label: &Label,
        specializations: &Specializations,
    ) -> Option<(Symbol, Ty)> {
        let Ty::Param(_, bounds) = receiver_ty else {
            return None;
        };

        let concrete_ty = specializations.apply(receiver_ty.clone());
        let conforming_id = self.symbol_from_ty(&concrete_ty, specializations).ok()?;

        let mut resolved = None;
        for protocol_id in bounds {
            let protocol_sym = Symbol::Protocol(*protocol_id);
            let Some(method_req) = self.lookup_method_requirement(&protocol_sym, label) else {
                continue;
            };

            let key = ConformanceKey {
                protocol_id: *protocol_id,
                conforming_id,
            };
            let Some(witness) = self.lookup_witness(&key, label, &method_req) else {
                continue;
            };

            if resolved.is_some() {
                return None;
            }
            resolved = Some((witness, concrete_ty.clone()));
        }

        resolved
    }

    fn add_receiver_type_args(
        &self,
        member_sym: &Symbol,
        receiver_ty: &Ty,
        specializations: &mut Specializations,
    ) {
        let Ty::Nominal { type_args, .. } = receiver_ty else {
            return;
        };
        if type_args.is_empty() {
            return;
        }

        let Some(TypeEntry::Poly(scheme)) = self.get_type_for(member_sym) else {
            return;
        };

        for (forall, arg) in scheme
            .foralls
            .iter()
            .filter_map(|forall| {
                if let ForAll::Ty(param) = forall {
                    Some(*param)
                } else {
                    None
                }
            })
            .zip(type_args.iter())
        {
            specializations.ty.insert(forall, arg.clone());
        }
    }

    fn add_associated_type_specializations(
        &self,
        callee_ty: &Ty,
        specializations: &mut Specializations,
    ) {
        let current_ty_specializations = specializations.ty.clone();
        for (param, concrete_ty) in current_ty_specializations {
            let bounds = callee_ty.protocol_bounds_for_param(param);
            if bounds.is_empty() {
                continue;
            }

            let Ok(conforming_id) = self.symbol_from_ty(&concrete_ty, specializations) else {
                continue;
            };

            let mut witness_specializations = specializations.clone();
            if let Ty::Nominal { symbol, type_args } = &concrete_ty
                && let Some(nominal) = self.types.catalog.nominals.get(symbol)
            {
                for (param, arg) in nominal.type_params.iter().zip(type_args) {
                    if let Ty::Param(param_id, _) = param {
                        witness_specializations.ty.insert(*param_id, arg.clone());
                    }
                }
            }

            for protocol_id in bounds {
                let key = ConformanceKey {
                    protocol_id,
                    conforming_id,
                };
                let Some(associated_type_witnesses) = self.associated_type_witnesses(&key) else {
                    continue;
                };
                let Some(associated_types) = self
                    .types
                    .catalog
                    .associated_types
                    .get(&Symbol::Protocol(protocol_id))
                else {
                    continue;
                };

                for (label, witness_ty) in &associated_type_witnesses {
                    let Some(associated_sym) = associated_types.get(label) else {
                        continue;
                    };
                    let Some(associated_entry) = self.types.get_symbol(associated_sym) else {
                        continue;
                    };
                    let Ty::Param(associated_param, _) = associated_entry.as_mono_ty() else {
                        continue;
                    };
                    let applied_witness = witness_specializations.apply(witness_ty.clone());
                    specializations
                        .ty
                        .insert(*associated_param, applied_witness);
                }
            }
        }
    }

    fn constructor_specializations(&self, callee: &TypedExpr, call_ty: &Ty) -> Specializations {
        let mut specializations = Specializations::default();
        let TypedExprKind::Constructor(symbol, ..) = &callee.kind else {
            return specializations;
        };

        let Ty::Nominal {
            symbol: ret_sym,
            type_args,
        } = call_ty
        else {
            return specializations;
        };

        if symbol != ret_sym {
            return specializations;
        }

        let Some(nominal) = self.types.catalog.nominals.get(symbol) else {
            return specializations;
        };

        for (param, arg) in nominal.type_params.iter().zip(type_args.iter()) {
            if let Ty::Param(id, _) = param {
                specializations.ty.insert(*id, arg.clone());
            }
        }

        specializations
    }

    fn symbol_from_ty(
        &self,
        ty: &Ty,
        specializations: &Specializations,
    ) -> Result<Symbol, TypeError> {
        let ty = specializations.apply(ty.clone());
        match ty {
            Ty::Primitive(sym) => Ok(sym),
            Ty::Nominal { symbol, .. } => Ok(symbol),
            Ty::Constructor { name, .. } => Ok(name.symbol().unwrap_or_else(|_| unreachable!())),
            _ => Err(TypeError::TypeNotFound(format!(
                "could not determine receiver: {ty:?}",
            ))),
        }
    }

    fn apply_explicit_type_args(
        &self,
        callee: &TypedExpr,
        _call_ty: &Ty,
        type_args: &[Ty],
        specializations: &mut Specializations,
    ) -> Result<(), TypeError> {
        if type_args.is_empty() {
            return Ok(());
        }

        let Some(callee_sym) = self.resolved_call_for(callee.id).map(|call| call.symbol()) else {
            return Ok(());
        };
        let Some(TypeEntry::Poly(scheme)) = self.get_type_for(&callee_sym) else {
            return Ok(());
        };

        let ty_params = scheme.foralls.iter().filter_map(|f| match f {
            ForAll::Ty(id) => Some(*id),
            ForAll::Row(_) => None,
        });

        for (param, arg) in ty_params.zip(type_args.iter()) {
            specializations.ty.insert(param, arg.clone());
        }

        Ok(())
    }

    /// Compute specializations for callees of a function and propagate.
    /// `specialized_caller` is the specialized symbol (e.g., `Array.get[Int]`)
    /// `original_caller` is the original symbol (e.g., `Array.get`)
    fn specialize_callees(
        &mut self,
        specialized_caller: Symbol,
        original_caller: Symbol,
        specializations: &Specializations,
    ) -> Result<(), TypeError> {
        // Skip if specializations are empty
        if specializations.is_empty() {
            return Ok(());
        }

        // Get callees from call tree - look up in imported module if needed
        let callees = self.get_call_tree_for(&original_caller);

        for callee_info in callees {
            // call_id is the callee expression ID, used for both instantiation lookup
            // and call_resolutions key (matches IR instruction meta)
            let (callee_sym, callee_specializations, call_id) = match callee_info {
                CalleeInfo::Direct { sym, call_id } => {
                    let callee_specs = self.compute_callee_specializations(
                        &original_caller,
                        &call_id,
                        specializations,
                    );
                    (sym, callee_specs, call_id)
                }
                CalleeInfo::Member { label, call_id } => {
                    let resolved_call = self.imported_resolved_call_for(&original_caller, call_id);
                    let receiver_tys =
                        self.call_receiver_tys(Some(&original_caller), call_id, specializations);
                    let target_member =
                        resolved_call.as_ref().and_then(|call| match &call.target {
                            CallTarget::Member { member, .. } => Some(*member),
                            _ => None,
                        });
                    let receiver_ty = receiver_tys
                        .as_ref()
                        .map(|(_, concrete_receiver_ty)| concrete_receiver_ty.clone());
                    let resolved_target = target_member.and_then(|member_sym| {
                        if let Symbol::MethodRequirement(_) = member_sym {
                            let concrete_receiver_ty = receiver_ty.as_ref()?;
                            self.resolve_witness_for_type(&member_sym, concrete_receiver_ty)
                                .map(|witness| (witness, receiver_ty.clone()))
                        } else {
                            Some((member_sym, receiver_ty.clone()))
                        }
                    });

                    let resolved_member = resolved_target
                        .or_else(|| {
                            receiver_tys.as_ref().and_then(|(_, concrete_receiver_ty)| {
                                self.resolve_choice_for_receiver(
                                    DimensionId(call_id),
                                    concrete_receiver_ty,
                                    specializations,
                                )
                                .map(|(witness, concrete_ty)| (witness, Some(concrete_ty)))
                            })
                        })
                        .or_else(|| {
                            receiver_tys.as_ref().and_then(|(raw_receiver_ty, _)| {
                                self.resolve_bounded_witness(
                                    raw_receiver_ty,
                                    &label,
                                    specializations,
                                )
                                .map(|(witness, concrete_ty)| (witness, Some(concrete_ty)))
                            })
                        })
                        .or_else(|| {
                            target_member.map(|member_sym| (member_sym, receiver_ty.clone()))
                        });

                    let Some((member_sym, receiver_ty)) = resolved_member else {
                        continue;
                    };

                    let mut callee_specs = self.compute_callee_specializations(
                        &original_caller,
                        &call_id,
                        specializations,
                    );

                    // For conformance witness methods (e.g., Array.show from
                    // extend Array<Element: Showable>: Showable), the inference pass
                    // doesn't record instantiation data mapping the witness's forall
                    // params (e.g., Element) to concrete types. Map them from the
                    // concrete receiver type's type_args.
                    if callee_specs.ty.is_empty()
                        && let Some(receiver_ty) = &receiver_ty
                    {
                        self.add_receiver_type_args(&member_sym, receiver_ty, &mut callee_specs);
                    }

                    (member_sym, callee_specs, call_id)
                }
            };

            // If the callee is a MethodRequirement (protocol method stub), resolve it to the
            // concrete witness. This happens when lookup_member goes through a conformance
            // and returns the protocol's method requirement instead of the witness.
            let original_callee_sym = callee_sym;
            let callee_sym = if let Symbol::MethodRequirement(_) = callee_sym {
                match self.resolve_method_req_to_witness(&callee_sym, &callee_specializations) {
                    Some(witness) => witness,
                    None => continue,
                }
            } else {
                callee_sym
            };

            // Specialize this callee and record the resolution
            let specialized_callee = self.specialize(&callee_sym, &callee_specializations);

            // Record: for this call site within specialized_caller, use specialized_callee.
            // This also records MethodRequirement -> witness rewrites where no new
            // specialized wrapper is needed.
            if specialized_callee != original_callee_sym {
                self.plan
                    .call_resolutions
                    .insert((specialized_caller, call_id), specialized_callee);
            }

            // Recursively propagate to callees
            self.specialize_callees(specialized_callee, callee_sym, &callee_specializations)?;
        }

        Ok(())
    }

    /// Get call tree entries for a function, looking in imported modules if needed
    fn get_call_tree_for(&self, caller: &Symbol) -> Vec<CalleeInfo> {
        // First check local types
        if let Some(callees) = self.types.call_tree.get(caller) {
            return callees.clone();
        }
        // Then check imported modules
        if let Some(module_id) = caller.external_module_id()
            && let Some(module) = self.modules.get_module(module_id)
            && let Some(callees) = module.types.call_tree.get(caller)
        {
            return callees.clone();
        }
        vec![]
    }

    /// Compute specializations for a callee based on instantiations at the call site.
    fn compute_callee_specializations(
        &self,
        caller: &Symbol,
        call_id: &NodeID,
        specializations: &Specializations,
    ) -> Specializations {
        let mut callee_specs = Specializations::default();

        // Look up instantiations - in imported module if caller is from there
        let (ty_insts, row_insts) = self.get_instantiations_for(caller, call_id);

        if let Some(ty_instantiations) = ty_insts {
            for (param, ty) in ty_instantiations {
                let specialized_ty = specializations.apply(ty.clone());
                // Skip type parameters (polymorphic) and metavariables (unresolved)
                if !matches!(specialized_ty, Ty::Param(..) | Ty::Var { .. }) {
                    callee_specs.ty.insert(*param, specialized_ty);
                }
            }
        }

        if let Some(row_instantiations) = row_insts {
            for (param, row) in row_instantiations {
                let specialized_row = if let Row::Param(row_id) = row
                    && let Some(replacement) = specializations.row.get(row_id)
                {
                    replacement.clone()
                } else {
                    row.clone()
                };
                // Skip row parameters (polymorphic) and row variables (unresolved)
                if !matches!(specialized_row, Row::Param(..) | Row::Var(..)) {
                    callee_specs.row.insert(*param, specialized_row);
                }
            }
        }

        callee_specs
    }

    /// Get instantiations for a call site, looking in imported modules if needed
    #[allow(clippy::type_complexity)]
    fn get_instantiations_for(
        &self,
        caller: &Symbol,
        call_id: &NodeID,
    ) -> (
        Option<&FxHashMap<Symbol, Ty>>,
        Option<&FxHashMap<RowParamId, Row>>,
    ) {
        // First check local catalog
        let local_ty = self.types.catalog.instantiations.ty.get(call_id);
        let local_row = self.types.catalog.instantiations.row.get(call_id);
        if local_ty.is_some() || local_row.is_some() {
            return (local_ty, local_row);
        }

        // Then check imported module based on caller's module
        if let Some(module_id) = caller.external_module_id()
            && let Some(module) = self.modules.get_module(module_id)
        {
            return (
                module.types.catalog.instantiations.ty.get(call_id),
                module.types.catalog.instantiations.row.get(call_id),
            );
        }

        (None, None)
    }

    /// Get type entry for a symbol, looking in imported modules if needed
    fn get_type_for(&self, sym: &Symbol) -> Option<TypeEntry> {
        // First check local types
        if let Some(ty) = self.types.types_by_symbol.get(sym) {
            return Some(ty.clone());
        }
        // Then check imported modules
        self.modules.lookup(sym)
    }

    fn specialize(&mut self, callee_sym: &Symbol, specializations: &Specializations) -> Symbol {
        if specializations.is_empty() {
            return *callee_sym;
        }

        // Single-pass filter: remove metavars (Ty::Var and Row::Var) from specializations
        // These represent unresolved types that shouldn't be specialized
        let filtered_specs = Specializations {
            ty: specializations
                .ty
                .iter()
                .filter(|(_, v)| !matches!(v, Ty::Var { .. }))
                .map(|(k, v)| (*k, v.clone()))
                .collect(),
            row: specializations
                .row
                .iter()
                .filter(|(_, v)| !matches!(v, Row::Var(..)))
                .map(|(k, v)| (*k, v.clone()))
                .collect(),
        };

        if filtered_specs.is_empty() {
            return *callee_sym;
        }

        // Get the original type - look in imported modules if needed
        let ty = self
            .get_type_for(callee_sym)
            .unwrap_or_else(|| unreachable!("did not get ty for {callee_sym:?}"));

        // Check if applying specializations actually changes the type
        // If not (e.g., for concrete witnesses like Int.add), no wrapper needed
        let mono_ty = ty.as_mono_ty();
        let specialized_ty = filtered_specs.apply(mono_ty.clone());
        if specialized_ty == *mono_ty {
            return *callee_sym;
        }

        // Use filtered specs for deduplication and storage
        let specializations = &filtered_specs;

        // Check if we already have a specialization for this callee + specializations
        if let Some(existing) = self.plan.specializations.get(callee_sym) {
            for &sym in existing {
                if let Some(callee) = self.plan.specialized_callees.get(&sym)
                    && &callee.specializations == specializations
                {
                    return sym;
                }
            }
        }

        let new_sym = self.symbols.next_synthesized(self.module_id);

        // Save the specialized version
        self.types.types_by_symbol.insert(
            new_sym.into(),
            TypeEntry::Mono(specializations.apply(ty.as_mono_ty().clone())),
        );

        // Record the specialization
        self.plan
            .specializations
            .entry(*callee_sym)
            .or_default()
            .push(new_sym.into());
        self.plan.specialized_callees.insert(
            new_sym.into(),
            SpecializedCallee {
                original_symbol: *callee_sym,
                specializations: specializations.clone(),
            },
        );

        // Save the name
        let original_name = self
            .resolved_names
            .symbol_names
            .get(callee_sym)
            .cloned()
            .unwrap_or_else(|| format!("{callee_sym:?}"));
        set_symbol_names(self.resolved_names.symbol_names.clone());
        let new_name = format!(
            "{original_name}[{}]",
            self.type_args_for_callee_scheme(callee_sym, specializations)
                .iter()
                .map(|v| format!("{v:?}"))
                .join(", ")
        );
        self.resolved_names
            .symbol_names
            .insert(new_sym.into(), new_name);

        new_sym.into()
    }

    fn resolve_witness_for_type(&self, method_req: &Symbol, receiver_ty: &Ty) -> Option<Symbol> {
        let (protocol_sym, label) = self.method_requirement_label(method_req)?;
        let Symbol::Protocol(protocol_id) = protocol_sym else {
            return None;
        };

        let conforming_sym = match receiver_ty {
            Ty::Nominal { symbol, .. } => *symbol,
            Ty::Primitive(sym) => *sym,
            _ => return None,
        };
        let key = ConformanceKey {
            conforming_id: conforming_sym,
            protocol_id,
        };
        self.lookup_witness(&key, &label, method_req)
    }

    /// Resolve a MethodRequirement to its concrete witness by looking up the conformance.
    /// Checks both local and imported module conformances.
    fn resolve_method_req_to_witness(
        &self,
        method_req: &Symbol,
        callee_specs: &Specializations,
    ) -> Option<Symbol> {
        let (protocol_sym, label) = self.method_requirement_label(method_req)?;
        let Symbol::Protocol(protocol_id) = protocol_sym else {
            return None;
        };

        let entry = self.get_type_for(method_req)?;
        let (receiver_ty, _) = consume_self(entry.as_mono_ty());
        let concrete_ty = callee_specs.apply(receiver_ty);
        let conforming_sym = match concrete_ty {
            Ty::Nominal { symbol, .. } => symbol,
            Ty::Primitive(sym) => sym,
            _ => return None,
        };
        let key = ConformanceKey {
            conforming_id: conforming_sym,
            protocol_id,
        };
        self.lookup_witness(&key, &label, method_req)
    }
}

#[cfg(test)]
pub mod tests {
    use crate::{
        compiling::driver::{Driver, DriverConfig, Source, Typed},
        compiling::module::ModuleId,
        fxhashmap,
        name_resolution::symbol::{
            GlobalId, Symbol, SynthesizedId, TypeParameterId, set_symbol_names,
        },
        types::{
            infer_ty::Ty,
            typed_ast::{TypedExprKind, TypedStmtKind},
        },
    };

    /// Helper to create a test type parameter symbol
    fn test_type_param(id: u32) -> Symbol {
        Symbol::TypeParameter(TypeParameterId::new(ModuleId::Current, id))
    }

    fn specialize(code: &'static str) -> Typed {
        let driver = Driver::new_bare(vec![Source::from(code)], DriverConfig::new("TestDriver"));
        let typed = driver
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap();

        typed.phase
    }

    #[test]
    fn specializes_generic_func_call() {
        let typed = specialize(
            "
      func inner(x) { x } // We'll need a specialized version of this one too
      func id(x) { inner(x) }
      id(123)
      ",
        );

        // Make sure we have specializations (deduplicated - one per unique function+specialization)
        // Note: inner doesn't get a specialization because its type arg inside id's body is a
        // metavar that gets filtered out. This is correct - we only specialize when we have
        // concrete types.
        set_symbol_names(typed.resolved_names.symbol_names.clone());
        assert_eq!(
            typed.specialization_plan.specializations(),
            &fxhashmap!( GlobalId::from(2).into() => vec![SynthesizedId::from(1).into()] )
        );

        // Synthesized(1) is id[Int]
        let callee1 = typed
            .specialization_plan
            .specialized_callees()
            .get(&SynthesizedId::from(1).into())
            .unwrap();
        assert_eq!(callee1.original_symbol, GlobalId::from(2).into());
        // id is called with Int, so its type param should specialize to Int
        assert_eq!(
            callee1.specializations.ty.get(&test_type_param(1)),
            Some(&Ty::Int)
        );

        // Make sure we're calling the specialized version
        let TypedStmtKind::Expr(expr) = &typed.ast.stmts[0].kind else {
            panic!("expected expr statement");
        };
        let TypedExprKind::Call {
            callee, callee_sym, ..
        } = &expr.kind
        else {
            panic!("expected call expression");
        };
        let TypedExprKind::Variable(sym) = &callee.kind else {
            panic!("expected variable callee");
        };
        // Both should reference the specialized version of id
        assert_eq!(*sym, Symbol::Synthesized(SynthesizedId::from(1)));
        assert_eq!(
            *callee_sym,
            Some(Symbol::Synthesized(SynthesizedId::from(1)))
        );
    }
}
