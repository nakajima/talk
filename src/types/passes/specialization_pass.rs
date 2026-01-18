use indexmap::IndexMap;
use itertools::Itertools;
use rustc_hash::FxHashMap;

use crate::{
    compiling::module::ModuleId,
    label::Label,
    name_resolution::{
        call_tree::RawCallee,
        name_resolver::ResolvedNames,
        symbol::{Symbol, Symbols, set_symbol_names},
    },
    types::{
        row::Row,
        scheme::ForAll,
        ty::{Specializations, Ty},
        type_error::TypeError,
        typed_ast::{
            TypedAST, TypedBlock, TypedDecl, TypedDeclKind, TypedExpr, TypedExprKind, TypedFunc,
            TypedMatchArm, TypedNode, TypedRecordField, TypedStmt, TypedStmtKind,
        },
        types::{TypeEntry, Types},
        variational::DimensionId,
    },
};

#[derive(Clone, Debug, PartialEq)]
pub struct SpecializedCallee {
    pub original_symbol: Symbol,
    pub specializations: Specializations,
}

pub struct SpecializationPass {
    ast: TypedAST<Ty>,
    symbols: Symbols,
    resolved_names: ResolvedNames,
    types: Types,
    pub(crate) specialized_callees: FxHashMap<Symbol, SpecializedCallee>,
    pub(crate) specializations: FxHashMap<Symbol, Vec<Symbol>>,
    current_specializations: Vec<Specializations>,
}

impl SpecializationPass {
    pub fn new(
        ast: TypedAST<Ty>,
        symbols: Symbols,
        resolved_names: ResolvedNames,
        types: Types,
    ) -> Self {
        Self {
            ast,
            symbols,
            resolved_names,
            types,
            specialized_callees: Default::default(),
            specializations: Default::default(),
            current_specializations: Default::default(),
        }
    }

    #[allow(clippy::type_complexity)]
    pub fn drive(
        mut self,
    ) -> Result<
        (
            TypedAST<Ty>,
            Symbols,
            ResolvedNames,
            Types,
            FxHashMap<Symbol, Vec<Symbol>>,
            FxHashMap<Symbol, SpecializedCallee>,
        ),
        TypeError,
    > {
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
            self.specializations,
            self.specialized_callees,
        ))
    }

    fn visit_stmt(&mut self, mut stmt: TypedStmt<Ty>) -> Result<TypedStmt<Ty>, TypeError> {
        stmt.kind = match stmt.kind {
            TypedStmtKind::Expr(expr) => TypedStmtKind::Expr(self.visit_expr(expr)?),
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
            kind => kind,
        };

        Ok(stmt)
    }

    fn visit_decl(&mut self, mut decl: TypedDecl<Ty>) -> Result<TypedDecl<Ty>, TypeError> {
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
        };
        Ok(decl)
    }

    fn visit_methods(
        &mut self,
        methods: IndexMap<Label, TypedFunc<Ty>>,
    ) -> Result<IndexMap<Label, TypedFunc<Ty>>, TypeError> {
        methods
            .into_iter()
            .map(|(label, func)| {
                let body = self.visit_block(func.body)?;
                Ok((label, TypedFunc { body, ..func }))
            })
            .collect()
    }

    fn visit_block(&mut self, block: TypedBlock<Ty>) -> Result<TypedBlock<Ty>, TypeError> {
        let body = block
            .body
            .into_iter()
            .map(|node| self.visit_node(node))
            .try_collect()?;
        Ok(TypedBlock { body, ..block })
    }

    fn visit_node(&mut self, node: TypedNode<Ty>) -> Result<TypedNode<Ty>, TypeError> {
        Ok(match node {
            TypedNode::Stmt(stmt) => TypedNode::Stmt(self.visit_stmt(stmt)?),
            TypedNode::Expr(expr) => TypedNode::Expr(self.visit_expr(expr)?),
            TypedNode::Decl(decl) => TypedNode::Decl(decl), // Decls are already processed at top level
        })
    }

    fn visit_expr(&mut self, mut expr: TypedExpr<Ty>) -> Result<TypedExpr<Ty>, TypeError> {
        // Apply current specializations to the type of this expression
        if !self.current_specializations.is_empty() {
            let specializations = self.collect_specializations();
            expr.ty = specializations.apply(expr.ty);
        }

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
            TypedExprKind::CallEffect { effect, args } => TypedExprKind::CallEffect {
                effect,
                args: args.into_iter().map(|i| self.visit_expr(i)).try_collect()?,
            },
            TypedExprKind::Constructor(name, args) => self.visit_constructor(name, args)?,
            TypedExprKind::Call { .. } => return self.visit_call(expr),
            TypedExprKind::Member {
                box receiver,
                label,
            } => TypedExprKind::Member {
                receiver: self.visit_expr(receiver)?.into(),
                label,
            },
            TypedExprKind::If(box cond, conseq, alt) => TypedExprKind::If(
                self.visit_expr(cond)?.into(),
                self.visit_block(conseq)?,
                self.visit_block(alt)?,
            ),
            TypedExprKind::Match(box scrutinee, arms) => {
                let new_arms = arms
                    .into_iter()
                    .map(|arm| {
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

    fn visit_variable(&mut self, name: Symbol) -> Result<TypedExprKind<Ty>, TypeError> {
        // Don't specialize builtins - they don't have polymorphic implementations
        if self.current_specializations.is_empty() || matches!(name, Symbol::Builtin(..)) {
            return Ok(TypedExprKind::Variable(name));
        }

        let specializations = self.collect_specializations();
        let new_symbol = self.specialize(&name, &specializations);

        Ok(TypedExprKind::Variable(new_symbol))
    }

    fn visit_constructor(
        &mut self,
        name: Symbol,
        args: Vec<Ty>,
    ) -> Result<TypedExprKind<Ty>, TypeError> {
        if self.current_specializations.is_empty() {
            return Ok(TypedExprKind::Constructor(name, args));
        }

        let specializations = self.collect_specializations();
        let new_symbol = self.specialize(&name, &specializations);

        Ok(TypedExprKind::Constructor(new_symbol, args))
    }

    fn visit_call(&mut self, mut expr: TypedExpr<Ty>) -> Result<TypedExpr<Ty>, TypeError> {
        let TypedExprKind::Call {
            box mut callee,
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

        if is_constructor
            && let TypedExprKind::Constructor(symbol, ..) = &callee.kind
            && let Some(init_sym) = self
                .types
                .catalog
                .initializers
                .get(symbol)
                .and_then(|inits| inits.get(&Label::Named("init".into())))
                .copied()
        {
            let specialized_init = self.specialize(&init_sym, &specializations);
            expr.kind = TypedExprKind::Call {
                callee: callee.into(),
                callee_ty,
                type_args,
                args: args.into_iter().map(|i| self.visit_expr(i)).try_collect()?,
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
                args: args.into_iter().map(|i| self.visit_expr(i)).try_collect()?,
                callee_sym: None,
            };
        } else {
            let type_args = if type_args.is_empty() {
                specializations.ty.values().cloned().collect()
            } else {
                type_args
            };

            self.current_specializations.push(specializations.clone());

            // Use accumulated specializations for resolving type params in nested calls
            let accumulated_specs = self.collect_specializations();
            let caller_result = self.symbol_for_callee(&callee, &expr.ty, &accumulated_specs);

            // If we can't resolve the callee (e.g., method on unspecialized type param),
            // just visit the expression tree without specialization.
            // The monomorphizer will handle this when the function is instantiated.
            let Ok(mut caller) = caller_result else {
                self.current_specializations.pop();

                let specialized_callee = self.visit_expr(callee.clone())?;
                let args: Vec<_> = args.into_iter().map(|i| self.visit_expr(i)).try_collect()?;

                expr.kind = TypedExprKind::Call {
                    callee: specialized_callee.into(),
                    callee_ty,
                    type_args,
                    args: args.into_iter().map(|i| self.visit_expr(i)).try_collect()?,
                    callee_sym: None, // Will be resolved at monomorphization
                };
                return Ok(expr);
            };

            // Handle protocol method resolution
            if let TypedExprKind::Member { receiver, label } = &callee.kind {
                // Check for direct protocol method calls: Protocol.method(arg1, arg2, ...)
                // In this case, the actual receiver is the first argument
                if let TypedExprKind::Constructor(Symbol::Protocol(protocol_id), _) =
                    &receiver.kind
                {
                    // This is a direct protocol method call like Add.add(1, 2)
                    // The conforming type comes from the first argument
                    if let Some(first_arg) = args.first() {
                        let arg_ty = accumulated_specs.apply(first_arg.ty.clone());
                        if let Ok(conforming_sym) =
                            self.symbol_from_ty(&arg_ty, &accumulated_specs)
                        {
                            // Look up the witness in conformances
                            let key = crate::types::conformance::ConformanceKey {
                                protocol_id: *protocol_id,
                                conforming_id: conforming_sym,
                            };
                            if let Some(conformance) = self.types.catalog.conformances.get(&key) {
                                if let Some(witness) =
                                    conformance.witnesses.methods.get(label).copied().or_else(
                                        || conformance.witnesses.requirements.get(&caller).copied(),
                                    )
                                {
                                    caller = witness;
                                }
                            }
                        }
                    }
                } else {
                    // Regular member access - use Resolution, then ChoiceStore for monomorphization
                    let dimension = DimensionId(callee.id);

                    if let Some(resolved_alt) = self.types.resolution.get(&dimension) {
                        // Use the resolved alternative from variational type checking
                        if let Some(alt) =
                            self.types.choices.get_alternative(dimension, resolved_alt)
                        {
                            caller = alt.witness_sym;
                        }
                    } else if self.types.choices.dimension_size(&dimension) > 0 {
                        // Monomorphization: resolve based on concrete receiver type
                        let receiver_ty = accumulated_specs.apply(receiver.ty.clone());
                        if let Ok(receiver_sym) =
                            self.symbol_from_ty(&receiver_ty, &accumulated_specs)
                        {
                            if let Some(witness_sym) =
                                self.types.choices.resolve_for_type(dimension, receiver_sym)
                            {
                                caller = witness_sym;
                            }
                        }
                    }
                }
            }

            let mut specialized_callee = self.visit_expr(callee.clone())?;
            let callee_sym = self.specialize(&caller, &accumulated_specs);
            self.specialize_callees(caller, &accumulated_specs)?;
            self.current_specializations.pop();

            let mut args: Vec<_> = args.into_iter().map(|i| self.visit_expr(i)).try_collect()?;

            if let TypedExprKind::Member { receiver, .. } = callee.kind {
                // Don't convert enum variant constructors to Variable - the lowerer needs the Member
                // expression to identify them as enum constructors
                let is_enum_variant = matches!(caller, Symbol::Variant(..));

                // Don't add receiver as first arg for enum constructors or unqualified variants (Hole)
                if !matches!(
                    receiver.kind,
                    TypedExprKind::Constructor(..) | TypedExprKind::Hole
                ) {
                    args.insert(0, *receiver);
                }

                if !is_enum_variant {
                    specialized_callee = TypedExpr {
                        id: callee.id,
                        ty: callee.ty,
                        kind: TypedExprKind::Variable(callee_sym),
                    };
                }
            } else if matches!(callee.kind, TypedExprKind::Variable(..)) {
                callee.kind = TypedExprKind::Variable(callee_sym);
            }

            expr.kind = TypedExprKind::Call {
                callee: specialized_callee.into(),
                callee_ty,
                type_args,
                args: args.into_iter().map(|i| self.visit_expr(i)).try_collect()?,
                callee_sym: Some(callee_sym),
            };
        }

        Ok(expr)
    }

    fn constructor_specializations(&self, callee: &TypedExpr<Ty>, call_ty: &Ty) -> Specializations {
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

    fn symbol_for_callee(
        &self,
        callee: &TypedExpr<Ty>,
        call_ty: &Ty,
        specializations: &Specializations,
    ) -> Result<Symbol, TypeError> {
        match &callee.kind {
            TypedExprKind::Variable(name) => Ok(*name),
            TypedExprKind::Constructor(symbol, ..) => Ok(*symbol),
            TypedExprKind::Func(func) => Ok(func.name),
            TypedExprKind::LiteralArray(..) => Ok(Symbol::Array),
            TypedExprKind::LiteralString(..) => Ok(Symbol::String),
            TypedExprKind::LiteralInt(..) => Ok(Symbol::Int),
            TypedExprKind::LiteralFloat(..) => Ok(Symbol::Float),
            TypedExprKind::LiteralTrue | TypedExprKind::LiteralFalse => Ok(Symbol::Bool),
            TypedExprKind::Member { receiver, label } => {
                let Some(receiver_ty) = self.types.get(&receiver.id) else {
                    return Err(TypeError::TypeNotFound(format!(
                        "could not find type for id: {:?}",
                        receiver.id
                    )));
                };

                // Try to get the receiver symbol, applying specializations
                let receiver_sym_result = if matches!(receiver.kind, TypedExprKind::Hole) {
                    // If it's an unqualified member (like .foo instead of Fizz.foo) then the receiver is
                    // Hole so we just take the type of the call (since enum constructors always return the enum)
                    self.symbol_from_ty(call_ty, specializations)
                } else {
                    self.symbol_from_ty(receiver_ty.as_mono_ty(), specializations)
                };

                // If we got a concrete receiver symbol, try normal member lookup
                if let Ok(receiver_sym) = receiver_sym_result {
                    if let Some((sym, _)) = self.types.catalog.lookup_member(&receiver_sym, label) {
                        return Ok(sym);
                    } else if let Some(sym) = self
                        .types
                        .catalog
                        .lookup_static_member(&receiver_sym, label)
                    {
                        return Ok(sym);
                    }
                }

                // If receiver is a type param that wasn't specialized, this is likely a protocol
                // method call inside a generic function. Return a MethodRequirement placeholder
                // that the monomorphizer will resolve at instantiation time.
                if let Ty::Param(_param_id, protocol_bounds) =
                    specializations.apply(receiver_ty.as_mono_ty().clone())
                {
                    // Look up the method requirement from the protocol bounds
                    for protocol_id in protocol_bounds {
                        if let Some((req_sym, _)) =
                            self.types.catalog.lookup_member(&protocol_id.into(), label)
                        {
                            return Ok(req_sym);
                        }
                    }

                    // For type params without protocol bounds (duck typing),
                    // we can't resolve the method at specialization time.
                    // Return an error that will be handled by returning a placeholder.
                    // The monomorphizer will resolve this when the function is instantiated.
                    // For now, we look up if there's a predicate member and use that.
                    // This is a fallback for structural polymorphism.
                }

                Err(TypeError::MemberNotFound(
                    receiver.ty.clone().into(),
                    label.to_string(),
                ))
            }
            _ => Err(TypeError::CalleeNotCallable(callee.ty.clone().into())),
        }
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
        callee: &TypedExpr<Ty>,
        call_ty: &Ty,
        type_args: &[Ty],
        specializations: &mut Specializations,
    ) -> Result<(), TypeError> {
        if type_args.is_empty() {
            return Ok(());
        }

        let callee_sym = self.symbol_for_callee(callee, call_ty, specializations)?;
        let Some(TypeEntry::Poly(scheme)) = self.types.types_by_symbol.get(&callee_sym) else {
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

    fn specialize_callees(
        &mut self,
        caller: Symbol,
        specializations: &Specializations,
    ) -> Result<(), TypeError> {
        if let Some(callees) = self.types.call_tree.lookup(&caller).cloned() {
            for callee in callees {
                let (callee_sym, callee_specializations) = match callee {
                    RawCallee::Symbol { sym, callee_id } => {
                        // Look up instantiations for this specific call site
                        let mut callee_specs = Specializations::default();
                        if let Some(ty_instantiations) =
                            self.types.catalog.instantiations.ty.get(&callee_id)
                        {
                            for (param, ty) in ty_instantiations {
                                // Apply current specializations to the instantiated type
                                let specialized_ty = specializations.apply(ty.clone());
                                if !matches!(specialized_ty, Ty::Param(..)) {
                                    callee_specs.ty.insert(*param, specialized_ty);
                                }
                            }
                        }
                        if let Some(row_instantiations) =
                            self.types.catalog.instantiations.row.get(&callee_id)
                        {
                            for (param, row) in row_instantiations {
                                // Apply row specializations
                                let specialized_row = if let Row::Param(row_id) = row
                                    && let Some(replacement) = specializations.row.get(row_id)
                                {
                                    replacement.clone()
                                } else {
                                    row.clone()
                                };
                                if !matches!(specialized_row, Row::Param(..)) {
                                    callee_specs.row.insert(*param, specialized_row);
                                }
                            }
                        }
                        (sym, callee_specs)
                    }
                    RawCallee::Member {
                        receiver_id,
                        label,
                        callee_id,
                    } => {
                        let Some(ty) = self.types.get(&receiver_id) else {
                            continue;
                        };

                        // If the receiver is still a type parameter, skip - we can't specialize yet
                        let receiver_sym =
                            match self.symbol_from_ty(ty.as_mono_ty(), specializations) {
                                Ok(sym) => sym,
                                Err(..) => continue,
                            };

                        // Look up the actual member symbol on the receiver
                        let member_sym = if let Some((member_sym, _)) =
                            self.types.catalog.lookup_member(&receiver_sym, &label)
                        {
                            member_sym
                        } else if let Some(member_sym) = self
                            .types
                            .catalog
                            .lookup_static_member(&receiver_sym, &label)
                        {
                            member_sym
                        } else {
                            // Member not found on this receiver - skip
                            continue;
                        };

                        // Look up instantiations for this specific call site
                        let mut callee_specs = Specializations::default();
                        if let Some(ty_instantiations) =
                            self.types.catalog.instantiations.ty.get(&callee_id)
                        {
                            for (param, ty) in ty_instantiations {
                                // Apply current specializations to the instantiated type
                                let specialized_ty = specializations.apply(ty.clone());
                                if !matches!(specialized_ty, Ty::Param(..)) {
                                    callee_specs.ty.insert(*param, specialized_ty);
                                }
                            }
                        }
                        if let Some(row_instantiations) =
                            self.types.catalog.instantiations.row.get(&callee_id)
                        {
                            for (param, row) in row_instantiations {
                                // Apply row specializations
                                let specialized_row = if let Row::Param(row_id) = row
                                    && let Some(replacement) = specializations.row.get(row_id)
                                {
                                    replacement.clone()
                                } else {
                                    row.clone()
                                };
                                if !matches!(specialized_row, Row::Param(..)) {
                                    callee_specs.row.insert(*param, specialized_row);
                                }
                            }
                        }
                        (member_sym, callee_specs)
                    }
                    RawCallee::Unqualified { .. } => unimplemented!(),
                    // Resolved variants - symbol already known
                    RawCallee::Property(sym) | RawCallee::Method(sym) => {
                        (sym, specializations.clone())
                    }
                };

                self.specialize(&callee_sym, &callee_specializations);
            }
        };

        Ok(())
    }

    fn specialize(&mut self, callee_sym: &Symbol, specializations: &Specializations) -> Symbol {
        if specializations.is_empty() {
            return *callee_sym;
        }

        // Get the original
        let ty = self
            .types
            .types_by_symbol
            .get(callee_sym)
            .unwrap_or_else(|| unreachable!("did not get ty for {callee_sym:?}"));

        // Check if applying specializations actually changes the type
        // If not (e.g., for concrete witnesses like Int.add), no wrapper needed
        let mono_ty = ty.as_mono_ty();
        let specialized_ty = specializations.apply(mono_ty.clone());
        if specialized_ty == *mono_ty {
            return *callee_sym;
        }

        let new_sym = self.symbols.next_synthesized(ModuleId::Current);

        // Save the specialized version
        self.types.types_by_symbol.insert(
            new_sym.into(),
            TypeEntry::Mono(specializations.apply(ty.as_mono_ty().clone())),
        );

        // Record the specialization
        self.specializations
            .entry(*callee_sym)
            .or_default()
            .push(new_sym.into());
        self.specialized_callees.insert(
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
            specializations
                .ty
                .values()
                .map(|v| format!("{v}"))
                .join(", ")
        );
        self.resolved_names
            .symbol_names
            .insert(new_sym.into(), new_name);

        new_sym.into()
    }

    fn collect_specializations(&self) -> Specializations {
        self.current_specializations.iter().fold(
            Specializations::default(),
            |mut acc, specializations| {
                acc.extend(specializations.clone());
                acc
            },
        )
    }
}

#[cfg(test)]
pub mod tests {
    use indexmap::indexmap;

    use crate::{
        assert_eq_diff,
        compiling::driver::{Driver, DriverConfig, Source, Typed},
        fxhashmap,
        name_resolution::symbol::{GlobalId, Symbol, SynthesizedId, set_symbol_names},
        node_id::NodeID,
        types::{
            passes::specialization_pass::SpecializedCallee,
            row::Row,
            ty::{Specializations, Ty},
            typed_ast::{TypedExpr, TypedExprKind, TypedStmtKind},
        },
    };

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

        // Make sure we have specializations
        set_symbol_names(typed.resolved_names.symbol_names.clone());
        assert_eq!(
            typed.specializations,
            fxhashmap!( GlobalId::from(1).into() => vec![SynthesizedId::from(3).into()], GlobalId::from(2).into() => vec![SynthesizedId::from(1).into(), SynthesizedId::from(2).into()] )
        );

        assert_eq!(
            *typed
                .specialized_callees
                .get(&SynthesizedId::from(1).into())
                .unwrap(),
            SpecializedCallee {
                original_symbol: GlobalId::from(2).into(),
                specializations: Specializations {
                    ty: indexmap! { 1.into() => Ty::Int },
                    row: Default::default(),
                }
            }
        );

        assert_eq!(
            *typed
                .specialized_callees
                .get(&SynthesizedId::from(2).into())
                .unwrap(),
            SpecializedCallee {
                original_symbol: GlobalId::from(2).into(),
                specializations: Specializations {
                    ty: indexmap! { 1.into() => Ty::Int },
                    row: Default::default(),
                }
            }
        );

        // Make sure we're calling the specialized version
        assert_eq_diff!(
            typed.ast.stmts[0].kind,
            TypedStmtKind::Expr(TypedExpr {
                id: NodeID::ANY,
                ty: Ty::Int,
                kind: TypedExprKind::Call {
                    callee: TypedExpr {
                        id: NodeID::ANY,
                        ty: Ty::Func(Ty::Int.into(), Ty::Int.into(), Row::Param(2.into()).into()),
                        kind: TypedExprKind::Variable(Symbol::Synthesized(SynthesizedId::from(1)))
                    }
                    .into(),
                    callee_ty: Ty::Func(
                        Ty::Param(1.into(), vec![]).into(),
                        Ty::Param(1.into(), vec![]).into(),
                        Row::Param(2.into()).into()
                    ),
                    type_args: vec![Ty::Int],
                    args: vec![TypedExpr {
                        id: NodeID::ANY,
                        ty: Ty::Int,
                        kind: TypedExprKind::LiteralInt("123".into())
                    }],
                    callee_sym: Some(Symbol::Synthesized(SynthesizedId::from(2))),
                }
            })
        )
    }
}
