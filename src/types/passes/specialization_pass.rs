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
    node_kinds::inline_ir_instruction::TypedInlineIRInstruction,
    types::{
        row::Row,
        scheme::ForAll,
        ty::{Specializations, Ty},
        type_error::TypeError,
        typed_ast::{
            TypedAST, TypedBlock, TypedExpr, TypedExprKind, TypedFunc, TypedMatchArm,
            TypedRecordField, TypedStmt, TypedStmtKind,
        },
        types::{TypeEntry, Types},
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
            TypedStmtKind::Handler { effect, func } => TypedStmtKind::Handler {
                effect,
                func: self.visit_func(func)?,
            },
            TypedStmtKind::Break => TypedStmtKind::Break,
        };

        Ok(stmt)
    }

    fn visit_expr(&mut self, mut expr: TypedExpr<Ty>) -> Result<TypedExpr<Ty>, TypeError> {
        expr.kind = match expr.kind {
            TypedExprKind::InlineIR(box instr) => {
                TypedExprKind::InlineIR(self.visit_inline_ir(instr)?.into())
            }
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
            TypedExprKind::Block(block) => TypedExprKind::Block(self.visit_block(block)?),
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
            TypedExprKind::Func(func) => TypedExprKind::Func(self.visit_func(func)?),
            TypedExprKind::If(box cond, conseq, alt) => TypedExprKind::If(
                self.visit_expr(cond)?.into(),
                self.visit_block(conseq)?,
                self.visit_block(alt)?,
            ),
            TypedExprKind::Match(box scrutinee, arms) => TypedExprKind::Match(
                self.visit_expr(scrutinee)?.into(),
                arms.into_iter()
                    .map(|a| self.visit_match_arm(a))
                    .try_collect()?,
            ),
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
            kind => kind,
        };

        Ok(expr)
    }

    fn visit_variable(&mut self, name: Symbol) -> Result<TypedExprKind<Ty>, TypeError> {
        if self.current_specializations.is_empty() {
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
            mut callee_sym,
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

        self.apply_explicit_type_args(&callee, &type_args, &mut specializations)?;

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
            callee_sym = Some(specialized_init);
            expr.kind = TypedExprKind::Call {
                callee: callee.into(),
                callee_ty,
                type_args,
                args: args.into_iter().map(|i| self.visit_expr(i)).try_collect()?,
                callee_sym,
            };
        } else {
            let type_args = if type_args.is_empty() {
                specializations.ty.values().cloned().collect()
            } else {
                type_args
            };

            self.current_specializations.push(specializations.clone());
            let caller = self.symbol_for_callee(&callee, &expr.ty, &specializations)?;
            let mut specialized_callee = self.visit_expr(callee.clone())?;
            callee_sym = Some(self.specialize(&caller, &specializations));
            self.specialize_callees(caller, &specializations)?;
            self.current_specializations.pop();

            let mut args: Vec<_> = args.into_iter().map(|i| self.visit_expr(i)).try_collect()?;

            if let TypedExprKind::Member { receiver, .. } = callee.kind {
                if !matches!(receiver.kind, TypedExprKind::Constructor(..)) {
                    args.insert(0, *receiver);
                }
                specialized_callee = TypedExpr {
                    id: callee.id,
                    ty: callee.ty,
                    kind: TypedExprKind::Variable(callee_sym.unwrap_or_else(|| unreachable!())),
                };
            } else if matches!(callee.kind, TypedExprKind::Variable(..)) {
                callee.kind = TypedExprKind::Variable(callee_sym.unwrap_or_else(|| unreachable!()));
            }

            expr.kind = TypedExprKind::Call {
                callee: specialized_callee.into(),
                callee_ty,
                type_args,
                args: args.into_iter().map(|i| self.visit_expr(i)).try_collect()?,
                callee_sym,
            };
        }

        Ok(expr)
    }

    fn visit_block(&mut self, block: TypedBlock<Ty>) -> Result<TypedBlock<Ty>, TypeError> {
        Ok(block)
    }

    fn visit_func(&mut self, func: TypedFunc<Ty>) -> Result<TypedFunc<Ty>, TypeError> {
        Ok(func)
    }

    fn visit_match_arm(
        &mut self,
        match_arm: TypedMatchArm<Ty>,
    ) -> Result<TypedMatchArm<Ty>, TypeError> {
        Ok(match_arm)
    }

    fn visit_inline_ir(
        &mut self,
        instr: TypedInlineIRInstruction<Ty>,
    ) -> Result<TypedInlineIRInstruction<Ty>, TypeError> {
        Ok(instr)
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
            if let Ty::Param(id) = param {
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

                let receiver_sym = if matches!(receiver.kind, TypedExprKind::Hole) {
                    // If it's an unqualified member (like .foo instead of Fizz.foo) then the receiver is
                    // Hole so we just take the type of the call (since enum constructors always return the enum)
                    self.symbol_from_ty(call_ty, specializations)?
                } else {
                    self.symbol_from_ty(receiver_ty.as_mono_ty(), specializations)?
                };

                if let Some((sym, _)) = self.types.catalog.lookup_member(&receiver_sym, label) {
                    Ok(sym)
                } else if let Some(sym) = self
                    .types
                    .catalog
                    .lookup_static_member(&receiver_sym, label)
                {
                    Ok(sym)
                } else {
                    Err(TypeError::MemberNotFound(
                        receiver.ty.clone().into(),
                        label.to_string(),
                    ))
                }
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
        type_args: &[Ty],
        specializations: &mut Specializations,
    ) -> Result<(), TypeError> {
        if type_args.is_empty() {
            return Ok(());
        }

        let callee_sym = self.symbol_for_callee(callee, &callee.ty, specializations)?;
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
        if let Some(callees) = self.resolved_names.call_tree.lookup(&caller).cloned() {
            for callee in callees {
                let callee_sym = match callee {
                    RawCallee::Symbol(symbol) => symbol,
                    RawCallee::Member { receiver_id, label } => {
                        let Some(ty) = self.types.get(&receiver_id) else {
                            return Ok(());
                        };

                        match self.symbol_from_ty(ty.as_mono_ty(), specializations) {
                            Ok(sym) => sym,
                            Err(..) => {
                                return Err(TypeError::MemberNotFound(
                                    Ty::Void.into(),
                                    label.to_string(),
                                ));
                            }
                        }
                    }
                    RawCallee::Unqualified { .. } => unimplemented!(),
                };

                self.specialize(&callee_sym, specializations);
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
                    ty: indexmap! { 2.into() => Ty::Int },
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
                    ty: indexmap! { 2.into() => Ty::Int },
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
                        Ty::Param(2.into()).into(),
                        Ty::Param(2.into()).into(),
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
