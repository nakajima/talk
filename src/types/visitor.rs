use std::collections::BTreeMap;

use tracing::trace_span;

use crate::{
    ExprMetaStorage, SymbolID, builtins,
    expr_id::ExprID,
    name::Name,
    parsed_expr::{self, IncompleteExpr, ParsedExpr},
    token_kind::TokenKind,
    type_checker::TypeError,
    types::{
        constraint::{Constraint, ConstraintCause, ConstraintKind, ConstraintState},
        constraint_set::{ConstraintId, ConstraintSet},
        row::RowVar,
        ty::{Primitive, Ty},
        type_checking_session::ExprIDTypeMap,
        type_var::{TypeVar, TypeVarKind},
        type_var_context::TypeVarContext,
    },
};

pub type Scope = BTreeMap<SymbolID, Ty>;

#[derive(Debug)]
struct VisitorContext {
    scopes: Vec<Scope>,
    // Stack of generic constraints being collected for each function scope
    generic_constraints_stack: Vec<Vec<ConstraintKind>>,
}

impl Default for VisitorContext {
    fn default() -> Self {
        Self {
            scopes: vec![builtins::default_type_checker_scope()], // Default scope
            generic_constraints_stack: vec![],
        }
    }
}

impl VisitorContext {
    fn start_scope(&mut self) {
        self.scopes.push(Scope::new())
    }

    fn end_scope(&mut self) {
        self.scopes.pop();
    }

    fn start_generic_function(&mut self) {
        self.generic_constraints_stack.push(vec![]);
    }

    fn end_generic_function(&mut self) -> Vec<ConstraintKind> {
        self.generic_constraints_stack.pop().unwrap_or_default()
    }

    fn add_generic_constraint(&mut self, constraint: ConstraintKind) {
        if let Some(constraints) = self.generic_constraints_stack.last_mut() {
            constraints.push(constraint);
        }
    }

    fn in_generic_function(&self) -> bool {
        !self.generic_constraints_stack.is_empty()
    }

    fn lookup(&mut self, name: &Name) -> Result<Ty, TypeError> {
        let symbol_id = name.symbol_id()?;

        if let Some(ty) = self
            .scopes
            .iter()
            .rev()
            .find_map(|frame| frame.get(&symbol_id))
        {
            return Ok(ty.clone());
        }

        Err(TypeError::Unknown(format!(
            "Undefined symbol: {}",
            name.name_str()
        )))
    }

    fn declare(&mut self, symbol_id: &SymbolID, ty: &Ty) -> Result<(), TypeError> {
        if let Some(ty) = self
            .scopes
            .last()
            .ok_or(TypeError::Unknown(format!(
                "Unable to declare symbol {symbol_id:?} without scope"
            )))?
            .get(symbol_id)
        {
            tracing::warn!("Already declared {symbol_id:?} in scope: {ty:?}");
        }

        self.scopes
            .last_mut()
            .ok_or(TypeError::Unknown(format!(
                "Unable to declare symbol {symbol_id:?} without scope"
            )))?
            .insert(*symbol_id, ty.clone());

        Ok(())
    }
}

#[derive(Debug)]
pub struct Visitor<'a> {
    type_var_context: &'a mut TypeVarContext,
    constraints: &'a mut ConstraintSet,
    expr_id_types: &'a mut ExprIDTypeMap,
    context: VisitorContext,
    meta: &'a ExprMetaStorage,
}

#[allow(clippy::todo)]
impl<'a> Visitor<'a> {
    pub fn new(
        type_var_context: &'a mut TypeVarContext,
        constraints: &'a mut ConstraintSet,
        expr_id_types: &'a mut ExprIDTypeMap,
        meta: &'a ExprMetaStorage,
    ) -> Self {
        Self {
            type_var_context,
            constraints,
            context: VisitorContext::default(),
            expr_id_types,
            meta,
        }
    }

    pub fn new_type_var(&mut self) -> TypeVar {
        self.type_var_context.new_var(TypeVarKind::None)
    }

    pub fn new_row_var(&mut self) -> RowVar {
        self.type_var_context.new_row_var()
    }

    pub fn new_canonical_type_var(&mut self) -> TypeVar {
        self.type_var_context.new_var(TypeVarKind::Canonical)
    }

    pub fn new_instantiated_type_var(&mut self) -> TypeVar {
        self.type_var_context.new_var(TypeVarKind::Instantiated)
    }

    pub fn declare(&mut self, symbol_id: &SymbolID, ty: Ty) -> Result<(), TypeError> {
        self.context.declare(symbol_id, &ty)
    }

    pub fn constrain(
        &mut self,
        expr_id: ExprID,
        kind: ConstraintKind,
        cause: ConstraintCause,
    ) -> Result<ConstraintId, TypeError> {
        let id = self.constraints.next_id();

        tracing::trace!("Constraining {id:?} kind: {kind:?} cause: {cause:?}");

        // If this constraint involves canonical type variables and we're in a generic function,
        // track it for later enforcement
        if kind.contains_canonical_var() && self.context.in_generic_function() {
            self.context.add_generic_constraint(kind.clone());
        }

        self.constraints.add(Constraint {
            id,
            expr_id,
            cause,
            kind,
            parent: None,
            children: vec![],
            state: ConstraintState::Pending,
        });

        Ok(id)
    }

    pub fn add_child(&mut self, parent: ConstraintId, child: ConstraintId) {
        if let Some(c) = self.constraints.find_mut(&parent) {
            c.children.push(child)
        }
    }

    pub fn visit_mult(&mut self, parsed: &[ParsedExpr]) -> Result<Vec<Ty>, TypeError> {
        let mut typed = vec![];
        for expr in parsed {
            typed.push(self.visit(expr)?);
        }
        Ok(typed)
    }

    pub fn visit(&mut self, parsed: &ParsedExpr) -> Result<Ty, TypeError> {
        let _s = trace_span!(
            "visit",
            expr = crate::formatter::Formatter::format_single_expr(self.meta, parsed)
        )
        .entered();

        match &parsed.expr {
            parsed_expr::Expr::Incomplete(incomplete_expr) => {
                self.visit_incomplete(parsed, incomplete_expr)
            }
            parsed_expr::Expr::Attribute(name) => self.visit_attribute(parsed, name),
            parsed_expr::Expr::LiteralArray(parsed_exprs) => {
                self.visit_literal_array(parsed, parsed_exprs)
            }
            parsed_expr::Expr::LiteralInt(_value) => self.visit_literal_int(parsed),
            parsed_expr::Expr::LiteralFloat(_value) => self.visit_literal_float(parsed),
            parsed_expr::Expr::LiteralTrue => self.visit_literal_true(parsed),
            parsed_expr::Expr::LiteralFalse => self.visit_literal_false(parsed),
            parsed_expr::Expr::LiteralString(value) => self.visit_literal_string(parsed, value),
            parsed_expr::Expr::Unary(token_kind, rhs) => self.visit_unary(parsed, token_kind, rhs),
            parsed_expr::Expr::Binary(lhs, token_kind, rhs) => {
                self.visit_binary(parsed, lhs, token_kind, rhs)
            }
            parsed_expr::Expr::Tuple(items) => self.visit_tuple(parsed, items),
            parsed_expr::Expr::Block(items) => self.visit_block(parsed, items),
            parsed_expr::Expr::Call {
                callee,
                type_args,
                args,
            } => self.visit_call(parsed, callee, type_args, args),
            parsed_expr::Expr::ParsedPattern(pattern) => self.visit_parsed_pattern(parsed, pattern),
            parsed_expr::Expr::Return(parsed_expr) => self.visit_return(parsed, parsed_expr),
            parsed_expr::Expr::Break => self.visit_break(parsed),
            parsed_expr::Expr::Extend {
                name,
                generics,
                conformances,
                body,
            } => self.visit_extend(parsed, name, generics, conformances, body),
            parsed_expr::Expr::Struct {
                name,
                generics,
                conformances,
                body,
            } => self.visit_struct(parsed, name, generics, conformances, body),
            parsed_expr::Expr::Property {
                name,
                type_repr,
                default_value,
            } => self.visit_property(parsed, name, type_repr, default_value),
            parsed_expr::Expr::TypeRepr {
                name,
                generics,
                conformances,
                introduces_type,
            } => self.visit_type_repr(parsed, name, generics, conformances, *introduces_type),
            parsed_expr::Expr::FuncTypeRepr(params, ret, introduces_type) => {
                self.visit_func_type_repr(parsed, params, ret, *introduces_type)
            }
            parsed_expr::Expr::TupleTypeRepr(items, introduces_type) => {
                self.visit_tuple_type_repr(parsed, items, *introduces_type)
            }
            parsed_expr::Expr::Member(Some(box receiver), name) => {
                self.visit_member(parsed, Some(receiver), name)
            }
            parsed_expr::Expr::Member(None, name) => self.visit_member(parsed, None, name),
            parsed_expr::Expr::Init(symbol_id, func) => self.visit_init(parsed, *symbol_id, func),
            parsed_expr::Expr::Func {
                name,
                generics,
                params,
                body,
                ret,
                captures,
                attributes,
            } => self.visit_func(
                parsed, name, generics, params, body, ret, captures, attributes,
            ),
            parsed_expr::Expr::Parameter(name, annotation) => {
                self.visit_parameter(parsed, name, annotation)
            }
            parsed_expr::Expr::CallArg { label, value } => {
                self.visit_call_arg(parsed, label, value)
            }
            parsed_expr::Expr::Let(name, annotation) => self.visit_let(parsed, name, annotation),
            parsed_expr::Expr::Assignment(lhs, rhs) => self.visit_assignment(parsed, lhs, rhs),
            parsed_expr::Expr::Variable(name) => self.visit_variable(parsed, name),
            parsed_expr::Expr::If(cond, conseq, alt) => self.visit_if(parsed, cond, conseq, alt),
            parsed_expr::Expr::Loop(cond, body) => self.visit_loop(parsed, cond, body),
            parsed_expr::Expr::EnumDecl {
                name,
                conformances,
                generics,
                body,
            } => self.visit_enum_decl(parsed, name, conformances, generics, body),
            parsed_expr::Expr::EnumVariant(name, values) => {
                self.visit_enum_variant(parsed, name, values)
            }
            parsed_expr::Expr::Match(scrutinee, arms) => self.visit_match(parsed, scrutinee, arms),
            parsed_expr::Expr::MatchArm(pattern, body) => {
                self.visit_match_arm(parsed, pattern, body)
            }
            parsed_expr::Expr::PatternVariant(enum_name, variant_name, values) => {
                self.visit_pattern_variant(parsed, enum_name, variant_name, values)
            }
            parsed_expr::Expr::RecordLiteral(fields) => self.visit_record_literal(parsed, fields),
            parsed_expr::Expr::RecordField { label, value } => {
                self.visit_record_field(parsed, label, value)
            }
            parsed_expr::Expr::RecordTypeRepr {
                fields,
                row_var,
                introduces_type,
            } => self.visit_record_type_repr(parsed, fields, row_var, *introduces_type),
            parsed_expr::Expr::RecordTypeField { label, ty } => {
                self.visit_record_type_field(parsed, label, ty)
            }
            parsed_expr::Expr::RowVariable(name) => self.visit_row_variable(parsed, name),
            parsed_expr::Expr::Spread(parsed_expr) => self.visit_spread(parsed, parsed_expr),
            parsed_expr::Expr::ProtocolDecl {
                name,
                associated_types,
                body,
                conformances,
            } => self.visit_protocol_decl(parsed, name, associated_types, body, conformances),
            parsed_expr::Expr::FuncSignature {
                name,
                params,
                generics,
                ret,
            } => self.visit_func_signature(parsed, name, params, generics, ret),
            parsed_expr::Expr::Import(module_name) => self.visit_import(parsed, module_name),
        }
    }

    fn visit_incomplete(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _incomplete_expr: &IncompleteExpr,
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_attribute(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _name: &Name,
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_literal_array(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _parsed_exprs: &[ParsedExpr],
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_literal_int(&mut self, parsed_expr: &ParsedExpr) -> Result<Ty, TypeError> {
        let ty = Ty::Var(self.type_var_context.new_var(TypeVarKind::IntLiteral));

        self.constrain(
            parsed_expr.id,
            ConstraintKind::LiteralPrimitive(ty.clone(), Primitive::Int),
            ConstraintCause::PrimitiveLiteral(parsed_expr.id, Primitive::Int),
        )?;

        Ok(ty)
    }

    fn visit_literal_float(&mut self, parsed_expr: &ParsedExpr) -> Result<Ty, TypeError> {
        let ty = Ty::Var(self.type_var_context.new_var(TypeVarKind::FloatLiteral));

        self.constrain(
            parsed_expr.id,
            ConstraintKind::LiteralPrimitive(ty.clone(), Primitive::Float),
            ConstraintCause::PrimitiveLiteral(parsed_expr.id, Primitive::Float),
        )?;

        Ok(ty)
    }

    fn visit_literal_true(&mut self, parsed_expr: &ParsedExpr) -> Result<Ty, TypeError> {
        self.expr_id_types.insert(parsed_expr.id, Ty::Bool);

        Ok(Ty::Bool)
    }

    fn visit_literal_false(&mut self, parsed_expr: &ParsedExpr) -> Result<Ty, TypeError> {
        self.expr_id_types.insert(parsed_expr.id, Ty::Bool);

        Ok(Ty::Bool)
    }

    fn visit_literal_string(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _value: &str,
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_unary(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _token_kind: &TokenKind,
        _rhs: &ParsedExpr,
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_binary(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _lhs: &ParsedExpr,
        _token_kind: &TokenKind,
        _rhs: &ParsedExpr,
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_tuple(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _items: &[ParsedExpr],
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_block(
        &mut self,
        parsed_expr: &ParsedExpr,
        items: &[ParsedExpr],
    ) -> Result<Ty, TypeError> {
        let mut ret = Ty::Void;

        for (i, item) in items.iter().enumerate() {
            let ty = self.visit(item)?;
            if i == items.len() - 1 {
                ret = ty;
            }
        }

        self.expr_id_types.insert(parsed_expr.id, ret.clone());

        Ok(ret)
    }

    fn visit_call(
        &mut self,
        parsed_expr: &ParsedExpr,
        callee: &ParsedExpr,
        type_args: &[ParsedExpr],
        args: &[ParsedExpr],
    ) -> Result<Ty, TypeError> {
        let substitutions = &mut Default::default();
        let callee = self
            .visit(callee)?
            .instantiate(self.type_var_context, substitutions);
        let type_args = self
            .visit_mult(type_args)?
            .iter()
            .map(|arg| arg.instantiate(self.type_var_context, substitutions))
            .collect();
        let args = self
            .visit_mult(args)?
            .iter()
            .map(|arg| arg.instantiate(self.type_var_context, substitutions))
            .collect();

        let returning = Ty::Var(self.new_type_var());

        self.constrain(
            parsed_expr.id,
            ConstraintKind::Call {
                callee,
                type_args,
                args,
                returning: returning.clone(),
            },
            ConstraintCause::Call,
        )?;

        Ok(returning)
    }

    fn visit_parsed_pattern(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _pattern: &parsed_expr::Pattern,
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_return(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _ret_expr: &Option<Box<ParsedExpr>>,
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_break(&mut self, _parsed_expr: &ParsedExpr) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_extend(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _name: &Name,
        _generics: &[ParsedExpr],
        _conformances: &[ParsedExpr],
        _body: &ParsedExpr,
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_struct(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _name: &Name,
        _generics: &[ParsedExpr],
        _conformances: &[ParsedExpr],
        _body: &ParsedExpr,
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_property(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _name: &Name,
        _type_repr: &Option<Box<ParsedExpr>>,
        _default_value: &Option<Box<ParsedExpr>>,
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_type_repr(
        &mut self,
        parsed_expr: &ParsedExpr,
        name: &Name,
        _generics: &[ParsedExpr],
        _conformances: &[ParsedExpr],
        introduces_type: bool,
    ) -> Result<Ty, TypeError> {
        if introduces_type {
            let ty = Ty::Var(self.new_canonical_type_var());
            self.context.declare(&name.symbol_id()?, &ty)?;
            return Ok(ty);
        }

        let ty = self.context.lookup(name)?;

        self.expr_id_types.insert(parsed_expr.id, ty.clone());

        Ok(ty)
    }

    fn visit_func_type_repr(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _params: &[ParsedExpr],
        _ret: &ParsedExpr,
        _introduces_type: bool,
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_tuple_type_repr(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _items: &[ParsedExpr],
        _introduces_type: bool,
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_member(
        &mut self,
        parsed_expr: &ParsedExpr,
        receiver: Option<&ParsedExpr>,
        name: &str,
    ) -> Result<Ty, TypeError> {
        match receiver {
            Some(receiver) => {
                let receiver_ty = self.visit(receiver)?;
                let var = self.new_type_var();
                self.constrain(
                    parsed_expr.id,
                    ConstraintKind::HasField {
                        record: receiver_ty,
                        label: name.to_string(),
                        ty: Ty::Var(var),
                    },
                    ConstraintCause::MemberAccess,
                )?;

                Ok(Ty::Var(var))
            }
            None => {
                todo!()
            }
        }
    }

    fn visit_init(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _symbol_id: Option<SymbolID>,
        _func: &ParsedExpr,
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    #[allow(clippy::too_many_arguments)]
    fn visit_func(
        &mut self,
        parsed_expr: &ParsedExpr,
        name: &Option<Name>,
        generics: &[ParsedExpr],
        params: &[ParsedExpr],
        body: &ParsedExpr,
        ret: &Option<Box<ParsedExpr>>,
        _captures: &[SymbolID],
        _attributes: &[ParsedExpr],
    ) -> Result<Ty, TypeError> {
        self.context.start_scope();

        // Always start tracking constraints for functions - we'll determine if it's generic
        // based on whether any canonical vars are used
        self.context.start_generic_function();

        for generic in generics {
            self.visit(generic)?;
        }

        let mut typed_params = vec![];
        for param in params {
            typed_params.push(self.visit(param)?)
        }

        let body_ty = self.visit(body)?;

        let typed_ret = if let Some(ret) = ret {
            let annotated_ty = self.visit(ret)?;
            self.constrain(
                ret.id,
                ConstraintKind::Equals(body_ty, annotated_ty.clone()),
                ConstraintCause::Annotation(ret.id),
            )?;
            annotated_ty
        } else {
            // For functions without explicit return types, check if the body type
            // contains canonical vars (making this a generic function)
            let ty = if body_ty.contains_canonical_var() {
                // This is a generic function, use a canonical var for the return type
                Ty::Var(self.new_canonical_type_var())
            } else {
                // Regular function, use a normal type var
                Ty::Var(self.new_type_var())
            };
            self.constrain(
                body.id,
                ConstraintKind::Equals(body_ty, ty.clone()),
                ConstraintCause::FuncReturn(body.id),
            )?;
            ty
        };

        self.context.end_scope();

        // Collect any generic constraints that were generated
        let generic_constraints = self.context.end_generic_function();

        let func_ty = Ty::Func {
            params: typed_params,
            returns: Box::new(typed_ret),
            generic_constraints,
        };

        self.expr_id_types.insert(parsed_expr.id, func_ty.clone());

        if let Some(name) = name {
            let Ty::Var(hoisted_ty) = self.context.lookup(name)? else {
                unreachable!()
            };

            // We should unify the hoisted ty with the new one
            self.type_var_context
                .unify_var_ty(hoisted_ty, func_ty.clone())?;
        }

        Ok(func_ty)
    }

    fn visit_parameter(
        &mut self,
        parsed_expr: &ParsedExpr,
        name: &Name,
        annotation: &Option<Box<ParsedExpr>>,
    ) -> Result<Ty, TypeError> {
        let param_ty = if let Some(hoisted) = self.expr_id_types.get(&parsed_expr.id) {
            hoisted.clone()
        } else if let Some(annotation) = annotation {
            self.visit(annotation)?
        } else {
            Ty::Var(self.new_canonical_type_var())
        };

        self.context.declare(&name.symbol_id()?, &param_ty)?;
        self.expr_id_types.insert(parsed_expr.id, param_ty.clone());

        Ok(param_ty)
    }

    fn visit_call_arg(
        &mut self,
        parsed_expr: &ParsedExpr,
        _label: &Option<Name>,
        value: &ParsedExpr,
    ) -> Result<Ty, TypeError> {
        let ty = self.visit(value)?;
        self.expr_id_types.insert(parsed_expr.id, ty.clone());
        Ok(ty)
    }

    fn visit_let(
        &mut self,
        parsed_expr: &ParsedExpr,
        name: &Name,
        annotation: &Option<Box<ParsedExpr>>,
    ) -> Result<Ty, TypeError> {
        let ty = Ty::Var(self.type_var_context.new_var(TypeVarKind::None));

        if let Some(annotation) = annotation {
            let annotation_ty = self.visit(annotation)?;
            self.constrain(
                parsed_expr.id,
                ConstraintKind::Equals(ty.clone(), annotation_ty),
                ConstraintCause::Annotation(annotation.id),
            )?;
        }

        self.context.declare(&name.symbol_id()?, &ty)?;

        Ok(ty)
    }

    fn visit_assignment(
        &mut self,
        parsed_expr: &ParsedExpr,
        lhs: &ParsedExpr,
        rhs: &ParsedExpr,
    ) -> Result<Ty, TypeError> {
        let lhs_ty = self.visit(lhs)?;
        let rhs_ty = self.visit(rhs)?;

        self.constrain(
            parsed_expr.id,
            ConstraintKind::Equals(lhs_ty.clone(), rhs_ty),
            ConstraintCause::Assignment(parsed_expr.id),
        )?;

        Ok(lhs_ty)
    }

    fn visit_variable(&mut self, parsed_expr: &ParsedExpr, name: &Name) -> Result<Ty, TypeError> {
        let scope_ty = self.context.lookup(name)?;
        self.expr_id_types.insert(parsed_expr.id, scope_ty.clone());
        Ok(scope_ty)
    }

    fn visit_if(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _cond: &ParsedExpr,
        _conseq: &ParsedExpr,
        _alt: &Option<Box<ParsedExpr>>,
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_loop(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _cond: &Option<Box<ParsedExpr>>,
        _body: &ParsedExpr,
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_enum_decl(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _name: &Name,
        _conformances: &[ParsedExpr],
        _generics: &[ParsedExpr],
        _body: &ParsedExpr,
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_enum_variant(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _name: &Name,
        _values: &[ParsedExpr],
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_match(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _scrutinee: &ParsedExpr,
        _arms: &[ParsedExpr],
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_match_arm(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _pattern: &ParsedExpr,
        _body: &ParsedExpr,
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_pattern_variant(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _enum_name: &Option<Name>,
        _variant_name: &Name,
        _values: &[ParsedExpr],
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_record_literal(
        &mut self,
        parsed_expr: &ParsedExpr,
        fields: &[ParsedExpr],
    ) -> Result<Ty, TypeError> {
        let var = self.new_type_var();

        let constraint_id = self.constrain(
            parsed_expr.id,
            ConstraintKind::RowClosed {
                record: Ty::Var(var),
            },
            ConstraintCause::RecordLiteral,
        )?;

        for field in fields {
            let field_ty = self.visit(field)?;
            let Ty::Label(label, value) = &field_ty else {
                return Err(TypeError::UnexpectedType(
                    "record field".to_string(),
                    field_ty.to_string(),
                ));
            };

            let child_id = self.constrain(
                field.id,
                ConstraintKind::HasField {
                    record: Ty::Var(var),
                    label: label.to_string(),
                    ty: *value.clone(),
                },
                ConstraintCause::RecordLiteral,
            )?;

            self.add_child(constraint_id, child_id);
        }

        self.expr_id_types.insert(parsed_expr.id, Ty::Var(var));

        Ok(Ty::Var(var))
    }

    fn visit_record_field(
        &mut self,
        parsed_expr: &ParsedExpr,
        label: &Name,
        value: &ParsedExpr,
    ) -> Result<Ty, TypeError> {
        let value = self.visit(value)?;
        let field_ty = Ty::Label(label.name_str(), Box::new(value));
        self.expr_id_types.insert(parsed_expr.id, field_ty.clone());
        Ok(field_ty)
    }

    fn visit_record_type_repr(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _fields: &[ParsedExpr],
        _row_var: &Option<Box<ParsedExpr>>,
        _introduces_type: bool,
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_record_type_field(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _label: &Name,
        _ty: &ParsedExpr,
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_row_variable(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _name: &Name,
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_spread(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _expr: &ParsedExpr,
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_protocol_decl(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _name: &Name,
        _associated_types: &[ParsedExpr],
        _body: &ParsedExpr,
        _conformances: &[ParsedExpr],
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_func_signature(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _name: &Name,
        _params: &[ParsedExpr],
        _generics: &[ParsedExpr],
        _ret: &ParsedExpr,
    ) -> Result<Ty, TypeError> {
        todo!()
    }

    fn visit_import(
        &mut self,
        _parsed_expr: &ParsedExpr,
        _module_name: &str,
    ) -> Result<Ty, TypeError> {
        todo!()
    }
}
