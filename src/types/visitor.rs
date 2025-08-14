use std::collections::BTreeMap;

use tracing::trace_span;

use crate::{
    ExprMetaStorage, SymbolID, SymbolTable, builtins,
    expr_id::ExprID,
    name::Name,
    parsed_expr::{self, IncompleteExpr, ParsedExpr},
    token_kind::TokenKind,
    type_checker::TypeError,
    types::{
        constraint::{Constraint, ConstraintCause, ConstraintState},
        constraint_kind::ConstraintKind,
        constraint_set::{ConstraintId, ConstraintSet},
        row::{Label, Row},
        row_kind::RowKind,
        ty::{GenericState, Primitive, Ty, TypeParameter},
        type_checking_session::ExprIDTypeMap,
        type_var::{TypeVar, TypeVarKind},
        type_var_context::{RowVar, TypeVarContext},
    },
};

pub type Scope = BTreeMap<SymbolID, Ty>;

#[derive(Debug)]
struct VisitorContext {
    scopes: Vec<Scope>,
    // Stack of generic constraints being collected for each function scope
    generic_constraints_stack: Vec<Vec<ConstraintKind>>,
    // Stack of `self` values
    self_stack: Vec<Ty>,
    metaself_stack: Vec<Ty>,

    expected_stack: Vec<Ty>,
}

impl Default for VisitorContext {
    fn default() -> Self {
        Self {
            scopes: vec![builtins::default_type_checker_scope()], // Default scope
            generic_constraints_stack: vec![],
            self_stack: vec![],
            metaself_stack: vec![],
            expected_stack: vec![],
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

    fn start_generic_context(&mut self) {
        self.generic_constraints_stack.push(vec![]);
    }

    fn end_generic_context(&mut self) -> Vec<ConstraintKind> {
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
    #[allow(unused)]
    symbols: &'a SymbolTable,
}

#[allow(clippy::todo)]
impl<'a> Visitor<'a> {
    pub fn new(
        type_var_context: &'a mut TypeVarContext,
        constraints: &'a mut ConstraintSet,
        expr_id_types: &'a mut ExprIDTypeMap,
        meta: &'a ExprMetaStorage,
        symbols: &'a SymbolTable,
    ) -> Self {
        Self {
            type_var_context,
            constraints,
            context: VisitorContext::default(),
            expr_id_types,
            meta,
            symbols,
        }
    }

    pub fn new_type_var(&mut self) -> TypeVar {
        self.type_var_context.new_var(TypeVarKind::None)
    }

    pub fn new_row_type_var(&mut self) -> RowVar {
        self.type_var_context.new_row_var()
    }

    pub fn new_canonical_type_var(&mut self) -> TypeParameter {
        self.type_var_context.new_type_param()
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

    pub fn named_row(
        &mut self,
        kind: RowKind,
        parsed_expr: &ParsedExpr,
        name: &Name,
        generics: &[ParsedExpr],
        _conformances: &[ParsedExpr],
        body: &ParsedExpr,
    ) -> Result<Ty, TypeError> {
        let Ok(metatype) = self.context.lookup(name) else {
            return Err(TypeError::Unknown("Did not hoist".to_string()));
        };

        let Ty::Metatype {
            ty:
                mut self_ty @ box Ty::Nominal {
                    properties: Row::Open(properties),
                    methods: Row::Open(methods),
                    ..
                },
            properties: Row::Open(meta_properties),
            methods: Row::Open(meta_methods),
        } = metatype.clone()
        else {
            return Err(TypeError::Unknown("Did not hoist".to_string()));
        };

        self.context.start_scope();
        self.context.start_generic_context();

        // Collect generic type parameters
        let mut type_params = vec![];
        for generic in generics {
            let ty = self.visit(generic)?;
            if let Ty::Var(tv) = ty {
                type_params.push(tv);
            }
        }

        // Update the nominal type with the generic parameters
        if let Ty::Nominal { generics, .. } = &mut *self_ty {
            *generics =
                GenericState::Template(type_params.iter().map(|t| t.to_type_parameter()).collect());
        }

        // Push the updated enum type to the stack (after setting type params)
        self.context.self_stack.push(*self_ty.clone());

        // Update the metatype with the updated nominal type
        let updated_metatype = Ty::Metatype {
            ty: self_ty.clone(),
            properties: Row::Open(meta_properties),
            methods: Row::Open(meta_methods),
        };
        self.context.metaself_stack.push(updated_metatype.clone());

        let parsed_expr::Expr::Block(items) = &body.expr else {
            unreachable!()
        };

        self.expr_id_types.insert(body.id, Ty::Void);

        use parsed_expr::Expr;

        let mut property_count = 0;

        for (index, item) in items.iter().enumerate() {
            match &item.expr {
                Expr::Property {
                    name, is_static, ..
                } if kind != RowKind::Enum => {
                    let property_ty = self.visit(item)?;

                    let row_var = if *is_static {
                        meta_properties
                    } else {
                        properties
                    };

                    self.constrain(
                        item.id,
                        ConstraintKind::HasField {
                            record: Row::Open(row_var),
                            label: Label::String(name.name_str()),
                            ty: property_ty,
                            index: Some(index),
                        },
                        ConstraintCause::PropertyDefinition,
                    )?;

                    if !*is_static {
                        property_count += 1;
                    }
                }
                Expr::Method { func, is_static } => {
                    // Extract the method name from the func expression
                    let method_name = if let Expr::Func {
                        name: Some(method_name),
                        ..
                    } = &func.expr
                    {
                        method_name.name_str()
                    } else {
                        return Err(TypeError::Unknown("Method must have a name".to_string()));
                    };

                    let row_var = if *is_static { meta_methods } else { methods };
                    let func_ty = self.visit(func)?;
                    self.expr_id_types.insert(item.id, func_ty.clone());
                    self.constrain(
                        item.id,
                        ConstraintKind::HasField {
                            record: Row::Open(row_var),
                            label: method_name.into(),
                            ty: func_ty,
                            index: Some(index),
                        },
                        ConstraintCause::MethodDefinition,
                    )?;
                }
                Expr::Init(_, func) if kind != RowKind::Enum => {
                    let Expr::Func {
                        name: _,
                        generics,
                        params,
                        body,
                        ret,
                        captures,
                        attributes,
                    } = &func.expr
                    else {
                        unreachable!()
                    };

                    let mut func_ty = self.visit_func(
                        func, &None, generics, params, body, ret, captures, attributes, true,
                    )?;
                    let self_ty_var = self.new_type_var();

                    // Replace the returns slot with our fresh self
                    func_ty = match func_ty {
                        Ty::Func {
                            params,
                            returns: _,
                            generic_constraints,
                        } => Ty::Func {
                            params,
                            returns: Box::new(Ty::Var(self_ty_var)),
                            generic_constraints,
                        },
                        other => {
                            return Err(TypeError::Mismatch(
                                name.name_str(),
                                format!("{other:?} (initializer must be a function)"),
                            ));
                        }
                    };

                    self.expr_id_types.insert(item.id, func_ty.clone());

                    self.constrain(
                        item.id,
                        ConstraintKind::Equals(*self_ty.clone(), Ty::Var(self_ty_var)),
                        ConstraintCause::InitializerDefinition,
                    )?;

                    // Ensure initializer returns `self` (this should always be the case since we synthesize
                    // a self at the end of inits).
                    self.constrain(
                        item.id,
                        ConstraintKind::HasField {
                            record: Row::Open(meta_methods),
                            label: Label::String("init".to_string()),
                            ty: func_ty,
                            index: Some(index),
                        },
                        ConstraintCause::InitializerDefinition,
                    )?;
                }
                Expr::FuncSignature { .. } if kind == RowKind::Protocol => (),
                Expr::EnumVariant(name, _values) if kind == RowKind::Enum => {
                    let property_ty = self.visit(item)?;

                    self.constrain(
                        item.id,
                        ConstraintKind::HasField {
                            record: Row::Open(meta_properties),
                            label: Label::String(name.name_str()),
                            ty: property_ty,
                            index: Some(index),
                        },
                        ConstraintCause::PropertyDefinition,
                    )?;
                }
                _ => (),
            }
        }

        // Always close the properties row, whether empty or not
        self.constrain(
            parsed_expr.id,
            ConstraintKind::RowClosed {
                record: Row::Open(properties),
            },
            if property_count == 0 {
                ConstraintCause::PropertiesEmpty
            } else {
                ConstraintCause::StructLiteral
            },
        )?;

        self.context.end_scope();
        self.context.self_stack.pop();
        self.context.metaself_stack.pop();
        self.context.end_generic_context();

        // Update the struct definition with the generic type parameters
        let final_metatype = Ty::Metatype {
            ty: self_ty.clone(),
            properties: Row::Open(meta_properties),
            methods: Row::Open(meta_methods),
        };
        self.context.declare(&name.symbol_id()?, &final_metatype)?;

        self.expr_id_types.insert(parsed_expr.id, *self_ty.clone());

        Ok(final_metatype)
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
            expr_id = parsed.id.0,
            expr = crate::formatter::Formatter::format_single_expr(self.meta, parsed)
        )
        .entered();

        let result = match &parsed.expr {
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
                is_static,
            } => self.visit_property(parsed, name, *is_static, type_repr, default_value),
            parsed_expr::Expr::Method { func, is_static } => {
                self.visit_method(parsed, func, *is_static)
            }
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
                parsed, name, generics, params, body, ret, captures, attributes, false,
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
        }?;

        self.expr_id_types.insert(parsed.id, result.clone());

        Ok(result)
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
        self.expr_id_types.insert(parsed_expr.id, ty.clone());

        self.constrain(
            parsed_expr.id,
            ConstraintKind::LiteralPrimitive(ty.clone(), Primitive::Int),
            ConstraintCause::PrimitiveLiteral(parsed_expr.id, Primitive::Int),
        )?;

        Ok(ty)
    }

    fn visit_literal_float(&mut self, parsed_expr: &ParsedExpr) -> Result<Ty, TypeError> {
        let ty = Ty::Var(self.type_var_context.new_var(TypeVarKind::FloatLiteral));
        self.expr_id_types.insert(parsed_expr.id, ty.clone());

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
        Ok(Ty::Var(self.new_type_var()))
    }

    fn visit_tuple(
        &mut self,
        parsed_expr: &ParsedExpr,
        items: &[ParsedExpr],
    ) -> Result<Ty, TypeError> {
        let var = self.new_row_type_var();

        let constraint_id = self.constrain(
            parsed_expr.id,
            ConstraintKind::RowClosed {
                record: Row::Open(var),
            },
            ConstraintCause::RecordLiteral,
        )?;

        for (i, item) in items.iter().enumerate() {
            let item_ty = self.visit(item)?;
            let child_id = self.constrain(
                item.id,
                ConstraintKind::HasField {
                    record: Row::Open(var),
                    label: Label::Int(i as u32),
                    ty: item_ty.clone(),
                    index: Some(i),
                },
                ConstraintCause::TupleLiteral,
            )?;

            self.add_child(constraint_id, child_id);
        }

        self.expr_id_types
            .insert(parsed_expr.id, Ty::Product(Row::Open(var)));

        Ok(Ty::Product(Row::Open(var)))
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
        let callee_ty = self.visit(callee)?;

        tracing::debug!("visit_call: callee_ty = {:?}", callee_ty);

        let (init_ty, returning) = if let Ty::Metatype {
            ty:
                box Ty::Nominal {
                    generics: GenericState::Template(type_params),
                    ..
                },
            ..
        } = &callee_ty
        {
            // For metatype calls (e.g., Person(...)), look up the static "init" on the metatype
            // and treat the call as invoking that initializer, returning an instance of the
            // underlying nominal type (instantiated if generic).
            let instantiated = if !type_params.is_empty() {
                let mut substitutions = BTreeMap::new();
                callee_ty.instantiate(self.type_var_context, &mut substitutions)
            } else {
                callee_ty.clone()
            };

            // Extract the nominal type from the (possibly instantiated) metatype for the return
            let returning_nominal = match &instantiated {
                Ty::Metatype { ty, .. } => ty.as_ref().clone(),
                _ => unreachable!(),
            };

            // Get the init method type via TyHasField on the metatype. Use the
            // (possibly) instantiated metatype so method parameter types are
            // expressed in terms of the per-call instantiated type variables.
            let init_ty = Ty::Var(self.new_type_var());
            self.constrain(
                parsed_expr.id,
                ConstraintKind::TyHasField {
                    receiver: instantiated.clone(),
                    label: "init".into(),
                    ty: init_ty.clone(),
                    index: None,
                },
                ConstraintCause::InitializerCall,
            )?;

            (init_ty, returning_nominal)
        } else if let Ty::Nominal {
            generics: GenericState::Template(type_params),
            ..
        } = &callee_ty
        {
            // Only instantiate if there are type parameters
            let instantiated = if !type_params.is_empty() {
                let mut substitutions = BTreeMap::new();
                callee_ty.instantiate(self.type_var_context, &mut substitutions)
            } else {
                // For non-generic structs, just use the type as-is
                callee_ty.clone()
            };

            // Get the init method type
            let init_ty = Ty::Var(self.new_type_var());

            // Use the appropriate constraint based on whether we have an instantiated type
            if !type_params.is_empty() {
                // For generic structs, use TyHasField on the instantiated type
                self.constrain(
                    parsed_expr.id,
                    ConstraintKind::TyHasField {
                        receiver: instantiated.clone(),
                        label: "init".into(),
                        ty: init_ty.clone(),
                        index: None,
                    },
                    ConstraintCause::InitializerCall,
                )?;
            } else {
                // Non-generic nominal calls should still route through the metatype's init
                // Since we don't have direct access to metatype rows here, rely on TyHasField
                // against the nominal; the solver will find the metatype initializer via
                // symbol table lookup.
                self.constrain(
                    parsed_expr.id,
                    ConstraintKind::TyHasField {
                        receiver: instantiated.clone(),
                        label: "init".into(),
                        ty: init_ty.clone(),
                        index: None,
                    },
                    ConstraintCause::InitializerCall,
                )?;
            }

            (init_ty, instantiated)
        } else {
            // For regular function calls, the return type will be determined by the Call constraint
            (callee_ty, Ty::Var(self.new_type_var()))
        };

        let type_args = self.visit_mult(type_args)?;
        let args = self.visit_mult(args)?;

        // Constrain the call itself
        self.constrain(
            parsed_expr.id,
            ConstraintKind::Call {
                callee: init_ty,
                type_args,
                args,
                returning: returning.clone(),
            },
            ConstraintCause::Call,
        )?;

        self.expr_id_types.insert(parsed_expr.id, returning.clone());

        Ok(returning)
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
        parsed_expr: &ParsedExpr,
        name: &Name,
        generics: &[ParsedExpr],
        conformances: &[ParsedExpr],
        body: &ParsedExpr,
    ) -> Result<Ty, TypeError> {
        self.named_row(
            RowKind::Struct,
            parsed_expr,
            name,
            generics,
            conformances,
            body,
        )
    }

    fn visit_property(
        &mut self,
        parsed_expr: &ParsedExpr,
        _name: &Name,
        _is_static: bool,
        type_repr: &Option<Box<ParsedExpr>>,
        default_value: &Option<Box<ParsedExpr>>,
    ) -> Result<Ty, TypeError> {
        let type_repr_ty = type_repr.as_ref().map(|t| self.visit(t)).transpose()?;
        let default_value_ty = default_value.as_ref().map(|t| self.visit(t)).transpose()?;

        let property_ty = match (type_repr_ty, default_value_ty) {
            (None, None) => Ty::Var(self.new_type_var()),
            (Some(ty), None) => ty,
            (None, Some(ty)) => ty,
            (Some(type_repr_ty), Some(default_value_ty)) => {
                self.constrain(
                    parsed_expr.id,
                    ConstraintKind::Equals(type_repr_ty.clone(), default_value_ty),
                    ConstraintCause::PropertyDefinition,
                )?;
                type_repr_ty
            }
        };

        Ok(property_ty)
    }

    fn visit_method(
        &mut self,
        _parsed_expr: &ParsedExpr,
        func: &ParsedExpr,
        _is_static: bool,
    ) -> Result<Ty, TypeError> {
        self.visit(func)
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
            let ty = Ty::TypeParameter(self.new_canonical_type_var());
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
        name: &Label,
    ) -> Result<Ty, TypeError> {
        match receiver {
            Some(receiver) => {
                let receiver_ty = self.visit(receiver)?;

                tracing::debug!(
                    "Member access - receiver: {:?}, field: {:?}",
                    receiver_ty,
                    name
                );

                let var = self.new_type_var();

                self.constrain(
                    parsed_expr.id,
                    ConstraintKind::TyHasField {
                        receiver: receiver_ty,
                        label: name.clone(),
                        ty: Ty::Var(var),
                        index: None,
                    },
                    ConstraintCause::MemberAccess,
                )?;

                self.expr_id_types.insert(parsed_expr.id, Ty::Var(var));
                Ok(Ty::Var(var))
            }
            None => {
                // Look up the identifier in the scopes
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
        skip_return_constraint: bool,
    ) -> Result<Ty, TypeError> {
        let mut constraint_set = ConstraintSet::new();

        self.context.start_scope();

        // Always start tracking constraints for functions - we'll determine if it's generic
        // based on whether any canonical vars are used
        self.context.start_generic_context();

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

            if !skip_return_constraint {
                constraint_set.constrain(
                    ret.id,
                    ConstraintKind::Equals(body_ty, annotated_ty.clone()),
                    ConstraintCause::Annotation(ret.id),
                );
            }
            annotated_ty
        } else {
            // For functions without explicit return types, check if the body type
            // contains canonical vars (making this a generic function)
            let ty = if body_ty.contains_canonical_var() {
                // This is a generic function, use a canonical var for the return type
                Ty::TypeParameter(self.new_canonical_type_var())
            } else {
                // Regular function, use a normal type var
                Ty::Var(self.new_type_var())
            };

            if !skip_return_constraint {
                self.constrain(
                    body.id,
                    ConstraintKind::Equals(body_ty, ty.clone()),
                    ConstraintCause::FuncReturn(body.id),
                )?;
            }

            ty
        };

        self.context.end_scope();

        // Collect any generic constraints that were generated
        let generic_constraints = self.context.end_generic_context();

        let func_ty = Ty::Func {
            params: typed_params,
            returns: Box::new(typed_ret),
            generic_constraints,
        };

        self.expr_id_types.insert(parsed_expr.id, func_ty.clone());

        if let Some(name) = name
            && let Ok(Ty::Var(hoisted_ty)) = self.context.lookup(name)
        {
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
            Ty::TypeParameter(self.new_canonical_type_var())
        };

        tracing::trace!("visit_parameter name: {name:?}, ty: {param_ty:?}");

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
        let scope_ty = if matches!(name, Name::_Self(..)) {
            let Some(self_ty) = self.context.self_stack.last() else {
                return Err(TypeError::Unknown("No ty for `self` found".to_string()));
            };

            self_ty.clone()
        } else {
            self.context.lookup(name)?
        };

        self.expr_id_types.insert(parsed_expr.id, scope_ty.clone());

        tracing::trace!("visit_variable name: {name:?}, ty: {scope_ty:?}");

        Ok(scope_ty)
    }

    fn visit_if(
        &mut self,
        parsed_expr: &ParsedExpr,
        cond: &ParsedExpr,
        conseq: &ParsedExpr,
        alt: &Option<Box<ParsedExpr>>,
    ) -> Result<Ty, TypeError> {
        let cond_ty = self.visit(cond)?;
        self.constrain(
            cond.id,
            ConstraintKind::Equals(cond_ty, Ty::Bool),
            ConstraintCause::Condition,
        )?;

        let conseq_ty = self.visit(conseq)?;

        let ty = if let Some(alt) = alt {
            let alt_ty = self.visit(alt)?;

            self.constrain(
                cond.id,
                ConstraintKind::Equals(conseq_ty.clone(), alt_ty),
                ConstraintCause::Condition,
            )?;

            conseq_ty
        } else {
            Ty::Void
        };

        self.expr_id_types.insert(parsed_expr.id, ty.clone());

        Ok(ty)
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
        parsed_expr: &ParsedExpr,
        name: &Name,
        conformances: &[ParsedExpr],
        generics: &[ParsedExpr],
        body: &ParsedExpr,
    ) -> Result<Ty, TypeError> {
        self.named_row(
            RowKind::Enum,
            parsed_expr,
            name,
            generics,
            conformances,
            body,
        )
    }

    fn visit_enum_variant(
        &mut self,
        _parsed_expr: &ParsedExpr,
        name: &Name,
        values: &[ParsedExpr],
    ) -> Result<Ty, TypeError> {
        let Some(enum_ty) = self.context.self_stack.last().cloned() else {
            return Err(TypeError::Unknown("No self stack found".to_string()));
        };

        tracing::trace!("visit_enum_variant: {name:?}");

        // Treat variants with attached values as function constructors for the enum,
        // otherwise just make it a static property.
        if values.is_empty() {
            Ok(enum_ty)
        } else {
            Ok(Ty::Func {
                params: self.visit_mult(values)?,
                returns: Box::new(enum_ty),
                generic_constraints: vec![],
            })
        }
    }

    fn expecting<T, F: Fn(&mut Self) -> T>(&mut self, expected_ty: Ty, f: F) -> T {
        self.context.expected_stack.push(expected_ty);
        let ret = f(self);
        self.context.expected_stack.pop();
        ret
    }

    fn visit_match(
        &mut self,
        _parsed_expr: &ParsedExpr,
        scrutinee: &ParsedExpr,
        arms: &[ParsedExpr],
    ) -> Result<Ty, TypeError> {
        let scrutinee_ty = self.visit(scrutinee)?;
        let typed_arms = self.expecting(scrutinee_ty, |v| v.visit_mult(arms))?;

        if let Some(first_arm) = typed_arms.first() {
            // Ensure arms agree
            for (i, other_arm) in typed_arms[1..].iter().enumerate() {
                self.constrain(
                    arms[i].id,
                    ConstraintKind::Equals(first_arm.clone(), other_arm.clone()),
                    ConstraintCause::MatchArm,
                )?;
            }

            Ok(first_arm.clone())
        } else {
            Ok(Ty::Void)
        }
    }

    fn visit_match_arm(
        &mut self,
        _parsed_expr: &ParsedExpr,
        pattern: &ParsedExpr,
        body: &ParsedExpr,
    ) -> Result<Ty, TypeError> {
        self.context.start_scope();
        let _pattern = self.visit(pattern)?;
        let body = self.visit(body)?;
        self.context.end_scope();

        Ok(body)
    }

    fn visit_parsed_pattern(
        &mut self,
        parsed_expr: &ParsedExpr,
        pattern: &parsed_expr::Pattern,
    ) -> Result<Ty, TypeError> {
        let Some(expected) = self.context.expected_stack.last().cloned() else {
            unreachable!("didn't get scrutinee type for pattern");
        };

        match pattern {
            parsed_expr::Pattern::LiteralInt(_val) => (),
            parsed_expr::Pattern::LiteralFloat(_val) => (),
            parsed_expr::Pattern::LiteralTrue => (),
            parsed_expr::Pattern::LiteralFalse => (),
            parsed_expr::Pattern::Bind(name) => {
                self.declare(&name.symbol_id()?, expected.clone())?;
            }
            parsed_expr::Pattern::Wildcard => (),
            parsed_expr::Pattern::Variant {
                enum_name,
                variant_name,
                fields,
            } => {
                let enum_ty = if let Some(enum_name) = enum_name {
                    self.context.lookup(enum_name)?
                } else {
                    Ty::Var(self.new_type_var())
                };

                if fields.is_empty() {
                    self.constrain(
                        parsed_expr.id,
                        ConstraintKind::TyHasField {
                            receiver: enum_ty,
                            label: variant_name.into(),
                            ty: expected.clone(),
                            index: None,
                        },
                        ConstraintCause::MatchArm,
                    )?;
                } else {
                    let mut params = vec![];

                    for field in fields {
                        let field_ty = Ty::Var(self.new_type_var());
                        params.push(field_ty.clone());
                        self.expecting(field_ty.clone(), |v| v.visit(field))?;
                    }

                    self.constrain(
                        parsed_expr.id,
                        ConstraintKind::TyHasField {
                            receiver: enum_ty,
                            label: variant_name.into(),
                            ty: Ty::Func {
                                params,
                                returns: Box::new(expected),
                                generic_constraints: vec![],
                            },
                            index: None,
                        },
                        ConstraintCause::MatchArm,
                    )?;
                }
            }
            parsed_expr::Pattern::Struct { .. } => (),
        };

        Ok(Ty::Void)
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
        let var = self.new_row_type_var();

        let constraint_id = self.constrain(
            parsed_expr.id,
            ConstraintKind::RowClosed {
                record: Row::Open(var),
            },
            ConstraintCause::RecordLiteral,
        )?;

        for (index, field) in fields.iter().enumerate() {
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
                    record: Row::Open(var),
                    label: label.clone(),
                    ty: *value.clone(),
                    index: Some(index),
                },
                ConstraintCause::RecordLiteral,
            )?;

            self.add_child(constraint_id, child_id);
        }

        self.expr_id_types
            .insert(parsed_expr.id, Ty::Product(Row::Open(var)));

        Ok(Ty::Product(Row::Open(var)))
    }

    fn visit_record_field(
        &mut self,
        parsed_expr: &ParsedExpr,
        label: &Name,
        value: &ParsedExpr,
    ) -> Result<Ty, TypeError> {
        let value = self.visit(value)?;
        let field_ty = Ty::Label(label.name_str().into(), Box::new(value));
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
