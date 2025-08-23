use std::{collections::BTreeMap, u32};

use tracing::trace_span;

use crate::{
    SymbolID, builtins,
    expr_id::ExprID,
    name::Name,
    parsed_expr::{Expr, ParsedExpr},
    raw_formatter::RawFormatter,
    type_checker::TypeError,
    types::{
        constraint::{Constraint, ConstraintCause, ConstraintState},
        constraint_kind::ConstraintKind,
        constraint_set::{ConstraintId, ConstraintSet},
        row::{Label, Row},
        row_kind::RowKind,
        ty::{GenericState, InferredDefinition, Primitive, Ty, TypeParameter},
        type_var::{TypeVar, TypeVarKind},
        type_var_context::{RowVar, RowVarKind, TypeVarContext},
        visitors::definition_visitor::{Definition, TypeScheme, TypeSchemeKind},
    },
};

#[derive(Clone, Debug)]
pub(crate) struct Substitutions {
    pub type_parameters: BTreeMap<TypeParameter, TypeVar>,
    pub rows: BTreeMap<RowVar, RowVar>,
}

impl Substitutions {
    pub fn get_type_parameter(&self, type_parameter: &TypeParameter) -> Option<&TypeVar> {
        self.type_parameters.get(type_parameter)
    }

    pub fn get_row(&self, row_var: &RowVar) -> Option<&RowVar> {
        self.rows.get(row_var)
    }
}

impl std::fmt::Display for TypeScheme<InferredDefinition> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            TypeSchemeKind::Func {
                quantified_vars,
                params,
                returns,
                ..
            } => {
                write!(
                    f,
                    "({:?}){} -> {returns}",
                    params,
                    if quantified_vars.is_empty() {
                        "".to_string()
                    } else {
                        quantified_vars
                            .iter()
                            .map(|a| format!("{a}"))
                            .collect::<Vec<String>>()
                            .join(", ")
                    }
                )
            }
            TypeSchemeKind::Property { name, value } => {
                write!(f, ".{} -> {value}", name.name_str())
            }
            TypeSchemeKind::Nominal {
                name,
                quantified_vars,
                ..
            } => write!(
                f,
                "{}{}",
                name.name_str(),
                if quantified_vars.is_empty() {
                    "".to_string()
                } else {
                    quantified_vars
                        .iter()
                        .map(|a| format!("{a}"))
                        .collect::<Vec<String>>()
                        .join(", ")
                }
            ),
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct NominalRowSet {
    pub properties: RowVar,
    pub methods: RowVar,
    pub meta_properties: RowVar,
    pub meta_methods: RowVar,
}

impl Default for NominalRowSet {
    fn default() -> Self {
        Self {
            properties: RowVar::new(u32::MAX, RowVarKind::Canonical),
            methods: RowVar::new(u32::MAX - 1, RowVarKind::Canonical),
            meta_properties: RowVar::new(u32::MAX - 2, RowVarKind::Canonical),
            meta_methods: RowVar::new(u32::MAX - 3, RowVarKind::Canonical),
        }
    }
}

#[derive(Clone, Debug)]
struct SelfRow {
    substitutions: BTreeMap<TypeParameter, TypeVar>,
    ty: Ty,
    rows: NominalRowSet,
    property_count: usize,
}

pub struct InferenceVisitor<'a> {
    pub constraints: ConstraintSet,
    pub(super) definitions: &'a BTreeMap<ExprID, TypeScheme<Definition>>,
    context: &'a mut TypeVarContext,
    scope_stack: Vec<Scope>,
    expected_type_stack: Vec<Ty>,
    typed_expr_ids: &'a mut BTreeMap<ExprID, Ty>,
    // Single stack for all generic constraint contexts
    generic_constraint_stack: Vec<(ExprID, Vec<Constraint>)>,
    self_row_stack: Vec<SelfRow>,
}

pub type Scope = BTreeMap<SymbolID, Ty>;

impl<'a> InferenceVisitor<'a> {
    pub fn new(
        context: &'a mut TypeVarContext,
        typed_expr_ids: &'a mut BTreeMap<ExprID, Ty>,
        definitions: &'a BTreeMap<ExprID, TypeScheme<Definition>>,
    ) -> Self {
        Self {
            context,
            definitions,
            constraints: ConstraintSet::new(),
            scope_stack: vec![builtins::default_type_checker_scope()],
            expected_type_stack: Default::default(),
            typed_expr_ids,
            generic_constraint_stack: Default::default(),
            self_row_stack: Default::default(),
        }
    }

    pub fn visit_mult(&mut self, exprs: &[ParsedExpr]) -> Result<Vec<Ty>, TypeError> {
        let mut typed_exprs = vec![];
        for expr in exprs {
            typed_exprs.push(self.visit(expr)?);
        }
        Ok(typed_exprs)
    }

    #[allow(clippy::todo)]
    pub fn visit(&mut self, parsed: &ParsedExpr) -> Result<Ty, TypeError> {
        let _s = trace_span!(
            "visit",
            expr_id = parsed.id.0,
            expr = RawFormatter::format_single_expr(&parsed.expr)
        )
        .entered();

        let ty = match &parsed.expr {
            Expr::LiteralInt(_) => {
                self.visit_primitive_literal(parsed.id, TypeVarKind::IntLiteral, Primitive::Int)
            }
            Expr::LiteralFloat(_) => {
                self.visit_primitive_literal(parsed.id, TypeVarKind::FloatLiteral, Primitive::Float)
            }
            Expr::LiteralTrue => {
                self.visit_primitive_literal(parsed.id, TypeVarKind::BoolLiteral, Primitive::Bool)
            }
            Expr::LiteralFalse => {
                self.visit_primitive_literal(parsed.id, TypeVarKind::BoolLiteral, Primitive::Bool)
            }
            Expr::LiteralString(_) => todo!(),
            Expr::Func {
                name,
                generics,
                params,
                body,
                ret,
                ..
            } => self.visit_func(
                parsed.id,
                name,
                generics,
                params,
                body,
                ret.as_ref().map(|r| &**r),
            ),
            Expr::Unary(_token_kind, _parsed_expr) => todo!(),
            Expr::Binary(_parsed_expr, _token_kind, _parsed_expr1) => todo!(),
            Expr::Tuple(items) => self.visit_tuple(parsed, items),
            Expr::Block(parsed_exprs) => self.visit_block(parsed_exprs),
            Expr::Call {
                callee,
                type_args,
                args,
            } => self.visit_call(parsed.id, callee, type_args, args),
            Expr::ParsedPattern(_pattern) => todo!(),
            Expr::Return(_parsed_expr) => todo!(),
            Expr::Break => todo!(),
            Expr::Extend { .. } => todo!(),
            Expr::Struct {
                name,
                generics,
                conformances,
                body,
            } => self.named_row(RowKind::Struct, parsed, name, generics, conformances, body),
            Expr::Property {
                name,
                is_static,
                type_repr,
                default_value,
            } => self.visit_property(parsed.id, name, *is_static, type_repr, default_value),
            Expr::Method { func, is_static } => self.visit_method(parsed.id, func, *is_static),
            Expr::TypeRepr {
                name,
                generics,
                conformances,
                introduces_type,
            } => self.visit_type_repr(parsed.id, name, generics, conformances, *introduces_type),
            Expr::FuncTypeRepr(_parsed_exprs, _parsed_expr, _) => todo!(),
            Expr::TupleTypeRepr(_parsed_exprs, _) => todo!(),
            Expr::Member(Some(box receiver), name) => {
                self.visit_member(parsed, Some(receiver), name)
            }
            Expr::Member(None, name) => self.visit_member(parsed, None, name),
            Expr::Init(_symbol_id, func) => self.visit_init(func),

            Expr::Parameter(name, Some(box type_repr)) => {
                self.visit_parameter(parsed.id, name, Some(type_repr))
            }
            Expr::Parameter(name, None) => self.visit_parameter(parsed.id, name, None),
            Expr::CallArg { label, value } => self.visit_call_arg(label, value),
            Expr::Let(name, Some(box type_repr)) => {
                self.visit_let(parsed.id, name, Some(type_repr))
            }
            Expr::Let(name, None) => self.visit_let(parsed.id, name, None),
            Expr::Assignment(lhs, rhs) => self.visit_assignment(parsed.id, lhs, rhs),
            Expr::Variable(name) => self.visit_variable(name),
            Expr::If(cond, conseq, alt) => self.visit_if(parsed, cond, conseq, alt),
            Expr::Loop(_parsed_expr, _parsed_expr1) => todo!(),
            Expr::EnumDecl { .. } => todo!(),
            Expr::EnumVariant(_name, _parsed_exprs) => todo!(),
            Expr::Match(_parsed_expr, _parsed_exprs) => todo!(),
            Expr::MatchArm(_parsed_expr, _parsed_expr1) => todo!(),
            Expr::PatternVariant(_name, _name1, _parsed_exprs) => todo!(),
            Expr::RecordLiteral(parsed_exprs) => self.visit_record_literal(parsed, parsed_exprs),
            Expr::RecordField { label, value } => self.visit_record_field(parsed, label, value),
            Expr::RecordTypeRepr { .. } => todo!(),
            Expr::RecordTypeField { .. } => todo!(),
            Expr::RowVariable(_name) => todo!(),
            Expr::Spread(_parsed_expr) => todo!(),
            Expr::ProtocolDecl { .. } => todo!(),
            Expr::FuncSignature { .. } => todo!(),
            Expr::Import(_) => todo!(),
            _ => Err(TypeError::Unknown(format!(
                "No inference handler for {:?}",
                parsed.expr
            ))),
        };

        if let Ok(ty) = ty.clone() {
            self.typed_expr_ids.insert(parsed.id, ty);
        }

        ty
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
        let Ok(Ty::RawScheme(TypeScheme {
            named_generics,
            kind:
                TypeSchemeKind::Nominal {
                    canonical_rows,
                    quantified_vars,
                    ..
                },
        })) = self.lookup(&name.symbol_id()?)
        else {
            return Err(TypeError::Unknown(format!("Did not hoist `{name:?}`")));
        };

        let nominal_type = Ty::Nominal {
            name: name.clone(),
            properties: Row::Open(canonical_rows.properties),
            methods: Row::Open(canonical_rows.methods),
        };

        let metatype = Ty::Metatype {
            ty: Box::new(nominal_type.clone()),
            properties: Row::Open(canonical_rows.meta_properties),
            methods: Row::Open(canonical_rows.meta_methods),
        };

        let nominal_row_set = canonical_rows;

        let substitutions = self.canonicalized_type_parameter_substitutions(&quantified_vars);

        let self_row = SelfRow {
            substitutions: substitutions.clone(),
            ty: nominal_type.clone(),
            rows: nominal_row_set,
            property_count: 0,
        };

        self.start_scope();
        self.self_row_stack.push(self_row);
        self.push_generic_constraint_context(parsed_expr.id);
        self.register_named_generics(&named_generics, &substitutions)?;
        self.visit_mult(generics)?;

        let Expr::Block(items) = &body.expr else {
            unreachable!()
        };

        for item in items {
            match &item.expr {
                Expr::Property { .. } | Expr::Init(..) | Expr::Method { .. } => {
                    self.visit(item)?;
                }
                _ => unreachable!("don't know how to handle {kind:?} body expr: {item:?}"),
            }
        }

        self.typed_expr_ids.insert(body.id, Ty::Void);
        let self_row = self.self_row_stack.pop().unwrap();
        self.end_scope();

        self.constrain(
            parsed_expr.id,
            ConstraintKind::RowClosed {
                record: Row::Open(canonical_rows.properties),
            },
            if self_row.property_count == 0 {
                ConstraintCause::PropertiesEmpty
            } else {
                ConstraintCause::StructLiteral
            },
        )?;

        let generic_constraints = self.pop_generic_constraint_context(parsed_expr.id)?;
        let ty = Ty::Scheme(TypeScheme {
            kind: TypeSchemeKind::Nominal {
                name: name.clone(),
                canonical_rows: nominal_row_set,
                quantified_vars: quantified_vars.to_vec(),
            },
            named_generics: named_generics.clone(),
        });

        // Update the declaration
        self.declare(&name.symbol_id()?, &ty)?;

        Ok(ty)
    }

    pub fn add_child(&mut self, parent: ConstraintId, child: ConstraintId) {
        self.constraints.add_child(parent, child);
    }

    #[allow(clippy::panic)]
    fn constrain(
        &mut self,
        expr_id: ExprID,
        kind: ConstraintKind,
        cause: ConstraintCause,
    ) -> Result<ConstraintId, TypeError> {
        // Either no canonical vars, has non-canonical vars, or is a method/init definition - solve immediately
        Ok(self.constraints.constrain(expr_id, kind, cause))
    }

    fn definition_to_ty(
        &mut self,
        substitutions: &BTreeMap<TypeParameter, TypeVar>,
        definition: &Definition,
    ) -> Result<Ty, TypeError> {
        match definition {
            Definition::Concrete(sym) => {
                let Ok(ty) = self.lookup(sym) else {
                    return Err(TypeError::Unknown(
                        "Unable to find concrete ty for symbol {sym:?}".to_string(),
                    ));
                };

                Ok(ty)
            }
            Definition::TypeParameter(tp) => {
                let Some(replacement) = substitutions.get(tp) else {
                    return Err(TypeError::Unknown(
                        "Did not get substitution during instantiation".to_string(),
                    ));
                };

                Ok(Ty::Var(*replacement))
            }
            Definition::Infer => Ok(Ty::Var(self.new_instantiated_type_var())),
        }
    }

    fn lookup(&mut self, symbol_id: &SymbolID) -> Result<Ty, TypeError> {
        if let Some(ty) = self
            .scope_stack
            .iter()
            .rev()
            .find_map(|frame| frame.get(symbol_id))
        {
            return Ok(ty.clone());
        }

        Err(TypeError::Unknown(format!(
            "Undefined symbol: {symbol_id:?}",
        )))
    }

    pub(super) fn declare(&mut self, symbol_id: &SymbolID, ty: &Ty) -> Result<(), TypeError> {
        if let Some(old_ty) = self
            .scope_stack
            .last()
            .ok_or(TypeError::Unknown(format!(
                "Unable to declare symbol {symbol_id:?} without scope"
            )))?
            .get(symbol_id)
        {
            tracing::warn!(
                "Already declared {symbol_id:?} in scope: {old_ty:?}. New value: {ty:?}"
            );
        }

        self.scope_stack
            .last_mut()
            .ok_or(TypeError::Unknown(format!(
                "Unable to declare symbol {symbol_id:?} without scope"
            )))?
            .insert(*symbol_id, ty.clone());

        Ok(())
    }

    pub fn new_row_type_var(&mut self, kind: RowVarKind) -> RowVar {
        self.context.new_row_var(kind)
    }

    pub(super) fn new_type_var(&mut self, kind: TypeVarKind) -> TypeVar {
        self.context.new_var(kind)
    }

    fn new_instantiated_type_var(&mut self) -> TypeVar {
        self.context.new_var(TypeVarKind::Instantiated)
    }

    fn expect(&mut self, expected: Ty) {
        self.expected_type_stack.push(expected)
    }

    fn get_expectation(&mut self) -> Option<Ty> {
        self.expected_type_stack.pop()
    }

    fn start_scope(&mut self) {
        self.scope_stack.push(Scope::default())
    }

    fn end_scope(&mut self) {
        self.scope_stack.pop();
    }

    fn push_generic_constraint_context(&mut self, expr_id: ExprID) {
        self.generic_constraint_stack
            .push((expr_id, Default::default()));
    }

    fn pop_generic_constraint_context(
        &mut self,
        expr_id: ExprID,
    ) -> Result<Vec<Constraint>, TypeError> {
        let Some((popped_expr_id, constraints)) = self.generic_constraint_stack.pop() else {
            return Err(TypeError::Unknown(format!(
                "Did not get generic constraints for expr id {expr_id:?}"
            )));
        };

        if popped_expr_id != expr_id {
            self.generic_constraint_stack
                .push((popped_expr_id, constraints));
            return Err(TypeError::Unknown(format!(
                "Wrong generic constraint set. Expected {expr_id:?}, got {popped_expr_id:}"
            )));
        }

        Ok(constraints)
    }

    fn register_named_generics(
        &mut self,
        named_generics: &BTreeMap<SymbolID, TypeParameter>,
        substitutions: &BTreeMap<TypeParameter, TypeVar>,
    ) -> Result<(), TypeError> {
        for (symbol_id, type_parameter) in named_generics.iter() {
            let Some(instantiated) = substitutions.get(type_parameter) else {
                return Err(TypeError::Unknown(format!(
                    "Did not find instantiation for type parameter: {type_parameter:?}",
                )));
            };

            self.declare(symbol_id, &Ty::Var(*instantiated))?;
        }

        Ok(())
    }

    fn canonicalized_type_parameter_substitutions(
        &mut self,
        type_parameters: &[TypeParameter],
    ) -> BTreeMap<TypeParameter, TypeVar> {
        type_parameters
            .iter()
            .map(|param| (*param, self.context.new_var(TypeVarKind::Canonical(*param))))
            .collect()
    }

    fn visit_init(&mut self, func: &ParsedExpr) -> Result<Ty, TypeError> {
        let Some(mut self_row) = self.self_row_stack.last().cloned() else {
            return Err(TypeError::Unknown("did not get self".to_string()));
        };

        let init = self.visit(func)?;

        self.constrain(
            func.id,
            ConstraintKind::HasField {
                record: Row::Open(self_row.rows.meta_methods),
                label: "init".into(),
                ty: init.clone(),
                index: None,
            },
            ConstraintCause::InitializerDefinition,
        )?;

        Ok(init)
    }

    fn visit_property(
        &mut self,
        expr_id: ExprID,
        name: &Name,
        is_static: bool,
        type_repr: &Option<Box<ParsedExpr>>,
        default_value: &Option<Box<ParsedExpr>>,
    ) -> Result<Ty, TypeError> {
        let type_repr_ty = type_repr.as_ref().map(|t| self.visit(t)).transpose()?;
        let default_value_ty = default_value.as_ref().map(|t| self.visit(t)).transpose()?;

        if let (Some(type_repr_ty), Some(default_value_ty)) = (type_repr_ty, default_value_ty) {
            self.constrain(
                type_repr.as_ref().unwrap().id,
                ConstraintKind::Equals(type_repr_ty.clone(), default_value_ty),
                ConstraintCause::PropertyDefinition,
            )?;
        }

        let Some(mut self_row) = self.self_row_stack.last().cloned() else {
            return Err(TypeError::Unknown("did not get self".to_string()));
        };

        let Some(TypeScheme {
            kind: TypeSchemeKind::Property { value, .. },
            ..
        }) = self.definitions.get(&expr_id)
        else {
            return Err(TypeError::Unknown(
                "did not get property definition".to_string(),
            ));
        };

        let property_ty = self.definition_to_ty(&self_row.substitutions, value)?;

        let record = if is_static {
            Row::Open(self_row.rows.meta_properties)
        } else {
            self_row.property_count += 1;
            Row::Open(self_row.rows.properties)
        };

        self.constrain(
            expr_id,
            ConstraintKind::HasField {
                record,
                label: Label::String(name.name_str().to_string()),
                ty: property_ty.clone(),
                index: Some(self_row.property_count),
            },
            ConstraintCause::PropertyDefinition,
        )?;

        let Some(old_self_row) = self.self_row_stack.last_mut() else {
            unreachable!()
        };

        // Update self row with new property count
        *old_self_row = self_row;

        Ok(property_ty)
    }

    fn visit_method(
        &mut self,
        expr_id: ExprID,
        func: &ParsedExpr,
        is_static: bool,
    ) -> Result<Ty, TypeError> {
        let Some(mut self_row) = self.self_row_stack.last().cloned() else {
            return Err(TypeError::Unknown("did not get self".to_string()));
        };

        let Expr::Func {
            name: Some(name), ..
        } = &func.expr
        else {
            unreachable!();
        };

        let func_ty = self.visit(func)?;
        let record = if is_static {
            Row::Open(self_row.rows.meta_methods)
        } else {
            Row::Open(self_row.rows.methods)
        };

        self.constrain(
            expr_id,
            ConstraintKind::HasField {
                record,
                label: Label::String(name.name_str().to_string()),
                ty: func_ty.clone(),
                index: Some(self_row.property_count),
            },
            ConstraintCause::MethodDefinition,
        )?;

        Ok(func_ty)
    }

    fn visit_type_repr(
        &mut self,
        expr_id: ExprID,
        name: &Name,
        generics: &[ParsedExpr],
        conformances: &[ParsedExpr],
        introduces_type: bool,
    ) -> Result<Ty, TypeError> {
        if introduces_type {
            // Should already be defined from a scheme's named_generics
            self.lookup(&name.symbol_id()?)
        } else {
            self.lookup(&name.symbol_id()?)
        }
    }

    fn visit_primitive_literal(
        &mut self,
        expr_id: ExprID,
        kind: TypeVarKind,
        primitive: Primitive,
    ) -> Result<Ty, TypeError> {
        let type_var = self.context.new_var(kind);

        self.constrain(
            expr_id,
            ConstraintKind::LiteralPrimitive(Ty::Var(type_var), primitive),
            ConstraintCause::PrimitiveLiteral(expr_id, primitive),
        )?;

        Ok(Ty::Var(type_var))
    }

    fn visit_func(
        &mut self,
        id: ExprID,
        name: &Option<Name>,
        generics: &[ParsedExpr],
        params: &[ParsedExpr],
        body: &ParsedExpr,
        returns: Option<&ParsedExpr>,
    ) -> Result<Ty, TypeError> {
        self.start_scope();

        let Some(TypeScheme {
            named_generics,
            kind:
                TypeSchemeKind::Func {
                    quantified_vars,
                    params: scheme_params,
                    returns: scheme_returns,
                    ..
                },
            ..
        }) = self.definitions.get(&id).cloned()
        else {
            return Err(TypeError::Unknown(format!(
                "Did not find type scheme for {name:?}"
            )));
        };

        let func_substitutions = self.canonicalized_type_parameter_substitutions(&quantified_vars);
        let substitutions = if let Some(self_row) = self.self_row_stack.last() {
            let mut subs = self_row.substitutions.clone();
            subs.extend(func_substitutions);
            subs
        } else {
            func_substitutions
        };

        self.register_named_generics(&named_generics, &substitutions)?;

        for generic in generics {
            self.visit(generic)?;
        }

        for (i, param) in params.iter().enumerate() {
            let param_ty = Ty::Var(self.new_type_var(TypeVarKind::FuncParam));
            self.expect(param_ty.clone());
            self.visit(param)?;

            let Expr::Parameter(name, _) = &param.expr else {
                unreachable!()
            };

            self.constrain(
                param.id,
                ConstraintKind::HasField {
                    record: scheme_params.clone(),
                    label: name.name_str().into(),
                    ty: param_ty,
                    index: Some(i),
                },
                ConstraintCause::FuncParam,
            )?;
        }

        self.constrain(
            id,
            ConstraintKind::RowClosed {
                record: scheme_params.clone(),
            },
            ConstraintCause::FuncParam,
        )?;

        let body_ty = self.visit(body)?;

        if let Some(returns) = returns {
            let returns_ty = if let Definition::TypeParameter(tp) = &scheme_returns {
                let Some(tv) = substitutions.get(tp) else {
                    return Err(TypeError::Unknown(format!(
                        "Did not find substitution for type parameter: {tp}"
                    )));
                };

                let returns_ty = self.visit(returns)?;
                self.constrain(
                    returns.id,
                    ConstraintKind::Equals(returns_ty.clone(), Ty::Var(*tv)),
                    ConstraintCause::FuncReturn(returns.id),
                )?;

                returns_ty
            } else {
                self.visit(returns)?
            };

            self.constrain(
                returns.id,
                ConstraintKind::Equals(returns_ty, body_ty.clone()),
                ConstraintCause::FuncReturn(returns.id),
            )?;
        } else if let Definition::TypeParameter(tp) = &scheme_returns {
            let Some(tv) = substitutions.get(tp) else {
                return Err(TypeError::Unknown(format!(
                    "Did not find substitution for return type parameter: {tp}"
                )));
            };

            self.constrain(
                body.id,
                ConstraintKind::Equals(body_ty.clone(), Ty::Var(*tv)),
                ConstraintCause::FuncReturn(body.id),
            )?;
        }

        self.end_scope();

        #[allow(clippy::expect_used)]
        let ty = if substitutions.is_empty() {
            Ty::Func {
                params: scheme_params,
                returns: Box::new(body_ty),
            }
        } else {
            let kind = TypeSchemeKind::<InferredDefinition>::Func {
                quantified_vars,
                params: scheme_params,
                returns: match scheme_returns {
                    Definition::TypeParameter(tp) => InferredDefinition::TypeParameter(tp),
                    _ => InferredDefinition::Concrete(body_ty.clone().into()),
                },
            };

            Ty::Scheme(TypeScheme {
                kind,
                named_generics,
            })
        };

        if let Some(name) = name {
            self.declare(&name.symbol_id()?, &ty)?;
        }

        Ok(ty)
    }

    fn visit_parameter(
        &mut self,
        expr_id: ExprID,
        name: &Name,
        type_repr: Option<&ParsedExpr>,
    ) -> Result<Ty, TypeError> {
        let Some(expected) = self.get_expectation() else {
            return Err(TypeError::Unknown(
                "No expected type for parameter. Should have been provided by visit_func"
                    .to_string(),
            ));
        };

        if let Some(type_repr) = type_repr {
            let type_repr_ty = self.visit(type_repr)?;
            self.constrain(
                expr_id,
                ConstraintKind::Equals(expected.clone(), type_repr_ty),
                ConstraintCause::Annotation(type_repr.id),
            )?;
        }

        self.declare(&name.symbol_id()?, &expected)?;

        Ok(expected)
    }

    fn visit_let(
        &mut self,
        expr_id: ExprID,
        name: &Name,
        type_repr: Option<&ParsedExpr>,
    ) -> Result<Ty, TypeError> {
        let ty = if let Some(type_repr) = type_repr {
            self.visit(type_repr)?
        } else {
            Ty::Var(self.new_type_var(TypeVarKind::Let))
        };

        self.declare(&name.symbol_id()?, &ty)?;

        Ok(ty)
    }

    fn visit_assignment(
        &mut self,
        expr_id: ExprID,
        lhs: &ParsedExpr,
        rhs: &ParsedExpr,
    ) -> Result<Ty, TypeError> {
        let lhs_ty = self.visit(lhs)?;
        let rhs_ty = self.visit(rhs)?;

        self.constrain(
            expr_id,
            ConstraintKind::Equals(lhs_ty, rhs_ty.clone()),
            ConstraintCause::Assignment(expr_id),
        )?;

        Ok(rhs_ty)
    }

    fn visit_variable(&mut self, name: &Name) -> Result<Ty, TypeError> {
        if let Name::_Self(_) = name {
            let Some(self_row) = self.self_row_stack.last() else {
                return Err(TypeError::Unknown("No self".to_string()));
            };

            Ok(self_row.ty.clone())
        } else {
            self.lookup(&name.symbol_id()?)
        }
    }

    fn visit_block(&mut self, items: &[ParsedExpr]) -> Result<Ty, TypeError> {
        let mut ret = Ty::Void;

        // TODO: handle explicit returns
        for (i, item) in items.iter().enumerate() {
            let ty = self.visit(item)?;
            if i == items.len() - 1 {
                ret = ty;
            }
        }

        Ok(ret)
    }

    fn visit_call(
        &mut self,
        expr_id: ExprID,
        callee: &ParsedExpr,
        type_args: &[ParsedExpr],
        args: &[ParsedExpr],
    ) -> Result<Ty, TypeError> {
        let _s = tracing::info_span!(
            "visit_call",
            callee = format!("{callee:?}"),
            args = format!("{args:?}")
        )
        .entered();

        let ty = self.visit(callee)?;
        let (params, returns) = match &ty {
            Ty::Func { params, returns } => (params.clone(), returns.clone()),
            Ty::Scheme(scheme) => {
                let (instantiated, _) = self.context.instantiate(scheme, &mut self.constraints)?;

                match &instantiated {
                    Ty::Func { params, returns } => (params.clone(), returns.clone()),
                    Ty::Metatype { ty, methods, .. } => {
                        let init_params_var = self.new_row_type_var(RowVarKind::Instantiated);
                        let init_ty = Ty::Func {
                            params: Row::Open(init_params_var),
                            returns: ty.clone(),
                        };
                        self.constrain(
                            callee.id,
                            ConstraintKind::HasField {
                                record: methods.clone(),
                                label: "init".into(),
                                ty: init_ty,
                                index: None,
                            },
                            ConstraintCause::InitializerCall,
                        )?;

                        (Row::Open(init_params_var), ty.clone())
                    }
                    _ => unreachable!(),
                }
            }
            _ => unreachable!("don't know how to call {ty}"),
        };

        let mut typed_type_args = vec![];
        for type_arg in type_args {
            typed_type_args.push(self.visit(type_arg)?);
        }

        let returning = Ty::Var(self.new_type_var(TypeVarKind::FuncRet));

        let args_row_var = self.new_row_type_var(RowVarKind::Instantiated);
        let args_row = Row::Open(args_row_var);

        for (i, arg) in args.iter().enumerate() {
            let arg_ty = self.visit(arg)?;
            let Expr::CallArg { label, .. } = &arg.expr else {
                unreachable!()
            };
            self.constrain(
                arg.id,
                ConstraintKind::HasField {
                    record: args_row.clone(),
                    label: label
                        .as_ref()
                        .map(|name| name.name_str().into())
                        .unwrap_or_else(|| Label::Int(i as u32)),
                    ty: arg_ty,
                    index: Some(i),
                },
                ConstraintCause::Call,
            )?;
        }

        self.constrain(
            callee.id,
            ConstraintKind::Equals(Ty::Product(params), Ty::Product(args_row)),
            ConstraintCause::Call,
        )?;

        self.constrain(
            expr_id,
            ConstraintKind::Equals(returning.clone(), *returns),
            ConstraintCause::Call,
        )?;

        Ok(returning)
    }

    fn visit_call_arg(
        &mut self,
        _label: &Option<Name>,
        value: &ParsedExpr,
    ) -> Result<Ty, TypeError> {
        self.visit(value)
    }

    fn visit_record_literal(
        &mut self,
        expr: &ParsedExpr,
        fields: &[ParsedExpr],
    ) -> Result<Ty, TypeError> {
        let var = self.new_row_type_var(RowVarKind::Instantiated); // Records aren't generic............. yet?

        let constraint_id = self.constrain(
            expr.id,
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
        Ok(field_ty)
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

                let var = self.new_type_var(TypeVarKind::Member);

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

                Ok(Ty::Var(var))
            }
            None => {
                todo!()
            }
        }
    }

    fn visit_tuple(
        &mut self,
        parsed_expr: &ParsedExpr,
        items: &[ParsedExpr],
    ) -> Result<Ty, TypeError> {
        let var = self.new_row_type_var(RowVarKind::Instantiated); // Tuples aren't generic ................. yet?

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

        Ok(Ty::Product(Row::Open(var)))
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

        Ok(ty)
    }
}
