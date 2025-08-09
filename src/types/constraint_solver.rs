use indexmap::IndexMap;
use std::collections::BTreeMap;
use tracing::trace_span;

use crate::{
    MemberKind, SymbolTable,
    type_checker::TypeError,
    types::{
        constraint::{Constraint, ConstraintCause, ConstraintState},
        constraint_kind::ConstraintKind,
        constraint_set::ConstraintSet,
        row::{ClosedRow, Label, Row},
        ty::{Primitive, Ty},
        type_var::{TypeVar, TypeVarKind},
        type_var_context::{RowVar, TypeVarContext},
    },
};

const MAX_FAILED_ATTEMPTS: usize = 2;

pub struct ConstraintSolver<'a> {
    context: &'a mut TypeVarContext,
    constraints: &'a mut ConstraintSet,
    record_fields: BTreeMap<RowVar, IndexMap<Label, Ty>>,
    errored: Vec<Constraint>,
    symbols: &'a SymbolTable,
    current_depth: u8,
}

impl<'a> ConstraintSolver<'a> {
    pub fn new(
        context: &'a mut TypeVarContext,
        constraints: &'a mut ConstraintSet,
        symbols: &'a SymbolTable,
    ) -> Self {
        Self {
            context,
            constraints,
            record_fields: Default::default(),
            errored: Default::default(),
            symbols,
            current_depth: 0,
        }
    }

    fn apply_instantiations(&mut self, ty: &Ty, instantiations: &BTreeMap<TypeVar, Ty>) -> Ty {
        match ty {
            Ty::Var(tv) => {
                // If this type var has an instantiation, use it and resolve it
                if let Some(instantiated) = instantiations.get(tv) {
                    self.context.resolve(instantiated)
                } else {
                    ty.clone()
                }
            }
            Ty::Func {
                params,
                returns,
                generic_constraints,
            } => {
                Ty::Func {
                    params: params
                        .iter()
                        .map(|p| self.apply_instantiations(p, instantiations))
                        .collect(),
                    returns: Box::new(self.apply_instantiations(returns, instantiations)),
                    generic_constraints: generic_constraints.clone(), // TODO: apply to constraints too
                }
            }
            Ty::Product(row) => Ty::Product(self.apply_instantiations_to_row(row, instantiations)),
            Ty::Nominal {
                name,
                properties,
                methods,
                type_params,
                instantiations: inst,
            } => Ty::Nominal {
                name: name.clone(),
                properties: self.apply_instantiations_to_row(properties, instantiations),
                methods: self.apply_instantiations_to_row(methods, instantiations),
                type_params: type_params.clone(),
                instantiations: inst.clone(),
            },
            _ => ty.clone(),
        }
    }

    fn apply_instantiations_to_row(
        &mut self,
        row: &Row,
        instantiations: &BTreeMap<TypeVar, Ty>,
    ) -> Row {
        match row {
            Row::Closed(ClosedRow { fields, values }) => Row::Closed(ClosedRow {
                fields: fields.clone(),
                values: values
                    .iter()
                    .map(|v| self.apply_instantiations(v, instantiations))
                    .collect(),
            }),
            Row::Open(_) => row.clone(),
        }
    }

    pub fn solve(mut self) -> Vec<Constraint> {
        let mut failed_attempts = 0;

        loop {
            let mut made_progress = false;
            let mut deferred = vec![];

            if self.constraints.is_empty() {
                break;
            }

            while let Some(mut constraint) = self.constraints.pop() {
                if !matches!(
                    constraint.state,
                    ConstraintState::Waiting | ConstraintState::Pending
                ) {
                    continue;
                }

                let before = constraint.state.clone();
                self.solve_constraint(&mut constraint).ok();
                made_progress |= before != constraint.state;

                if constraint.is_solved() {
                    self.current_depth = 0;
                } else {
                    deferred.push(constraint);
                }
            }

            if failed_attempts == MAX_FAILED_ATTEMPTS {
                break;
            }

            if failed_attempts == MAX_FAILED_ATTEMPTS - 1 && self.context.apply_defaults().is_err()
            {
                tracing::error!("Error applying defaults");
            }

            if !made_progress {
                failed_attempts += 1;
            }

            for constraint in deferred {
                self.constraints.add(constraint);
            }
        }

        self.errored
    }

    pub fn solve_constraint(&mut self, constraint: &mut Constraint) -> Result<(), TypeError> {
        let _s = trace_span!(
            "solve_constraint",
            id = constraint.id.0,
            state = %constraint.state,
            cause = %constraint.cause,
            kind = %constraint.kind,
            priority = constraint.priority()
        )
        .entered();

        let result = match constraint.kind.clone() {
            ConstraintKind::Equals(lhs, rhs) => self.solve_equals(constraint, lhs, rhs),
            ConstraintKind::LiteralPrimitive(ty, primitive) => {
                self.solve_literal_primitive(constraint, &ty, &primitive)
            }
            ConstraintKind::Call {
                callee,
                args,
                type_args,
                returning,
            } => self.solve_call(constraint, callee, type_args, args, returning),
            ConstraintKind::HasField {
                record, label, ty, ..
            } => self.solve_has_field(constraint, &record, label, ty),
            ConstraintKind::TyHasField {
                receiver,
                label,
                ty,
                ..
            } => self.solve_ty_has_field(constraint, &receiver, label, ty),
            ConstraintKind::RowClosed { record } => self.solve_row_closed(constraint, &record),
            #[allow(clippy::todo)]
            ConstraintKind::RowCombine(..) => todo!(),
        };

        match result {
            Ok(_) => (),
            Err(err) => {
                constraint.error(err);
                self.errored.push(constraint.clone())
            }
        }

        Ok(())
    }

    // If we just have a type, it could potentially be a nominal type in which case there might be _two_ places to check for
    // fields (properties vs methods). So this constraint just handles those cases.
    fn solve_ty_has_field(
        &mut self,
        constraint: &mut Constraint,
        receiver: &Ty,
        label: Label,
        ty: Ty,
    ) -> Result<(), TypeError> {
        let receiver = self.context.resolve(receiver);
        if matches!(receiver, Ty::Var(_)) {
            constraint.wait();
            return Ok(());
        }

        match receiver {
            Ty::Nominal {
                name,
                properties,
                methods,
                instantiations,
                ..
            } => {
                let Some(member) = self
                    .symbols
                    .member_kind(&name.symbol_id()?, &label.to_string())
                else {
                    constraint.error(TypeError::MemberNotFound(
                        name.name_str().to_string(),
                        label.to_string(),
                    ));

                    return Err(TypeError::MemberNotFound(
                        name.name_str().to_string(),
                        label.to_string(),
                    ));
                };

                match member.kind {
                    MemberKind::Property => {
                        // For instantiated types with open rows, we need to look at the base type
                        // to find the field type, then apply instantiations
                        let field_ty =
                            if !instantiations.is_empty() && matches!(properties, Row::Open(_)) {
                                // Find the field type from the base struct definition
                                // The base struct would have the canonical type variable
                                self.find_base_field_type(&name, &label)?
                            } else {
                                self.get_field_type(&properties, &label)?
                            };

                        // Apply instantiations to get the actual type for this instance
                        let instantiated_ty = self.apply_instantiations(&field_ty, &instantiations);

                        // Unify with the expected type
                        self.context.unify_ty_ty(&ty, &instantiated_ty)?;

                        constraint.state = ConstraintState::Solved;
                        Ok(())
                    }
                    MemberKind::Method | MemberKind::Initializer => {
                        // Get the method type
                        let method_ty =
                            if !instantiations.is_empty() && matches!(methods, Row::Open(_)) {
                                // For instantiated types, look up the base method and apply instantiations
                                self.find_base_method_type(&name, &label)?
                            } else {
                                self.get_field_type(&methods, &label)?
                            };

                        // Apply instantiations to the method type
                        let instantiated_method =
                            self.apply_instantiations(&method_ty, &instantiations);

                        // Unify with the expected type
                        self.context.unify_ty_ty(&ty, &instantiated_method)?;

                        constraint.state = ConstraintState::Solved;
                        Ok(())
                    }
                    _ => todo!("don't know how to handle {member:?} yet"),
                }
            }
            Ty::Product(row) => self.solve_has_field(constraint, &row, label, ty),
            _ => {
                constraint.wait();
                Ok(())
            }
        }
    }

    fn get_field_type(&self, row: &Row, label: &Label) -> Result<Ty, TypeError> {
        match row {
            Row::Closed(ClosedRow { fields, values }) => {
                for (field_label, field_value) in fields.iter().zip(values) {
                    if field_label == label {
                        return Ok(field_value.clone());
                    }
                }
                Err(TypeError::Unknown(format!(
                    "Field {label:?} not found in row"
                )))
            }
            Row::Open(row_var) => {
                if let Some(fields) = self.record_fields.get(row_var)
                    && let Some(ty) = fields.get(label)
                {
                    return Ok(ty.clone());
                }
                Err(TypeError::Unknown(format!(
                    "Field {label:?} not found in open row"
                )))
            }
        }
    }

    fn find_base_field_type(
        &self,
        _name: &crate::name::Name,
        label: &Label,
    ) -> Result<Ty, TypeError> {
        // Look for the field in the base struct definition (with RowVar::new(0))
        // This is where the canonical type variable would be stored
        if let Some(fields) = self.record_fields.get(&RowVar::new(0))
            && let Some(ty) = fields.get(label)
        {
            tracing::debug!("Found base field type for {label:?}: {ty:?}");
            return Ok(ty.clone());
        }

        Err(TypeError::Unknown(format!(
            "Field {label:?} not found in base struct {_name:?}"
        )))
    }

    fn find_base_method_type(
        &self,
        _name: &crate::name::Name,
        label: &Label,
    ) -> Result<Ty, TypeError> {
        // Look for the method in the base struct definition (with RowVar::new(1))
        // This is where the canonical type variable would be stored
        if let Some(methods) = self.record_fields.get(&RowVar::new(1))
            && let Some(ty) = methods.get(label)
        {
            return Ok(ty.clone());
        }

        Err(TypeError::Unknown(format!(
            "Method {label:?} not found in base struct {_name:?}"
        )))
    }

    fn solve_has_field(
        &mut self,
        constraint: &mut Constraint,
        record: &Row,
        label: Label,
        ty: Ty,
    ) -> Result<(), TypeError> {
        let row = self.context.resolve_row(record).clone();
        let ty = self.context.resolve(&ty);

        match &row {
            Row::Closed(ClosedRow { fields, values }) => {
                for (closed_label, closed_value) in fields.iter().zip(values) {
                    if &label == closed_label {
                        if closed_value != &ty {
                            self.context.unify_ty_ty(closed_value, &ty)?;
                        }

                        constraint.state = ConstraintState::Solved;
                        return Ok(());
                    }
                }

                constraint.state = ConstraintState::Error(TypeError::Unknown(format!(
                    "Closed row doesn't satisfy has field requirement. Row {row:?}, req: {label:?}: {ty:?}"
                )));
            }
            Row::Open(row_var) => {
                if let Some(existing) = self.record_fields.entry(*row_var).or_default().get(&label)
                {
                    tracing::debug!("Found existing receiver: record: {row:?} {existing:?}");
                    self.context.unify_ty_ty(existing, &ty)?;
                    existing.clone()
                } else {
                    tracing::debug!(
                        "Did not find existing for record: {row:?}, adding: {label:?}->{ty:?}"
                    );
                    self.record_fields
                        .entry(*row_var)
                        .or_default()
                        .insert(label, ty.clone());
                    ty
                };
            }
        }

        // Store the resolved field type in the output
        constraint.state = ConstraintState::Solved;

        Ok(())
    }

    fn solve_row_closed(
        &mut self,
        constraint: &mut Constraint,
        record: &Row,
    ) -> Result<(), TypeError> {
        if self
            .constraints
            .row_constraints_for(record)?
            .iter()
            .all(|c| c.is_solved())
        {
            let var = match record {
                Row::Open(var) => var,
                Row::Closed(..) => return Ok(()),
            };

            // Gather the fields
            let fields = self.record_fields.remove(var).unwrap_or_default();

            let mut labels = vec![];
            let mut values = vec![];

            for (label, ty) in fields.into_iter() {
                labels.push(label);
                values.push(self.context.resolve(&ty));
            }

            self.context.unify_row_var(
                *var,
                Row::Closed(ClosedRow {
                    fields: labels,
                    values,
                }),
            )?;

            constraint.state = ConstraintState::Solved;

            return Ok(());
        }

        // We don't have enough yet
        constraint.state = ConstraintState::Waiting;

        Ok(())
    }

    fn solve_call(
        &mut self,
        constraint: &mut Constraint,
        callee: Ty,
        type_args: Vec<Ty>,
        args: Vec<Ty>,
        returning: Ty,
    ) -> Result<(), TypeError> {
        let callee = self.context.resolve(&callee);

        let (params, returns, generic_constraints) = match callee {
            Ty::Func {
                params,
                returns,
                generic_constraints,
            } => (params, *returns, generic_constraints),
            Ty::Var(_) => {
                // Create a synthetic function type that matches the call
                // This will be unified with the actual function type later
                let params: Vec<Ty> = args
                    .iter()
                    .map(|_| Ty::Var(self.context.new_var(TypeVarKind::None)))
                    .collect();

                let returns = Ty::Var(self.context.new_var(TypeVarKind::None));

                let func_ty = Ty::Func {
                    params: params.clone(),
                    returns: Box::new(returns.clone()),
                    generic_constraints: vec![],
                };

                let id = self.constraints.next_id();
                let child = self.constraints.add(Constraint {
                    id,
                    expr_id: constraint.expr_id,
                    cause: ConstraintCause::Call,
                    kind: ConstraintKind::Equals(callee, func_ty),
                    parent: Some(constraint.id),
                    children: vec![],
                    state: ConstraintState::Pending,
                });

                constraint.children.push(child);

                (params, returns, vec![])
            }
            _ => {
                constraint.error(TypeError::Unknown("Can't call non-func type".to_string()))?;
            }
        };

        // If it's the first time this constraint has been attempted, spawn the child
        // constraints
        if constraint.state == ConstraintState::Pending {
            let mut substitutions = Default::default();

            if self.current_depth > 128 {
                tracing::trace!("Ran into 128 depth");
                let var = self.context.new_var(TypeVarKind::Void);
                self.context.unify_ty_ty(&returns, &Ty::Var(var))?;
                constraint.state = ConstraintState::Solved;
                return Ok(());
            }

            self.current_depth += 1;

            for (param, arg) in params.iter().zip(args.iter()) {
                let param = param.instantiate(self.context, &mut substitutions);

                let id = self.constraints.next_id();
                let child = Constraint {
                    id,
                    expr_id: constraint.expr_id, // TODO: It'd be nicer to use the arg id
                    cause: ConstraintCause::Call,
                    kind: ConstraintKind::Equals(param.clone(), arg.clone()),
                    parent: Some(constraint.id),
                    children: vec![],
                    state: ConstraintState::Pending,
                };

                self.constraints.add(child);
                constraint.children.push(id);
            }

            let returns = returns.instantiate(self.context, &mut substitutions);
            let id = self.constraints.next_id();
            let child = Constraint {
                id,
                expr_id: constraint.expr_id, // TODO: It'd be nicer to use the ret id
                cause: ConstraintCause::Call,
                kind: ConstraintKind::Equals(returns.clone(), returning.clone()),
                parent: Some(constraint.id),
                children: vec![],
                state: ConstraintState::Pending,
            };
            self.constraints.add(child);
            constraint.children.push(id);

            // Add generic constraints as children
            for generic_constraint in generic_constraints {
                let instantiated = generic_constraint.instantiate(self.context, &mut substitutions);
                let id = self.constraints.next_id();
                let child = Constraint {
                    id,
                    expr_id: constraint.expr_id,
                    cause: ConstraintCause::Call,
                    kind: instantiated,
                    parent: Some(constraint.id),
                    children: vec![],
                    state: ConstraintState::Pending,
                };
                self.constraints.add(child);
                constraint.children.push(id);
            }

            constraint.state = ConstraintState::Waiting;
        } else if constraint.state == ConstraintState::Waiting
            && constraint
                .children
                .iter()
                .all(|c| self.constraints.state_for(c) == Some(ConstraintState::Solved))
        {
            constraint.state = ConstraintState::Solved;
        } else {
            constraint.state = ConstraintState::Waiting;
        }

        Ok(())
    }

    fn solve_equals(
        &mut self,
        constraint: &mut Constraint,
        lhs: Ty,
        rhs: Ty,
    ) -> Result<(), TypeError> {
        let lhs = self.context.resolve(&lhs);
        let rhs = self.context.resolve(&rhs);

        match (lhs, rhs) {
            (Ty::Var(lhs), Ty::Var(rhs)) => {
                // Determine which type var should constrain the other based on specificity
                let (to_unify, with) = if lhs.kind.is_more_specific_than(&rhs.kind) {
                    (rhs, lhs)
                } else {
                    (lhs, rhs)
                };

                self.context.unify_var_ty(to_unify, Ty::Var(with))?;
                constraint.state = ConstraintState::Waiting;
                Ok(())
            }
            (Ty::Var(var), ty) | (ty, Ty::Var(var)) => {
                // Check if the type variable can accept this type
                if !var.accepts(&ty) {
                    constraint.state = ConstraintState::Error(TypeError::Mismatch(
                        format!("{var:?}"),
                        format!("{ty:?}"),
                    ));
                    return Err(TypeError::Mismatch(format!("{var:?}"), format!("{ty:?}")));
                }

                self.context.unify_var_ty(var, ty.clone())?;
                tracing::trace!("Unifying {var:?} -> {ty:?}");
                constraint.state = ConstraintState::Solved;
                Ok(())
            }
            (Ty::Primitive(p1), Ty::Primitive(p2)) if p1 == p2 => {
                constraint.state = ConstraintState::Solved;
                Ok(())
            }
            (lhs_ty, rhs_ty) => {
                constraint.state = ConstraintState::Error(TypeError::Mismatch(
                    format!("{lhs_ty:?}"),
                    format!("{rhs_ty:?}"),
                ));
                Err(TypeError::Mismatch(
                    format!("{lhs_ty:?}"),
                    format!("{rhs_ty:?}"),
                ))
            }
        }
    }

    fn solve_literal_primitive(
        &mut self,
        constraint: &mut Constraint,
        ty: &Ty,
        primitive: &Primitive,
    ) -> Result<(), TypeError> {
        let resolved = self.context.resolve(ty);

        match resolved {
            Ty::Primitive(p) => {
                if p == *primitive {
                    constraint.state = ConstraintState::Solved;
                    self.context.unify_ty_ty(ty, &Ty::Primitive(*primitive))?;
                } else {
                    constraint.state = ConstraintState::Error(TypeError::Mismatch(
                        primitive.to_string(),
                        p.to_string(),
                    ));
                }
            }
            Ty::Var(type_var) => {
                if type_var.accepts(&Ty::Primitive(*primitive)) {
                    constraint.state = ConstraintState::Waiting;
                } else {
                    constraint.state =
                        ConstraintState::Error(TypeError::Unknown("Unexpected type".to_string()));
                }
            }
            _ => unreachable!("Internal error"),
        }

        Ok(())
    }
}
