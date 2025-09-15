use crate::{
    label::Label,
    name::Name,
    name_resolution::symbol::Symbol,
    span::Span,
    types::{
        constraint::{Constraint, ConstraintCause},
        fields::TypeFields,
        passes::inference_pass::{InferencePass, Wants},
        ty::{Level, Ty},
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, apply, unify},
        type_session::TypeDef,
    },
};

#[derive(Debug, Clone)]
pub struct Member {
    pub receiver: Ty,
    pub label: Label,
    pub ty: Ty,
    pub cause: ConstraintCause,
    pub span: Span,
}

impl Member {
    pub fn solve(
        &self,
        pass: &mut InferencePass,
        next_wants: &mut Wants,
        substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        let receiver = apply(self.receiver.clone(), substitutions);
        let ty = apply(self.ty.clone(), substitutions);

        if matches!(receiver, Ty::UnificationVar { .. }) {
            // If we don't know what the receiver is yet, we can't do much
            next_wants.push(Constraint::Member(self.clone()));
            return Ok(false);
        }

        println!("receiver: {receiver:?}");

        if let Ty::Struct(Some(Name::Resolved(Symbol::Type(type_id), _)), _) = &receiver {
            // If it's a nominal type, check methods first
            if let Some(TypeDef {
                fields: TypeFields::Struct { methods, .. },
                ..
            }) = pass.session.phase.type_constructors.get(type_id)
                && let Some(method) = methods.get(&self.label)
                && !method.is_static
            {
                let Some(method_entry) = pass.term_env.lookup(&method.symbol).cloned() else {
                    panic!("did not find type for method named {:?}", self.label);
                };

                let method_ty = method_entry.solver_instantiate(
                    pass,
                    Level(1),
                    substitutions,
                    next_wants,
                    self.span,
                );

                // For instance methods, the method_ty looks like: self -> arg1 -> arg2 -> ret
                // We need to apply the receiver to get: arg1 -> arg2 -> ret
                // Or for zero-arg instance methods: self -> ret, we need to return func() -> ret
                let applied_method_ty = if let Ty::Func(param, rest) = method_ty {
                    // Unify the receiver with the self parameter
                    unify(&receiver, &param, substitutions, &mut pass.session.vars)?;
                    // Return the rest of the function type (without self)
                    // If rest is not a function, it means this was a zero-arg method (only had self)
                    // In that case, we need to wrap it in a zero-arg function
                    if !matches!(*rest, Ty::Func(..)) {
                        // Zero-arg method: wrap return type in func(void) -> ret
                        Ty::Func(Box::new(Ty::Void), rest)
                    } else {
                        *rest
                    }
                } else {
                    unreachable!()
                };

                return unify(
                    &ty,
                    &applied_method_ty,
                    substitutions,
                    &mut pass.session.vars,
                );
            }
        }

        // See if it's a static method or enum variant constructor
        if let Ty::Constructor { type_id, .. } = &receiver
            && let Some(TypeDef {
                fields: TypeFields::Struct { methods, .. },
                ..
            }) = pass.session.phase.type_constructors.get(type_id)
            && let Some(method) = methods.get(&self.label)
            && method.is_static
        {
            // If it's a nominal type, check methods first
            let Some(method_entry) = pass.term_env.lookup(&method.symbol).cloned() else {
                panic!("did not find type for method named {:?}", self.label);
            };

            let method_ty = method_entry.solver_instantiate(
                pass,
                Level(1),
                substitutions,
                next_wants,
                self.span,
            );

            return unify(&ty, &method_ty, substitutions, &mut pass.session.vars);
        }

        // See if it's an enum constructor
        if let Ty::Sum(Some(Name::Resolved(Symbol::Type(type_id), _)), _) = &receiver {
            // If it's a nominal type, check methods first
            if let Some(TypeDef {
                fields: TypeFields::Enum { variants, .. },
                ..
            }) = pass.session.phase.type_constructors.get(type_id)
                && let Some(variant) = variants.get(&self.label)
            {
                let variant_entry = pass
                    .term_env
                    .lookup(&variant.symbol)
                    .cloned()
                    .expect("didn't get variant ty from term env");

                let variant_ty = variant_entry.solver_instantiate(
                    pass,
                    Level(1),
                    substitutions,
                    next_wants,
                    self.span,
                );

                println!("variant_ty: {variant_ty:?}. ty: {ty:?}");

                return unify(&ty, &variant_ty, substitutions, &mut pass.session.vars);
            }
        }

        // If it's not a method, figure out the row and emit a has field constraint
        let (Ty::Struct(_, row) | Ty::Sum(_, row)) = receiver else {
            return Err(TypeError::ExpectedRow(receiver));
        };

        next_wants._has_field(
            *row,
            self.label.clone(),
            self.ty.clone(),
            self.cause,
            self.span,
        );

        Ok(true)
    }
}
