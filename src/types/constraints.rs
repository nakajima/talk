use crate::{
    label::Label,
    name::Name,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    span::Span,
    types::{
        fields::TypeFields,
        passes::inference_pass::{InferencePass, Wants},
        row::Row,
        scheme::Predicate,
        term_environment::EnvEntry,
        ty::{Level, Ty},
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, apply, apply_row, unify},
        type_session::TypeDef,
    },
};

#[derive(Debug, Clone, Copy)]
pub enum ConstraintCause {
    Annotation(NodeID),
    Member(NodeID),
    Literal(NodeID),
    Assignment(NodeID),
    Call(NodeID),
    Condition(NodeID),
    Pattern(NodeID),
    MatchArm(NodeID),
    CallTypeArg(NodeID),
    Internal,
}

#[derive(Debug, Clone)]
pub struct Equals {
    pub lhs: Ty,
    pub rhs: Ty,
    pub cause: ConstraintCause,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct HasField {
    pub row: Row,
    pub label: Label,
    pub ty: Ty,
    pub cause: ConstraintCause,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Member {
    pub receiver: Ty,
    pub label: Label,
    pub ty: Ty,
    pub cause: ConstraintCause,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum Constraint {
    Equals(Equals),
    HasField(HasField),
    Member(Member),
}

impl Constraint {
    pub fn span(&self) -> Span {
        match self {
            Constraint::Equals(c) => c.span,
            Constraint::HasField(c) => c.span,
            Constraint::Member(c) => c.span,
        }
    }

    pub fn apply(mut self, substitutions: &mut UnificationSubstitutions) -> Constraint {
        match &mut self {
            Constraint::Equals(e) => {
                e.lhs = apply(e.lhs.clone(), substitutions);
                e.rhs = apply(e.rhs.clone(), substitutions);
            }
            Constraint::HasField(h) => {
                h.row = apply_row(h.row.clone(), substitutions);
                h.ty = apply(h.ty.clone(), substitutions);
            }
            Constraint::Member(member) => {
                member.ty = apply(member.ty.clone(), substitutions);
                member.receiver = apply(member.receiver.clone(), substitutions)
            }
        }
        self
    }

    pub fn into_predicate(&self, substitutions: &mut UnificationSubstitutions) -> Predicate {
        match self {
            Self::HasField(has_field) => {
                let Row::Param(row_param) = apply_row(has_field.row.clone(), substitutions) else {
                    panic!("HasField predicate must be for row")
                };
                Predicate::HasField {
                    row: row_param,
                    label: has_field.label.clone(),
                    ty: apply(has_field.ty.clone(), substitutions),
                }
            }
            Self::Member(member) => Predicate::Member {
                receiver: apply(member.receiver.clone(), substitutions),
                label: member.label.clone(),
                ty: apply(member.ty.clone(), substitutions),
            },
            _ => unimplemented!("No predicate for constraint: {self:?}"),
        }
    }
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

        if matches!(receiver, Ty::MetaVar { .. }) {
            // If we don't know what the receiver is yet, we can't do much
            next_wants.push(Constraint::Member(self.clone()));
            return Ok(false);
        }

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

                let method_ty = match &method_entry {
                    EnvEntry::Mono(ty) => ty.clone(),
                    EnvEntry::Scheme(scheme) => {
                        scheme
                            .solver_instantiate(
                                pass,
                                Level(1),
                                next_wants,
                                self.span,
                                substitutions,
                            )
                            .0
                    }
                };

                // For instance methods, the method_ty looks like: self -> arg1 -> arg2 -> ret
                // We need to apply the receiver to get: arg1 -> arg2 -> ret
                // Or for zero-arg instance methods: self -> ret, we get just ret
                let applied_method_ty = if let Ty::Func(param, rest) = method_ty {
                    // Unify the receiver with the self parameter
                    unify(&receiver, &param, substitutions, &mut pass.session.vars)?;
                    // Return the rest of the function type (without self)
                    *rest
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

        // See if it's a static method
        if let Ty::Constructor { type_id, .. } = &receiver {
            // If it's a nominal type, check methods first
            if let Some(TypeDef {
                fields: TypeFields::Struct { methods, .. },
                ..
            }) = pass.session.phase.type_constructors.get(type_id)
                && let Some(method) = methods.get(&self.label)
                && method.is_static
            {
                println!("constructor static check: {:?}", self.label);
                let Some(method_entry) = pass.term_env.lookup(&method.symbol).cloned() else {
                    panic!("did not find type for method named {:?}", self.label);
                };

                let method_ty = match &method_entry {
                    EnvEntry::Mono(ty) => ty.clone(),
                    EnvEntry::Scheme(scheme) => {
                        scheme
                            .solver_instantiate(
                                pass,
                                Level(1),
                                next_wants,
                                self.span,
                                substitutions,
                            )
                            .0
                    }
                };

                let Ty::Func(_head, rest) = method_ty else {
                    unreachable!()
                };

                return unify(&ty, &rest, substitutions, &mut pass.session.vars);
            }

            // See if it's an enum constructor
            if let Some(TypeDef {
                fields: TypeFields::Enum { variants, .. },
                ..
            }) = pass.session.phase.type_constructors.get(type_id)
                && let Some(variant) = variants.get(&self.label).cloned()
            {
                let variant_entry = pass
                    .term_env
                    .lookup(&variant.symbol)
                    .cloned()
                    .expect("did not get entry for variant");
                println!(
                    "enum constructor check: {:?}, {variant_entry:?}",
                    self.label
                );

                let variant_ty = match &variant_entry {
                    EnvEntry::Mono(ty) => ty.clone(),
                    EnvEntry::Scheme(scheme) => {
                        scheme
                            .solver_instantiate(
                                pass,
                                Level(1),
                                next_wants,
                                self.span,
                                substitutions,
                            )
                            .0
                    }
                };

                return unify(&self.ty, &variant_ty, substitutions, &mut pass.session.vars);
            }
        }

        println!("got past those?");

        // If it's not a method, figure out the row and emit a has field constraint
        let (Ty::Struct(_, row) | Ty::Variant(_, row)) = receiver else {
            return Err(TypeError::ExpectedRow(receiver));
        };

        println!("got row: {:?} {row:?}", self.label);

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
