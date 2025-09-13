use crate::{
    label::Label,
    name::Name,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    span::Span,
    types::{
        passes::inference_pass::{InferencePass, Wants},
        row::Row,
        scheme::Predicate,
        term_environment::EnvEntry,
        ty::{Level, Ty},
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, apply, apply_row, unify},
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
            if let Some(entry) = pass
                .term_env
                .lookup_method(*type_id, self.label.clone())
                .cloned()
            {
                let method_ty = match entry {
                    EnvEntry::Mono(ty) => ty.clone(),
                    EnvEntry::Scheme(scheme) => {
                        scheme.instantiate(pass, Level(1), next_wants, self.span).0
                    }
                };

                return unify(&ty, &method_ty, substitutions, &mut pass.session.vars);
            }
        }

        // If it's not a method, figure out the row and emit a has field constraint
        let Ty::Struct(_, row) = receiver else {
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
