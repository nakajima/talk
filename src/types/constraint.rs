use std::collections::BTreeMap;
use std::fmt::{self, Display};
use std::hash::Hash;

use crate::types::ty::TypeParameter;
use crate::types::visitors::inference_visitor::Substitutions;
use crate::{
    expr_id::ExprID,
    type_checker::TypeError,
    types::{
        constraint_kind::ConstraintKind, constraint_set::ConstraintId, ty::Primitive,
        type_var::TypeVar,
    },
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstraintState {
    Pending,
    Waiting,
    Solved,
    Error(TypeError),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstraintCause {
    Annotation(ExprID),
    Assignment(ExprID),
    FuncReturn(ExprID),
    PrimitiveLiteral(ExprID, Primitive),
    EnumLiteral,
    RecordLiteral,
    TupleLiteral,
    Hoisted,
    Variable,
    Call,
    MemberAccess,
    Condition,
    StructLiteral,
    MethodDefinition,
    StaticMethodDefinition,
    PropertyDefinition,
    InitializerDefinition,
    InitializerCall,
    PropertiesEmpty,
    MatchArm,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constraint {
    pub id: ConstraintId,
    pub expr_id: ExprID,
    pub cause: ConstraintCause,
    pub kind: ConstraintKind,
    pub parent: Option<ConstraintId>,
    pub children: Vec<ConstraintId>,
    pub state: ConstraintState,
}

impl PartialOrd for Constraint {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Constraint {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id.0.cmp(&other.id.0)
    }
}

impl Hash for Constraint {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl Constraint {
    pub(crate) fn instantiate(
        &self,
        substitutions: &Substitutions,
    ) -> Result<Constraint, TypeError> {
        let kind = match self.kind.clone() {
            ConstraintKind::Equals(lhs, rhs) => ConstraintKind::Equals(
                lhs.substituting(substitutions)?,
                rhs.substituting(substitutions)?,
            ),
            ConstraintKind::Call {
                callee,
                type_args,
                args,
                returning,
            } => {
                let mut new_type_args = vec![];
                let mut new_args = vec![];

                for arg in type_args {
                    new_type_args.push(arg.substituting(substitutions)?);
                }

                for arg in args {
                    new_args.push(arg.substituting(substitutions)?);
                }
                ConstraintKind::Call {
                    callee: callee.substituting(substitutions)?,
                    type_args: new_type_args,
                    args: new_args,
                    returning: returning.substituting(substitutions)?,
                }
            }
            ConstraintKind::LiteralPrimitive(ty, primitive) => {
                ConstraintKind::LiteralPrimitive(ty.substituting(substitutions)?, primitive)
            }
            ConstraintKind::RowCombine(expr_id, row_combination) => {
                ConstraintKind::RowCombine(expr_id, row_combination)
            }
            ConstraintKind::RowClosed { record } => ConstraintKind::RowClosed {
                record: record.substituting(substitutions)?,
            },
            ConstraintKind::HasField {
                record,
                label,
                ty,
                index,
            } => ConstraintKind::HasField {
                record: record.substituting(substitutions)?,
                label,
                ty: ty.substituting(substitutions)?,
                index,
            },
            ConstraintKind::TyHasField {
                receiver,
                label,
                ty,
                index,
            } => ConstraintKind::TyHasField {
                receiver: receiver.substituting(substitutions)?,
                label,
                ty: ty.substituting(substitutions)?,
                index,
            },
        };

        Ok(Constraint {
            id: self.id,
            expr_id: self.expr_id,
            cause: self.cause.clone(),
            kind,
            parent: self.parent,
            children: self.children.clone(),
            state: self.state.clone(),
        })
    }

    pub fn type_vars(&self) -> Vec<TypeVar> {
        match &self.kind {
            ConstraintKind::Equals(lhs, rhs) => {
                [lhs, rhs].iter().flat_map(|t| t.type_vars()).collect()
            }
            ConstraintKind::LiteralPrimitive(ty, _) => ty.type_vars(),
            ConstraintKind::Call {
                callee,
                args,
                returning,
                type_args,
            } => {
                let mut res = vec![];
                res.extend(callee.type_vars());
                res.extend(args.iter().flat_map(|t| t.type_vars()));
                res.extend(type_args.iter().flat_map(|t| t.type_vars()));
                res.extend(returning.type_vars());
                res
            }
            ConstraintKind::HasField { ty, .. } => {
                let mut res = vec![];
                res.extend(ty.type_vars());
                res
            }
            ConstraintKind::TyHasField { receiver, ty, .. } => {
                let mut res = vec![];
                res.extend(receiver.type_vars());
                res.extend(ty.type_vars());
                res
            }
            ConstraintKind::RowClosed { .. } => vec![],
            #[allow(clippy::todo)]
            ConstraintKind::RowCombine(..) => {
                todo!()
            }
        }
    }

    pub fn priority(&self) -> usize {
        match &self.kind {
            ConstraintKind::Equals(..) => 100,
            ConstraintKind::Call { .. } => 50,
            ConstraintKind::LiteralPrimitive(..) => 100,
            ConstraintKind::HasField {
                index: Some(index), ..
            } => 60 - index, // Per-field constraints for struct defs/blocks
            ConstraintKind::HasField { index: None, .. } => 30, // Method/initializer lookup
            ConstraintKind::TyHasField { .. } => 20,
            ConstraintKind::RowClosed { .. } => 1,
            ConstraintKind::RowCombine(..) => 10,
        }
    }

    pub fn is_solved(&self) -> bool {
        self.state == ConstraintState::Solved
    }

    pub fn error(&mut self, error: TypeError) -> Result<!, TypeError> {
        self.state = ConstraintState::Error(error.clone());
        Err(error)
    }

    pub fn wait(&mut self) {
        self.state = ConstraintState::Waiting
    }
}

impl Display for ConstraintState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConstraintState::Pending => write!(f, "PENDING"),
            ConstraintState::Waiting => write!(f, "WAITING"),
            ConstraintState::Solved => write!(f, "SOLVED"),
            ConstraintState::Error(_) => write!(f, "ERROR"),
        }
    }
}

impl Display for ConstraintCause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::fmt::Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{:?} ⊑ {} {:?}]", self.expr_id, self.kind, self.cause,)
    }
}
