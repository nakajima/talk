use std::fmt::{self, Display};
use std::hash::Hash;

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
    RecordLiteral,
    TupleLiteral,
    Hoisted,
    Variable,
    Call,
    MemberAccess,
    Condition,
    StructLiteral,
    MethodDefinition,
    PropertyDefinition,
    InitializerDefinition,
    InitializerCall,
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

impl Hash for Constraint {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl Constraint {
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
            #[allow(clippy::todo)]
            ConstraintKind::HasField { ty, .. } => {
                let mut res = vec![];
                res.extend(ty.type_vars());
                res
            }
            ConstraintKind::RowClosed { record } => record.type_vars(),
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
            } => 40 - index,
            ConstraintKind::HasField { index: None, .. } => 20,
            ConstraintKind::RowClosed { .. } => 10,
            ConstraintKind::RowCombine(..) => 10,
        }
    }

    pub fn is_solved(&self) -> bool {
        self.state == ConstraintState::Solved
    }

    pub fn error(&mut self, error: TypeError) {
        self.state = ConstraintState::Error(error)
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

impl Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[C{} @ E{}] {} | {} | ",
            self.id, self.expr_id, self.state, self.cause
        )?;

        if let Some(parent) = self.parent {
            write!(f, "parent:{parent} | ")?;
        }

        write!(f, "{}", self.kind)?;

        if !self.children.is_empty() {
            write!(f, " | children:")?;
            for (i, child) in self.children.iter().enumerate() {
                if i > 0 {
                    write!(f, ",")?;
                }
                write!(f, "C{child}")?;
            }
        }

        Ok(())
    }
}
