use std::{collections::BTreeMap, fmt::Display};

use derive_visitor::DriveMut;

use crate::{
    name::Name,
    types::{
        constraint_kind::ConstraintKind,
        row::{ClosedRow, Label, Row},
        type_var::{TypeVar, TypeVarKind},
        type_var_context::TypeVarContext,
    },
};

#[derive(Debug, Clone, Hash, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Primitive {
    Void,
    Int,
    Float,
    Bool,
    Pointer,
    Byte,
}

impl Display for Primitive {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, DriveMut, PartialOrd, Ord)]
pub enum Ty {
    Primitive(#[drive(skip)] Primitive),
    Func {
        params: Vec<Ty>,
        returns: Box<Ty>,
        // Constraints that must be checked when this function is instantiated
        generic_constraints: Vec<ConstraintKind>,
    },
    Nominal {
        #[drive(skip)]
        name: Name,
        properties: Row,
        methods: Row,
        generic_constraints: Vec<ConstraintKind>,
    },
    Product(Row),
    Var(#[drive(skip)] TypeVar),
    Sum(Row),
    Label(#[drive(skip)] Label, Box<Self>),
}

impl Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty::Primitive(primitive) => write!(f, "{primitive:?}"),
            _ => write!(f, "{self:?}"),
        }
    }
}

#[allow(non_upper_case_globals)]
impl Ty {
    pub const Int: Ty = Ty::Primitive(Primitive::Int);
    pub const Float: Ty = Ty::Primitive(Primitive::Float);
    pub const Bool: Ty = Ty::Primitive(Primitive::Bool);
    pub const Byte: Ty = Ty::Primitive(Primitive::Byte);
    pub const Pointer: Ty = Ty::Primitive(Primitive::Pointer);
    pub const Void: Ty = Ty::Primitive(Primitive::Void);

    pub fn optional(&self) -> Ty {
        self.clone() // TODO:
    }

    pub fn type_vars(&self) -> Vec<TypeVar> {
        match self {
            Self::Var(type_var) => vec![*type_var],
            _ => vec![],
        }
    }

    pub fn contains_canonical_var(&self) -> bool {
        match self {
            Ty::Nominal {
                properties,
                methods,
                ..
            } => {
                if let Row::Closed(ClosedRow { values, .. }) = properties {
                    return values.iter().any(|t| t.contains_canonical_var());
                }

                if let Row::Closed(ClosedRow { values, .. }) = methods {
                    return values.iter().any(|t| t.contains_canonical_var());
                }

                false
            }
            Ty::Primitive(..) => false,
            Ty::Func {
                params,
                returns,
                generic_constraints,
            } => {
                params.iter().any(|p| p.contains_canonical_var())
                    || returns.contains_canonical_var()
                    || generic_constraints
                        .iter()
                        .any(|c| c.contains_canonical_var())
            }
            Ty::Var(type_var) => type_var.kind == TypeVarKind::Canonical,
            Ty::Product(..) => false,
            Ty::Sum(..) => false,
            Ty::Label(_, ty) => ty.contains_canonical_var(),
        }
    }

    pub fn instantiate(
        &self,
        context: &mut TypeVarContext,
        substitutions: &mut BTreeMap<TypeVar, TypeVar>,
    ) -> Ty {
        match self {
            Ty::Primitive(..) => self.clone(),
            Ty::Nominal {
                name,
                properties,
                methods,
                generic_constraints,
            } => Ty::Nominal {
                name: name.clone(),
                properties: if let Row::Closed(ClosedRow { fields, values }) = properties {
                    Row::Closed(ClosedRow {
                        fields: fields.clone(),
                        values: values
                            .iter()
                            .map(|v| v.instantiate(context, substitutions))
                            .collect(),
                    })
                } else {
                    properties.clone()
                },
                methods: if let Row::Closed(ClosedRow { fields, values }) = methods {
                    Row::Closed(ClosedRow {
                        fields: fields.clone(),
                        values: values
                            .iter()
                            .map(|v| v.instantiate(context, substitutions))
                            .collect(),
                    })
                } else {
                    methods.clone()
                },
                generic_constraints: generic_constraints
                    .iter()
                    .map(|c| c.instantiate(context, substitutions))
                    .collect(),
            },
            Ty::Func {
                params,
                returns,
                generic_constraints,
            } => Ty::Func {
                params: params
                    .iter()
                    .map(|p| p.instantiate(context, substitutions))
                    .collect(),
                returns: Box::new(returns.instantiate(context, substitutions)),
                generic_constraints: generic_constraints
                    .iter()
                    .map(|c| c.instantiate(context, substitutions))
                    .collect(),
            },
            Ty::Var(type_var) => {
                if type_var.kind == TypeVarKind::Canonical {
                    let new_var = substitutions
                        .entry(*type_var)
                        .or_insert_with(|| context.new_var(TypeVarKind::Instantiated));
                    tracing::trace!("replacing canonical {type_var:?} with {new_var:?}");
                    Ty::Var(*new_var)
                } else {
                    self.clone()
                }
            }
            #[allow(clippy::todo)]
            Ty::Product(..) => todo!(),
            #[allow(clippy::todo)]
            Ty::Sum(..) => todo!(),
            #[allow(clippy::todo)]
            Ty::Label(_, _) => todo!(),
        }
    }
}
