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

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeParameter(pub u32);

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, DriveMut, Ord)]
pub enum GenericState {
    #[drive(skip)]
    Template(Vec<TypeParameter>),
    Instance(BTreeMap<TypeParameter, Ty>),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, DriveMut, PartialOrd, Ord)]
pub enum Ty {
    Primitive(#[drive(skip)] Primitive),
    Metatype {
        ty: Box<Ty>,
        properties: Row,
        methods: Row,
    },
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
        generics: GenericState,
    },
    Product(Row),
    Var(#[drive(skip)] TypeVar),
    TypeParameter(#[drive(skip)] TypeParameter),
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
            Ty::Metatype {
                ty,
                properties,
                methods,
            } => {
                if let Row::Closed(ClosedRow { values, .. }) = properties {
                    return values.iter().any(|t| t.contains_canonical_var());
                }

                if let Row::Closed(ClosedRow { values, .. }) = methods {
                    return values.iter().any(|t| t.contains_canonical_var());
                }

                ty.contains_canonical_var()
            }
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
            Ty::TypeParameter(_) => true,
            Ty::Var(..) => false,
            Ty::Product(..) => false,
            Ty::Sum(..) => false,
            Ty::Label(_, ty) => ty.contains_canonical_var(),
        }
    }

    pub fn instantiate(
        &self,
        context: &mut TypeVarContext,
        substitutions: &mut BTreeMap<TypeParameter, TypeVar>,
    ) -> Ty {
        match self {
            Ty::Metatype {
                ty,
                properties,
                methods,
            } => Ty::Metatype {
                ty: Box::new(ty.instantiate(context, substitutions)),
                properties: properties.clone(),
                methods: methods.clone(),
            },
            Ty::Primitive(..) => self.clone(),
            Ty::Nominal {
                generics: GenericState::Instance(..),
                ..
            } => self.clone(),
            Ty::Nominal {
                name,
                properties,
                methods,
                generics: GenericState::Template(type_params),
            } => {
                // Create fresh type variables for each generic parameter
                let mut local_subs = BTreeMap::new();
                for type_param in type_params {
                    if !substitutions.contains_key(type_param) {
                        let fresh_var = context.new_var(TypeVarKind::Instantiated);
                        substitutions.insert(*type_param, fresh_var);
                        local_subs.insert(*type_param, fresh_var);
                    }
                }

                // Instantiate property and method rows with the substitutions
                let inst_properties = properties.instantiate_row(context, substitutions);
                let inst_methods = methods.instantiate_row(context, substitutions);

                // Build instantiations map for this instance
                let mut inst_map = BTreeMap::new();
                for (canonical, instantiated) in local_subs.iter() {
                    inst_map.insert(*canonical, Ty::Var(*instantiated));
                }

                Ty::Nominal {
                    name: name.clone(),
                    properties: inst_properties,
                    methods: inst_methods,
                    generics: GenericState::Instance(inst_map),
                }
            }
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
            Ty::TypeParameter(type_param) => {
                if let Some(existing) = substitutions.get(type_param) {
                    Ty::Var(*existing)
                } else {
                    let fresh_var = context.new_var(TypeVarKind::Instantiated);
                    substitutions.insert(*type_param, fresh_var);
                    Ty::Var(fresh_var)
                }
            }
            Ty::Var(type_var) => self.clone(),
            #[allow(clippy::todo)]
            Ty::Product(..) => todo!(),
            #[allow(clippy::todo)]
            Ty::Sum(..) => todo!(),
            #[allow(clippy::todo)]
            Ty::Label(_, _) => todo!(),
        }
    }
}
