use std::{collections::BTreeMap, fmt::Display};

use derive_visitor::DriveMut;

use crate::{
    name::Name,
    type_checker::TypeError,
    types::{
        constraint_kind::ConstraintKind,
        row::{ClosedRow, Label, Row},
        type_var::{TypeVar, TypeVarKind},
        type_var_context::{RowVarKind, TypeVarContext},
        visitors::{
            definition_visitor::{Definition, TypeScheme, TypeSchemeKind},
            inference_visitor::Substitutions,
        },
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

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum InferredDefinition {
    // We carry the canonical type parameter and its per-function-substitution
    // canonical type var, so instantiation can reuse the mapping.
    TypeParameter(TypeParameter),
    Concrete(Box<Ty>),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, DriveMut, PartialOrd, Ord)]
pub enum Ty {
    Primitive(#[drive(skip)] Primitive),
    Metatype {
        ty: Box<Ty>,
        properties: Row,
        methods: Row,
    },
    RawScheme(#[drive(skip)] TypeScheme<Definition>),
    Scheme(#[drive(skip)] TypeScheme<InferredDefinition>),
    Func {
        params: Vec<Ty>,
        returns: Box<Ty>,
        // Constraints that must be checked when this function is instantiated
        // TODO: This needs to go
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

    pub fn canonical_type_vars(&self) -> Vec<TypeVar> {
        match self {
            Self::Var(type_var) if matches!(type_var.kind, TypeVarKind::Canonical(_)) => {
                vec![*type_var]
            }
            _ => vec![],
        }
    }

    pub fn contains_canonical_var(&self) -> bool {
        match self {
            Ty::RawScheme(_) => true,
            Ty::Scheme(_) => true,
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
                match properties {
                    Row::Closed(ClosedRow { values, .. }) => {
                        if values.iter().any(|v| v.contains_canonical_var()) {
                            return true;
                        }
                    }
                    Row::Open(row_var) => {
                        if row_var.is_canonical() {
                            return true;
                        }
                    }
                }

                match methods {
                    Row::Closed(ClosedRow { values, .. }) => {
                        if values.iter().any(|v| v.contains_canonical_var()) {
                            return true;
                        }
                    }
                    Row::Open(row_var) => {
                        if row_var.is_canonical() {
                            return true;
                        }
                    }
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
            Ty::Var(type_var) => matches!(type_var.kind, TypeVarKind::Canonical(_)),
            Ty::Product(row) => match row {
                Row::Closed(ClosedRow { values, .. }) => {
                    values.iter().any(|v| v.contains_canonical_var())
                }
                Row::Open(row_var) => row_var.is_canonical(),
            },
            Ty::Sum(..) => false,
            Ty::Label(_, ty) => ty.contains_canonical_var(),
        }
    }

    pub(crate) fn substituting(self, substitutions: &Substitutions) -> Result<Ty, TypeError> {
        let ty = match self {
            #[allow(clippy::panic)]
            Ty::RawScheme(_) => panic!("Cannot instantiate raw scheme: {self:?}"),
            Ty::Var(type_var) => {
                if let TypeVarKind::Canonical(tp) = type_var.kind
                    && let Some(new_var) = substitutions.get_type_parameter(&tp)
                {
                    Ty::Var(*new_var)
                } else {
                    self
                }
            }
            Ty::Primitive(..) => self,
            Ty::Metatype {
                ty,
                properties,
                methods,
            } => Ty::Metatype {
                ty: ty.substituting(substitutions)?.into(),
                properties: properties.substituting(substitutions)?,
                methods: methods.substituting(substitutions)?,
            },
            Ty::Scheme(scheme) => match scheme {
                TypeScheme {
                    kind:
                        TypeSchemeKind::Nominal {
                            name,
                            quantified_vars,
                            constraints,
                            canonical_rows,
                            ..
                        },
                    ..
                } => Ty::Nominal {
                    name: name.clone(),
                    properties: Row::Open(
                        *substitutions.get_row(&canonical_rows.properties).unwrap(),
                    ),
                    methods: Row::Open(*substitutions.get_row(&canonical_rows.methods).unwrap()),
                    generics: GenericState::Instance(Default::default()),
                },
                TypeScheme {
                    kind: TypeSchemeKind::Property { value, .. },
                    ..
                } => match value {
                    InferredDefinition::Concrete(box ty) => ty,
                    InferredDefinition::TypeParameter(tp) => {
                        if let Some(var) = substitutions.get_type_parameter(&tp) {
                            Ty::Var(*var)
                        } else {
                            return Err(TypeError::Unknown(
                                "Did not get type parameter substitution".to_string(),
                            ));
                        }
                    }
                },
                TypeScheme {
                    kind:
                        TypeSchemeKind::Func {
                            quantified_vars,
                            params,
                            returns,
                            constraints,
                        },
                    ..
                } => {
                    let mut instantiated_params = vec![];
                    for param in params {
                        instantiated_params.push(match &param {
                            InferredDefinition::Concrete(ty) => InferredDefinition::Concrete(
                                ty.clone().substituting(substitutions)?.into(),
                            ),
                            InferredDefinition::TypeParameter(tp) => {
                                if let Some(var) = substitutions.get_type_parameter(tp) {
                                    InferredDefinition::Concrete(Ty::Var(*var).into())
                                } else {
                                    return Err(TypeError::Unknown(format!(
                                        "Did not find instantiation for type parameter: {tp:?}"
                                    )));
                                }
                            }
                        });
                    }

                    let returns = match &returns {
                        InferredDefinition::Concrete(ty) => InferredDefinition::Concrete(
                            ty.clone().substituting(substitutions)?.into(),
                        ),
                        InferredDefinition::TypeParameter(tp) => {
                            if let Some(var) = substitutions.get_type_parameter(tp) {
                                InferredDefinition::Concrete(Ty::Var(*var).into())
                            } else {
                                return Err(TypeError::Unknown(format!(
                                    "Did not find instantiation for type parameter: {tp:?}"
                                )));
                            }
                        }
                    };

                    let mut new_constraints = vec![];
                    for constraint in constraints {
                        new_constraints.push(constraint.instantiate(substitutions)?);
                    }

                    Ty::Scheme(TypeScheme {
                        kind: TypeSchemeKind::Func {
                            quantified_vars: quantified_vars.clone(),
                            params: instantiated_params,
                            returns,
                            constraints: new_constraints,
                        },
                        named_generics: scheme.named_generics.clone(),
                    })
                }
            }, // TODO: Do we need to instantiate here too?
            Ty::Func {
                params,
                returns,
                generic_constraints,
            } => {
                let mut new_params = vec![];
                for param in params.iter() {
                    new_params.push(param.clone().substituting(substitutions)?);
                }
                Ty::Func {
                    params: new_params,
                    returns: Box::new(returns.substituting(substitutions)?),
                    generic_constraints,
                }
            }
            Ty::Nominal {
                name,
                properties,
                methods,
                generics,
            } => Ty::Nominal {
                name,
                properties: properties.substituting(substitutions)?,
                methods: methods.substituting(substitutions)?,
                generics,
            },
            Ty::Product(row) => Ty::Product(row.substituting(substitutions)?),
            Ty::TypeParameter(..) => todo!(),
            Ty::Sum(row) => Ty::Sum(row.substituting(substitutions)?),
            Ty::Label(label, ty) => Ty::Label(label, Box::new(ty.substituting(substitutions)?)),
        };

        Ok(ty)
    }

    pub fn instantiate(
        &self,
        context: &mut TypeVarContext,
        substitutions: &mut BTreeMap<TypeParameter, TypeVar>,
    ) -> Ty {
        match self {
            #[allow(clippy::panic)]
            Ty::RawScheme(_) => panic!("Cannot instantiate raw scheme: {self:?}"),
            Ty::Scheme(_) => self.clone(),
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
                for type_param in type_params {
                    if !substitutions.contains_key(type_param) {
                        let fresh_var = context.new_var(TypeVarKind::Instantiated);
                        substitutions.insert(*type_param, fresh_var);
                    }
                }

                // Instantiate property and method rows with the substitutions
                let inst_properties = properties.instantiate_row(context, substitutions);
                let inst_methods = methods.instantiate_row(context, substitutions);

                // Build instantiations map for this instance
                let mut inst_map = BTreeMap::new();
                for type_param in type_params {
                    if let Some(instantiated) = substitutions.get(type_param) {
                        inst_map.insert(*type_param, Ty::Var(*instantiated));
                    }
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
            Ty::Var(_type_var) => self.clone(),
            #[allow(clippy::todo)]
            Ty::Product(..) => todo!(),
            #[allow(clippy::todo)]
            Ty::Sum(..) => todo!(),
            #[allow(clippy::todo)]
            Ty::Label(_, _) => todo!(),
        }
    }
}
