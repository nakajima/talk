use std::{collections::BTreeMap, fmt::Display};

use derive_visitor::DriveMut;

use crate::{
    name::Name,
    type_checker::TypeError,
    types::{
        constraint_set::GenericConstraintKey,
        row::{ClosedRow, Label, Row},
        type_var::{TypeVar, TypeVarKind},
        type_var_context::{RowVar, RowVarKind},
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

impl InferredDefinition {
    pub(crate) fn substituting(&self, substitutions: &Substitutions) -> Result<Ty, TypeError> {
        match self {
            Self::Concrete(ty) => ty.clone().substituting(substitutions),
            Self::TypeParameter(tp) => {
                if let Some(var) = substitutions.get_type_parameter(tp) {
                    Ok(Ty::Var(*var))
                } else {
                    tracing::error!(
                        "Did not find substitution for type parameter: {tp:?} in {substitutions:?}"
                    );
                    Err(TypeError::Unknown(format!(
                        "Did not find substitution for type parameter: {tp:?}"
                    )))
                }
            }
        }
    }
}

impl std::fmt::Display for InferredDefinition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InferredDefinition::TypeParameter(tp) => write!(f, "T{}", tp.0),
            InferredDefinition::Concrete(ty) => write!(f, "{ty}"),
        }
    }
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
        params: Row,
        returns: Box<Ty>,
    },
    Nominal {
        #[drive(skip)]
        name: Name,
        properties: Row,
        methods: Row,
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
            Ty::Primitive(primitive) => write!(f, "{primitive}"),
            Ty::Metatype { ty, .. } => write!(f, "{ty}.Type"),
            Ty::RawScheme(type_scheme) => {
                write!(f, "∀ (raw) {type_scheme}")
            }
            Ty::Scheme(type_scheme) => write!(f, "∀ {type_scheme}"),
            Ty::Func { params, returns } => {
                write!(f, "({params:?}) -> {returns}",)
            }
            Ty::Nominal { name, .. } => write!(f, "{}", name.name_str(),),
            Ty::Product(row) => write!(f, "{row:?}"),
            Ty::Var(type_var) => write!(f, "[α{} {:?}]", type_var.id, type_var.kind),
            Ty::TypeParameter(type_parameter) => write!(f, "τ{}", type_parameter.0),
            Ty::Sum(_row) => todo!(),
            Ty::Label(label, ty) => write!(f, "({label}: {ty})"),
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

    pub fn generic_index_keys(&self) -> Vec<GenericConstraintKey> {
        let mut result = vec![];
        match self {
            Ty::Var(type_var) => {
                if let TypeVarKind::Canonical(param) = type_var.kind {
                    return vec![GenericConstraintKey::TypeParameter(param)];
                } else {
                    return vec![];
                }
            }
            Ty::Metatype {
                ty,
                properties,
                methods,
            } => {
                result.extend(ty.generic_index_keys());

                if let Row::Open(row_var @ RowVar(_, RowVarKind::Canonical)) = properties {
                    result.push(GenericConstraintKey::RowVar(*row_var))
                }

                if let Row::Open(row_var @ RowVar(_, RowVarKind::Canonical)) = methods {
                    result.push(GenericConstraintKey::RowVar(*row_var))
                }
            }
            Ty::Nominal {
                properties,
                methods,
                ..
            } => {
                if let Row::Open(row_var @ RowVar(_, RowVarKind::Canonical)) = properties {
                    result.push(GenericConstraintKey::RowVar(*row_var))
                }

                if let Row::Open(row_var @ RowVar(_, RowVarKind::Canonical)) = methods {
                    result.push(GenericConstraintKey::RowVar(*row_var))
                }
            }
            Ty::Primitive(..) => (),
            Ty::Func { params, returns } => {
                if let Row::Open(row_var @ RowVar(_, RowVarKind::Canonical)) = params {
                    result.push(GenericConstraintKey::RowVar(*row_var))
                }

                result.extend(returns.generic_index_keys());
            }
            Ty::TypeParameter(tp) => result.push(GenericConstraintKey::TypeParameter(*tp)),
            Ty::Product(row) => {
                if let Row::Open(row_var @ RowVar(_, RowVarKind::Canonical)) = row {
                    result.push(GenericConstraintKey::RowVar(*row_var))
                }
            }
            Ty::Sum(row) => {
                if let Row::Open(row_var @ RowVar(_, RowVarKind::Canonical)) = row {
                    result.push(GenericConstraintKey::RowVar(*row_var))
                }
            }
            Ty::Label(_, ty) => result.extend(ty.generic_index_keys()),
            Ty::RawScheme(_) | Ty::Scheme(_) => (), // Schemes are already instantiated
        }

        result
    }

    /// Returns true if this type contains non-canonical type variables
    /// (ones that won't be substituted during instantiation)
    pub fn contains_non_canonical_var(&self) -> bool {
        match self {
            Ty::Var(type_var) => !matches!(type_var.kind, TypeVarKind::Canonical(_)),
            Ty::Metatype {
                ty,
                properties,
                methods,
            } => {
                ty.contains_non_canonical_var()
                    || properties.contains_non_canonical_var()
                    || methods.contains_non_canonical_var()
            }
            Ty::Nominal {
                properties,
                methods,
                ..
            } => properties.contains_non_canonical_var() || methods.contains_non_canonical_var(),
            Ty::Primitive(..) => false,
            Ty::Func { params, returns } => {
                params.contains_non_canonical_var() || returns.contains_non_canonical_var()
            }
            Ty::TypeParameter(_) => false,
            Ty::Product(row) => row.contains_non_canonical_var(),
            Ty::Sum(row) => row.contains_non_canonical_var(),
            Ty::Label(_, ty) => ty.contains_non_canonical_var(),
            Ty::RawScheme(_) | Ty::Scheme(_) => false, // Schemes are already instantiated
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
            Ty::Func { params, returns } => {
                params.contains_canonical_var() || returns.contains_canonical_var()
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
                            params,
                            returns,
                            quantified_vars,
                            ..
                        },
                    ..
                } => {
                    tracing::debug!(
                        "Substituting Func scheme with quantified_vars: {quantified_vars:?}, params: {params:?}, substitutions: {substitutions:?}"
                    );
                    // When substituting a Func scheme, we should instantiate it to a regular Func type
                    let instantiated_params = params.substituting(substitutions)?;
                    let returns_ty = returns.substituting(substitutions)?;

                    tracing::debug!("After substitution: params: {instantiated_params:?}");

                    // Return a regular Func type, not a Scheme
                    Ty::Func {
                        params: instantiated_params,
                        returns: Box::new(returns_ty),
                    }
                }
            },
            Ty::Func { params, returns } => Ty::Func {
                params: params.substituting(substitutions)?,
                returns: Box::new(returns.substituting(substitutions)?),
            },
            Ty::Nominal {
                name,
                properties,
                methods,
            } => Ty::Nominal {
                name,
                properties: properties.substituting(substitutions)?,
                methods: methods.substituting(substitutions)?,
            },
            Ty::Product(row) => Ty::Product(row.substituting(substitutions)?),
            Ty::TypeParameter(..) => todo!(),
            Ty::Sum(row) => Ty::Sum(row.substituting(substitutions)?),
            Ty::Label(label, ty) => Ty::Label(label, Box::new(ty.substituting(substitutions)?)),
        };

        Ok(ty)
    }
}
