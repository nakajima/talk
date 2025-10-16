use crate::{
    compiling::module::ModuleId,
    name::Name,
    name_resolution::symbol::{Symbol, StructId},
    types::{infer_ty::TypeParamId, row::Row, type_session::TypeDefKind},
};

pub trait SomeType: std::fmt::Debug + PartialEq + Clone {
    type RowType: PartialEq + Clone + std::fmt::Debug;
    fn contains_var(&self) -> bool;
}

impl SomeType for Ty {
    type RowType = Row;
    fn contains_var(&self) -> bool {
        false
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Ty {
    Primitive(Symbol),
    Param(TypeParamId),
    Constructor {
        name: Name,
        params: Vec<Ty>,
        ret: Box<Ty>,
    },

    Func(Box<Ty>, Box<Ty>),
    Tuple(Vec<Ty>),
    Record(Box<Row>),

    // Nominal types (we look up their information from the TypeCatalog)
    Nominal {
        symbol: Symbol,
        row: Box<Row>,
    },
}

impl std::fmt::Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty::Primitive(symbol) => match *symbol {
                Symbol::Int => write!(f, "Int"),
                Symbol::Float => write!(f, "Float"),
                Symbol::Bool => write!(f, "Bool"),
                Symbol::Void => write!(f, "Void"),
                _ => write!(f, "{symbol}"),
            },
            Ty::Param(type_param_id) => write!(f, "{:?}", type_param_id),
            Ty::Constructor { name, .. } => {
                write!(f, "{}", name.name_str())
            }
            Ty::Func(param, ret) => {
                write!(
                    f,
                    "({}) -> {ret}",
                    param
                        .clone()
                        .uncurry_params()
                        .iter()
                        .map(|p| format!("{p}"))
                        .collect::<Vec<_>>()
                        .join(", "),
                )
            }
            Ty::Tuple(items) => {
                write!(
                    f,
                    "({})",
                    items
                        .iter()
                        .map(|p| format!("{p}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            Ty::Record(row) => write!(
                f,
                "{{ {} }}",
                row.close()
                    .iter()
                    .map(|(k, v)| format!("{k}: {v}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Ty::Nominal { symbol, .. } => {
                write!(f, "Nominal({symbol})")
            }
        }
    }
}

#[allow(non_upper_case_globals)]
#[allow(non_snake_case)]
impl Ty {
    pub const Int: Ty = Ty::Primitive(Symbol::Int);
    pub const Float: Ty = Ty::Primitive(Symbol::Float);
    pub const Bool: Ty = Ty::Primitive(Symbol::Bool);
    pub const Void: Ty = Ty::Primitive(Symbol::Void);
    pub fn String() -> Ty {
        Ty::Nominal {
            symbol: Symbol::Struct(StructId {
                module_id: ModuleId::Core,
                local_id: 2,
            }),
            row: Box::new(Row::Empty(TypeDefKind::Struct)),
        }
    }
    pub fn Array(_t: Ty) -> Ty {
        Ty::Nominal {
            symbol: Symbol::Struct(StructId {
                module_id: ModuleId::Core,
                local_id: 3,
            }),
            row: Box::new(Row::Empty(TypeDefKind::Struct)),
        }
    }

    pub(crate) fn uncurry_params(self) -> Vec<Ty> {
        let mut result = vec![];

        match self {
            Ty::Void => (),
            Ty::Primitive(..) => result.push(self),
            Ty::Param(..) => result.push(self),
            Ty::Constructor { .. } => result.push(self),
            Ty::Func(param, ..) => result.extend(param.uncurry_params()),
            Ty::Tuple(..) => result.push(self),
            Ty::Record(..) => result.push(self),
            Ty::Nominal { .. } => result.push(self),
        }

        result
    }
}
