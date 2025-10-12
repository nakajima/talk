use crate::{
    compiling::module::ModuleId,
    name::Name,
    name_resolution::symbol::{Symbol, TypeId},
    types::{infer_ty::TypeParamId, row::Row, type_session::TypeDefKind},
};

pub trait SomeType: std::fmt::Debug + PartialEq + Clone {
    fn contains_var(&self) -> bool;
}

impl SomeType for Ty {
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
        type_args: Vec<Ty>,
        row: Box<Row>,
    },
}

impl std::fmt::Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
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
            symbol: Symbol::Type(TypeId {
                module_id: ModuleId::Core,
                local_id: 2,
            }),
            type_args: vec![],
            row: Box::new(Row::Empty(TypeDefKind::Struct)),
        }
    }
    pub fn Array(t: Ty) -> Ty {
        Ty::Nominal {
            symbol: Symbol::Type(TypeId {
                module_id: ModuleId::Core,
                local_id: 3,
            }),
            type_args: vec![t],
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
