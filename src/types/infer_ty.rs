use itertools::Itertools;

use crate::{
    compiling::module::ModuleId,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    types::{
        infer_row::InferRow,
        scheme::ForAll,
        ty::{SomeType, Ty},
    },
};

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct UnificationVarId(u32);
impl From<u32> for UnificationVarId {
    fn from(value: u32) -> Self {
        UnificationVarId(value)
    }
}

impl std::fmt::Debug for UnificationVarId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "meta({})", self.0)
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct TypeParamId(u32);
impl From<u32> for TypeParamId {
    fn from(value: u32) -> Self {
        TypeParamId(value)
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct SkolemId(u32);
impl From<u32> for SkolemId {
    fn from(value: u32) -> Self {
        SkolemId(value)
    }
}

#[derive(PartialEq, PartialOrd, Clone, Copy, Debug, Eq, Hash)]
pub struct Level(pub u32);
impl Level {
    pub fn next(&self) -> Level {
        Level(self.0 + 1)
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum Primitive {
    Int(Symbol),
    Float(Symbol),
    Bool(Symbol),
    Void(Symbol),
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub enum InferTy {
    Hole(NodeID),
    Primitive(Symbol),

    Param(TypeParamId),
    Rigid(SkolemId),
    UnificationVar {
        id: UnificationVarId,
        level: Level,
    },

    Constructor {
        symbol: Symbol,
        params: Vec<InferTy>,
        ret: Box<InferTy>,
    },

    Func(Box<InferTy>, Box<InferTy>),
    Tuple(Vec<InferTy>),
    Record(Box<InferRow>),

    // Nominal types (we look up their information from the TypeCatalog)
    Nominal {
        symbol: Symbol,
        type_args: Vec<InferTy>,
        row: Box<InferRow>,
    },
}

impl From<InferTy> for Ty {
    fn from(value: InferTy) -> Self {
        match value {
            InferTy::Primitive(primitive) => Ty::Primitive(primitive),
            InferTy::Param(type_param_id) => Ty::Param(type_param_id),
            InferTy::Constructor {
                symbol,
                params,
                box ret,
            } => Ty::Constructor {
                symbol,
                params: params.into_iter().map(|p| p.into()).collect(),
                ret: Box::new(ret.into()),
            },
            InferTy::Func(box param, box ret) => {
                Ty::Func(Box::new(param.into()), Box::new(ret.into()))
            }
            InferTy::Tuple(items) => Ty::Tuple(items.into_iter().map(|t| t.into()).collect()),
            InferTy::Record(box infer_row) => Ty::Record(Box::new(infer_row.into())),
            InferTy::Nominal {
                symbol,
                type_args,
                box row,
            } => Ty::Nominal {
                symbol,
                type_args: type_args.into_iter().map(|t| t.into()).collect(),
                row: Box::new(row.into()),
            },
            ty => panic!("Ty cannot contain variables: {ty:?}"),
        }
    }
}

impl From<Ty> for InferTy {
    fn from(value: Ty) -> Self {
        match value {
            Ty::Primitive(primitive) => InferTy::Primitive(primitive),
            Ty::Param(type_param_id) => InferTy::Param(type_param_id),
            Ty::Constructor {
                symbol,
                params,
                box ret,
            } => InferTy::Constructor {
                symbol,
                params: params.into_iter().map(|p| p.into()).collect(),
                ret: Box::new(ret.into()),
            },
            Ty::Func(box param, box ret) => {
                InferTy::Func(Box::new(param.into()), Box::new(ret.into()))
            }
            Ty::Tuple(items) => InferTy::Tuple(items.into_iter().map(|t| t.into()).collect()),
            Ty::Record(box infer_row) => InferTy::Record(Box::new(infer_row.into())),
            Ty::Nominal {
                symbol,
                type_args,
                box row,
            } => InferTy::Nominal {
                symbol,
                type_args: type_args.into_iter().map(|t| t.into()).collect(),
                row: Box::new(row.into()),
            },
        }
    }
}

impl SomeType for InferTy {
    fn contains_var(&self) -> bool {
        match self {
            InferTy::Hole(..) => false,
            InferTy::Param(..) => false,
            InferTy::Rigid(..) => false,
            InferTy::UnificationVar { .. } => true,
            InferTy::Primitive(..) => false,
            InferTy::Constructor { params, .. } => params.iter().any(|p| p.contains_var()),
            InferTy::Func(ty, ty1) => ty.contains_var() || ty1.contains_var(),
            InferTy::Tuple(items) => items.iter().any(|i| i.contains_var()),
            InferTy::Record(box row) => match row {
                InferRow::Extend { row, ty, .. } => {
                    InferTy::Record(row.clone()).contains_var() || ty.contains_var()
                }
                InferRow::Var(_) => true,
                _ => false,
            },
            InferTy::Nominal {
                type_args, box row, ..
            } => {
                let row_contains = match row {
                    InferRow::Extend { row, ty, .. } => {
                        InferTy::Record(row.clone()).contains_var() || ty.contains_var()
                    }
                    InferRow::Var(_) => true,
                    _ => false,
                };

                if row_contains {
                    return true;
                }

                type_args.iter().any(|t| t.contains_var())
            }
        }
    }
}

#[allow(non_upper_case_globals)]
impl InferTy {
    pub const Int: InferTy = InferTy::Primitive(Symbol::Int);
    pub const Float: InferTy = InferTy::Primitive(Symbol::Float);
    pub const Bool: InferTy = InferTy::Primitive(Symbol::Bool);
    pub const Void: InferTy = InferTy::Primitive(Symbol::Void);

    pub fn collect_foralls(&self) -> Vec<ForAll> {
        let mut result = vec![];
        match self {
            InferTy::Hole(..) => (),
            InferTy::Param(id) => result.push(ForAll::Ty(*id)),
            InferTy::Rigid(..) => (),
            InferTy::UnificationVar { .. } => (),
            InferTy::Primitive(..) => (),
            InferTy::Constructor { params, .. } => {
                for item in params {
                    result.extend(item.collect_foralls());
                }
            }
            InferTy::Func(ty, ty1) => {
                result.extend(ty.collect_foralls());
                result.extend(ty1.collect_foralls());
            }
            InferTy::Tuple(items) => {
                for item in items {
                    result.extend(item.collect_foralls());
                }
            }
            InferTy::Nominal { box row, .. } | InferTy::Record(box row) => match row {
                InferRow::Empty(..) => (),
                InferRow::Extend { row, ty, .. } => {
                    result.extend(InferTy::Record(row.clone()).collect_foralls());
                    result.extend(ty.collect_foralls());
                }
                InferRow::Param(id) => {
                    result.push(ForAll::Row(*id));
                }
                InferRow::Var(_) => (),
            },
        }
        result
    }

    pub fn fold<T, F: FnMut(&InferTy) -> T>(&self, f: &mut F) -> T {
        match self {
            InferTy::Hole(..) => f(self),
            InferTy::Primitive(..) => f(self),
            InferTy::Param(..) => f(self),
            InferTy::Rigid(..) => f(self),
            InferTy::UnificationVar { .. } => f(self),
            InferTy::Constructor { params, ret, .. } => {
                _ = params.iter().map(&mut *f);
                _ = f(ret);
                f(self)
            }
            InferTy::Func(ty, ty1) => {
                f(ty);
                f(ty1);
                f(self)
            }
            InferTy::Tuple(items) => {
                _ = items.iter().map(&mut *f);
                f(self)
            }
            InferTy::Record(box row) => match row {
                InferRow::Extend { ty, .. } => {
                    f(ty);
                    f(self)
                }
                _ => f(self),
            },
            InferTy::Nominal { box row, .. } => match row {
                InferRow::Extend { ty, .. } => {
                    f(ty);
                    f(self)
                }
                _ => f(self),
            },
        }
    }

    pub fn import(self, module_id: ModuleId) -> InferTy {
        match self {
            InferTy::Hole(..) => self,
            InferTy::Primitive(..) => self,
            InferTy::Param(..) => self,
            InferTy::Rigid(..) => self,
            InferTy::UnificationVar { .. } => self,
            InferTy::Constructor {
                symbol,
                params,
                ret,
            } => InferTy::Constructor {
                symbol: symbol.import(module_id),
                params,
                ret,
            },
            InferTy::Func(ty, ty1) => {
                InferTy::Func(ty.import(module_id).into(), ty1.import(module_id).into())
            }
            InferTy::Tuple(items) => {
                InferTy::Tuple(items.into_iter().map(|i| i.import(module_id)).collect())
            }
            InferTy::Record(row) => InferTy::Record(row.import(module_id).into()),
            InferTy::Nominal {
                symbol,
                type_args,
                row,
            } => InferTy::Nominal {
                symbol: symbol.import(module_id),
                type_args: type_args.into_iter().map(|t| t.import(module_id)).collect(),
                row: row.import(module_id).into(),
            },
        }
    }
}

impl std::fmt::Debug for InferTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InferTy::Hole(..) => write!(f, "Hole"),
            InferTy::Param(id) => write!(f, "typeparam(α{})", id.0),
            InferTy::Rigid(id) => write!(f, "rigid(α{})", id.0),
            InferTy::UnificationVar { id, level } => write!(f, "meta(α{}, {})", id.0, level.0),
            InferTy::Primitive(primitive) => write!(f, "{primitive:?}"),
            InferTy::Constructor { params, .. } => {
                write!(f, "Constructor({params:?})")
            }
            InferTy::Func(param, ret) => write!(f, "func({param:?}) -> {ret:?}"),
            InferTy::Tuple(items) => {
                write!(f, "({})", items.iter().map(|i| format!("{i:?}")).join(", "))
            }
            InferTy::Nominal {
                symbol,
                row,
                type_args,
            } => {
                write!(f, "Type({symbol:?}, {type_args:?}, {row:?})")
            }
            InferTy::Record(box row) => {
                let row_debug = match row {
                    InferRow::Empty(..) => "".to_string(),
                    InferRow::Param(id) => format!("rowparam(π{})", id.0),
                    InferRow::Extend { .. } => {
                        let closed = row.close();
                        let mut parts = vec![];
                        for (field, value) in closed {
                            parts.push(format!("{field}: {value:?}"));
                        }
                        parts.join(", ")
                    }
                    InferRow::Var(row_meta_id) => format!("rowmeta(π{})", row_meta_id.0),
                };

                write!(f, "{{{row_debug}}}",)
            }
        }
    }
}
