use derive_visitor::{Drive, DriveMut};
use ena::unify::{UnifyKey, UnifyValue};
use indexmap::IndexSet;
use itertools::Itertools;
use std::hash::Hash;

use crate::{
    compiling::module::ModuleId,
    label::Label,
    name::Name,
    name_resolution::symbol::{ProtocolId, StructId, Symbol},
    types::{
        infer_row::{Row, RowMetaId},
        predicate::Predicate,
        scheme::{ForAll, Scheme},
        term_environment::EnvEntry,
        type_error::TypeError,
    },
};

#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub enum Meta {
    Ty(MetaVarId),
    Row(RowMetaId),
}

#[derive(
    PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub struct MetaVarId(u32);
impl From<u32> for MetaVarId {
    fn from(value: u32) -> Self {
        MetaVarId(value)
    }
}

impl UnifyKey for MetaVarId {
    type Value = Level;

    fn index(&self) -> u32 {
        self.0
    }

    fn from_index(u: u32) -> Self {
        Self(u)
    }

    fn tag() -> &'static str {
        "meta"
    }
}

impl std::fmt::Debug for MetaVarId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "meta({})", self.0)
    }
}

#[derive(
    Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub struct TypeParamId(pub u32);
impl TypeParamId {
    pub const IR_TYPE_PARAM: TypeParamId = TypeParamId(u32::MAX - 1);
}
impl From<u32> for TypeParamId {
    fn from(value: u32) -> Self {
        TypeParamId(value)
    }
}

#[derive(
    Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub struct SkolemId(u32);
impl From<u32> for SkolemId {
    fn from(value: u32) -> Self {
        SkolemId(value)
    }
}

#[derive(
    Default,
    PartialEq,
    PartialOrd,
    Clone,
    Copy,
    Debug,
    Eq,
    Hash,
    serde::Serialize,
    serde::Deserialize,
)]
pub struct Level(pub u32);
impl Level {
    pub fn next(&self) -> Level {
        Level(self.0 + 1)
    }

    pub fn prev(&self) -> Level {
        Level(self.0.saturating_sub(1))
    }
}

impl UnifyValue for Level {
    type Error = TypeError;

    fn unify_values(lhs: &Self, rhs: &Self) -> Result<Self, Self::Error> {
        Ok(if lhs.0 > rhs.0 { *rhs } else { *lhs })
    }
}

/// Unified type representation - used for both inference and final types.
/// The inference-specific variants (Var, Rigid, Projection, Error) are only
/// populated during type checking and should be resolved before codegen.
#[derive(PartialEq, Eq, Clone, Hash, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub enum Ty {
    Primitive(#[drive(skip)] Symbol),
    Param(#[drive(skip)] Symbol, #[drive(skip)] Vec<ProtocolId>),
    /// Skolem (rigid) type variable - used during subsumption checking
    Rigid(#[drive(skip)] SkolemId),
    /// Meta (unification) type variable - used during inference
    Var {
        #[drive(skip)]
        id: MetaVarId,
        #[drive(skip)]
        level: Level,
    },
    /// Type projection - e.g., T.AssociatedType where T conforms to a protocol
    Projection {
        base: Box<Self>,
        #[drive(skip)]
        protocol_id: ProtocolId,
        #[drive(skip)]
        associated: Label,
    },
    Constructor {
        #[drive(skip)]
        name: Name,
        params: Vec<Self>,
        ret: Box<Self>,
    },
    Func(Box<Self>, Box<Self>, Box<Row>),
    Tuple(Vec<Self>),
    Record(#[drive(skip)] Option<Symbol>, Box<Row>),
    Nominal {
        #[drive(skip)]
        symbol: Symbol,
        type_args: Vec<Self>,
    },
    Error(#[drive(skip)] Box<TypeError>),
}

impl Ty {
    pub fn mapping(
        self,
        ty_map: &mut impl FnMut(Ty) -> Ty,
        row_map: &mut impl FnMut(Row) -> Row,
    ) -> Self {
        match self {
            Ty::Projection {
                box base,
                protocol_id,
                associated,
            } => Ty::Projection {
                base: base.mapping(ty_map, row_map).into(),
                protocol_id,
                associated,
            },
            Ty::Constructor {
                name,
                params,
                box ret,
            } => Ty::Constructor {
                name,
                params: params
                    .into_iter()
                    .map(|p| p.mapping(ty_map, row_map))
                    .collect(),
                ret: ty_map(ret).into(),
            },
            Ty::Func(box param, box ret, box effects) => Ty::Func(
                param.mapping(ty_map, row_map).into(),
                ret.mapping(ty_map, row_map).into(),
                row_map(effects).into(),
            ),
            Ty::Tuple(items) => Ty::Tuple(
                items
                    .into_iter()
                    .map(|i| i.mapping(ty_map, row_map))
                    .collect(),
            ),
            Ty::Record(sym, box row) => Ty::Record(sym, row_map(row).into()),
            Ty::Nominal { symbol, type_args } => Ty::Nominal {
                symbol,
                type_args: type_args
                    .into_iter()
                    .map(|i| i.mapping(ty_map, row_map))
                    .collect(),
            },
            other => ty_map(other),
        }
    }

    /// Visit all types and rows in the tree, returning early if the visitor returns true.
    /// This does NOT clone the tree and is more efficient for read-only traversal.
    pub fn visit(
        &self,
        ty_visitor: &mut impl FnMut(&Ty) -> bool,
        row_visitor: &mut impl FnMut(&Row) -> bool,
    ) -> bool {
        if ty_visitor(self) {
            return true;
        }
        match self {
            Ty::Projection { base, .. } => base.visit(ty_visitor, row_visitor),
            Ty::Constructor { params, ret, .. } => {
                params.iter().any(|p| p.visit(ty_visitor, row_visitor))
                    || ret.visit(ty_visitor, row_visitor)
            }
            Ty::Func(param, ret, effects) => {
                param.visit(ty_visitor, row_visitor)
                    || ret.visit(ty_visitor, row_visitor)
                    || effects.visit_ty(ty_visitor, row_visitor)
            }
            Ty::Tuple(items) => items.iter().any(|i| i.visit(ty_visitor, row_visitor)),
            Ty::Record(_, row) => row.visit_ty(ty_visitor, row_visitor),
            Ty::Nominal { type_args, .. } => {
                type_args.iter().any(|a| a.visit(ty_visitor, row_visitor))
            }
            _ => false,
        }
    }
}

#[allow(non_upper_case_globals)]
#[allow(non_snake_case)]
impl Ty {
    pub const Int: Self = Self::Primitive(Symbol::Int);
    pub const Float: Self = Self::Primitive(Symbol::Float);
    pub const Bool: Self = Self::Primitive(Symbol::Bool);
    pub const RawPtr: Self = Self::Primitive(Symbol::RawPtr);
    pub const Void: Self = Self::Primitive(Symbol::Void);
    pub const Never: Self = Self::Primitive(Symbol::Never);
    pub const Byte: Self = Self::Primitive(Symbol::Byte);
    pub fn String() -> Self {
        Self::Nominal {
            symbol: Symbol::String,
            type_args: Default::default(),
        }
    }
    pub fn Array(t: Self) -> Self {
        Self::Nominal {
            symbol: Symbol::Struct(StructId {
                module_id: ModuleId::Core,
                local_id: 3,
            }),
            type_args: vec![t],
        }
    }

    pub fn contains_var(&self) -> bool {
        self.visit(&mut |t| matches!(t, Ty::Var { .. }), &mut |r| {
            matches!(r, Row::Var(..))
        })
    }

    pub fn import(self, module_id: ModuleId) -> Self {
        match self {
            Self::Primitive(symbol) => Self::Primitive(symbol),
            Self::Param(type_param_id, bounds) => Self::Param(type_param_id, bounds),
            Self::Constructor {
                name: Name::Resolved(sym, name),
                params,
                ret,
            } => Self::Constructor {
                name: Name::Resolved(sym.import(module_id), name),
                params: params.into_iter().map(|p| p.import(module_id)).collect(),
                ret: ret.import(module_id).into(),
            },
            Self::Func(param, ret, effects) => Self::Func(
                param.import(module_id).into(),
                ret.import(module_id).into(),
                effects.import(module_id).into(),
            ),
            Self::Tuple(items) => {
                Self::Tuple(items.into_iter().map(|t| t.import(module_id)).collect())
            }
            Self::Record(sym, box row) => Self::Record(
                sym.map(|s| s.import(module_id)),
                row.import(module_id).into(),
            ),
            Self::Nominal { symbol, type_args } => Self::Nominal {
                symbol: symbol.import(module_id),
                type_args: type_args.into_iter().map(|t| t.import(module_id)).collect(),
            },
            other => other,
        }
    }

    pub fn collect_metas(&self) -> IndexSet<Self> {
        let mut out = IndexSet::default();

        match self {
            Self::Error(..) => {}
            Self::Param(..) => {}
            Self::Var { .. } => {
                out.insert(self.clone());
            }
            Self::Projection { base, .. } => {
                out.extend(base.collect_metas());
            }
            Self::Func(param, ret, effects) => {
                out.extend(param.collect_metas());
                out.extend(ret.collect_metas());
                out.extend(effects.collect_metas());
            }
            Self::Tuple(items) => {
                for item in items {
                    out.extend(item.collect_metas());
                }
            }
            Self::Record(sym, box row) => match row {
                Row::Empty => (),
                Row::Var(..) => {
                    out.insert(self.clone());
                }
                Row::Param(..) => (),
                Row::Extend { row, ty, .. } => {
                    out.extend(ty.collect_metas());
                    out.extend(Self::Record(*sym, row.clone()).collect_metas());
                }
            },
            Self::Nominal { type_args, .. } => {
                for arg in type_args {
                    out.extend(arg.collect_metas());
                }
            }
            Self::Constructor { params, .. } => {
                for param in params {
                    out.extend(param.collect_metas());
                }
            }
            Self::Primitive(_) | Self::Rigid(_) => {}
        }

        out
    }

    pub fn to_entry(&self) -> EnvEntry {
        let foralls: IndexSet<ForAll> = self.collect_foralls().into_iter().collect();
        if foralls.is_empty() {
            EnvEntry::Mono(self.clone())
        } else {
            EnvEntry::Scheme(Scheme {
                ty: self.clone(),
                foralls,
                predicates: vec![],
            })
        }
    }

    pub fn collect_foralls(&self) -> IndexSet<ForAll> {
        let mut result: IndexSet<ForAll> = Default::default();
        match self {
            Self::Param(id, _) => {
                result.insert(ForAll::Ty(*id));
            }
            Self::Error(..) => (),
            Self::Rigid(..) => (),
            Self::Var { .. } => (),
            Self::Primitive(..) => (),
            Self::Nominal { type_args, .. } => {
                for arg in type_args {
                    result.extend(arg.collect_foralls());
                }
            }
            Self::Projection { base, .. } => {
                result.extend(base.collect_foralls());
            }
            Self::Constructor { params, .. } => {
                for item in params {
                    result.extend(item.collect_foralls());
                }
            }
            Self::Func(ty, ty1, effects) => {
                result.extend(ty.collect_foralls());
                result.extend(ty1.collect_foralls());
                result.extend(effects.collect_foralls());
            }
            Self::Tuple(items) => {
                for item in items {
                    result.extend(item.collect_foralls());
                }
            }
            Self::Record(_, box row) => {
                result.extend(row.collect_foralls());
            }
        }
        result
    }

    /// Collects Conforms predicates from bounds embedded in Ty::Param nodes
    pub fn collect_param_predicates(&self) -> Vec<Predicate> {
        let mut result = vec![];
        match self {
            Self::Param(id, bounds) => {
                for protocol_id in bounds {
                    result.push(Predicate::Conforms {
                        param: *id,
                        protocol_id: *protocol_id,
                    });
                }
            }
            Self::Nominal { type_args, .. } => {
                for arg in type_args {
                    result.extend(arg.collect_param_predicates());
                }
            }
            Self::Projection { base, .. } => {
                result.extend(base.collect_param_predicates());
            }
            Self::Constructor { params, .. } => {
                for item in params {
                    result.extend(item.collect_param_predicates());
                }
            }
            Self::Func(ty, ty1, effects) => {
                result.extend(ty.collect_param_predicates());
                result.extend(ty1.collect_param_predicates());
                result.extend(effects.collect_param_predicates());
            }
            Self::Tuple(items) => {
                for item in items {
                    result.extend(item.collect_param_predicates());
                }
            }
            Self::Record(_, box row) => {
                result.extend(row.collect_param_predicates());
            }
            _ => (),
        }
        result
    }

    /// Returns true if this type contains any unsubstituted type parameters.
    pub fn contains_type_params(&self) -> bool {
        match self {
            Self::Param(..) => true,
            Self::Primitive(..) => false,
            Self::Constructor { params, ret, .. } => {
                params.iter().any(|p| p.contains_type_params()) || ret.contains_type_params()
            }
            Self::Func(param, ret, effects) => {
                param.contains_type_params()
                    || ret.contains_type_params()
                    || effects.contains_type_params()
            }
            Self::Tuple(items) => items.iter().any(|i| i.contains_type_params()),
            Self::Record(_, row) => row.contains_type_params(),
            Self::Nominal { type_args, .. } => type_args.iter().any(|t| t.contains_type_params()),
            Self::Rigid(_) | Self::Var { .. } | Self::Error(_) => false,
            Self::Projection { base, .. } => base.contains_type_params(),
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
            Ty::Var { .. } | Ty::Rigid(_) | Ty::Projection { .. } | Ty::Error(_) => {
                // These variants should be resolved before reaching codegen
                // but we allow them through for error recovery
                result.push(self)
            }
        }

        result
    }
}

impl std::fmt::Debug for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Error(err) => write!(f, "Error Ty: {err}"),
            Self::Param(sym, _) => write!(f, "typeparam({sym:?})"),
            Self::Rigid(id) => write!(f, "rigid(a{id:?})"),
            Self::Var { id, level } => write!(f, "meta(a{id:?}, {level:?})"),
            Self::Primitive(primitive) => write!(f, "{primitive:?}"),
            Self::Constructor { name, params, .. } => {
                write!(f, "Constructor({name:?},{params:?})")
            }
            Self::Projection {
                base,
                associated,
                protocol_id,
            } => write!(f, "{base:?}.{associated:?}[{protocol_id:?}"),
            Self::Func(param, ret, effects) => {
                write!(f, "func({param:?}) {effects:?} -> {ret:?}")
            }
            Self::Tuple(items) => {
                write!(f, "({})", items.iter().map(|i| format!("{i:?}")).join(", "))
            }
            Self::Nominal { symbol, type_args } => {
                write!(f, "Nominal({symbol:?}, {type_args:?})")
            }
            Self::Record(_, row) => {
                write!(f, "{{{row:?}}}")
            }
        }
    }
}
