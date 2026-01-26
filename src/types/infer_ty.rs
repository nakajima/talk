use derive_visitor::{Drive, DriveMut};
use ena::unify::{UnifyKey, UnifyValue};
use indexmap::IndexSet;
use itertools::Itertools;
use std::hash::Hash;

use crate::{
    compiling::module::ModuleId,
    label::Label,
    name::Name,
    name_resolution::symbol::{ProtocolId, StructId, Symbol, TypeParameterId},
    types::{
        infer_row::{InferRow, InnerRow, RowMetaId, RowParamId},
        mappable::Mappable,
        predicate::Predicate,
        scheme::{ForAll, Scheme},
        term_environment::EnvEntry,
        ty::Ty,
        type_error::TypeError,
    },
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Meta {
    Ty(MetaVarId),
    Row(RowMetaId),
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
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

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct TypeParamId(pub u32);
impl TypeParamId {
    pub const IR_TYPE_PARAM: TypeParamId = TypeParamId(u32::MAX - 1);
}
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

#[derive(Default, PartialEq, PartialOrd, Clone, Copy, Debug, Eq, Hash)]
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

pub(crate) trait TypePhase:
    std::fmt::Debug + PartialEq + Eq + Clone + Hash + Copy + 'static
{
    type RigidVar: PartialEq + Eq + Clone + Hash + Copy + 'static;
    type TypeVar: PartialEq + Eq + Clone + Hash + Copy + 'static;
    type RowVar: PartialEq + Eq + Clone + Hash + Copy + 'static;
}
#[derive(Debug, PartialEq, Eq, Clone, Hash, Copy)]
pub struct Infer {}
impl TypePhase for Infer {
    type RigidVar = SkolemId;
    type TypeVar = MetaVarId;
    type RowVar = RowMetaId;
}
pub type InferTy = InnerTy<Infer>;

#[derive(PartialEq, Eq, Clone, Hash, Drive, DriveMut)]
pub enum InnerTy<Phase: TypePhase> {
    Primitive(#[drive(skip)] Symbol),
    Param(#[drive(skip)] Symbol, #[drive(skip)] Vec<ProtocolId>),
    Rigid(#[drive(skip)] SkolemId),
    Var {
        #[drive(skip)]
        id: Phase::TypeVar,
        #[drive(skip)]
        level: Level,
    },
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
    Func(Box<Self>, Box<Self>, Box<InnerRow<Phase>>),
    Tuple(Vec<Self>),
    Record(Box<InnerRow<Phase>>),
    Nominal {
        #[drive(skip)]
        symbol: Symbol,
        type_args: Vec<Self>,
    },
    Error(#[drive(skip)] Box<TypeError>),
}

impl<T: TypePhase, U: TypePhase> Mappable<T, U> for InnerTy<T> {
    type Output = InnerTy<U>;
    fn mapping(
        self,
        ty_map: &mut impl FnMut(InnerTy<T>) -> InnerTy<U>,
        row_map: &mut impl FnMut(InnerRow<T>) -> InnerRow<U>,
    ) -> Self::Output {
        match self {
            InnerTy::Projection {
                box base,
                protocol_id,
                associated,
            } => InnerTy::Projection {
                base: base.mapping(ty_map, row_map).into(),
                protocol_id,
                associated,
            },
            InnerTy::Constructor {
                name,
                params,
                box ret,
            } => InnerTy::Constructor {
                name,
                params: params
                    .into_iter()
                    .map(|p| p.mapping(ty_map, row_map))
                    .collect(),
                ret: ty_map(ret).into(),
            },
            InnerTy::Func(box param, box ret, box effects) => InnerTy::Func(
                param.mapping(ty_map, row_map).into(),
                ret.mapping(ty_map, row_map).into(),
                row_map(effects).into(),
            ),
            InnerTy::Tuple(items) => InnerTy::Tuple(
                items
                    .into_iter()
                    .map(|i| i.mapping(ty_map, row_map))
                    .collect(),
            ),
            InnerTy::Record(box infer_row) => InnerTy::Record(row_map(infer_row).into()),
            InnerTy::Nominal { symbol, type_args } => InnerTy::Nominal {
                symbol,
                type_args: type_args
                    .into_iter()
                    .map(|i| i.mapping(ty_map, row_map))
                    .collect(),
            },
            other => ty_map(other),
        }
    }
}

impl From<InferTy> for Ty {
    #[allow(clippy::panic)]
    fn from(value: InferTy) -> Self {
        match value {
            InferTy::Primitive(primitive) => Ty::Primitive(primitive),
            InferTy::Param(type_param_id, bounds) => Ty::Param(type_param_id, bounds),
            InferTy::Constructor {
                name,
                params,
                box ret,
            } => Ty::Constructor {
                name,
                params: params.into_iter().map(|p| p.into()).collect(),
                ret: Box::new(ret.into()),
            },
            InferTy::Func(box param, box ret, box effects) => Ty::Func(
                Box::new(param.into()),
                Box::new(ret.into()),
                Box::new(effects.into()),
            ),
            InferTy::Tuple(items) => Ty::Tuple(items.into_iter().map(|t| t.into()).collect()),
            InferTy::Record(box infer_row) => Ty::Record(Box::new(infer_row.into())),
            InferTy::Nominal { symbol, type_args } => Ty::Nominal {
                symbol,
                type_args: type_args.into_iter().map(|p| p.into()).collect(),
            },
            InferTy::Projection { .. } => Ty::Param(
                Symbol::TypeParameter(TypeParameterId::new(ModuleId::Core, 420420)),
                vec![],
            ), // FIXME
            _ => Ty::Param(
                Symbol::TypeParameter(TypeParameterId::new(ModuleId::Core, 420420)),
                vec![],
            ),
        }
    }
}

impl From<Ty> for InferTy {
    fn from(value: Ty) -> Self {
        match value {
            Ty::Primitive(primitive) => InferTy::Primitive(primitive),
            Ty::Param(type_param_id, bounds) => InferTy::Param(type_param_id, bounds),
            Ty::Constructor {
                name,
                params,
                box ret,
            } => InferTy::Constructor {
                name,
                params: params.into_iter().map(|p| p.into()).collect(),
                ret: Box::new(ret.into()),
            },
            Ty::Func(box param, box ret, box effects) => InferTy::Func(
                Box::new(param.into()),
                Box::new(ret.into()),
                Box::new(effects.into()),
            ),
            Ty::Tuple(items) => InferTy::Tuple(items.into_iter().map(|t| t.into()).collect()),
            Ty::Record(.., box infer_row) => InferTy::Record(Box::new(infer_row.into())),
            Ty::Nominal { symbol, type_args } => InferTy::Nominal {
                symbol,
                type_args: type_args.into_iter().map(|t| t.into()).collect(),
            },
        }
    }
}

#[allow(non_upper_case_globals)]
#[allow(non_snake_case)]
impl<P: TypePhase> InnerTy<P> {
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
        let mut ty_contains = false;
        let mut row_contains = false;
        _ = self.clone().mapping(
            &mut |t| {
                ty_contains |= matches!(t, InnerTy::Var { .. });
                t
            },
            &mut |r| {
                row_contains |= r.contains_var();
                r
            },
        );
        ty_contains || row_contains
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
            Self::Record(box row) => Self::Record(row.import(module_id).into()),
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
            Self::Record(box row) => match row {
                InnerRow::Empty => (),
                InnerRow::Var(..) => {
                    out.insert(self.clone());
                }
                InnerRow::Param(..) => (),
                InnerRow::Extend { row, ty, .. } => {
                    out.extend(ty.collect_metas());
                    out.extend(Self::Record(row.clone()).collect_metas());
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

    pub fn to_entry(&self) -> EnvEntry<P> {
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
            Self::Record(box row) => {
                result.extend(row.collect_foralls());
            }
        }
        result
    }

    /// Collects Conforms predicates from bounds embedded in InferTy::Param nodes
    pub fn collect_param_predicates(&self) -> Vec<Predicate<P>> {
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
            Self::Record(box row) => {
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
        }
    }
}

impl<Phase: TypePhase> std::fmt::Debug for InnerTy<Phase> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Error(err) => write!(f, "Error Ty: {err}"),
            Self::Param(sym, _) => write!(f, "typeparam({sym:?})"),
            Self::Rigid(id) => write!(f, "rigid(α{})", id.0),
            Self::Var { id, level } => write!(f, "meta(α{}, {})", id.0, level.0),
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
            Self::Record(box row) => {
                let row_debug = match row {
                    InferRow::Empty => "emptyrow()".to_string(),
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

impl std::fmt::Display for InferTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Error(..) => write!(f, "error"),
            Self::Param(sym, _) => write!(f, "{sym}"),
            Self::Rigid(id) => write!(f, "^T{}", id.0),
            Self::Var { id, .. } => write!(f, "?T{}", id.0),
            Self::Primitive(primitive) => write!(f, "{}", format_symbol_name(*primitive)),
            Self::Projection {
                base, associated, ..
            } => write!(f, "{}.{}", base.as_ref(), associated),
            Self::Constructor { name, params, ret } => {
                if params.is_empty() {
                    write!(f, "{}", name.name_str())
                } else {
                    let params = params
                        .iter()
                        .map(|p| p.to_string())
                        .collect::<Vec<_>>()
                        .join(", ");
                    write!(f, "({}) -> {}", params, ret.as_ref())
                }
            }
            Self::Func(..) => {
                let mut params = Vec::new();
                let ret = collect_func_params(self, &mut params);
                let params = params
                    .into_iter()
                    .map(|p| p.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({}) -> {}", params, ret)
            }
            Self::Tuple(items) => write!(
                f,
                "({})",
                items
                    .iter()
                    .map(|p| p.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Self::Record(row) => write!(f, "{{ {} }}", format_row(row)),
            Self::Nominal { symbol, type_args } => {
                let base = format_symbol_name(*symbol);
                if type_args.is_empty() {
                    write!(f, "{base}")
                } else {
                    let args = type_args
                        .iter()
                        .map(|t| t.to_string())
                        .collect::<Vec<_>>()
                        .join(", ");
                    write!(f, "{base}<{args}>")
                }
            }
        }
    }
}

fn collect_func_params<'a>(ty: &'a InferTy, params: &mut Vec<&'a InferTy>) -> &'a InferTy {
    match ty {
        InferTy::Func(param, ret, ..) => {
            if **param != InferTy::Void {
                params.push(param);
            }
            collect_func_params(ret, params)
        }
        _ => ty,
    }
}

fn format_symbol_name(symbol: Symbol) -> String {
    match symbol {
        Symbol::Int => "Int".to_string(),
        Symbol::Float => "Float".to_string(),
        Symbol::Bool => "Bool".to_string(),
        Symbol::Void => "Void".to_string(),
        Symbol::Never => "Never".to_string(),
        Symbol::RawPtr => "RawPtr".to_string(),
        Symbol::Byte => "Byte".to_string(),
        Symbol::String => "String".to_string(),
        Symbol::Array => "Array".to_string(),
        _ => symbol.to_string(),
    }
}

pub(super) fn format_row(row: &InferRow) -> String {
    let mut fields: Vec<(Label, InferTy)> = Vec::new();
    let mut tail: Option<RowTailDisplay> = None;
    let mut cursor = row;

    loop {
        match cursor {
            InferRow::Empty => break,
            InferRow::Param(id) => {
                tail = Some(RowTailDisplay::Param(*id));
                break;
            }
            InferRow::Var(id) => {
                tail = Some(RowTailDisplay::Var(*id));
                break;
            }
            InferRow::Extend { row, label, ty } => {
                fields.push((label.clone(), ty.clone()));
                cursor = row.as_ref();
            }
        }
    }

    fields.reverse();
    let mut rendered = fields
        .into_iter()
        .map(|(label, ty)| format!("{label}: {ty}"))
        .collect::<Vec<_>>();

    if let Some(tail) = tail {
        rendered.push(tail.to_string());
    }

    rendered.join(", ")
}

enum RowTailDisplay {
    Param(RowParamId),
    Var(RowMetaId),
}

impl std::fmt::Display for RowTailDisplay {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RowTailDisplay::Param(id) => write!(f, "..R{}", id.0),
            RowTailDisplay::Var(id) => write!(f, ".._R{}", id.0),
        }
    }
}
