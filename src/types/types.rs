use derive_visitor::{Drive, DriveMut};
use rustc_hash::FxHashMap;

use crate::{
    compiling::module::ModuleId,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    types::{
        infer_ty::InferTy,
        mappable::Mappable,
        matcher::MatchPlan,
        scheme::Scheme,
        term_environment::EnvEntry,
        ty::{SomeType, Ty},
        type_catalog::TypeCatalog,
    },
};

#[derive(Debug, Clone, PartialEq, Drive, DriveMut)]
pub enum TypeEntry {
    Mono(Ty),
    Poly(Scheme<Ty>),
}

impl Mappable<Ty, Ty> for TypeEntry {
    type Output = TypeEntry;
    fn mapping(
        self,
        ty_map: &mut impl FnMut(Ty) -> Ty,
        row_map: &mut impl FnMut(<Ty as SomeType>::RowType) -> <Ty as SomeType>::RowType,
    ) -> Self::Output {
        match self {
            Self::Mono(ty) => TypeEntry::Mono(ty.mapping(ty_map, row_map)),
            Self::Poly(scheme) => Self::Poly(Scheme {
                ty: scheme.ty.mapping(ty_map, row_map),
                foralls: scheme.foralls,
                predicates: scheme
                    .predicates
                    .into_iter()
                    .map(|p| p.mapping(ty_map, row_map))
                    .collect(),
            }),
        }
    }
}

impl TypeEntry {
    pub fn as_mono_ty(&self) -> &Ty {
        match self {
            Self::Mono(ty) => ty,
            Self::Poly(scheme) => &scheme.ty,
        }
    }

    pub fn import(self, module_id: ModuleId) -> Self {
        match self {
            Self::Mono(ty) => Self::Mono(ty.import(module_id)),
            Self::Poly(scheme) => Self::Poly(scheme.import(module_id)),
        }
    }
}

impl From<EnvEntry<InferTy>> for TypeEntry {
    fn from(value: EnvEntry<InferTy>) -> Self {
        match value {
            EnvEntry::Mono(ty) => TypeEntry::Mono(ty.into()),
            EnvEntry::Scheme(scheme) => TypeEntry::Poly(Scheme {
                foralls: scheme.foralls,
                predicates: scheme.predicates.into_iter().map(|p| p.into()).collect(),
                ty: scheme.ty.into(),
            }),
        }
    }
}

impl From<TypeEntry> for EnvEntry<InferTy> {
    fn from(value: TypeEntry) -> Self {
        match value {
            TypeEntry::Mono(ty) => EnvEntry::Mono(ty.into()),
            TypeEntry::Poly(scheme) => EnvEntry::Scheme(Scheme {
                foralls: scheme.foralls,
                predicates: scheme
                    .predicates
                    .into_iter()
                    .map(|p| p.mapping(&mut |t| t.into(), &mut |r| r.into()))
                    .collect(),
                ty: scheme.ty.into(),
            }),
        }
    }
}

// the Types object is the final result of the type checking phase
#[derive(Clone, Debug, Default)]
pub struct Types {
    pub types_by_node: FxHashMap<NodeID, TypeEntry>,
    pub types_by_symbol: FxHashMap<Symbol, TypeEntry>,
    pub catalog: TypeCatalog<Ty>,
    pub(crate) match_plans: FxHashMap<NodeID, MatchPlan>,
}

impl Types {
    pub fn define(&mut self, symbol: Symbol, ty: TypeEntry) {
        self.types_by_symbol.insert(symbol, ty);
    }

    pub fn get(&self, id: &NodeID) -> Option<&TypeEntry> {
        self.types_by_node.get(id)
    }

    pub fn get_symbol(&self, sym: &Symbol) -> Option<&TypeEntry> {
        self.types_by_symbol.get(sym)
    }

    pub fn import_as(self, module_id: ModuleId) -> Types {
        Types {
            types_by_node: self
                .types_by_node
                .into_iter()
                .map(|(k, v)| (k, v.import(module_id)))
                .collect(),
            types_by_symbol: self
                .types_by_symbol
                .into_iter()
                .map(|(k, v)| (k.import(module_id), v.import(module_id)))
                .collect(),
            catalog: self.catalog.import_as(module_id),
            match_plans: self.match_plans,
        }
    }
}
