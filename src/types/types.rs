use derive_visitor::{Drive, DriveMut};
use rustc_hash::FxHashMap;

use crate::{
    compiling::module::ModuleId,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    types::{
        call_tree::CallTree,
        infer_row::Row,
        infer_ty::Ty,
        matcher::MatchPlan,
        scheme::Scheme,
        term_environment::EnvEntry,
        type_catalog::TypeCatalog,
        variational::{ChoiceStore, ErrorConstraintStore},
    },
};

#[derive(Debug, Clone, PartialEq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub enum TypeEntry {
    Mono(Ty),
    Poly(Scheme),
}

impl TypeEntry {
    pub fn mapping(
        self,
        ty_map: &mut impl FnMut(Ty) -> Ty,
        row_map: &mut impl FnMut(Row) -> Row,
    ) -> Self {
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

impl From<EnvEntry> for TypeEntry {
    fn from(value: EnvEntry) -> Self {
        match value {
            EnvEntry::Mono(ty) => TypeEntry::Mono(ty),
            EnvEntry::Scheme(scheme) => TypeEntry::Poly(scheme),
        }
    }
}

impl From<TypeEntry> for EnvEntry {
    fn from(value: TypeEntry) -> Self {
        match value {
            TypeEntry::Mono(ty) => EnvEntry::Mono(ty),
            TypeEntry::Poly(scheme) => EnvEntry::Scheme(scheme),
        }
    }
}

// the Types object is the final result of the type checking phase
#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct Types {
    pub types_by_node: FxHashMap<NodeID, TypeEntry>,
    pub types_by_symbol: FxHashMap<Symbol, TypeEntry>,
    pub catalog: TypeCatalog,
    pub(crate) match_plans: FxHashMap<NodeID, MatchPlan>,
    /// Variational choices for protocol method resolution.
    /// Maps call sites to alternatives with witness symbols.
    pub choices: ChoiceStore,
    /// Error constraints from type checking - used to resolve overloads.
    pub error_constraints: ErrorConstraintStore,
    /// Call tree mapping each function to the callees in its body.
    pub call_tree: CallTree,
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
            choices: self.choices,
            error_constraints: self.error_constraints,
            // Import call tree so specialization can propagate to callees in imported modules
            call_tree: self
                .call_tree
                .into_iter()
                .map(|(k, v)| {
                    (
                        k.import(module_id),
                        v.into_iter().map(|c| c.import(module_id)).collect(),
                    )
                })
                .collect(),
        }
    }
}
