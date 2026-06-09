use derive_visitor::{Drive, DriveMut};
use rustc_hash::FxHashMap;

use crate::{
    compiling::module::{ModuleEnvironment, ModuleId},
    label::Label,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    types::{
        callee::Callees,
        conformance::ConformanceKey,
        infer_row::Row,
        infer_ty::Ty,
        matcher::MatchPlan,
        scheme::Scheme,
        term_environment::EnvEntry,
        type_catalog::{MemberBinding, TypeCatalog},
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

// The final result of type checking.
//
// Completed post-typecheck consumers should ask `Types` for member, witness,
// and method-requirement lookup. `TypeCatalog` remains the local storage for
// raw tables and materialized indexes, while `TypeSession` owns solver-time
// mutable lookup.
#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct Types {
    pub types_by_node: FxHashMap<NodeID, TypeEntry>,
    pub types_by_symbol: FxHashMap<Symbol, TypeEntry>,
    pub catalog: TypeCatalog,
    pub(crate) match_plans: FxHashMap<NodeID, MatchPlan>,
    /// Type-checker-resolved callees keyed by call/effect expression ID.
    pub callees: Callees,
    pub(crate) callee_owners: FxHashMap<NodeID, Symbol>,
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

    pub(crate) fn lookup_local_member(&self, receiver: &Symbol, label: &Label) -> Option<Symbol> {
        self.catalog.lookup_member(receiver, label)
    }

    pub(crate) fn lookup_local_constructor_member(
        &self,
        receiver: &Symbol,
        label: &Label,
    ) -> Option<Symbol> {
        self.catalog.lookup_constructor_member(receiver, label)
    }

    pub fn lookup_member(
        &self,
        modules: &ModuleEnvironment,
        receiver: &Symbol,
        label: &Label,
    ) -> Option<Symbol> {
        self.lookup_member_binding(modules, receiver, label)
            .map(|binding| binding.symbol)
    }

    pub fn lookup_member_binding(
        &self,
        modules: &ModuleEnvironment,
        receiver: &Symbol,
        label: &Label,
    ) -> Option<MemberBinding> {
        self.catalog
            .lookup_member_binding(receiver, label)
            .or_else(|| modules.lookup_member_binding(receiver, label))
    }

    pub fn lookup_constructor_member(
        &self,
        modules: &ModuleEnvironment,
        receiver: &Symbol,
        label: &Label,
    ) -> Option<Symbol> {
        self.catalog
            .lookup_constructor_member(receiver, label)
            .or_else(|| modules.lookup_constructor_member(receiver, label))
    }

    pub fn lookup_witness(
        &self,
        modules: &ModuleEnvironment,
        key: &ConformanceKey,
        label: &Label,
        method_req: &Symbol,
    ) -> Option<Symbol> {
        self.catalog
            .lookup_witness(key, label, method_req)
            .or_else(|| modules.lookup_witness(key, label, method_req))
    }

    pub fn associated_type_witnesses(
        &self,
        modules: &ModuleEnvironment,
        key: &ConformanceKey,
    ) -> Option<FxHashMap<Label, Ty>> {
        self.catalog
            .associated_type_witnesses(key)
            .or_else(|| modules.lookup_associated_type_witnesses(key))
    }

    pub fn lookup_method_requirement(
        &self,
        modules: &ModuleEnvironment,
        protocol_sym: &Symbol,
        label: &Label,
    ) -> Option<Symbol> {
        self.catalog
            .lookup_method_requirement(protocol_sym, label)
            .or_else(|| modules.lookup_method_requirement(protocol_sym, label))
    }

    pub fn method_requirement_label(
        &self,
        modules: &ModuleEnvironment,
        method_req: &Symbol,
    ) -> Option<(Symbol, Label)> {
        self.catalog
            .method_requirement_label(method_req)
            .or_else(|| modules.method_requirement_label(method_req))
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
            callees: self
                .callees
                .into_iter()
                .map(|(k, v)| (k, v.import(module_id)))
                .collect(),
            callee_owners: self
                .callee_owners
                .into_iter()
                .map(|(id, owner)| (id, owner.import(module_id)))
                .collect(),
        }
    }
}
