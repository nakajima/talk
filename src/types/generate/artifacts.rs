use super::*;

#[derive(Default)]
pub(super) struct TypeArtifacts {
    pub(super) node_types: FxHashMap<NodeID, Ty>,
    pub(super) instantiations: FxHashMap<NodeID, Vec<(Symbol, Ty)>>,
    pub(super) member_resolutions: FxHashMap<NodeID, MemberResolution>,
    pub(super) coerce_clones: FxHashSet<NodeID>,
    pub(super) existential_packs: FxHashMap<NodeID, ExistentialPack>,
    pub(super) performs_into: FxHashMap<Symbol, FxHashSet<Symbol>>,
    pub(super) binder_refs: FxHashMap<Symbol, FxHashSet<Symbol>>,
    pub(super) handler_payload_tys: FxHashMap<Symbol, Vec<Ty>>,
    pub(super) handlers_defined: FxHashMap<Symbol, FxHashSet<Symbol>>,
    pub(super) display_names: FxHashMap<Symbol, String>,
}
