//! The type catalog: nominal type information collected from declarations
//! before any body is checked — the analogue of THIH's class and type
//! environments (Mark P. Jones, *Typing Haskell in Haskell*, 1999). Member
//! tables are built here because the name resolver's `child_types` records
//! only nested *type* declarations, not properties/methods/variants.
//!
//! GADT-readiness (approved plan): every variant stores a full result type,
//! defaulting to the enum applied to its own parameters. GADT case syntax
//! (milestone 8) overrides `result`; nothing else reshapes.

use indexmap::IndexMap;
use rustc_hash::FxHashMap;

use crate::name_resolution::symbol::Symbol;
use crate::types::ty::Ty;

#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct StructInfo {
    /// Declared generic parameters, as rigid `Ty::Param` symbols.
    pub params: Vec<Symbol>,
    /// Field name → (property symbol, declared type over `params`).
    pub fields: IndexMap<String, (Symbol, Ty)>,
    /// Instance method name → method symbol.
    pub methods: IndexMap<String, Symbol>,
    /// Static method name → method symbol.
    pub statics: IndexMap<String, Symbol>,
    /// Initializer symbols (explicit or resolver-synthesized memberwise).
    pub inits: Vec<Symbol>,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct VariantInfo {
    pub symbol: Symbol,
    /// Payload types over the enum's `params`.
    pub payloads: Vec<Ty>,
    /// The constructed type; `Enum<params...>` for ordinary enums, refined
    /// for GADT variants in milestone 8.
    pub result: Ty,
}

#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct EnumInfo {
    pub params: Vec<Symbol>,
    pub variants: IndexMap<String, VariantInfo>,
    /// Instance method name → method symbol (methods on enums dispatch
    /// exactly like struct methods).
    pub methods: IndexMap<String, Symbol>,
}

/// A protocol method requirement. The signature is self-prepended and ranges
/// over `Ty::Param(protocol symbol)` for Self and `Ty::Param(assoc symbol)`
/// for associated types; its effect tail is `EffTail::Param(requirement
/// symbol)` so every use refreshes it.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Requirement {
    pub symbol: Symbol,
    pub sig: Ty,
    pub has_default: bool,
}

#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct ProtocolInfo {
    /// Associated types by source name (name-keyed so a sub-protocol's
    /// same-named `associated` refines its super's, Swift-style).
    pub assoc: IndexMap<String, Symbol>,
    /// Super-protocols (`protocol Comparable: Equatable`): a bound on P
    /// satisfies its supers transitively.
    pub supers: Vec<Symbol>,
    pub requirements: IndexMap<String, Requirement>,
}

/// One `extend Head: Protocol` row: requirement label → witness symbol, and
/// the associated-type bindings inferred by matching witness signatures
/// against requirement signatures (Chakravarty et al., ICFP 2005's
/// instance-determined synonyms). Conditional conformance (`extend
/// Array<Element: Showable>: Showable`) is an instance with a context (Hall,
/// Hammond, Peyton Jones & Wadler, TOPLAS 1996): `params` are the row's own
/// rigid variables, `self_args` the head application they appear in, and
/// `context` the bounds discharged as new wanteds at use.
#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct Conformance {
    pub params: Vec<Symbol>,
    pub self_args: Vec<Ty>,
    pub context: Vec<(Symbol, Vec<Symbol>)>,
    pub witnesses: FxHashMap<String, Symbol>,
    pub assoc: FxHashMap<Symbol, Ty>,
}

/// An inherent (protocol-less) extend member: `extend Float { func _trunc()
/// ... }`. The signature comes from annotations, over the extend's rigid
/// params; its effect tail is `EffTail::Param(symbol)` so uses refresh it.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct InherentMember {
    pub symbol: Symbol,
    pub sig: Ty,
    pub params: Vec<Symbol>,
    pub self_args: Vec<Ty>,
}

/// An effect operation signature (`effect 'io(request: IORequest) -> Int`).
/// Rows carry only the effect symbol; this is the catalog half (Plotkin &
/// Pretnar, ESOP 2009 operations; Koka MSFP 2014 keeps signatures out of
/// rows the same way).
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct EffectSig {
    /// Declared generic parameters (`effect 'state<T>(value: T) -> T`),
    /// instantiated fresh at each perform site; rigid in the handler.
    pub generics: Vec<Symbol>,
    pub params: Vec<Ty>,
    pub ret: Ty,
}

/// A transparent type alias. `params` are captured nominal parameters when
/// the alias is a child type (`struct Box<T> { typealias Item = T }`), so a
/// path use like `Box<Int>.Item` can substitute the base application's args.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct TypeAliasInfo {
    pub params: Vec<Symbol>,
    pub ty: Ty,
}

/// A candidate owner of a member name, for the unique-owner improvement rule
/// (Jones, FPCA 1995): protocols own their requirement labels, nominals own
/// their fields/methods.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum MemberOwner {
    Protocol(Symbol),
    Nominal(Symbol),
}

#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct TypeCatalog {
    pub structs: FxHashMap<Symbol, StructInfo>,
    pub enums: FxHashMap<Symbol, EnumInfo>,
    pub protocols: FxHashMap<Symbol, ProtocolInfo>,
    pub conformances: FxHashMap<(Symbol, Symbol), Conformance>,
    /// Type head → protocols it conforms to (for member search by head).
    pub conformances_by_head: FxHashMap<Symbol, Vec<Symbol>>,
    /// Member label → candidate owners, for improvement.
    pub member_owners: FxHashMap<String, Vec<MemberOwner>>,
    /// Rigid type parameter → declared protocol bounds.
    pub param_bounds: FxHashMap<Symbol, Vec<Symbol>>,
    /// Inherent extend members by type head.
    pub extend_members: FxHashMap<Symbol, IndexMap<String, InherentMember>>,
    /// Effect operation signatures.
    pub effects: FxHashMap<Symbol, EffectSig>,
    /// Transparent type aliases exported through the catalog for imports.
    #[serde(default)]
    pub type_aliases: FxHashMap<Symbol, TypeAliasInfo>,
    /// Protocols auto-derived for structs and enums when no explicit
    /// conformance exists (today: Showable, matching the previous
    /// implementation's show-derivation). The derived instance's context is
    /// structural: every field/payload must conform too.
    pub derivable: Vec<Symbol>,
}

impl TypeCatalog {
    /// Remap every symbol for an importer (the catalog half of
    /// `Module::import_as`).
    pub fn import_as(self, target: crate::compiling::module::ModuleId) -> TypeCatalog {
        use crate::types::ty::import_symbol as imp;
        let imp_ty = |t: &Ty| t.import_symbols(target);
        TypeCatalog {
            structs: self
                .structs
                .into_iter()
                .map(|(k, v)| {
                    (
                        imp(k, target),
                        StructInfo {
                            params: v.params.iter().map(|s| imp(*s, target)).collect(),
                            fields: v
                                .fields
                                .into_iter()
                                .map(|(l, (s, t))| (l, (imp(s, target), imp_ty(&t))))
                                .collect(),
                            methods: v
                                .methods
                                .into_iter()
                                .map(|(l, s)| (l, imp(s, target)))
                                .collect(),
                            statics: v
                                .statics
                                .into_iter()
                                .map(|(l, s)| (l, imp(s, target)))
                                .collect(),
                            inits: v.inits.iter().map(|s| imp(*s, target)).collect(),
                        },
                    )
                })
                .collect(),
            enums: self
                .enums
                .into_iter()
                .map(|(k, v)| {
                    (
                        imp(k, target),
                        EnumInfo {
                            params: v.params.iter().map(|s| imp(*s, target)).collect(),
                            variants: v
                                .variants
                                .into_iter()
                                .map(|(l, variant)| {
                                    (
                                        l,
                                        VariantInfo {
                                            symbol: imp(variant.symbol, target),
                                            payloads: variant.payloads.iter().map(&imp_ty).collect(),
                                            result: imp_ty(&variant.result),
                                        },
                                    )
                                })
                                .collect(),
                            methods: v
                                .methods
                                .into_iter()
                                .map(|(l, s)| (l, imp(s, target)))
                                .collect(),
                        },
                    )
                })
                .collect(),
            protocols: self
                .protocols
                .into_iter()
                .map(|(k, v)| {
                    (
                        imp(k, target),
                        ProtocolInfo {
                            assoc: v
                                .assoc
                                .into_iter()
                                .map(|(name, s)| (name, imp(s, target)))
                                .collect(),
                            supers: v.supers.iter().map(|s| imp(*s, target)).collect(),
                            requirements: v
                                .requirements
                                .into_iter()
                                .map(|(l, r)| {
                                    (
                                        l,
                                        Requirement {
                                            symbol: imp(r.symbol, target),
                                            sig: imp_ty(&r.sig),
                                            has_default: r.has_default,
                                        },
                                    )
                                })
                                .collect(),
                        },
                    )
                })
                .collect(),
            conformances: self
                .conformances
                .into_iter()
                .map(|((head, protocol), c)| {
                    (
                        (imp(head, target), imp(protocol, target)),
                        Conformance {
                            params: c.params.iter().map(|s| imp(*s, target)).collect(),
                            self_args: c.self_args.iter().map(&imp_ty).collect(),
                            context: c
                                .context
                                .into_iter()
                                .map(|(s, bounds)| {
                                    (
                                        imp(s, target),
                                        bounds.iter().map(|b| imp(*b, target)).collect(),
                                    )
                                })
                                .collect(),
                            witnesses: c
                                .witnesses
                                .into_iter()
                                .map(|(l, s)| (l, imp(s, target)))
                                .collect(),
                            assoc: c
                                .assoc
                                .into_iter()
                                .map(|(s, t)| (imp(s, target), imp_ty(&t)))
                                .collect(),
                        },
                    )
                })
                .collect(),
            conformances_by_head: self
                .conformances_by_head
                .into_iter()
                .map(|(head, protocols)| {
                    (
                        imp(head, target),
                        protocols.iter().map(|p| imp(*p, target)).collect(),
                    )
                })
                .collect(),
            member_owners: self
                .member_owners
                .into_iter()
                .map(|(l, owners)| {
                    (
                        l,
                        owners
                            .into_iter()
                            .map(|owner| match owner {
                                MemberOwner::Protocol(s) => {
                                    MemberOwner::Protocol(imp(s, target))
                                }
                                MemberOwner::Nominal(s) => MemberOwner::Nominal(imp(s, target)),
                            })
                            .collect(),
                    )
                })
                .collect(),
            param_bounds: self
                .param_bounds
                .into_iter()
                .map(|(s, bounds)| {
                    (
                        imp(s, target),
                        bounds.iter().map(|b| imp(*b, target)).collect(),
                    )
                })
                .collect(),
            extend_members: self
                .extend_members
                .into_iter()
                .map(|(head, members)| {
                    (
                        imp(head, target),
                        members
                            .into_iter()
                            .map(|(l, m)| {
                                (
                                    l,
                                    InherentMember {
                                        symbol: imp(m.symbol, target),
                                        sig: imp_ty(&m.sig),
                                        params: m.params.iter().map(|s| imp(*s, target)).collect(),
                                        self_args: m.self_args.iter().map(&imp_ty).collect(),
                                    },
                                )
                            })
                            .collect(),
                    )
                })
                .collect(),
            effects: self
                .effects
                .into_iter()
                .map(|(s, sig)| {
                    (
                        imp(s, target),
                        EffectSig {
                            generics: sig.generics.iter().map(|g| imp(*g, target)).collect(),
                            params: sig.params.iter().map(&imp_ty).collect(),
                            ret: imp_ty(&sig.ret),
                        },
                    )
                })
                .collect(),
            type_aliases: self
                .type_aliases
                .into_iter()
                .map(|(s, alias)| {
                    (
                        imp(s, target),
                        TypeAliasInfo {
                            params: alias.params.iter().map(|p| imp(*p, target)).collect(),
                            ty: imp_ty(&alias.ty),
                        },
                    )
                })
                .collect(),
            derivable: self.derivable.iter().map(|s| imp(*s, target)).collect(),
        }
    }

    /// Merge an imported module's catalog (Phase 0 of checking: the
    /// environment a group solves against).
    pub fn merge(&mut self, other: TypeCatalog) {
        self.structs.extend(other.structs);
        self.enums.extend(other.enums);
        self.protocols.extend(other.protocols);
        self.conformances.extend(other.conformances);
        for (head, protocols) in other.conformances_by_head {
            let entry = self.conformances_by_head.entry(head).or_default();
            for protocol in protocols {
                if !entry.contains(&protocol) {
                    entry.push(protocol);
                }
            }
        }
        for (label, owners) in other.member_owners {
            for owner in owners {
                self.add_owner(&label, owner);
            }
        }
        self.param_bounds.extend(other.param_bounds);
        for (head, members) in other.extend_members {
            self.extend_members.entry(head).or_default().extend(members);
        }
        self.effects.extend(other.effects);
        self.type_aliases.extend(other.type_aliases);
        for protocol in other.derivable {
            if !self.derivable.contains(&protocol) {
                self.derivable.push(protocol);
            }
        }
    }

    pub fn add_owner(&mut self, label: &str, owner: MemberOwner) {
        let owners = self.member_owners.entry(label.to_string()).or_default();
        if !owners.contains(&owner) {
            owners.push(owner);
        }
    }

    /// Return `protocol` followed by all transitive super-protocols, with
    /// duplicates removed. Conformance to a protocol entails conformance to
    /// every super-protocol, so both registration and lookup use this closure.
    pub fn protocol_and_supers(&self, protocol: Symbol) -> Vec<Symbol> {
        let mut result = vec![];
        let mut queue = vec![protocol];
        while let Some(current) = queue.pop() {
            if result.contains(&current) {
                continue;
            }
            result.push(current);
            if let Some(info) = self.protocols.get(&current) {
                queue.extend(info.supers.iter().rev().copied());
            }
        }
        result
    }

    /// Every requirement that a conformance to `protocol` must satisfy,
    /// including inherited requirements. The owning protocol is retained
    /// because associated-type projections and default bodies are keyed by the
    /// protocol that declared the requirement.
    pub fn requirements_for_conformance(
        &self,
        protocol: Symbol,
    ) -> Vec<(Symbol, String, Requirement)> {
        let mut requirements: Vec<(Symbol, String, Requirement)> = vec![];
        for owner in self.protocol_and_supers(protocol) {
            let Some(info) = self.protocols.get(&owner) else {
                continue;
            };
            for (label, requirement) in &info.requirements {
                if requirements
                    .iter()
                    .any(|(_, _, existing)| existing.symbol == requirement.symbol)
                {
                    continue;
                }
                requirements.push((owner, label.clone(), requirement.clone()));
            }
        }
        requirements
    }

    /// Does a bound set satisfy `target`, directly or through super-protocol
    /// closure?
    pub fn bounds_satisfy(&self, bounds: &[Symbol], target: Symbol) -> bool {
        let mut queue: Vec<Symbol> = bounds.to_vec();
        let mut seen: Vec<Symbol> = vec![];
        while let Some(protocol) = queue.pop() {
            if protocol == target {
                return true;
            }
            if seen.contains(&protocol) {
                continue;
            }
            seen.push(protocol);
            if let Some(info) = self.protocols.get(&protocol) {
                queue.extend(info.supers.iter().copied());
            }
        }
        false
    }

    /// Find an associated type named `label` reachable from a protocol
    /// (through supers). Returns (owning protocol, associated type symbol).
    pub fn associated_type_in(&self, protocol: Symbol, label: &str) -> Option<(Symbol, Symbol)> {
        let mut queue: Vec<Symbol> = vec![protocol];
        let mut seen: Vec<Symbol> = vec![];
        while let Some(current) = queue.pop() {
            if seen.contains(&current) {
                continue;
            }
            seen.push(current);
            if let Some(info) = self.protocols.get(&current) {
                if let Some(&assoc) = info.assoc.get(label) {
                    return Some((current, assoc));
                }
                queue.extend(info.supers.iter().copied());
            }
        }
        None
    }

    /// Find a requirement named `label` reachable from a protocol (through
    /// supers). Returns (owning protocol, requirement).
    pub fn requirement_in(&self, protocol: Symbol, label: &str) -> Option<(Symbol, &Requirement)> {
        let mut queue: Vec<Symbol> = vec![protocol];
        let mut seen: Vec<Symbol> = vec![];
        while let Some(current) = queue.pop() {
            if seen.contains(&current) {
                continue;
            }
            seen.push(current);
            if let Some(info) = self.protocols.get(&current) {
                if let Some(requirement) = info.requirements.get(label) {
                    return Some((current, requirement));
                }
                queue.extend(info.supers.iter().copied());
            }
        }
        None
    }
}
