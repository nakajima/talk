//! The type catalog: nominal type information collected from declarations
//! before any body is checked — the analogue of THIH's class and type
//! environments (Mark P. Jones, *Typing Haskell in Haskell*, 1999). Member
//! tables are built here because the name resolver's `child_types` records
//! only nested *type* declarations, not properties/methods/variants.
//!
//! GADT support: every variant stores a full constructor scheme whose result
//! defaults to the enum applied to its own parameters, and explicit GADT case
//! results override that default without reshaping callers.

use indexmap::IndexMap;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::name_resolution::symbol::Symbol;
use crate::types::ty::{Predicate, ProtocolRef, Scheme, Ty, match_key_pattern, match_pattern};

/// The usage grade of a declaration over the substructural lattice:
/// `Copy` values duplicate freely, `Affine` values (the default) move and may
/// be silently dropped, `Linear` values must be consumed exactly once.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Grade {
    Copy,
    Affine,
    Linear,
}

#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct StructInfo {
    /// Declared with the `linear` modifier: must be consumed exactly once.
    #[serde(default)]
    pub linear: bool,
    /// Declared `'heap`: reference semantics, region-allocated.
    #[serde(default)]
    pub heap: bool,
    /// Declared generic parameters, as rigid `Ty::Param` symbols.
    pub params: Vec<Symbol>,
    /// Implicit effect-row parameters, one per free row tail in the
    /// closure-typed fields — quantified per construction and carried as
    /// `Ty::Eff` arguments after the type args on this nominal's head.
    #[serde(default)]
    pub eff_params: Vec<Symbol>,
    /// Field name → (property symbol, declared type over `params`).
    pub fields: IndexMap<String, (Symbol, Ty)>,
    /// Instance method name → method symbol.
    pub methods: IndexMap<String, Symbol>,
    /// Static method name → method symbol.
    pub statics: IndexMap<String, Symbol>,
    /// Initializer symbols (explicit or resolver-synthesized memberwise).
    pub inits: Vec<Symbol>,
    /// Well-formedness predicates over `params` for every application of
    /// this nominal.
    pub predicates: Vec<Predicate>,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Variant {
    pub symbol: Symbol,
    /// Labels are source metadata for fixed payload positions. They never
    /// contribute to the constructor scheme or enum representation.
    #[serde(default)]
    pub payload_labels: Vec<Option<String>>,
    /// The constructor's qualified function type. Payload-less variants are
    /// still recorded as nullary functions here; source member lookup unwraps
    /// them back to bare values.
    pub constructor_scheme: Scheme,
}

#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct Enum {
    /// Declared with the `linear` modifier: must be consumed exactly once.
    #[serde(default)]
    pub linear: bool,
    pub params: Vec<Symbol>,
    pub variants: IndexMap<String, Variant>,
    /// Instance method name → method symbol (methods on enums dispatch
    /// exactly like struct methods).
    pub methods: IndexMap<String, Symbol>,
    /// Well-formedness predicates over `params` for every application of
    /// this nominal.
    pub predicates: Vec<Predicate>,
}

/// A protocol method requirement. The catalog carries only the structure
/// (label keying, witness matching, defaultedness); the requirement's
/// TYPE lives in the schemes table under `symbol`, like every other
/// callable — one signature carrier, one instantiation/sanitize/export
/// path. The scheme's ty is self-prepended, ranges over
/// `Ty::Param(protocol symbol)` for Self and `Ty::Param(assoc symbol)`
/// for associated types, and its effect tail plus inner closure rows are
/// eff_params freshened per use.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Requirement {
    pub symbol: Symbol,
    pub has_default: bool,
}

#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct ProtocolInfo {
    /// Protocol input parameters, in source order.
    pub params: Vec<Symbol>,
    /// Default arguments for `params`, in the same order.
    pub param_defaults: Vec<Option<Ty>>,
    /// Associated types by source name (name-keyed so a sub-protocol's
    /// same-named `associated` refines its super's, Swift-style).
    pub assoc: IndexMap<String, Symbol>,
    /// Super-protocol applications (`protocol Comparable<R>: Equatable<R>`):
    /// a bound on P satisfies its supers transitively.
    pub supers: Vec<ProtocolRef>,
    /// Protocol refinements over `Self = Ty::Param(protocol symbol)`.
    pub predicates: Vec<Predicate>,
    pub requirements: IndexMap<String, Requirement>,
}

/// A selected protocol application: `self_ty` witnesses the full protocol
/// reference `protocol`. This is the single model for binding protocol `Self`,
/// protocol input parameters, and associated projections when a requirement is
/// instantiated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProtocolApplication {
    pub self_ty: Ty,
    pub protocol: ProtocolRef,
}

impl ProtocolApplication {
    pub fn new(self_ty: Ty, protocol: ProtocolRef) -> Self {
        Self { self_ty, protocol }
    }

    pub fn assoc_projection(&self, assoc: Symbol) -> Ty {
        Ty::Proj(Box::new(self.self_ty.clone()), self.protocol.clone(), assoc)
    }

    pub fn substitution(&self, catalog: &TypeCatalog) -> FxHashMap<Symbol, Ty> {
        let mut tys = FxHashMap::default();
        tys.insert(self.protocol.protocol, self.self_ty.clone());

        let Some(info) = catalog.protocols.get(&self.protocol.protocol) else {
            return tys;
        };

        for (param, arg) in info
            .params
            .iter()
            .copied()
            .zip(self.protocol.args.iter().cloned())
        {
            tys.insert(param, arg);
        }

        for (name, assoc) in &info.assoc {
            let binding = match &self.self_ty {
                Ty::Param(self_protocol @ Symbol::Protocol(_)) => catalog
                    .protocols
                    .get(self_protocol)
                    .and_then(|receiver_info| receiver_info.assoc.get(name).copied())
                    .map(Ty::Param)
                    .unwrap_or_else(|| self.assoc_projection(*assoc)),
                Ty::Any {
                    assoc: overrides, ..
                } => overrides
                    .iter()
                    .find_map(|(symbol, ty)| (symbol == assoc).then(|| ty.clone()))
                    .unwrap_or_else(|| self.assoc_projection(*assoc)),
                _ => self.assoc_projection(*assoc),
            };
            tys.insert(*assoc, binding);
        }

        tys
    }
}

/// One `extend Head: Protocol` row: requirement label → witness symbol, and
/// the associated-type bindings inferred by matching witness signatures
/// against requirement signatures (Chakravarty et al., ICFP 2005's
/// instance-determined synonyms). Conditional conformance (`extend
/// Array<Element: Showable>: Showable`) is an instance with a context (Hall,
/// Hammond, Peyton Jones & Wadler, TOPLAS 1996): `params` are the row's own
/// rigid variables, `self_args` the head application they appear in, and
/// `context` the predicates discharged as new wanteds at use.
#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct Conformance {
    pub params: Vec<Symbol>,
    pub self_args: Vec<Ty>,
    pub protocol_args: Vec<Ty>,
    pub context: Vec<Predicate>,
    pub witnesses: FxHashMap<String, Symbol>,
    pub assoc: FxHashMap<Symbol, Ty>,
}

/// An inherent (protocol-less) extend member: `extend Float { func _trunc()
/// ... }`.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct InherentMember {
    pub symbol: Symbol,
    /// The extend's rigid params and the head application they index —
    /// the instance-head pattern bound against the receiver at dispatch.
    /// The member's TYPE lives in the schemes table under `symbol`.
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
    pub predicates: Vec<Predicate>,
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
    pub enums: FxHashMap<Symbol, Enum>,
    pub protocols: FxHashMap<Symbol, ProtocolInfo>,
    pub conformances: FxHashMap<(Symbol, ProtocolRef), Conformance>,
    /// Type head -> protocol applications it conforms to (for member search by head).
    pub conformances_by_head: FxHashMap<Symbol, Vec<ProtocolRef>>,
    /// Member label → candidate owners, for improvement.
    pub member_owners: FxHashMap<String, Vec<MemberOwner>>,
    /// Rigid type parameter → declared protocol bounds.
    pub param_bounds: FxHashMap<Symbol, Vec<ProtocolRef>>,
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

/// One type-carrier the catalog embeds. Raw types sanitize per-`Ty`;
/// schemes sanitize as schemes (their minted eff/row params register);
/// predicates sanitize through their own folder.
pub struct ConformanceMatch<'a> {
    pub protocol: &'a ProtocolRef,
    pub conformance: &'a Conformance,
    pub substitution: FxHashMap<Symbol, Ty>,
}

pub(crate) enum EmbeddedTypes<'a> {
    Ty(&'a mut Ty),
    Scheme(&'a mut Scheme),
    Predicate(&'a mut Predicate),
}

impl TypeCatalog {
    /// Visit every type the catalog embeds, with its owning symbol. THE
    /// single authority for "types the catalog carries": finalization
    /// bakes and sanitizes through this walk, and the module-boundary
    /// portability assertion re-walks it — a new catalog field inherits
    /// both by being added here (and only here).
    pub(crate) fn for_each_embedded_mut(&mut self, f: &mut impl FnMut(Symbol, EmbeddedTypes)) {
        for (symbol, info) in self.structs.iter_mut() {
            for (_, field_ty) in info.fields.values_mut() {
                f(*symbol, EmbeddedTypes::Ty(field_ty));
            }
            for predicate in info.predicates.iter_mut() {
                f(*symbol, EmbeddedTypes::Predicate(predicate));
            }
        }
        for (symbol, info) in self.enums.iter_mut() {
            for variant in info.variants.values_mut() {
                f(
                    *symbol,
                    EmbeddedTypes::Scheme(&mut variant.constructor_scheme),
                );
            }
            for predicate in info.predicates.iter_mut() {
                f(*symbol, EmbeddedTypes::Predicate(predicate));
            }
        }
        // Requirements carry no types: their signatures are ordinary
        // schemes (finalized and exported through the schemes path).
        for (symbol, info) in self.protocols.iter_mut() {
            for predicate in info.predicates.iter_mut() {
                f(*symbol, EmbeddedTypes::Predicate(predicate));
            }
        }
        for ((head, _), conformance) in self.conformances.iter_mut() {
            for ty in conformance.self_args.iter_mut() {
                f(*head, EmbeddedTypes::Ty(ty));
            }
            for ty in conformance.protocol_args.iter_mut() {
                f(*head, EmbeddedTypes::Ty(ty));
            }
            for ty in conformance.assoc.values_mut() {
                f(*head, EmbeddedTypes::Ty(ty));
            }
            for predicate in conformance.context.iter_mut() {
                f(*head, EmbeddedTypes::Predicate(predicate));
            }
        }
        // Inherent members carry no signature (it's a scheme); only
        // the instance-head pattern is catalog-embedded.
        for members in self.extend_members.values_mut() {
            for member in members.values_mut() {
                let owner = member.symbol;
                for ty in member.self_args.iter_mut() {
                    f(owner, EmbeddedTypes::Ty(ty));
                }
            }
        }
        for (symbol, sig) in self.effects.iter_mut() {
            for ty in sig.params.iter_mut() {
                f(*symbol, EmbeddedTypes::Ty(ty));
            }
            f(*symbol, EmbeddedTypes::Ty(&mut sig.ret));
            for predicate in sig.predicates.iter_mut() {
                f(*symbol, EmbeddedTypes::Predicate(predicate));
            }
        }
        for (symbol, alias) in self.type_aliases.iter_mut() {
            f(*symbol, EmbeddedTypes::Ty(&mut alias.ty));
        }
    }

    /// Debug-mode boundary check: no unification variable may survive
    /// into a catalog that crosses a module boundary (a foreign store
    /// would misread its ids). Panics naming the owner on violation.
    pub fn debug_assert_portable(&mut self) {
        let mut violations: Vec<String> = vec![];
        self.for_each_embedded_mut(&mut |owner, item| {
            let leaked = match item {
                EmbeddedTypes::Ty(ty) => ty.has_unification_vars(),
                EmbeddedTypes::Scheme(scheme) => scheme.has_unification_vars(),
                EmbeddedTypes::Predicate(predicate) => predicate.has_unification_vars(),
            };
            if leaked {
                violations.push(format!("{owner}"));
            }
        });
        assert!(
            violations.is_empty(),
            "catalog leaks unification vars across the module boundary (owners: {violations:?})"
        );
    }

    /// The usage grade of a nominal: `Linear` iff declared `linear`, `Copy`
    /// for scalars and explicit `Copy` conformances, `Affine` otherwise
    /// (including unknown heads — affine is the safe default for both).
    /// Declared `'heap`: values are region-allocated objects with
    /// reference semantics.
    pub fn is_heap(&self, symbol: Symbol) -> bool {
        self.structs.get(&symbol).is_some_and(|info| info.heap)
    }

    pub fn grade_of(&self, symbol: Symbol) -> Grade {
        if matches!(
            symbol,
            Symbol::Int | Symbol::Float | Symbol::Bool | Symbol::Void
        ) || symbol == Symbol::RawPtr
            || symbol == Symbol::Byte
        {
            return Grade::Copy;
        }
        let linear = self
            .structs
            .get(&symbol)
            .map(|info| info.linear)
            .or_else(|| self.enums.get(&symbol).map(|info| info.linear))
            .unwrap_or(false);
        if linear {
            return Grade::Linear;
        }
        if self.has_bare_conformance(symbol, Symbol::Copy) {
            return Grade::Copy;
        }
        Grade::Affine
    }

    /// The copy-out-of-borrow judgment: an owned slot accepts a borrowed
    /// value of this head because extraction is free — Copy grade (a
    /// scalar borrow is a value copy at runtime) or CheapClone (an O(1)
    /// buffer retain, emitted by lowering at the coercion node). The one
    /// rule unify's coercion and generation's Apply-preservation share.
    pub fn copies_out_of_borrow(&self, symbol: Symbol) -> bool {
        self.grade_of(symbol) == Grade::Copy
            || self.has_bare_conformance(symbol, Symbol::CheapClone)
    }

    /// Canonicalize a protocol-argument type for conformance lookup. Borrowed
    /// Copy values satisfy owned protocol inputs by value, so `&Int` and `Int`
    /// select the same conformance key. Non-Copy borrows stay explicit: a
    /// borrow-shaped witness such as `Equatable<Pt>` must not become
    /// `Equatable<&Pt>`.
    pub fn canonical_conformance_arg(&self, ty: Ty) -> Ty {
        match ty {
            Ty::Borrow(perm, inner) => {
                let inner = self.canonical_conformance_arg(*inner);
                match &inner {
                    Ty::Nominal(symbol, _) if self.grade_of(*symbol) == Grade::Copy => inner,
                    _ => Ty::Borrow(perm, Box::new(inner)),
                }
            }
            Ty::Nominal(symbol, args) => Ty::Nominal(
                symbol,
                args.into_iter()
                    .map(|arg| self.canonical_conformance_arg(arg))
                    .collect(),
            ),
            Ty::Tuple(items) => Ty::Tuple(
                items
                    .into_iter()
                    .map(|item| self.canonical_conformance_arg(item))
                    .collect(),
            ),
            Ty::Func(args, ret, eff) => Ty::Func(
                args.into_iter()
                    .map(|arg| self.canonical_conformance_arg(arg))
                    .collect(),
                Box::new(self.canonical_conformance_arg(*ret)),
                eff,
            ),
            Ty::Record(record) => Ty::Record(crate::types::ty::Row {
                fields: record
                    .fields
                    .into_iter()
                    .map(|(label, field)| (label, self.canonical_conformance_arg(field)))
                    .collect(),
                tail: record.tail,
            }),
            Ty::Proj(base, protocol, assoc) => Ty::Proj(
                Box::new(self.canonical_conformance_arg(*base)),
                self.canonical_protocol_ref(protocol),
                assoc,
            ),
            other => other,
        }
    }

    pub fn canonical_protocol_ref(&self, protocol: ProtocolRef) -> ProtocolRef {
        ProtocolRef {
            protocol: protocol.protocol,
            args: protocol
                .args
                .into_iter()
                .map(|arg| self.canonical_conformance_arg(arg))
                .collect(),
        }
    }

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
                            linear: v.linear,
                            heap: v.heap,
                            params: v.params.iter().map(|s| imp(*s, target)).collect(),
                            eff_params: v.eff_params.iter().map(|s| imp(*s, target)).collect(),
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
                            predicates: v
                                .predicates
                                .into_iter()
                                .map(|predicate| predicate.import_symbols(target))
                                .collect(),
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
                        Enum {
                            linear: v.linear,
                            params: v.params.iter().map(|s| imp(*s, target)).collect(),
                            variants: v
                                .variants
                                .into_iter()
                                .map(|(l, variant)| {
                                    (
                                        l,
                                        Variant {
                                            symbol: imp(variant.symbol, target),
                                            payload_labels: variant.payload_labels,
                                            constructor_scheme: variant
                                                .constructor_scheme
                                                .import_symbols(target),
                                        },
                                    )
                                })
                                .collect(),
                            methods: v
                                .methods
                                .into_iter()
                                .map(|(l, s)| (l, imp(s, target)))
                                .collect(),
                            predicates: v
                                .predicates
                                .into_iter()
                                .map(|predicate| predicate.import_symbols(target))
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
                            params: v.params.iter().map(|s| imp(*s, target)).collect(),
                            param_defaults: v
                                .param_defaults
                                .iter()
                                .map(|default| default.as_ref().map(&imp_ty))
                                .collect(),
                            assoc: v
                                .assoc
                                .into_iter()
                                .map(|(name, s)| (name, imp(s, target)))
                                .collect(),
                            supers: v.supers.iter().map(|s| s.import_symbols(target)).collect(),
                            predicates: v
                                .predicates
                                .into_iter()
                                .map(|predicate| predicate.import_symbols(target))
                                .collect(),
                            requirements: v
                                .requirements
                                .into_iter()
                                .map(|(l, r)| {
                                    (
                                        l,
                                        Requirement {
                                            symbol: imp(r.symbol, target),
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
                        (imp(head, target), protocol.import_symbols(target)),
                        Conformance {
                            params: c.params.iter().map(|s| imp(*s, target)).collect(),
                            self_args: c.self_args.iter().map(&imp_ty).collect(),
                            protocol_args: c.protocol_args.iter().map(&imp_ty).collect(),
                            context: c
                                .context
                                .into_iter()
                                .map(|predicate| predicate.import_symbols(target))
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
                        protocols.iter().map(|p| p.import_symbols(target)).collect(),
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
                                MemberOwner::Protocol(s) => MemberOwner::Protocol(imp(s, target)),
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
                        bounds.iter().map(|b| b.import_symbols(target)).collect(),
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
                            predicates: sig
                                .predicates
                                .into_iter()
                                .map(|predicate| predicate.import_symbols(target))
                                .collect(),
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

    /// Return `protocol` followed by all transitive super-protocol
    /// applications, with duplicates removed.
    pub fn protocol_and_supers(&self, protocol: &ProtocolRef) -> Vec<ProtocolRef> {
        let mut result = vec![];
        let mut seen = FxHashSet::default();
        let mut queue = vec![protocol.clone()];
        while let Some(current) = queue.pop() {
            if !seen.insert(current.protocol) {
                continue;
            }
            result.push(current.clone());
            if let Some(info) = self.protocols.get(&current.protocol) {
                let tys: FxHashMap<Symbol, Ty> = info
                    .params
                    .iter()
                    .copied()
                    .zip(current.args.iter().cloned())
                    .collect();
                queue.extend(
                    info.supers
                        .iter()
                        .rev()
                        .map(|sup| sup.substitute(&tys, &Default::default(), &Default::default())),
                );
            }
        }
        result
    }

    /// Every requirement that a conformance to `protocol` must satisfy,
    /// including inherited requirements. The owning protocol application is
    /// retained because projections are keyed by the full protocol ref.
    pub fn requirements_for_conformance(
        &self,
        protocol: &ProtocolRef,
    ) -> Vec<(ProtocolRef, String, Requirement)> {
        let mut requirements: Vec<(ProtocolRef, String, Requirement)> = vec![];
        for owner in self.protocol_and_supers(protocol) {
            let Some(info) = self.protocols.get(&owner.protocol) else {
                continue;
            };
            for (label, requirement) in &info.requirements {
                if requirements
                    .iter()
                    .any(|(_, _, existing)| existing.symbol == requirement.symbol)
                {
                    continue;
                }
                requirements.push((owner.clone(), label.clone(), requirement.clone()));
            }
        }
        requirements
    }

    /// Does a bound set satisfy `target`, directly or through super-protocol
    /// closure?
    pub fn bounds_satisfy(&self, bounds: &[ProtocolRef], target: &ProtocolRef) -> bool {
        bounds.iter().any(|bound| {
            self.protocol_and_supers(bound)
                .into_iter()
                .any(|candidate| candidate == *target)
        })
    }

    pub fn has_bare_conformance(&self, head: Symbol, protocol: Symbol) -> bool {
        self.conformances
            .contains_key(&(head, ProtocolRef::bare(protocol)))
    }

    pub fn conformance_rows_overlap(
        &self,
        left_protocol: &ProtocolRef,
        left: &Conformance,
        right_protocol: &ProtocolRef,
        right: &Conformance,
    ) -> bool {
        if left_protocol.protocol != right_protocol.protocol
            || left.self_args.len() != right.self_args.len()
            || left.protocol_args.len() != right.protocol_args.len()
        {
            return false;
        }
        let mut forward = FxHashMap::default();
        let forward_matches = left
            .self_args
            .iter()
            .zip(&right.self_args)
            .all(|(left, right)| match_pattern(left, right, &mut forward))
            && left
                .protocol_args
                .iter()
                .zip(&right.protocol_args)
                .all(|(left, right)| match_key_pattern(left, right, &mut forward));

        let mut reverse = FxHashMap::default();
        let reverse_matches = left
            .self_args
            .iter()
            .zip(&right.self_args)
            .all(|(left, right)| match_pattern(right, left, &mut reverse))
            && left
                .protocol_args
                .iter()
                .zip(&right.protocol_args)
                .all(|(left, right)| match_key_pattern(right, left, &mut reverse));

        forward_matches && reverse_matches
    }

    pub fn matching_conformances<'a>(
        &'a self,
        head: Symbol,
        self_args: &[Ty],
        target: &ProtocolRef,
    ) -> Vec<ConformanceMatch<'a>> {
        let self_ty = Ty::Nominal(head, self_args.to_vec());
        self.conformances
            .iter()
            .filter_map(|((candidate_head, candidate_protocol), conformance)| {
                self.match_conformance_row(
                    *candidate_head,
                    candidate_protocol,
                    conformance,
                    Some((head, self_args)),
                    &self_ty,
                    target,
                )
            })
            .collect()
    }

    pub fn matching_protocol_head_conformances<'a>(
        &'a self,
        self_ty: &Ty,
        target: &ProtocolRef,
    ) -> Vec<ConformanceMatch<'a>> {
        self.conformances
            .iter()
            .filter_map(|((candidate_head, candidate_protocol), conformance)| {
                self.match_conformance_row(
                    *candidate_head,
                    candidate_protocol,
                    conformance,
                    None,
                    self_ty,
                    target,
                )
            })
            .collect()
    }

    fn match_conformance_row<'a>(
        &'a self,
        candidate_head: Symbol,
        candidate_protocol: &'a ProtocolRef,
        conformance: &'a Conformance,
        nominal_head: Option<(Symbol, &[Ty])>,
        self_ty: &Ty,
        target: &ProtocolRef,
    ) -> Option<ConformanceMatch<'a>> {
        if candidate_protocol.protocol != target.protocol
            || conformance.protocol_args.len() != target.args.len()
        {
            return None;
        }
        let mut substitution = FxHashMap::default();
        let self_matches = if matches!(candidate_head, Symbol::Protocol(_)) {
            conformance.self_args.is_empty()
                && match_pattern(&Ty::Param(candidate_head), self_ty, &mut substitution)
        } else if let Some((head, _)) = nominal_head {
            candidate_head == head
                && match_pattern(
                    &Ty::Nominal(candidate_head, conformance.self_args.clone()),
                    self_ty,
                    &mut substitution,
                )
        } else {
            false
        };
        let protocol_matches = conformance
            .protocol_args
            .iter()
            .zip(&target.args)
            .all(|(pattern, actual)| match_key_pattern(pattern, actual, &mut substitution));
        (self_matches && protocol_matches).then_some(ConformanceMatch {
            protocol: candidate_protocol,
            conformance,
            substitution,
        })
    }

    /// All associated types reachable from a protocol (through supers), in a
    /// stable traversal order. Same-named associated types are overridden by
    /// the most-specific protocol reached first.
    pub fn associated_types_in(&self, protocol: Symbol) -> Vec<(String, Symbol)> {
        self.associated_types_in_ref(&ProtocolRef::bare(protocol))
            .into_iter()
            .map(|(name, _, assoc)| (name, assoc))
            .collect()
    }

    pub fn declared_associated_types_in_ref(
        &self,
        protocol: &ProtocolRef,
    ) -> Vec<(String, ProtocolRef, Symbol)> {
        let Some(info) = self.protocols.get(&protocol.protocol) else {
            return vec![];
        };
        info.assoc
            .iter()
            .map(|(name, symbol)| (name.clone(), protocol.clone(), *symbol))
            .collect()
    }

    pub fn associated_types_in_ref(
        &self,
        protocol: &ProtocolRef,
    ) -> Vec<(String, ProtocolRef, Symbol)> {
        let mut result = IndexMap::new();
        for current in self.protocol_and_supers(protocol) {
            if let Some(info) = self.protocols.get(&current.protocol) {
                for (name, symbol) in &info.assoc {
                    result
                        .entry(name.clone())
                        .or_insert((current.clone(), *symbol));
                }
            }
        }
        result
            .into_iter()
            .map(|(name, (owner, assoc))| (name, owner, assoc))
            .collect()
    }

    /// Find an associated type named `label` reachable from a protocol
    /// (through supers). Returns (owning protocol application, assoc symbol).
    pub fn associated_type_in_ref(
        &self,
        protocol: &ProtocolRef,
        label: &str,
    ) -> Option<(ProtocolRef, Symbol)> {
        self.associated_types_in_ref(protocol)
            .into_iter()
            .find_map(|(name, owner, assoc)| (name == label).then_some((owner, assoc)))
    }

    pub fn associated_type_in(&self, protocol: Symbol, label: &str) -> Option<(Symbol, Symbol)> {
        self.associated_type_in_ref(&ProtocolRef::bare(protocol), label)
            .map(|(owner, assoc)| (owner.protocol, assoc))
    }

    /// Find a requirement named `label` reachable from a protocol (through
    /// supers). Returns (owning protocol application, requirement).
    pub fn requirement_in_ref(
        &self,
        protocol: &ProtocolRef,
        label: &str,
    ) -> Option<(ProtocolRef, &Requirement)> {
        for current in self.protocol_and_supers(protocol) {
            if let Some(info) = self.protocols.get(&current.protocol)
                && let Some(requirement) = info.requirements.get(label)
            {
                return Some((current, requirement));
            }
        }
        None
    }

    pub fn requirement_in(&self, protocol: Symbol, label: &str) -> Option<(Symbol, &Requirement)> {
        self.requirement_in_ref(&ProtocolRef::bare(protocol), label)
            .map(|(owner, requirement)| (owner.protocol, requirement))
    }
}
