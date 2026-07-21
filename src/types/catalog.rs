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

use crate::types::ty::{
    Predicate, ProtocolRef, Scheme, SchemeParam, Ty, match_key_pattern, match_pattern,
};
use crate::{compiling::module::ModuleId, name_resolution::symbol::Symbol};

/// The usage grade of a declaration over the substructural lattice:
/// `Copy` values duplicate freely, `Affine` values (the default) move and may
/// be silently dropped, `Linear` values must be consumed exactly once.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Grade {
    Copy,
    Affine,
    Linear,
}

/// How a borrowed value of some head fills an owned slot (tier 2 of the
/// borrow-coercion ladder): a `Copy` head extracts by value, a
/// `CheapClone` head by a silent O(1) clone lowering emits at the
/// coercion node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CoerceKind {
    Copy,
    CheapClone,
}

#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct StructInfo {
    /// Declared with the `linear` modifier: must be consumed exactly once.
    #[serde(default)]
    pub linear: bool,
    /// Declared `'heap`: reference semantics, region-allocated.
    #[serde(default)]
    pub heap: bool,
    /// Declared generic parameters — the canonical records: symbol, kind
    /// (type or ADR 0035 static value), and declared default.
    pub params: Vec<SchemeParam>,
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
    /// Initializers (explicit or resolver-synthesized memberwise) with
    /// their declared arity, `self` included.
    pub inits: Vec<(Symbol, usize)>,
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
    /// Declared generic parameters (see `StructInfo::params`).
    pub params: Vec<SchemeParam>,
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
    /// Protocol input parameters, in source order — canonical records
    /// carrying kind and declared default.
    pub params: Vec<SchemeParam>,
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

        for (param, arg) in info.params.iter().zip(self.protocol.args.iter().cloned()) {
            tys.insert(param.symbol, arg);
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
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub struct ConformanceId {
    pub module_id: ModuleId,
    pub local_id: u32,
}

impl ConformanceId {
    pub fn new(module_id: ModuleId, local_id: u32) -> Self {
        Self {
            module_id,
            local_id,
        }
    }

    pub fn import(self, module_id: ModuleId) -> Self {
        if self.module_id == ModuleId::Current {
            Self { module_id, ..self }
        } else {
            self
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Conformance {
    /// Nominal or protocol family at the self-pattern head.
    pub head: Symbol,
    /// Complete target protocol pattern. Its arguments participate in row
    /// identity and match with the self pattern through one substitution.
    pub protocol: ProtocolRef,
    pub params: Vec<Symbol>,
    pub self_args: Vec<Ty>,
    pub context: Vec<Predicate>,
    pub witnesses: FxHashMap<String, Symbol>,
    pub assoc: FxHashMap<Symbol, Ty>,
}

impl Conformance {
    pub fn new(head: Symbol, protocol: ProtocolRef) -> Self {
        Self {
            head,
            protocol,
            params: vec![],
            self_args: vec![],
            context: vec![],
            witnesses: FxHashMap::default(),
            assoc: FxHashMap::default(),
        }
    }
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
    /// The same canonical records as schemes and nominals carry — kind
    /// (type or static value) and default included.
    pub generics: Vec<SchemeParam>,
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
    /// Stable conformance rows. The row owns its complete semantic head;
    /// indexes contain IDs only and are never a second source of truth.
    pub conformances: IndexMap<ConformanceId, Conformance>,
    /// Type head -> candidate row IDs.
    pub conformances_by_head: FxHashMap<Symbol, Vec<ConformanceId>>,
    #[serde(default)]
    next_conformance_id: u32,
    /// Member label → candidate owners, for improvement.
    pub member_owners: FxHashMap<String, Vec<MemberOwner>>,
    /// Rigid type parameter → declared protocol bounds.
    pub param_bounds: FxHashMap<Symbol, Vec<ProtocolRef>>,
    /// Static value parameter → its declared value type (ADR 0035). A
    /// DERIVED index over the canonical parameter records (single writer:
    /// `register_static_param`), kept for the symbol-keyed queries that
    /// have no parameter list in hand — a static param used as a value in
    /// a body (`lookup_symbol_ty`), and annotation-slot interpretation by
    /// position (`lower_generic_args`). Scheme-carried parameters answer
    /// kind questions from `SchemeParam::kind` directly.
    #[serde(default)]
    pub static_params: FxHashMap<Symbol, Ty>,
    /// Inherent extend members by type head.
    pub extend_members: FxHashMap<Symbol, IndexMap<String, InherentMember>>,
    /// Effect operation signatures.
    pub effects: FxHashMap<Symbol, EffectSig>,
    /// Transparent type aliases exported through the catalog for imports.
    #[serde(default)]
    pub type_aliases: FxHashMap<Symbol, TypeAliasInfo>,
    /// Protocols auto-derived for structs and enums when no explicit
    /// conformance exists. The derived instance's context is structural:
    /// every field/payload must conform too.
    pub derivable: Vec<Symbol>,
}

/// One type-carrier the catalog embeds. Raw types sanitize per-`Ty`;
/// schemes sanitize as schemes (their minted eff/row params register);
/// predicates sanitize through their own folder.
pub struct ConformanceMatch<'a> {
    pub id: ConformanceId,
    pub protocol: &'a ProtocolRef,
    pub conformance: &'a Conformance,
    pub substitution: FxHashMap<Symbol, Ty>,
}

impl ConformanceMatch<'_> {
    /// The complete type substitution lowering needs for this selected row:
    /// rigid head parameters plus associated-type witnesses.
    pub fn evidence_substitution(&self) -> Vec<(Symbol, Ty)> {
        let mut substitution = self
            .substitution
            .iter()
            .map(|(symbol, ty)| (*symbol, ty.clone()))
            .collect::<Vec<_>>();
        substitution.extend(self.conformance.assoc.iter().map(|(assoc, bound)| {
            (
                *assoc,
                bound.substitute(
                    &self.substitution,
                    &FxHashMap::default(),
                    &FxHashMap::default(),
                ),
            )
        }));
        substitution
    }
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
            for param in info.params.iter_mut() {
                if let Some(default) = param.default.as_mut() {
                    f(*symbol, EmbeddedTypes::Ty(default));
                }
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
            for param in info.params.iter_mut() {
                if let Some(default) = param.default.as_mut() {
                    f(*symbol, EmbeddedTypes::Ty(default));
                }
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
        for conformance in self.conformances.values_mut() {
            let head = conformance.head;
            for ty in conformance.self_args.iter_mut() {
                f(head, EmbeddedTypes::Ty(ty));
            }
            for ty in conformance.protocol.args.iter_mut() {
                f(head, EmbeddedTypes::Ty(ty));
            }
            for ty in conformance.assoc.values_mut() {
                f(head, EmbeddedTypes::Ty(ty));
            }
            for predicate in conformance.context.iter_mut() {
                f(head, EmbeddedTypes::Predicate(predicate));
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
        for (symbol, ty) in self.static_params.iter_mut() {
            f(*symbol, EmbeddedTypes::Ty(ty));
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
    /// for scalars, payload-free enums (bare tags at runtime), and explicit
    /// `Copy` conformances, `Affine` otherwise (including unknown heads;
    /// affine is the safe default for both).
    /// Declared `'heap`: values are region-allocated objects with
    /// reference semantics.
    pub fn is_heap(&self, symbol: Symbol) -> bool {
        self.structs.get(&symbol).is_some_and(|info| info.heap)
    }

    pub fn grade_of(&self, symbol: Symbol) -> Grade {
        if self.is_scalar(symbol) {
            return Grade::Copy;
        }
        if self.is_linear_decl(symbol) {
            return Grade::Linear;
        }
        if self.payload_free_enum(symbol) {
            return Grade::Copy;
        }
        if self.has_bare_conformance(symbol, Symbol::Copy) {
            return Grade::Copy;
        }
        Grade::Affine
    }

    fn is_scalar(&self, symbol: Symbol) -> bool {
        matches!(
            symbol,
            Symbol::Int | Symbol::Float | Symbol::Bool | Symbol::Void
        ) || symbol == Symbol::RawPtr
            || symbol == Symbol::Byte
    }

    fn is_linear_decl(&self, symbol: Symbol) -> bool {
        self.structs
            .get(&symbol)
            .map(|info| info.linear)
            .or_else(|| self.enums.get(&symbol).map(|info| info.linear))
            .unwrap_or(false)
    }

    /// A payload-free enum is a bare tag at runtime: nothing to own,
    /// nothing to drop, so it copies like a scalar.
    fn payload_free_enum(&self, symbol: Symbol) -> bool {
        self.enums.get(&symbol).is_some_and(|info| {
            !info.variants.is_empty()
                && info.variants.values().all(|variant| {
                    matches!(&variant.constructor_scheme.ty, Ty::Func(payloads, ..) if payloads.is_empty())
                })
        })
    }

    /// Copy with no declaration needed: scalars and payload-free non-linear
    /// enums. Such a head stores none of its type arguments, so intrinsic
    /// copyability holds regardless of what the (phantom) arguments are.
    pub fn intrinsic_copy(&self, symbol: Symbol) -> bool {
        self.is_scalar(symbol) || (!self.is_linear_decl(symbol) && self.payload_free_enum(symbol))
    }

    /// The copy-out-of-borrow judgment: an owned slot accepts a borrowed
    /// value of this head because extraction is free — Copy grade (a
    /// scalar borrow is a value copy at runtime) or CheapClone (an O(1)
    /// buffer retain, emitted by lowering at the coercion node). The one
    /// rule unify's coercion and generation's Apply-preservation share.
    pub fn copies_out_of_borrow(&self, symbol: Symbol) -> bool {
        self.coerce_kind(symbol).is_some()
    }

    /// The tier-2 classification behind [`Self::copies_out_of_borrow`]:
    /// `Copy` heads extract by value (nothing to emit); `CheapClone` heads
    /// extract by an O(1) buffer retain that lowering emits at the
    /// recorded coercion node. Every site that records a `coerce_clones`
    /// entry maps from this — the action is not re-derived per site.
    pub fn coerce_kind(&self, symbol: Symbol) -> Option<CoerceKind> {
        if self.grade_of(symbol) == Grade::Copy {
            return Some(CoerceKind::Copy);
        }
        if self.has_bare_conformance(symbol, Symbol::CheapClone) {
            return Some(CoerceKind::CheapClone);
        }
        None
    }

    /// [`Self::coerce_kind`] for a rigid parameter, judged from its
    /// declared bounds.
    pub fn bounds_coerce_kind(&self, bounds: &[ProtocolRef]) -> Option<CoerceKind> {
        if self.bounds_satisfy(bounds, &ProtocolRef::bare(Symbol::Copy)) {
            return Some(CoerceKind::Copy);
        }
        if self.bounds_satisfy(bounds, &ProtocolRef::bare(Symbol::CheapClone)) {
            return Some(CoerceKind::CheapClone);
        }
        None
    }

    /// A CheapClone row matching this application with its where-clause
    /// context satisfied. The collect-time marker field check reaches the same
    /// rows through [`Self::ty_satisfies_marker`].
    pub fn cheap_clone_rows(&self, symbol: Symbol, args: &[Ty]) -> bool {
        // Fast path for the common shape (`extend Array<Element>:
        // CheapClone {}`): the row keyed at (head, CheapClone) has no
        // where-clause context and a fully generic self pattern, so it
        // matches every application of the head, with no row scan or context
        // check. The O(rows) scan below handles conditional and protocol-head
        // rows.
        if self.conformances_for_head(symbol).any(|(_, row)| {
            row.protocol == ProtocolRef::bare(Symbol::CheapClone)
                && row.context.is_empty()
                && unconditional_self_pattern(row)
        }) {
            return true;
        }
        self.matching_conformances(symbol, args, &ProtocolRef::bare(Symbol::CheapClone))
            .iter()
            .any(|found| self.marker_context_satisfied(found, &[]))
    }

    /// Marker (Copy/CheapClone) satisfaction for a stored type. Declared
    /// conformance rows are the authority: a matching row satisfies the
    /// marker when its where-clause context does (under the match
    /// substitution), and a Copy row also satisfies CheapClone. `ambient`
    /// carries the where-clause predicates of a conformance currently
    /// being validated, so its own rigid params can satisfy the marker.
    pub fn ty_satisfies_marker(&self, ty: &Ty, marker: Symbol, ambient: &[Predicate]) -> bool {
        match ty {
            // Error is poison; a variable here means the field type is still
            // being collected — the conformance's own use sites will re-check.
            Ty::Error | Ty::Var(_) => true,
            // A unique value is the sole reference: never Copy/CheapClone.
            Ty::Unique(_) => false,
            Ty::Nominal(symbol, args) => {
                // Scalars and payload-free enums store nothing, so any
                // (phantom) arguments are irrelevant.
                if self.intrinsic_copy(*symbol) {
                    return true;
                }
                // Otherwise the declared rows decide.
                let row_satisfies = |protocol: Symbol| {
                    self.matching_conformances(*symbol, args, &ProtocolRef::bare(protocol))
                        .iter()
                        .any(|found| self.marker_context_satisfied(found, ambient))
                };
                row_satisfies(Symbol::Copy)
                    || (marker == Symbol::CheapClone && row_satisfies(Symbol::CheapClone))
            }
            Ty::Param(symbol) => {
                let bound_satisfies = |bounds: &Vec<ProtocolRef>| {
                    bounds.contains(&ProtocolRef::bare(marker))
                        || (marker == Symbol::CheapClone
                            && bounds.contains(&ProtocolRef::bare(Symbol::Copy)))
                };
                self.param_bounds.get(symbol).is_some_and(bound_satisfies)
                    || ambient.iter().any(|predicate| {
                        matches!(
                            predicate,
                            Predicate::Conforms { ty: Ty::Param(bound), protocol }
                                if bound == symbol
                                    && protocol.args.is_empty()
                                    && (protocol.protocol == marker
                                        || (marker == Symbol::CheapClone
                                            && protocol.protocol == Symbol::Copy))
                        )
                    })
            }
            Ty::Tuple(items) => items
                .iter()
                .all(|item| self.ty_satisfies_marker(item, marker, ambient)),
            Ty::Record(row) => {
                row.tail.is_none()
                    && row
                        .fields
                        .iter()
                        .all(|(_, field)| self.ty_satisfies_marker(field, marker, ambient))
            }
            // An effect argument is runtime-inert: it never blocks a
            // marker (Copy/CheapClone judge values, not rows). A static
            // argument is likewise phase-only (ADR 0035: evidence erases).
            Ty::Eff(_) | Ty::Static(_) => true,
            Ty::Borrow(..) | Ty::Func(..) | Ty::Any { .. } | Ty::Proj(..) => false,
        }
    }

    /// A matched conformance row holds for marker purposes when every
    /// where-clause predicate does, under the match's substitution. Only
    /// marker predicates are decidable here without the solver; anything
    /// else stays conservative (the claim's use sites re-check).
    fn marker_context_satisfied(&self, found: &ConformanceMatch, ambient: &[Predicate]) -> bool {
        found.conformance.context.iter().all(|predicate| {
            let Predicate::Conforms { ty, protocol } = predicate else {
                return false;
            };
            if !matches!(protocol.protocol, Symbol::Copy | Symbol::CheapClone)
                || !protocol.args.is_empty()
            {
                return false;
            }
            let bound = ty.substitute(
                &found.substitution,
                &FxHashMap::default(),
                &FxHashMap::default(),
            );
            self.ty_satisfies_marker(&bound, protocol.protocol, ambient)
        })
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

    /// The application an auto-derived protocol has for `Self`. Derivation
    /// only applies when every protocol input has a default; each default is
    /// instantiated left-to-right so `Equatable<RHS = Self>` becomes
    /// `Equatable<Self>` while a parameterless protocol remains bare.
    pub fn derived_protocol_ref(&self, protocol: Symbol, self_ty: &Ty) -> Option<ProtocolRef> {
        let info = self.protocols.get(&protocol)?;
        let mut substitution = FxHashMap::default();
        substitution.insert(protocol, self_ty.clone());
        let mut args = Vec::with_capacity(info.params.len());
        for param in &info.params {
            let default = param.default.as_ref()?;
            let arg = default.substitute(&substitution, &Default::default(), &Default::default());
            substitution.insert(param.symbol, arg.clone());
            args.push(arg);
        }
        Some(self.canonical_protocol_ref(ProtocolRef { protocol, args }))
    }

    /// Remap every symbol for an importer (the catalog half of
    /// `Module::import_as`).
    pub fn import_as(self, target: crate::compiling::module::ModuleId) -> TypeCatalog {
        use crate::types::ty::import_symbol as imp;
        let imp_ty = |t: &Ty| t.import_symbols(target);
        let imp_param = |param: &SchemeParam| SchemeParam {
            symbol: imp(param.symbol, target),
            kind: match &param.kind {
                crate::types::ty::ParamKind::Type => crate::types::ty::ParamKind::Type,
                crate::types::ty::ParamKind::Static(value_ty) => {
                    crate::types::ty::ParamKind::Static(imp_ty(value_ty))
                }
            },
            default: param.default.as_ref().map(&imp_ty),
        };
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
                            params: v.params.iter().map(imp_param).collect(),
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
                            inits: v
                                .inits
                                .iter()
                                .map(|(s, arity)| (imp(*s, target), *arity))
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
            enums: self
                .enums
                .into_iter()
                .map(|(k, v)| {
                    (
                        imp(k, target),
                        Enum {
                            linear: v.linear,
                            params: v.params.iter().map(imp_param).collect(),
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
                            params: v.params.iter().map(imp_param).collect(),
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
                .map(|(id, c)| {
                    (
                        id.import(target),
                        Conformance {
                            head: imp(c.head, target),
                            protocol: c.protocol.import_symbols(target),
                            params: c.params.iter().map(|s| imp(*s, target)).collect(),
                            self_args: c.self_args.iter().map(&imp_ty).collect(),
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
                .map(|(head, ids)| {
                    (
                        imp(head, target),
                        ids.into_iter().map(|id| id.import(target)).collect(),
                    )
                })
                .collect(),
            next_conformance_id: self.next_conformance_id,
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
            static_params: self
                .static_params
                .into_iter()
                .map(|(s, ty)| (imp(s, target), imp_ty(&ty)))
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
                            generics: sig.generics.iter().map(imp_param).collect(),
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
        self.next_conformance_id = self.next_conformance_id.max(other.next_conformance_id);
        for (id, conformance) in other.conformances {
            if self
                .conformances
                .values()
                .any(|existing| existing == &conformance)
            {
                continue;
            }
            let head = conformance.head;
            self.conformances.insert(id, conformance);
            self.conformances_by_head.entry(head).or_default().push(id);
        }
        for (label, owners) in other.member_owners {
            for owner in owners {
                self.add_owner(&label, owner);
            }
        }
        self.param_bounds.extend(other.param_bounds);
        self.static_params.extend(other.static_params);
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
                    .map(|param| param.symbol)
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

    pub fn insert_conformance(&mut self, conformance: Conformance) -> ConformanceId {
        let id = ConformanceId::new(ModuleId::Current, self.next_conformance_id);
        self.next_conformance_id += 1;
        let head = conformance.head;
        self.conformances.insert(id, conformance);
        self.conformances_by_head.entry(head).or_default().push(id);
        id
    }

    pub fn conformance(&self, id: ConformanceId) -> Option<&Conformance> {
        self.conformances.get(&id)
    }

    pub fn conformance_mut(&mut self, id: ConformanceId) -> Option<&mut Conformance> {
        self.conformances.get_mut(&id)
    }

    pub fn conformances_for_head(
        &self,
        head: Symbol,
    ) -> impl Iterator<Item = (ConformanceId, &Conformance)> {
        self.conformances_by_head
            .get(&head)
            .into_iter()
            .flatten()
            .filter_map(|id| self.conformances.get(id).map(|row| (*id, row)))
    }

    pub fn has_bare_conformance(&self, head: Symbol, protocol: Symbol) -> bool {
        self.conformances_for_head(head)
            .any(|(_, row)| row.protocol.protocol == protocol && row.protocol.args.is_empty())
    }

    pub fn family_unconditionally_conforms(&self, head: Symbol, protocol: Symbol) -> bool {
        let family_args: Vec<Ty> = self
            .structs
            .get(&head)
            .map(|info| {
                info.params
                    .iter()
                    .map(|param| Ty::Param(param.symbol))
                    .collect()
            })
            .or_else(|| {
                self.enums.get(&head).map(|info| {
                    info.params
                        .iter()
                        .map(|param| Ty::Param(param.symbol))
                        .collect()
                })
            })
            .unwrap_or_default();
        self.matching_conformances(head, &family_args, &ProtocolRef::bare(protocol))
            .into_iter()
            .filter(|matched| matched.conformance.head == head)
            .any(|matched| {
                unconditional_self_pattern(matched.conformance)
                    && matched.conformance.context.iter().all(|predicate| {
                        let predicate = predicate.substitute(
                            &matched.substitution,
                            &FxHashMap::default(),
                            &FxHashMap::default(),
                        );
                        match predicate {
                            Predicate::Conforms {
                                ty: Ty::Param(param),
                                protocol,
                            } => self
                                .param_bounds
                                .get(&param)
                                .is_some_and(|bounds| self.bounds_satisfy(bounds, &protocol)),
                            Predicate::TypeEq(left, right) => left == right,
                            _ => false,
                        }
                    })
            })
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
            || left_protocol.args.len() != right_protocol.args.len()
        {
            return false;
        }
        let mut forward = FxHashMap::default();
        let forward_matches = left
            .self_args
            .iter()
            .zip(&right.self_args)
            .all(|(left, right)| match_pattern(left, right, &mut forward))
            && left_protocol
                .args
                .iter()
                .zip(&right_protocol.args)
                .all(|(left, right)| match_key_pattern(left, right, &mut forward));

        let mut reverse = FxHashMap::default();
        let reverse_matches = left
            .self_args
            .iter()
            .zip(&right.self_args)
            .all(|(left, right)| match_pattern(right, left, &mut reverse))
            && left_protocol
                .args
                .iter()
                .zip(&right_protocol.args)
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
        let mut matches = self
            .conformances_for_head(head)
            .filter_map(|(id, conformance)| {
                self.match_conformance_row(
                    id,
                    conformance,
                    Some((head, self_args)),
                    &self_ty,
                    target,
                )
            })
            .collect::<Vec<_>>();
        // A direct declaration is the canonical evidence for P when another
        // row reaches P only through a subprotocol. This is inheritance
        // projection, not ordered instance specialization.
        if matches
            .iter()
            .any(|matched| matched.conformance.protocol.protocol == target.protocol)
        {
            matches.retain(|matched| matched.conformance.protocol.protocol == target.protocol);
        }
        matches.extend(self.matching_protocol_head_conformances(&self_ty, target));
        matches
    }

    pub fn match_conformance<'a>(
        &'a self,
        id: ConformanceId,
        self_ty: &Ty,
        target: &ProtocolRef,
    ) -> Option<ConformanceMatch<'a>> {
        let conformance = self.conformance(id)?;
        let nominal_head = match self_ty {
            Ty::Nominal(head, args) => Some((*head, args.as_slice())),
            _ => None,
        };
        self.match_conformance_row(id, conformance, nominal_head, self_ty, target)
    }

    pub fn matching_protocol_head_conformances<'a>(
        &'a self,
        self_ty: &Ty,
        target: &ProtocolRef,
    ) -> Vec<ConformanceMatch<'a>> {
        self.conformances
            .iter()
            .filter_map(|(id, conformance)| {
                self.match_conformance_row(*id, conformance, None, self_ty, target)
            })
            .collect()
    }

    fn match_conformance_row<'a>(
        &'a self,
        id: ConformanceId,
        conformance: &'a Conformance,
        nominal_head: Option<(Symbol, &[Ty])>,
        self_ty: &Ty,
        target: &ProtocolRef,
    ) -> Option<ConformanceMatch<'a>> {
        let candidate_head = conformance.head;
        let candidate_protocol = &conformance.protocol;
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
        let protocol_matches = self
            .protocol_and_supers(candidate_protocol)
            .into_iter()
            .filter(|candidate| {
                candidate.protocol == target.protocol && candidate.args.len() == target.args.len()
            })
            .any(|candidate| {
                let mut probe = substitution.clone();
                let matches = candidate
                    .args
                    .iter()
                    .zip(&target.args)
                    .all(|(pattern, actual)| match_key_pattern(pattern, actual, &mut probe));
                if matches {
                    substitution = probe;
                }
                matches
            });
        (self_matches && protocol_matches).then_some(ConformanceMatch {
            id,
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

/// Every self arg of a conformance row is a distinct rigid pattern
/// variable (`extend Array<Element>`): the row matches ANY application of
/// its head, so a match needs no per-application pattern binding.
fn unconditional_self_pattern(row: &Conformance) -> bool {
    let mut seen = FxHashSet::default();
    row.self_args.iter().all(
        |arg| matches!(arg, Ty::Param(param) if row.params.contains(param) && seen.insert(*param)),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::name_resolution::symbol::{DeclaredLocalId, StructId};

    fn catalog_with_row(head: Symbol, mut row: Conformance) -> TypeCatalog {
        let mut catalog = TypeCatalog::default();
        row.head = head;
        row.protocol = ProtocolRef::bare(Symbol::CheapClone);
        catalog.insert_conformance(row);
        catalog
    }

    #[test]
    fn cheap_clone_rows_fast_paths_unconditional_rows() {
        // `extend Box<T>: CheapClone {}`: no context, fully generic self
        // pattern — every application is CheapClone, straight off the
        // (head, protocol) key.
        let head = Symbol::Struct(StructId::from(1));
        let param = Symbol::DeclaredLocal(DeclaredLocalId(10));
        let catalog = catalog_with_row(
            head,
            Conformance {
                params: vec![param],
                self_args: vec![Ty::Param(param)],
                ..Conformance::new(head, ProtocolRef::bare(Symbol::CheapClone))
            },
        );
        assert!(catalog.cheap_clone_rows(head, &[Ty::Nominal(Symbol::Int, vec![])]));
        assert!(catalog.cheap_clone_rows(head, &[Ty::Nominal(Symbol::String, vec![])]));
    }

    #[test]
    fn cheap_clone_rows_conditional_row_consults_the_context() {
        // `extend Box<T>: CheapClone where T: CheapClone {}`: the fast
        // path must NOT fire — the where-clause context decides per
        // application through the full row scan.
        let head = Symbol::Struct(StructId::from(1));
        let param = Symbol::DeclaredLocal(DeclaredLocalId(10));
        let catalog = catalog_with_row(
            head,
            Conformance {
                params: vec![param],
                self_args: vec![Ty::Param(param)],
                context: vec![Predicate::Conforms {
                    ty: Ty::Param(param),
                    protocol: ProtocolRef::bare(Symbol::CheapClone),
                }],
                ..Conformance::new(head, ProtocolRef::bare(Symbol::CheapClone))
            },
        );
        // String is intrinsically CheapClone-satisfying only via declared
        // rows; this catalog has none for it, so the context fails…
        assert!(!catalog.cheap_clone_rows(head, &[Ty::Nominal(Symbol::String, vec![])]));
        // …while an intrinsically-Copy scalar satisfies it.
        assert!(catalog.cheap_clone_rows(head, &[Ty::Nominal(Symbol::Int, vec![])]));
    }

    #[test]
    fn cheap_clone_rows_without_a_row_is_false() {
        let head = Symbol::Struct(StructId::from(1));
        let catalog = TypeCatalog::default();
        assert!(!catalog.cheap_clone_rows(head, &[]));
    }

    #[test]
    fn cheap_clone_rows_specialized_self_pattern_skips_the_fast_path() {
        // A row whose self pattern is concrete (`extend Box<Int>:
        // CheapClone {}`) matches only that application: the fast path
        // must defer to the pattern match.
        let head = Symbol::Struct(StructId::from(1));
        let catalog = catalog_with_row(
            head,
            Conformance {
                self_args: vec![Ty::Nominal(Symbol::Int, vec![])],
                ..Conformance::new(head, ProtocolRef::bare(Symbol::CheapClone))
            },
        );
        assert!(catalog.cheap_clone_rows(head, &[Ty::Nominal(Symbol::Int, vec![])]));
        assert!(!catalog.cheap_clone_rows(head, &[Ty::Nominal(Symbol::String, vec![])]));
    }
}
