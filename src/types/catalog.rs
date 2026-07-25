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

const MAX_MARKER_PROOF_DEPTH: usize = 64;

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
    /// Exclusive-borrow parameter count of the declared signature
    /// (receiver included). The declaration fixes the writeback shape
    /// every implementation must follow: each such parameter comes back
    /// appended to the result tuple.
    #[serde(default)]
    pub writeback_width: usize,
    /// Declared `mut func`: the receiver parameter is an exclusive
    /// borrow, so every implementation returns `(result, final self)`
    /// for the caller's writeback.
    #[serde(default)]
    pub mut_receiver: bool,
}

/// The declaration context whose rigid parameters range over a member
/// body (ADR 0038): check-mode compilation binds them the way a
/// concrete receiver's instantiation (or a conformance's selected
/// application) would.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum OwnerBinding {
    /// A nominal's method, static, or initializer — or an inherent
    /// extend member, whose binders are the extend row's own rigid
    /// parameters rather than the nominal's.
    Nominal { params: Vec<Symbol> },
    /// A protocol requirement's default body: `Self` and the protocol's
    /// input parameters bind rigidly.
    Protocol(Symbol),
}

/// The structural implementation the checker derives when a conformance
/// has no source body — keyed by well-known protocol identity, never by
/// requirement name. Lowering synthesizes the corresponding glue.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum DerivedRecipe {
    /// `Name(field: value…)` / `Name.variant(payloads…)` rendering.
    Show,
    /// Component-wise equality.
    Equality,
}

/// One committed dictionary entry (ADR 0038): how a conformance
/// implements one protocol requirement, decided at typing. Entries sit
/// in protocol requirement declaration order — the witness-table slot
/// order after the two fixed ownership slots.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum DictionaryEntry {
    /// A callable implements the requirement: the row's declared
    /// witness, or the protocol's default body.
    Implementation {
        symbol: Symbol,
        /// Copied from the declared requirement; see
        /// [`Requirement::writeback_width`].
        writeback_width: usize,
    },
    /// The checker derived the implementation structurally.
    Derived(DerivedRecipe),
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
    /// The committed dictionary (ADR 0038): one entry per protocol
    /// requirement in declaration order, completed by
    /// [`TypeCatalog::commit_dictionaries`] once collection is done.
    #[serde(default)]
    pub dictionary: Vec<DictionaryEntry>,
    /// Materialized by `synthesize_derived_conformances` rather than
    /// declared. Compile-local: stripped from module exports (each
    /// downstream compile re-synthesizes against its own merged view),
    /// and evicted whenever a declared row for the same head and
    /// protocol arrives (retroactive extends win).
    #[serde(default)]
    pub synthesized: bool,
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
            dictionary: vec![],
            synthesized: false,
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
    /// Committed Deinit dictionary (ADR 0038): family head → its Deinit
    /// rows (disjoint by the overlap rules; usually one). A derived
    /// index — rebuilt after merge — so drop sites dereference committed
    /// rows instead of running a conformance search at teardown. A
    /// conditional row is evidence only where its context holds
    /// (ADR 0036), verified per application at dereference — the
    /// sanctioned specialization-time selection. Typing rejects
    /// protocol-head Deinit rows, which cannot commit per family.
    #[serde(default)]
    pub deinit_rows: FxHashMap<Symbol, Vec<ConformanceId>>,
    /// Member symbol → its owner's rigid binding context (ADR 0038). A
    /// derived index over the member tables, committed after collection
    /// and rebuilt after merge, so consumers never scan the catalogs
    /// per query.
    #[serde(default)]
    pub callable_owners: FxHashMap<Symbol, OwnerBinding>,
    /// Inherent extend members by type head. Each label holds every
    /// registered instance row (ADR 0036): disjoint heads may define the
    /// same label; overlapping heads are rejected at collection.
    pub extend_members: FxHashMap<Symbol, IndexMap<String, Vec<InherentMember>>>,
    /// Effect operation signatures.
    pub effects: FxHashMap<Symbol, EffectSig>,
    /// Transparent type aliases exported through the catalog for imports.
    #[serde(default)]
    pub type_aliases: FxHashMap<Symbol, TypeAliasInfo>,
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
            for member in members.values_mut().flatten() {
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

    /// Whether a value of this type may be implicitly duplicated by a
    /// retain at a value boundary (implicit sharing's clone-at-boundary
    /// rule). Linearity and uniqueness are the only refusals — they exist
    /// precisely to forbid duplication. Rigid parameters and unsolved
    /// variables answer false here; their proof goes through bounds.
    pub fn implicitly_duplicable(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Unique(_) => false,
            Ty::Borrow(_, inner) => self.implicitly_duplicable(inner),
            Ty::Nominal(symbol, args) => {
                self.grade_of(*symbol) != Grade::Linear
                    && args
                        .iter()
                        .filter(|arg| !matches!(arg, Ty::Eff(_) | Ty::Static(_)))
                        .all(|arg| self.implicitly_duplicable(arg))
            }
            Ty::Tuple(items) => items.iter().all(|item| self.implicitly_duplicable(item)),
            Ty::Record(row) => row
                .fields
                .iter()
                .all(|(_, field)| self.implicitly_duplicable(field)),
            Ty::Func(..) | Ty::Any { .. } => true,
            _ => false,
        }
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
        // Head-only grading is a family fact: a specialized or conditional
        // Copy row (ADR 0036) is evidence only for matching applications and
        // must not grade the whole nominal. Callers holding a complete
        // application use `grade_of_application`.
        if self.family_unconditionally_conforms(symbol, Symbol::Copy) {
            return Grade::Copy;
        }
        Grade::Affine
    }

    /// [`Self::grade_of`] for a complete application: specialized and
    /// conditional Copy rows apply exactly where they match and their
    /// context holds.
    pub fn grade_of_application(&self, symbol: Symbol, args: &[Ty]) -> Grade {
        let head_grade = self.grade_of(symbol);
        if head_grade != Grade::Affine {
            return head_grade;
        }
        let ty = Ty::Nominal(symbol, args.to_vec());
        if self.ty_satisfies_marker(&ty, Symbol::Copy, &[]) {
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

    /// The copy-out-of-borrow POSSIBILITY judgment: whether any application
    /// of this head could accept a borrowed value in an owned slot (Copy
    /// grade, or any declared Copy/CheapClone row — conditional and
    /// specialized rows included). Deliberately an over-approximation: it
    /// only preserves the `Apply` reason while types are still resolving;
    /// the actual coercion is proven per application
    /// ([`Self::coerce_kind_application`]) in the solver.
    pub fn copies_out_of_borrow(&self, symbol: Symbol) -> bool {
        self.grade_of(symbol) == Grade::Copy
            || self.has_bare_conformance(symbol, Symbol::Copy)
            || self.has_bare_conformance(symbol, Symbol::CheapClone)
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
        // Same family rule as `grade_of`: specialized/conditional CheapClone
        // rows never speak for the whole nominal at head level.
        if self.family_unconditionally_conforms(symbol, Symbol::CheapClone) {
            return Some(CoerceKind::CheapClone);
        }
        None
    }

    /// [`Self::coerce_kind`] for a complete application.
    pub fn coerce_kind_application(&self, symbol: Symbol, args: &[Ty]) -> Option<CoerceKind> {
        if self.grade_of_application(symbol, args) == Grade::Copy {
            return Some(CoerceKind::Copy);
        }
        if self.cheap_clone_rows(symbol, args) {
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
        self.ty_satisfies_marker_at(ty, marker, ambient, &mut FxHashSet::default())
    }

    fn ty_satisfies_marker_at(
        &self,
        ty: &Ty,
        marker: Symbol,
        ambient: &[Predicate],
        active: &mut FxHashSet<(Ty, Symbol)>,
    ) -> bool {
        if active.len() >= MAX_MARKER_PROOF_DEPTH {
            return false;
        }

        let goal = (ty.clone(), marker);
        if !active.insert(goal.clone()) {
            return false;
        }

        let satisfied = self.ty_satisfies_marker_inner(ty, marker, ambient, active);
        active.remove(&goal);
        satisfied
    }

    fn ty_satisfies_marker_inner(
        &self,
        ty: &Ty,
        marker: Symbol,
        ambient: &[Predicate],
        active: &mut FxHashSet<(Ty, Symbol)>,
    ) -> bool {
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

                let copy = self
                    .matching_conformances(*symbol, args, &ProtocolRef::bare(Symbol::Copy))
                    .iter()
                    .any(|found| self.marker_context_satisfied_at(found, ambient, active));
                copy || (marker == Symbol::CheapClone
                    && self
                        .matching_conformances(
                            *symbol,
                            args,
                            &ProtocolRef::bare(Symbol::CheapClone),
                        )
                        .iter()
                        .any(|found| self.marker_context_satisfied_at(found, ambient, active)))
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
                .all(|item| self.ty_satisfies_marker_at(item, marker, ambient, active)),
            Ty::Record(row) => {
                row.tail.is_none()
                    && row.fields.iter().all(|(_, field)| {
                        self.ty_satisfies_marker_at(field, marker, ambient, active)
                    })
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
        self.marker_context_satisfied_at(found, ambient, &mut FxHashSet::default())
    }

    fn marker_context_satisfied_at(
        &self,
        found: &ConformanceMatch,
        ambient: &[Predicate],
        active: &mut FxHashSet<(Ty, Symbol)>,
    ) -> bool {
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
            self.ty_satisfies_marker_at(&bound, protocol.protocol, ambient, active)
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
                    Ty::Nominal(symbol, args)
                        if self.grade_of_application(*symbol, args) == Grade::Copy =>
                    {
                        inner
                    }
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

    /// Merge an imported module's catalog (Phase 0 of checking: the
    /// environment a group solves against).
    pub fn merge(&mut self, other: TypeCatalog) {
        self.structs.extend(other.structs);
        self.enums.extend(other.enums);
        self.protocols.extend(other.protocols);
        // Rows are numbered per declaring module, so counters never
        // interact across catalogs.
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
            let ours = self.extend_members.entry(head).or_default();
            for (label, rows) in members {
                let target = ours.entry(label).or_default();
                for row in rows {
                    // The same declaration reaches a consumer through
                    // several import paths (core re-exported by every
                    // module); one row per member symbol. DISTINCT
                    // declarations from sibling modules stay separate and
                    // surface as use-site ambiguity when they overlap.
                    if !target.iter().any(|existing| existing.symbol == row.symbol) {
                        target.push(row);
                    }
                }
            }
        }
        self.effects.extend(other.effects);
        self.type_aliases.extend(other.type_aliases);
        // Row ids shift across the value-dedup above; the committed
        // Deinit index is derived, so rebuild it from the merged rows.
        self.commit_deinit_rows();
        // Rows can arrive before their protocol's info was in reach;
        // recommit dictionaries over the merged view (idempotent).
        self.commit_dictionaries();
        self.commit_callable_owners();
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

    pub fn insert_conformance(
        &mut self,
        module: ModuleId,
        conformance: Conformance,
    ) -> ConformanceId {
        // Absolute identity at mint (ADR 0038): rows are numbered under
        // their declaring module, so merged catalogs never collide and
        // no import seam respells ids.
        // A declared row supersedes a synthesized twin (retroactive
        // extends and REPL-session declarations arrive after synthesis).
        if !conformance.synthesized {
            let stale: Vec<ConformanceId> = self
                .conformances_for_head(conformance.head)
                .filter(|(_, row)| {
                    row.synthesized && row.protocol.protocol == conformance.protocol.protocol
                })
                .map(|(id, _)| id)
                .collect();
            for id in stale {
                self.conformances.shift_remove(&id);
                if let Some(ids) = self.conformances_by_head.get_mut(&conformance.head) {
                    ids.retain(|existing| *existing != id);
                }
            }
        }
        let id = ConformanceId::new(module, self.next_conformance_id);
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

    /// [`Self::matching_conformances`] restricted to rows whose substituted
    /// context is PROVEN for this application. This is the query for callers
    /// with no typing-time proof in hand (backend marker, ownership, and
    /// `Deinit` selection): a conditional row is evidence only where its
    /// context holds.
    /// Rebuild the committed Deinit index from the current rows
    /// (ADR 0038). Called after collection and after every merge.
    pub fn commit_deinit_rows(&mut self) {
        let mut rows: FxHashMap<Symbol, Vec<ConformanceId>> = FxHashMap::default();
        for (id, row) in &self.conformances {
            if row.protocol.protocol == Symbol::Deinit {
                rows.entry(row.head).or_default().push(*id);
            }
        }
        self.deinit_rows = rows;
    }

    /// The recipe behind a checker-derived conformance, keyed by
    /// well-known protocol identity — the one place that knows which
    /// protocols derive structurally.
    pub fn derived_recipe(protocol: Symbol) -> Option<DerivedRecipe> {
        match protocol {
            Symbol::Showable => Some(DerivedRecipe::Show),
            Symbol::Equatable => Some(DerivedRecipe::Equality),
            _ => None,
        }
    }

    /// Protocols auto-derived for structs and enums when no explicit
    /// conformance exists. The derived instance's context is structural:
    /// every field/payload must conform too.
    pub fn derivable_protocols() -> [Symbol; 2] {
        [Symbol::Showable, Symbol::Equatable]
    }

    /// Materialize derived conformances as ordinary conditional rows —
    /// the `derive`-generates-a-real-impl model. The structural judgment
    /// runs here once, over the complete catalog; every later consumer
    /// (constraint solving, context proving, dictionary dereference) sees
    /// plain rows and needs no derivation special case.
    ///
    /// A candidate head derives a protocol when every field or
    /// GADT-refined payload is admissible: a type parameter (the emitted
    /// context re-requires it per application), a nominal with a matching
    /// row whose context is admissible, or another surviving candidate —
    /// ground recursive knots (`Node` holding `[Node]`) resolve here,
    /// coinductively, in one fixed point instead of at every use. The
    /// emitted context carries predicates only for parameter-mentioning
    /// leaf types, so row solving stays inductive: no synthesized context
    /// reaches back to its own head.
    pub fn synthesize_derived_conformances(&mut self, module: ModuleId) {
        let heads: Vec<Symbol> = self
            .structs
            .keys()
            .copied()
            .chain(self.enums.keys().copied())
            .collect();
        let mut candidates: FxHashSet<(Symbol, Symbol)> = FxHashSet::default();
        for head in &heads {
            if self.is_heap(*head) {
                continue;
            }
            for protocol in Self::derivable_protocols() {
                let declared = self
                    .conformances_for_head(*head)
                    .any(|(_, row)| row.protocol.protocol == protocol);
                if !declared {
                    candidates.insert((*head, protocol));
                }
            }
        }
        loop {
            let survivors: FxHashSet<(Symbol, Symbol)> = candidates
                .iter()
                .copied()
                .filter(|(head, protocol)| {
                    self.derivation_admissible(*head, *protocol, &candidates)
                })
                .collect();
            if survivors.len() == candidates.len() {
                break;
            }
            candidates = survivors;
        }
        let mut rows: Vec<(Symbol, Symbol)> = candidates.into_iter().collect();
        rows.sort();
        // Merged catalogs carry rows minted by other compiles; never
        // reuse a (module, local) pair they already occupy.
        let ceiling = self
            .conformances
            .keys()
            .filter(|id| id.module_id == module)
            .map(|id| id.local_id + 1)
            .max()
            .unwrap_or(0);
        self.next_conformance_id = self.next_conformance_id.max(ceiling);
        for (head, protocol) in rows {
            if let Some(row) = self.synthesized_row(head, protocol) {
                self.insert_conformance(module, row);
            }
        }
    }

    /// Drop compile-local synthesized rows: module exports carry only
    /// declared conformances, and each importer re-synthesizes against
    /// its own merged view (so a downstream retroactive extend never
    /// collides with an upstream synthetic row).
    pub fn strip_synthesized_conformances(&mut self) {
        let stale: Vec<ConformanceId> = self
            .conformances
            .iter()
            .filter(|(_, row)| row.synthesized)
            .map(|(id, _)| *id)
            .collect();
        for id in &stale {
            if let Some(row) = self.conformances.shift_remove(id) {
                if let Some(ids) = self.conformances_by_head.get_mut(&row.head) {
                    ids.retain(|existing| existing != id);
                }
            }
        }
    }

    /// The declared type parameters and field/payload leaf types of a
    /// derivation candidate, at the generic level (payloads GADT-refined
    /// against the generic self; unrefinable variants contribute none).
    fn derivation_leaves(&self, head: Symbol) -> Option<(Vec<Symbol>, Vec<Ty>)> {
        if let Some(info) = self.structs.get(&head) {
            let params: Vec<Symbol> = info.params.iter().map(|param| param.symbol).collect();
            let leaves = info
                .fields
                .values()
                .map(|(_, field_ty)| field_ty.clone())
                .collect();
            return Some((params, leaves));
        }
        if let Some(info) = self.enums.get(&head) {
            let params: Vec<Symbol> = info.params.iter().map(|param| param.symbol).collect();
            let self_ty = Ty::Nominal(head, params.iter().map(|param| Ty::Param(*param)).collect());
            let mut leaves = Vec::new();
            for variant in info.variants.values() {
                let Some(instantiation) = variant
                    .instantiate(&FxHashMap::default(), &Default::default(), &Default::default())
                    .refined_by_result(&self_ty)
                else {
                    continue;
                };
                leaves.extend(instantiation.argument_types);
            }
            return Some((params, leaves));
        }
        None
    }

    fn derivation_admissible(
        &self,
        head: Symbol,
        protocol: Symbol,
        assumed: &FxHashSet<(Symbol, Symbol)>,
    ) -> bool {
        let Some((params, leaves)) = self.derivation_leaves(head) else {
            return false;
        };
        let self_ty = Ty::Nominal(head, params.iter().map(|param| Ty::Param(*param)).collect());
        if self.derived_protocol_ref(protocol, &self_ty).is_none() {
            return false;
        }
        leaves.iter().all(|leaf| {
            self.derived_protocol_ref(protocol, leaf)
                .is_some_and(|target| self.admissibly_conforms(leaf, &target, assumed, 0))
        })
    }

    /// Whether a leaf type conforms under the synthesis assumptions: a
    /// parameter is deferred to the row's context, a nominal resolves
    /// through matching rows (contexts checked recursively) or the
    /// surviving-candidate set. Conservative elsewhere, like the solver.
    fn admissibly_conforms(
        &self,
        ty: &Ty,
        target: &ProtocolRef,
        assumed: &FxHashSet<(Symbol, Symbol)>,
        depth: usize,
    ) -> bool {
        if depth > 64 {
            return false;
        }
        match ty {
            Ty::Borrow(_, inner) => self.admissibly_conforms(inner, target, assumed, depth),
            Ty::Param(_) => true,
            Ty::Nominal(head, args) => {
                if assumed.contains(&(*head, target.protocol)) {
                    return true;
                }
                if target.args.is_empty()
                    && target.protocol == Symbol::Copy
                    && self.intrinsic_copy(*head)
                {
                    return true;
                }
                self.matching_conformances(*head, args, target)
                    .into_iter()
                    .any(|matched| {
                        matched.conformance.context.iter().all(|predicate| {
                            let predicate = predicate.substitute(
                                &matched.substitution,
                                &FxHashMap::default(),
                                &FxHashMap::default(),
                            );
                            match &predicate {
                                Predicate::Conforms { ty, protocol } => {
                                    self.admissibly_conforms(ty, protocol, assumed, depth + 1)
                                }
                                Predicate::TypeEq(left, right) => left == right,
                                _ => false,
                            }
                        })
                    })
            }
            _ => false,
        }
    }

    /// Build one synthesized row: generic self pattern, context predicates
    /// for the parameter-mentioning leaves (a self-recursive generic leaf
    /// decomposes to bare parameter predicates so the context never
    /// mentions its own head), no witnesses — `commit_dictionaries` fills
    /// the dictionary with the structural recipe.
    fn synthesized_row(&self, head: Symbol, protocol: Symbol) -> Option<Conformance> {
        let (params, leaves) = self.derivation_leaves(head)?;
        let self_args: Vec<Ty> = params.iter().map(|param| Ty::Param(*param)).collect();
        let self_ty = Ty::Nominal(head, self_args.clone());
        let target = self.derived_protocol_ref(protocol, &self_ty)?;
        fn mentions(ty: &Ty, of: &dyn Fn(&Ty) -> bool) -> bool {
            if of(ty) {
                return true;
            }
            match ty {
                Ty::Borrow(_, inner) => mentions(inner, of),
                Ty::Nominal(_, args) => args.iter().any(|arg| mentions(arg, of)),
                Ty::Tuple(items) => items.iter().any(|item| mentions(item, of)),
                _ => false,
            }
        }
        let mut context: Vec<Predicate> = Vec::new();
        let push = |predicate: Predicate, context: &mut Vec<Predicate>| {
            if !context.contains(&predicate) {
                context.push(predicate);
            }
        };
        for leaf in &leaves {
            let mentions_param =
                mentions(leaf, &|ty| matches!(ty, Ty::Param(param) if params.contains(param)));
            if !mentions_param {
                continue;
            }
            let mentions_own_head =
                mentions(leaf, &|ty| matches!(ty, Ty::Nominal(h, _) if *h == head));
            if mentions_own_head {
                for param in &params {
                    if mentions(leaf, &|ty| matches!(ty, Ty::Param(p) if p == param)) {
                        let param_ty = Ty::Param(*param);
                        if let Some(target) = self.derived_protocol_ref(protocol, &param_ty) {
                            push(
                                Predicate::Conforms {
                                    ty: param_ty,
                                    protocol: target,
                                },
                                &mut context,
                            );
                        }
                    }
                }
            } else if let Some(target) = self.derived_protocol_ref(protocol, leaf) {
                push(
                    Predicate::Conforms {
                        ty: leaf.clone(),
                        protocol: target,
                    },
                    &mut context,
                );
            }
        }
        Some(Conformance {
            params,
            self_args,
            context,
            synthesized: true,
            ..Conformance::new(head, target)
        })
    }

    /// Complete every conformance row's dictionary (ADR 0038): one entry
    /// per protocol requirement in declaration order — the declared
    /// witness, the structural recipe for a derivable protocol's bodyless
    /// requirement, or the protocol's default body. Runs once collection
    /// is done and again after merge (idempotent).
    pub fn commit_dictionaries(&mut self) {
        let mut dictionaries: Vec<(ConformanceId, Vec<DictionaryEntry>)> = Vec::new();
        for (id, row) in &self.conformances {
            let Some(info) = self.protocols.get(&row.protocol.protocol) else {
                continue;
            };
            let recipe = Self::derived_recipe(row.protocol.protocol);
            let entries = info
                .requirements
                .iter()
                .map(|(label, requirement)| match row.witnesses.get(label) {
                    Some(witness) => DictionaryEntry::Implementation {
                        symbol: *witness,
                        writeback_width: requirement.writeback_width,
                    },
                    None => match recipe {
                        Some(recipe) if !requirement.has_default => {
                            DictionaryEntry::Derived(recipe)
                        }
                        _ => DictionaryEntry::Implementation {
                            symbol: requirement.symbol,
                            writeback_width: requirement.writeback_width,
                        },
                    },
                })
                .collect();
            dictionaries.push((*id, entries));
        }
        for (id, entries) in dictionaries {
            if let Some(row) = self.conformances.get_mut(&id) {
                row.dictionary = entries;
            }
        }
    }

    /// Commit the owner-binding index (ADR 0038): every member symbol
    /// maps to the declaration context whose rigid parameters range
    /// over its body. A derived index over the member tables — one
    /// derivation, rebuilt after merge.
    pub fn commit_callable_owners(&mut self) {
        let mut owners = FxHashMap::default();
        for info in self.structs.values() {
            let params: Vec<Symbol> = info.params.iter().map(|param| param.symbol).collect();
            for symbol in info
                .methods
                .values()
                .chain(info.statics.values())
                .copied()
                .chain(info.inits.iter().map(|(init, _)| *init))
            {
                owners.insert(
                    symbol,
                    OwnerBinding::Nominal {
                        params: params.clone(),
                    },
                );
            }
        }
        for info in self.enums.values() {
            let params: Vec<Symbol> = info.params.iter().map(|param| param.symbol).collect();
            for symbol in info.methods.values().copied() {
                owners.insert(
                    symbol,
                    OwnerBinding::Nominal {
                        params: params.clone(),
                    },
                );
            }
        }
        // Inherent extend members carry their own rigid params (the
        // instance-head binders).
        for members in self.extend_members.values() {
            for rows in members.values() {
                for row in rows {
                    owners.insert(
                        row.symbol,
                        OwnerBinding::Nominal {
                            params: row.params.clone(),
                        },
                    );
                }
            }
        }
        for (protocol, info) in &self.protocols {
            for requirement in info.requirements.values() {
                owners.insert(requirement.symbol, OwnerBinding::Protocol(*protocol));
            }
        }
        self.callable_owners = owners;
    }

    /// Dereference a committed conformance row for a concrete
    /// application (ADR 0038): match that single row — no search across
    /// rows, no overlap arbitration. A conditional row's context is
    /// verified against this application (evidence only where it holds,
    /// ADR 0036) — the sanctioned specialization-time check, since a
    /// where-clause over a rigid parameter is abstract until the
    /// instance is concrete.
    pub fn committed_conformance(
        &self,
        id: ConformanceId,
        head: Symbol,
        self_args: &[Ty],
    ) -> Option<ConformanceMatch<'_>> {
        let row = self.conformances.get(&id)?;
        let self_ty = Ty::Nominal(head, self_args.to_vec());
        let target = row.protocol.clone();
        self.match_conformance_row(id, row, Some((head, self_args)), &self_ty, &target)
            .filter(|matched| self.row_context_holds(matched, 0))
    }

    pub fn satisfied_conformances<'a>(
        &'a self,
        head: Symbol,
        self_args: &[Ty],
        target: &ProtocolRef,
    ) -> Vec<ConformanceMatch<'a>> {
        self.matching_conformances(head, self_args, target)
            .into_iter()
            .filter(|matched| self.row_context_holds(matched, 0))
            .collect()
    }

    fn row_context_holds(&self, matched: &ConformanceMatch, depth: usize) -> bool {
        matched.conformance.context.iter().all(|predicate| {
            let predicate = predicate.substitute(
                &matched.substitution,
                &FxHashMap::default(),
                &FxHashMap::default(),
            );
            self.predicate_holds(&predicate, depth)
        })
    }

    /// Whether a fully substituted predicate provably holds. Conservative:
    /// unprovable forms are false, so a conditional row is simply not
    /// selected. The depth guard breaks pathological row cycles; derived
    /// conformances are ordinary synthesized rows whose contexts never
    /// mention their own head, so no coinduction is needed here.
    fn predicate_holds(&self, predicate: &Predicate, depth: usize) -> bool {
        if depth > 64 {
            return false;
        }
        match predicate {
            Predicate::Conforms { ty, protocol } => self.ty_conforms_at(ty, protocol, depth + 1),
            Predicate::TypeEq(left, right) => left == right,
            _ => false,
        }
    }

    /// Whether a concrete (or bounds-carrying rigid) type provably conforms.
    pub fn ty_conforms(&self, ty: &Ty, target: &ProtocolRef) -> bool {
        self.ty_conforms_at(ty, target, 0)
    }

    fn ty_conforms_at(&self, ty: &Ty, target: &ProtocolRef, depth: usize) -> bool {
        if depth > 64 {
            return false;
        }
        match ty {
            Ty::Borrow(_, inner) => self.ty_conforms_at(inner, target, depth),
            Ty::Nominal(head, args) => {
                if target.args.is_empty()
                    && target.protocol == Symbol::Copy
                    && self.intrinsic_copy(*head)
                {
                    return true;
                }
                self.matching_conformances(*head, args, target)
                    .into_iter()
                    .any(|matched| self.row_context_holds(&matched, depth))
            }
            Ty::Param(param) => self
                .param_bounds
                .get(param)
                .is_some_and(|bounds| self.bounds_satisfy(bounds, target)),
            _ => false,
        }
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
/// Two inherent instance rows overlap when some fully instantiated
/// application matches both self patterns — the same bidirectional rule
/// conformance rows use.
pub fn inherent_rows_overlap(left: &[Ty], right: &[Ty]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut forward = FxHashMap::default();
    let forward_matches = left
        .iter()
        .zip(right)
        .all(|(left, right)| match_pattern(left, right, &mut forward));
    let mut reverse = FxHashMap::default();
    let reverse_matches = left
        .iter()
        .zip(right)
        .all(|(left, right)| match_pattern(right, left, &mut reverse));
    forward_matches && reverse_matches
}

pub(crate) fn unconditional_self_pattern(row: &Conformance) -> bool {
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
        catalog.insert_conformance(ModuleId::Current, row);
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
    fn cyclic_marker_context_fails_closed() {
        let head = Symbol::Struct(StructId::from(1));
        let catalog = catalog_with_row(
            head,
            Conformance {
                context: vec![Predicate::Conforms {
                    ty: Ty::Nominal(head, vec![]),
                    protocol: ProtocolRef::bare(Symbol::CheapClone),
                }],
                ..Conformance::new(head, ProtocolRef::bare(Symbol::CheapClone))
            },
        );

        assert!(!catalog.cheap_clone_rows(head, &[]));
    }

    #[test]
    fn type_growing_marker_context_hits_the_proof_limit() {
        let head = Symbol::Struct(StructId::from(1));
        let param = Symbol::DeclaredLocal(DeclaredLocalId(10));
        let catalog = catalog_with_row(
            head,
            Conformance {
                params: vec![param],
                self_args: vec![Ty::Param(param)],
                context: vec![Predicate::Conforms {
                    ty: Ty::Nominal(head, vec![Ty::Nominal(head, vec![Ty::Param(param)])]),
                    protocol: ProtocolRef::bare(Symbol::CheapClone),
                }],
                ..Conformance::new(head, ProtocolRef::bare(Symbol::CheapClone))
            },
        );

        assert!(!catalog.cheap_clone_rows(head, &[Ty::Nominal(Symbol::Int, vec![])]));
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
