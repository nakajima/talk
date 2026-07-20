//! Type representation for the Talk type system.
//!
//! Schemes are qualified types `forall params. predicates => type`:
//! `Scheme.predicates` is the context P from Jones, *A Theory of Qualified
//! Types* (ESOP 1992; revised SCP version). Quantified
//! variables are rigid `Ty::Param(Symbol)`s; first-class rigids keep GADT
//! given-equalities out of the union-find entirely.
//!
//! Records are row types in the scoped-labels style (Leijen, *Extensible
//! Records with Scoped Labels*, TFP 2005) with Talk choosing no lacks
//! predicates. Effect rows follow Leijen, *Koka: Programming with
//! Row-Polymorphic Effect Types* (MSR-TR-2013-79): entries carry the
//! effect label plus its instantiation arguments (duplicates allowed and
//! inert — see docs/generic-effects-plan.md); an effect's operation
//! signature lives in the catalog, never in the row.

use std::ops::ControlFlow;

use rustc_hash::FxHashMap;

use crate::label::Label;
use crate::name_resolution::symbol::Symbol;

/// A type unification variable: an index into the solver's `VarStore`.
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub struct TyVar(pub u32);

/// A record-row unification variable.
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub struct RowVar(pub u32);

/// An effect-row unification variable.
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub struct EffVar(pub u32);

/// The tail of an open record row: either still being solved, or a rigid
/// quantified row parameter.
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum RowTail {
    Var(RowVar),
    Param(Symbol),
}

/// The tail of an open effect row.
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum EffTail {
    Var(EffVar),
    Param(Symbol),
}

/// A borrow-permission unification variable.
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub struct PermVar(pub u32);

/// The permission of a borrow, over the two-point lattice {Shared,
/// Exclusive}: either concrete, still being solved, or a rigid quantified
/// permission parameter (grade polymorphism, so one accessor can serve `&`
/// and `&mut` call sites alike).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum Perm {
    Shared,
    Exclusive,
    Var(PermVar),
    Param(Symbol),
}

impl Perm {
    /// Whether this permission grants write access. Only meaningful on
    /// concrete permissions; defaulting binds every leftover perm var to
    /// `Shared` before anything downstream of the type phase runs.
    pub fn is_exclusive(self) -> bool {
        matches!(self, Perm::Exclusive)
    }
}

/// A record row: sorted labeled fields plus an optional tail.
/// `tail: None` means the row is closed (exactly these fields).
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct Row {
    pub fields: Vec<(Label, Ty)>,
    pub tail: Option<RowTail>,
}

impl Row {
    pub fn closed(mut fields: Vec<(Label, Ty)>) -> Self {
        fields.sort_by(|(a, _), (b, _)| a.cmp(b));
        Row { fields, tail: None }
    }

    /// Visit every type contained in this row's fields. Row-tail symbols are
    /// not `Ty` nodes; callers that care about row params should inspect
    /// `tail` directly after this traversal.
    pub fn try_visit<B>(&self, visitor: &mut impl FnMut(&Ty) -> ControlFlow<B>) -> ControlFlow<B> {
        for (_, ty) in &self.fields {
            ty.try_visit(visitor)?;
        }
        ControlFlow::Continue(())
    }

    /// Walk two rows in lockstep, visiting corresponding field types. Row-tail
    /// symbols are not `Ty` nodes; callers that care about row params should
    /// compare `tail` directly. Returns `false` if field labels or arity differ
    /// or if the visitor rejects a corresponding type pair.
    pub fn try_zip(&self, other: &Row, visitor: &mut impl FnMut(&Ty, &Ty) -> bool) -> bool {
        self.fields.len() == other.fields.len()
            && self.fields.iter().zip(&other.fields).all(
                |((left_label, left_ty), (right_label, right_ty))| {
                    left_label == right_label && left_ty.try_zip(right_ty, visitor)
                },
            )
    }
}

/// One effect occurrence in a row: its label plus the type arguments of
/// this occurrence (`'state<Int>`; empty for non-generic effects).
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct EffectEntry {
    pub effect: Symbol,
    pub args: Vec<Ty>,
}

impl EffectEntry {
    pub fn label(effect: Symbol) -> Self {
        EffectEntry {
            effect,
            args: vec![],
        }
    }
}

/// An effect row: effect entries plus an optional tail. Operation
/// signatures live in the catalog, not here. Duplicate labels are allowed
/// — the same effect may occur at several instantiations — and unification
/// pairs same-label occurrences in order (scoped labels: Leijen, TFP 2005;
/// Koka's effect rows). Entries are kept stable-sorted by label, the
/// canonical form Eq/Hash rely on; relative order within a label is
/// occurrence order.
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct EffectRow {
    pub effects: Vec<EffectEntry>,
    pub tail: Option<EffTail>,
}

impl EffectRow {
    /// The canonical constructor: stable-sorts entries by label.
    pub fn new(mut effects: Vec<EffectEntry>, tail: Option<EffTail>) -> Self {
        effects.sort_by_key(|entry| entry.effect);
        EffectRow { effects, tail }
    }

    /// The pure, closed row `<>`.
    pub fn pure() -> Self {
        EffectRow {
            effects: vec![],
            tail: None,
        }
    }

    /// An empty open row `<|e>` — the usual state of a function under
    /// inference, so its effects can still grow.
    pub fn open(tail: EffVar) -> Self {
        EffectRow {
            effects: vec![],
            tail: Some(EffTail::Var(tail)),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct ProtocolRef {
    pub protocol: Symbol,
    pub args: Vec<Ty>,
}

impl std::fmt::Display for ProtocolRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", render_protocol_ref(self, &FxHashMap::default()))
    }
}

impl ProtocolRef {
    pub fn bare(protocol: Symbol) -> Self {
        Self {
            protocol,
            args: vec![],
        }
    }

    pub fn has_unification_vars(&self) -> bool {
        self.args.iter().any(Ty::has_unification_vars)
    }

    pub fn substitute(
        &self,
        tys: &FxHashMap<Symbol, Ty>,
        effs: &FxHashMap<Symbol, EffTail>,
        rows: &FxHashMap<Symbol, RowTail>,
    ) -> Self {
        Self {
            protocol: self.protocol,
            args: self
                .args
                .iter()
                .map(|arg| arg.substitute(tys, effs, rows))
                .collect(),
        }
    }

    pub fn import_symbols(&self, target: crate::compiling::module::ModuleId) -> Self {
        Self {
            protocol: import_symbol(self.protocol, target),
            args: self
                .args
                .iter()
                .map(|arg| arg.import_symbols(target))
                .collect(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum Ty {
    /// A unification variable, owned by the solver's VarStore.
    Var(TyVar),
    /// A rigid type parameter (user-declared generic or checker-minted
    /// implicit generic; also associated types).
    Param(Symbol),
    /// A nominal type application: structs, enums, builtins.
    /// `Int` is `Nominal(Symbol::Int, [])`.
    Nominal(Symbol, Vec<Ty>),
    /// A borrowed view of another type. Flow checking owns the lifetime
    /// facts; the type records the access permission.
    Borrow(Perm, Box<Ty>),
    /// A uniquely-owned value: statically the sole reference, so in-place
    /// mutation needs no runtime checks. An owned value moves into `*T` at
    /// a call boundary (the move makes it unique).
    Unique(Box<Ty>),
    /// A function type with its latent effect row.
    Func(Vec<Ty>, Box<Ty>, EffectRow),
    Tuple(Vec<Ty>),
    Record(Row),
    /// A first-class protocol existential `any P<Assoc = T>`. This is an
    /// existential package in the Mitchell/Plotkin sense: hidden payload type,
    /// protocol evidence, and associated-type equality evidence. The vector is
    /// canonicalized by associated-type symbol.
    Any {
        protocol: ProtocolRef,
        assoc: Vec<(Symbol, Ty)>,
    },
    /// An associated-type projection `base.Assoc` through a protocol — an
    /// associated type synonym application (Chakravarty, Keller & Peyton
    /// Jones, *Associated Type Synonyms*, ICFP 2005; `<T as Trait>::Assoc`
    /// in Rust terms). The solver normalizes it through the conformance
    /// table once `base`'s head is concrete; over a rigid base it is
    /// irreducible and equal only to itself (projections are NOT injective —
    /// OutsideIn(X) treats type functions as free symbols).
    Proj(Box<Ty>, ProtocolRef, Symbol),
    /// An effect row in type-argument position — a kind-restricted
    /// argument on `Ty::Nominal` (Koka-style E-kinded type argument).
    /// Carries a struct instance's closure-field effect rows in its type,
    /// so construction pins them and member reads recover them. Never a
    /// value's type; appears only inside a Nominal's argument list (and
    /// substitution payloads).
    Eff(EffectRow),
    /// A static value in generic-argument position (ADR 0035) — the second
    /// kind-restricted argument alongside `Ty::Eff`. Never a value's type;
    /// appears only where a declared `static` parameter is being supplied.
    /// Integer content is kept in canonical affine form so `N + 1` and
    /// `1 + N` are one type; a bare parameter or metavariable is NOT
    /// wrapped here — it stays `Ty::Param`/`Ty::Var` (the canonical
    /// collapse in [`StaticInt::into_ty`]), so arithmetic-free programs
    /// ride the ordinary generic machinery.
    Static(StaticValue),
    /// Poison type for error recovery: equalities involving it succeed
    /// silently so one mistake doesn't cascade.
    Error,
}

/// A static generic argument's canonical content (ADR 0035). The initial
/// static domain is nonnegative `Int`, `Bool`, and fieldless enum cases;
/// only the integer domain has arithmetic.
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum StaticValue {
    /// A canonical affine integer index. Follows the restricted-index
    /// tradition (Xi & Pfenning, *Dependent Types in Practical
    /// Programming*, POPL 1999): a decidable arithmetic domain separate
    /// from ordinary expressions.
    Int(StaticInt),
    Bool(bool),
    /// A case of a fieldless enum: the owning enum (carried for
    /// source-oriented rendering, `Color.red`) and the variant.
    Case(Symbol, Symbol),
}

/// One symbolic unknown inside an affine index: a rigid static parameter
/// or a solver metavariable minted at instantiation.
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub enum StaticAtom {
    Param(Symbol),
    Var(TyVar),
}

impl StaticAtom {
    pub(crate) fn as_ty(&self) -> Ty {
        match self {
            StaticAtom::Param(symbol) => Ty::Param(*symbol),
            StaticAtom::Var(var) => Ty::Var(*var),
        }
    }
}

/// An affine integer index in canonical form: `constant + Σ coeff·atom`,
/// terms sorted by atom with no zero coefficients. Arithmetic is over the
/// mathematical integers (ADR 0035 §3: normalization cannot overflow); a
/// concrete result is validated against the signed 64-bit `Int` range
/// only once it becomes a closed generic argument.
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct StaticInt {
    pub constant: num_bigint::BigInt,
    pub terms: Vec<(StaticAtom, num_bigint::BigInt)>,
}

impl StaticInt {
    pub fn constant(value: impl Into<num_bigint::BigInt>) -> StaticInt {
        StaticInt {
            constant: value.into(),
            terms: vec![],
        }
    }

    pub fn atom(atom: StaticAtom) -> StaticInt {
        StaticInt {
            constant: 0.into(),
            terms: vec![(atom, 1.into())],
        }
    }

    /// Read a type as an affine index: a bare param/var is a single-term
    /// form, `Ty::Static(Int)` is itself. Anything else has the wrong kind.
    pub fn from_ty(ty: &Ty) -> Option<StaticInt> {
        match ty {
            Ty::Param(symbol) => Some(StaticInt::atom(StaticAtom::Param(*symbol))),
            Ty::Var(var) => Some(StaticInt::atom(StaticAtom::Var(*var))),
            Ty::Static(StaticValue::Int(int)) => Some(int.clone()),
            _ => None,
        }
    }

    /// The canonical type for this index: a closed form or genuine affine
    /// content stays `Ty::Static`; `0 + 1·atom` collapses to the bare
    /// `Ty::Param`/`Ty::Var` so arithmetic-free arguments are ordinary
    /// generic arguments.
    pub fn into_ty(self) -> Ty {
        if self.constant == 0.into()
            && let [(atom, coeff)] = self.terms.as_slice()
            && *coeff == 1.into()
        {
            return atom.as_ty();
        }
        Ty::Static(StaticValue::Int(self))
    }

    pub fn as_constant(&self) -> Option<&num_bigint::BigInt> {
        self.terms.is_empty().then_some(&self.constant)
    }

    /// The closed value when it fits Talk's signed 64-bit `Int`.
    pub fn as_i64(&self) -> Option<i64> {
        i64::try_from(self.as_constant()?.clone()).ok()
    }

    pub fn is_zero(&self) -> bool {
        self.terms.is_empty() && self.constant == 0.into()
    }

    pub fn add(&self, other: &StaticInt) -> StaticInt {
        let constant = &self.constant + &other.constant;
        let mut terms: FxHashMap<StaticAtom, num_bigint::BigInt> = FxHashMap::default();
        for (atom, coeff) in self.terms.iter().chain(&other.terms) {
            *terms.entry(*atom).or_insert_with(|| 0.into()) += coeff;
        }
        let mut terms: Vec<(StaticAtom, num_bigint::BigInt)> = terms
            .into_iter()
            .filter(|(_, coeff)| *coeff != 0.into())
            .collect();
        terms.sort_by_key(|(atom, _)| *atom);
        StaticInt { constant, terms }
    }

    pub fn sub(&self, other: &StaticInt) -> StaticInt {
        self.add(&other.scale(&(-1).into()))
    }

    pub fn scale(&self, factor: &num_bigint::BigInt) -> StaticInt {
        if *factor == 0.into() {
            return StaticInt::constant(0);
        }
        StaticInt {
            constant: &self.constant * factor,
            terms: self
                .terms
                .iter()
                .map(|(atom, coeff)| (*atom, coeff * factor))
                .collect(),
        }
    }

    /// Divide every coefficient by `divisor`, only when exact — the
    /// integer-domain guard on equation solving.
    pub fn div_exact(&self, divisor: &num_bigint::BigInt) -> Option<StaticInt> {
        let zero = num_bigint::BigInt::from(0);
        if *divisor == zero || &self.constant % divisor != zero {
            return None;
        }
        let terms = self
            .terms
            .iter()
            .map(|(atom, coeff)| (coeff % divisor == zero).then(|| (*atom, coeff / divisor)))
            .collect::<Option<Vec<_>>>()?;
        Some(StaticInt {
            constant: &self.constant / divisor,
            terms,
        })
    }
}

/// One logical predicate in the checker's constraint domain. Jones's
/// qualified types use predicates to restrict type-scheme quantification;
/// OutsideIn(X) separates origin-free facts from the originated wanteds/givens
/// that carry blame. This enum is the shared fact language for schemes,
/// declaration contexts, solver givens, and GADT refinements.
///
/// Research anchors: Jones, *A Theory of Qualified Types*;
/// Vytiniotis/Peyton Jones/Schrijvers/Sulzmann, *OutsideIn(X)*;
/// Wadler/Blott type classes; Chakravarty/Keller/Peyton Jones associated
/// type synonyms; Gaster/Jones extensible-record predicates; and Leijen row
/// polymorphism for records/effects.
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum Predicate {
    /// Same-type constraint. Associated-type applications lower to `Ty::Proj`
    /// plus this equality, following Chakravarty/Keller/Peyton Jones.
    TypeEq(Ty, Ty),
    /// Same-effect-row constraint; part of the internal predicate language so
    /// Koka-style effect polymorphism does not need a separate architecture.
    EffectEq(EffectRow, EffectRow),
    /// Same-record-row constraint for row-polymorphic records.
    RowEq(Row, Row),
    /// Protocol conformance as a class predicate in the Wadler/Blott sense.
    /// Associated types are projections plus `TypeEq`, not payloads here.
    Conforms { ty: Ty, protocol: ProtocolRef },
    /// A member-access predicate carried by schemes when the receiver head is
    /// not yet known; the record-predicate lineage is Gaster/Jones.
    HasMember {
        receiver: Ty,
        label: Label,
        member: Ty,
    },
    /// A static integer relation (ADR 0035): equality or ordering over
    /// static-Int-kinded operands (canonical affine forms, bare static
    /// params, or metavariables). Entailment is quantifier-free linear
    /// integer arithmetic in the Xi/Pfenning restricted-index tradition;
    /// evidence erases.
    StaticCmp { op: StaticCmpOp, lhs: Ty, rhs: Ty },
}

/// The relations of the static integer theory (ADR 0035 §4).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum StaticCmpOp {
    Eq,
    Lt,
    Le,
}

impl StaticCmpOp {
    pub fn as_str(&self) -> &'static str {
        match self {
            StaticCmpOp::Eq => "==",
            StaticCmpOp::Lt => "<",
            StaticCmpOp::Le => "<=",
        }
    }
}

impl Predicate {
    /// Visit every type contained in this predicate. Effect-row tails and
    /// row-tail symbols are not `Ty` nodes; callers that care about those
    /// params should inspect those structures directly.
    pub fn try_visit<B>(&self, visitor: &mut impl FnMut(&Ty) -> ControlFlow<B>) -> ControlFlow<B> {
        match self {
            Predicate::TypeEq(lhs, rhs) => {
                lhs.try_visit(visitor)?;
                rhs.try_visit(visitor)?;
            }
            Predicate::RowEq(lhs, rhs) => {
                lhs.try_visit(visitor)?;
                rhs.try_visit(visitor)?;
            }
            Predicate::Conforms { ty, protocol } => {
                ty.try_visit(visitor)?;
                for arg in &protocol.args {
                    arg.try_visit(visitor)?;
                }
            }
            Predicate::HasMember {
                receiver, member, ..
            } => {
                receiver.try_visit(visitor)?;
                member.try_visit(visitor)?;
            }
            Predicate::StaticCmp { lhs, rhs, .. } => {
                lhs.try_visit(visitor)?;
                rhs.try_visit(visitor)?;
            }
            Predicate::EffectEq(..) => {}
        }
        ControlFlow::Continue(())
    }
}

impl Ty {
    pub fn unit() -> Ty {
        Ty::Nominal(Symbol::Void, vec![])
    }

    pub fn is_never(&self) -> bool {
        matches!(self, Ty::Nominal(sym, _) if *sym == Symbol::Never)
    }

    /// Preorder traversal over this type and every nested type. Effect and
    /// row tails are not `Ty` nodes; visitors that care about those params
    /// should inspect the enclosing `EffectRow`/`Row` separately.
    pub fn try_visit<B>(&self, visitor: &mut impl FnMut(&Ty) -> ControlFlow<B>) -> ControlFlow<B> {
        visitor(self)?;
        match self {
            Ty::Nominal(_, args) | Ty::Tuple(args) => {
                for arg in args {
                    arg.try_visit(visitor)?;
                }
            }
            Ty::Borrow(_, inner) => inner.try_visit(visitor)?,
            Ty::Unique(inner) => inner.try_visit(visitor)?,
            Ty::Func(params, ret, _) => {
                for param in params {
                    param.try_visit(visitor)?;
                }
                ret.try_visit(visitor)?;
            }
            Ty::Record(row) => row.try_visit(visitor)?,
            Ty::Any { protocol, assoc } => {
                for arg in &protocol.args {
                    arg.try_visit(visitor)?;
                }
                for (_, ty) in assoc {
                    ty.try_visit(visitor)?;
                }
            }
            Ty::Proj(base, protocol, _) => {
                base.try_visit(visitor)?;
                for arg in &protocol.args {
                    arg.try_visit(visitor)?;
                }
            }
            Ty::Eff(eff) => {
                for entry in &eff.effects {
                    for arg in &entry.args {
                        arg.try_visit(visitor)?;
                    }
                }
            }
            // Affine atoms surface as the param/var leaves they stand for,
            // so var- and param-collectors see through static content.
            Ty::Static(StaticValue::Int(int)) => {
                for (atom, _) in &int.terms {
                    atom.as_ty().try_visit(visitor)?;
                }
            }
            Ty::Static(StaticValue::Bool(_) | StaticValue::Case(..)) => {}
            Ty::Var(_) | Ty::Param(_) | Ty::Error => {}
        }
        ControlFlow::Continue(())
    }

    /// Walk two types in lockstep, visiting every corresponding type pair.
    /// Returns `false` if the structures cannot be zipped or if the visitor
    /// rejects any pair. Effect and row tails are not `Ty` nodes; callers that
    /// care about them should compare those structures from the enclosing node.
    pub fn try_zip(&self, other: &Ty, visitor: &mut impl FnMut(&Ty, &Ty) -> bool) -> bool {
        if !visitor(self, other) {
            return false;
        }
        match (self, other) {
            (Ty::Nominal(_, left_args), Ty::Nominal(_, right_args))
            | (Ty::Tuple(left_args), Ty::Tuple(right_args)) => {
                left_args.len() == right_args.len()
                    && left_args
                        .iter()
                        .zip(right_args)
                        .all(|(left, right)| left.try_zip(right, visitor))
            }
            (Ty::Borrow(left_kind, left_inner), Ty::Borrow(right_kind, right_inner)) => {
                left_kind == right_kind && left_inner.try_zip(right_inner, visitor)
            }
            (Ty::Func(left_params, left_ret, _), Ty::Func(right_params, right_ret, _)) => {
                left_params.len() == right_params.len()
                    && left_params
                        .iter()
                        .zip(right_params)
                        .all(|(left, right)| left.try_zip(right, visitor))
                    && left_ret.try_zip(right_ret, visitor)
            }
            (Ty::Record(left), Ty::Record(right)) => left.try_zip(right, visitor),
            (
                Ty::Any {
                    protocol: left_protocol,
                    assoc: left_assoc,
                },
                Ty::Any {
                    protocol: right_protocol,
                    assoc: right_assoc,
                },
            ) => {
                left_protocol.protocol == right_protocol.protocol
                    && left_protocol.args.len() == right_protocol.args.len()
                    && left_protocol
                        .args
                        .iter()
                        .zip(&right_protocol.args)
                        .all(|(left, right)| left.try_zip(right, visitor))
                    && left_assoc.len() == right_assoc.len()
                    && left_assoc.iter().zip(right_assoc).all(
                        |((left_symbol, left_ty), (right_symbol, right_ty))| {
                            left_symbol == right_symbol && left_ty.try_zip(right_ty, visitor)
                        },
                    )
            }
            (Ty::Proj(left_base, left_protocol, _), Ty::Proj(right_base, right_protocol, _)) => {
                left_protocol.protocol == right_protocol.protocol
                    && left_protocol.args.len() == right_protocol.args.len()
                    && left_protocol
                        .args
                        .iter()
                        .zip(&right_protocol.args)
                        .all(|(left, right)| left.try_zip(right, visitor))
                    && left_base.try_zip(right_base, visitor)
            }
            // Canonical forms compare structurally; there are no child
            // type pairs to visit.
            (Ty::Static(left), Ty::Static(right)) => left == right,
            (Ty::Var(_), Ty::Var(_))
            | (Ty::Param(_), Ty::Param(_))
            | (Ty::Eff(_), Ty::Eff(_))
            | (Ty::Error, Ty::Error) => true,
            _ => false,
        }
    }

    /// Substitute rigid `Param`s with types, and quantified row/effect tails
    /// with fresh tails. Used by scheme instantiation.
    pub fn substitute(
        &self,
        tys: &FxHashMap<Symbol, Ty>,
        effs: &FxHashMap<Symbol, EffTail>,
        rows: &FxHashMap<Symbol, RowTail>,
    ) -> Ty {
        Substituter { tys, effs, rows }.fold_ty(self)
    }

    /// Substitute quantified permission params. A separate fold from
    /// [`Ty::substitute`] because only scheme instantiation carries perms;
    /// the many type-only substitution sites stay three-argument.
    pub fn substitute_perms(&self, perms: &FxHashMap<Symbol, Perm>) -> Ty {
        PermSubstituter { perms }.fold_ty(self)
    }

    /// Substitute effect-row PARAMS with full rows, splicing entries: a
    /// tail `Param(p)` replaced by `['ping | t]` contributes both the
    /// entry and the new tail. [`Ty::substitute`]'s tail-for-tail map
    /// cannot carry entries — this is the member-read side of struct
    /// effect params, where the instance's row (which may have accrued
    /// entries) replaces the field's quantified tail.
    pub fn substitute_eff_rows(&self, rows: &FxHashMap<Symbol, EffectRow>) -> Ty {
        EffRowSubstituter { rows }.fold_ty(self)
    }

    /// Strip effect arguments from nominal applications — the typed-tree bake:
    /// effect args are typing-internal (capabilities ride closure
    /// environments at runtime), so flow and lowering never see them.
    pub fn erase_eff_args(&self) -> Ty {
        EffArgEraser.fold_ty(self)
    }
}

/// A rebuilding fold over the type structure (Lämmel & Peyton Jones, *Scrap
/// Your Boilerplate*, TLDI 2003, `gmapT`). `fold_ty`'s default owns the
/// structural arms — `Nominal`/`Func`/`Tuple`/`Record`/`Any`/`Proj` and the
/// row/effect tails — once; an implementor overrides only the leaves it
/// transforms (`Var`, `Param`, head symbols, tails). Every same-type rebuild
/// over `Ty` is one of these.
pub(crate) trait TyFold {
    /// Dispatch one node. Defaults to a structural rebuild ([`fold_children`]);
    /// a top-down transform (e.g. normalization) overrides this to act on the
    /// node before/after recursing, then calls `fold_children` for the arms.
    ///
    /// [`fold_children`]: TyFold::fold_children
    fn fold_ty(&mut self, ty: &Ty) -> Ty {
        self.fold_children(ty)
    }

    /// Rebuild a node from its immediate children, routing each through
    /// `fold_ty` (so a `fold_ty` override is honored at every depth) and the
    /// leaves through `fold_var`/`fold_param`/`fold_symbol`/`fold_eff`/
    /// `fold_row`. The one owner of the structural arms.
    fn fold_children(&mut self, ty: &Ty) -> Ty {
        match ty {
            Ty::Var(v) => self.fold_var(*v),
            Ty::Param(symbol) => self.fold_param(*symbol),
            Ty::Nominal(symbol, args) => Ty::Nominal(
                self.fold_symbol(*symbol),
                args.iter().map(|a| self.fold_ty(a)).collect(),
            ),
            Ty::Borrow(perm, inner) => collapse_borrow(self.fold_perm(*perm), self.fold_ty(inner)),
            Ty::Unique(inner) => Ty::Unique(Box::new(self.fold_ty(inner))),
            Ty::Func(params, ret, eff) => Ty::Func(
                params.iter().map(|p| self.fold_ty(p)).collect(),
                Box::new(self.fold_ty(ret)),
                self.fold_eff(eff),
            ),
            Ty::Tuple(items) => Ty::Tuple(items.iter().map(|i| self.fold_ty(i)).collect()),
            Ty::Record(row) => Ty::Record(self.fold_row(row)),
            Ty::Any { protocol, assoc } => Ty::Any {
                protocol: self.fold_protocol_ref(protocol),
                assoc: assoc
                    .iter()
                    .map(|(symbol, ty)| (self.fold_symbol(*symbol), self.fold_ty(ty)))
                    .collect(),
            },
            Ty::Proj(base, protocol, assoc) => Ty::Proj(
                Box::new(self.fold_ty(base)),
                self.fold_protocol_ref(protocol),
                self.fold_symbol(*assoc),
            ),
            Ty::Eff(eff) => Ty::Eff(self.fold_eff(eff)),
            Ty::Static(value) => self.fold_static(value),
            Ty::Error => Ty::Error,
        }
    }

    /// Rebuild static content, renormalizing affine forms: each atom folds
    /// as the param/var leaf it stands for, and whatever comes back (a
    /// bare atom, another affine form, or a closed value) is folded back
    /// in arithmetically. Substitution through static arguments therefore
    /// cannot leave a non-canonical form behind.
    fn fold_static(&mut self, value: &StaticValue) -> Ty {
        match value {
            StaticValue::Int(int) => {
                let mut acc = StaticInt::constant(int.constant.clone());
                for (atom, coeff) in &int.terms {
                    let folded = match atom {
                        StaticAtom::Param(symbol) => self.fold_param(*symbol),
                        StaticAtom::Var(var) => self.fold_var(*var),
                    };
                    // A non-index substitution target is a kind error
                    // reported where the substitution was formed; poison.
                    let Some(term) = StaticInt::from_ty(&folded) else {
                        return Ty::Error;
                    };
                    acc = acc.add(&term.scale(coeff));
                }
                acc.into_ty()
            }
            StaticValue::Bool(value) => Ty::Static(StaticValue::Bool(*value)),
            StaticValue::Case(owner, case) => Ty::Static(StaticValue::Case(
                self.fold_symbol(*owner),
                self.fold_symbol(*case),
            )),
        }
    }

    fn fold_var(&mut self, var: TyVar) -> Ty {
        Ty::Var(var)
    }

    fn fold_perm(&mut self, perm: Perm) -> Perm {
        match perm {
            Perm::Param(symbol) => Perm::Param(self.fold_symbol(symbol)),
            other => other,
        }
    }

    fn fold_symbol(&mut self, symbol: Symbol) -> Symbol {
        symbol
    }

    fn fold_param(&mut self, symbol: Symbol) -> Ty {
        Ty::Param(self.fold_symbol(symbol))
    }

    fn fold_protocol_ref(&mut self, protocol: &ProtocolRef) -> ProtocolRef {
        ProtocolRef {
            protocol: self.fold_symbol(protocol.protocol),
            args: protocol.args.iter().map(|arg| self.fold_ty(arg)).collect(),
        }
    }

    fn fold_eff(&mut self, eff: &EffectRow) -> EffectRow {
        EffectRow::new(
            eff.effects
                .iter()
                .map(|entry| EffectEntry {
                    effect: self.fold_symbol(entry.effect),
                    args: entry.args.iter().map(|ty| self.fold_ty(ty)).collect(),
                })
                .collect(),
            self.fold_eff_tail(&eff.tail),
        )
    }

    fn fold_eff_tail(&mut self, tail: &Option<EffTail>) -> Option<EffTail> {
        tail.clone()
    }

    fn fold_row(&mut self, row: &Row) -> Row {
        Row {
            fields: row
                .fields
                .iter()
                .map(|(label, ty)| (label.clone(), self.fold_ty(ty)))
                .collect(),
            tail: self.fold_row_tail(&row.tail),
        }
    }

    fn fold_row_tail(&mut self, tail: &Option<RowTail>) -> Option<RowTail> {
        tail.clone()
    }
}

/// Scheme instantiation: rigid params become types, quantified row/effect
/// tails become fresh tails, and a row-param tail bound to a record splices
/// its fields in (monomorphization closing a row-polymorphic signature).
struct Substituter<'a> {
    tys: &'a FxHashMap<Symbol, Ty>,
    effs: &'a FxHashMap<Symbol, EffTail>,
    rows: &'a FxHashMap<Symbol, RowTail>,
}

/// Instantiation's permission-param leg (see [`Ty::substitute_perms`]).
struct PermSubstituter<'a> {
    perms: &'a FxHashMap<Symbol, Perm>,
}

/// Row-splicing effect substitution (see [`Ty::substitute_eff_rows`]).
struct EffRowSubstituter<'a> {
    rows: &'a FxHashMap<Symbol, EffectRow>,
}

impl TyFold for EffRowSubstituter<'_> {
    fn fold_eff(&mut self, eff: &EffectRow) -> EffectRow {
        let mut effects: Vec<EffectEntry> = eff
            .effects
            .iter()
            .map(|entry| EffectEntry {
                effect: entry.effect,
                args: entry.args.iter().map(|ty| self.fold_ty(ty)).collect(),
            })
            .collect();
        let tail = match &eff.tail {
            Some(EffTail::Param(sym)) if self.rows.contains_key(sym) => {
                let replacement = &self.rows[sym];
                effects.extend(replacement.effects.iter().cloned());
                replacement.tail.clone()
            }
            other => other.clone(),
        };
        EffectRow { effects, tail }
    }
}

/// Effect-argument erasure (see [`Ty::erase_eff_args`]).
struct EffArgEraser;

impl TyFold for EffArgEraser {
    fn fold_ty(&mut self, ty: &Ty) -> Ty {
        match ty {
            Ty::Nominal(symbol, args) => Ty::Nominal(
                *symbol,
                args.iter()
                    .filter(|a| !matches!(a, Ty::Eff(_)))
                    .map(|a| self.fold_ty(a))
                    .collect(),
            ),
            other => self.fold_children(other),
        }
    }
}

impl TyFold for PermSubstituter<'_> {
    fn fold_perm(&mut self, perm: Perm) -> Perm {
        match perm {
            Perm::Param(symbol) => self.perms.get(&symbol).copied().unwrap_or(perm),
            other => other,
        }
    }
}

impl TyFold for Substituter<'_> {
    fn fold_param(&mut self, symbol: Symbol) -> Ty {
        self.tys.get(&symbol).cloned().unwrap_or(Ty::Param(symbol))
    }

    fn fold_eff_tail(&mut self, tail: &Option<EffTail>) -> Option<EffTail> {
        match tail {
            Some(EffTail::Param(sym)) => {
                Some(self.effs.get(sym).cloned().unwrap_or(EffTail::Param(*sym)))
            }
            other => other.clone(),
        }
    }

    fn fold_row(&mut self, row: &Row) -> Row {
        let mut fields: Vec<(Label, Ty)> = row
            .fields
            .iter()
            .map(|(label, ty)| (label.clone(), self.fold_ty(ty)))
            .collect();
        let tail = match &row.tail {
            Some(RowTail::Param(sym)) => match self.tys.get(sym) {
                Some(Ty::Record(rest)) => {
                    for (label, ty) in &rest.fields {
                        fields.push((label.clone(), self.fold_ty(ty)));
                    }
                    rest.tail.clone()
                }
                _ => Some(self.rows.get(sym).cloned().unwrap_or(RowTail::Param(*sym))),
            },
            other => other.clone(),
        };
        fields.sort_by(|(a, _), (b, _)| a.cmp(b));
        Row { fields, tail }
    }
}

/// Remap every symbol minted by the exporting module to the importer's id.
struct SymbolImporter {
    target: crate::compiling::module::ModuleId,
}

impl TyFold for SymbolImporter {
    fn fold_symbol(&mut self, symbol: Symbol) -> Symbol {
        import_symbol(symbol, self.target)
    }

    fn fold_eff_tail(&mut self, tail: &Option<EffTail>) -> Option<EffTail> {
        tail.as_ref().map(|tail| match tail {
            EffTail::Var(v) => EffTail::Var(*v),
            EffTail::Param(sym) => EffTail::Param(import_symbol(*sym, self.target)),
        })
    }

    fn fold_row_tail(&mut self, tail: &Option<RowTail>) -> Option<RowTail> {
        tail.as_ref().map(|tail| match tail {
            RowTail::Var(v) => RowTail::Var(*v),
            RowTail::Param(sym) => RowTail::Param(import_symbol(*sym, self.target)),
        })
    }
}

/// Prepare a type for export: a leftover unification variable degrades to
/// `Error` (the store does not travel), and a leftover row/effect var tail
/// becomes a rigid param keyed by the owning binder. The minted flags let
/// `Scheme::sanitize_for_export` register those params for instantiation
/// to freshen (an owner-keyed tail means "any effects", not a rigid row).
struct ExportSanitizer {
    owner: Symbol,
    minted_eff: bool,
    minted_row: bool,
}

impl TyFold for ExportSanitizer {
    fn fold_var(&mut self, _var: TyVar) -> Ty {
        Ty::Error
    }

    // A leftover perm var degrades to the safe default rather than poisoning
    // the whole type: `&T` is always a sound reading of an undecided borrow.
    //
    // CONTRACT: this fold is store-free, so it must only see post-`final_ty`
    // input. `final_ty` runs `default_unsolved_perms` (binding every
    // unsolved perm var to `Shared` in the store), so a finalized type
    // contains no `Perm::Var` at all and this arm is belt-and-suspenders.
    // On a PRE-finalize type the rewrite would be unsound: a var the store
    // solved to `Exclusive` would launder to a shared borrow here, exactly
    // the mismatch the store-aware defaulting exists to prevent. The
    // assertion keeps the arm loud if a caller ever feeds unfinalized types.
    fn fold_perm(&mut self, perm: Perm) -> Perm {
        match perm {
            Perm::Var(_) => {
                debug_assert!(
                    false,
                    "ExportSanitizer saw a Perm::Var: input was not finalized \
                     (final_ty defaults unsolved perm vars in the store)"
                );
                Perm::Shared
            }
            other => other,
        }
    }

    fn fold_eff_tail(&mut self, tail: &Option<EffTail>) -> Option<EffTail> {
        match tail {
            Some(EffTail::Var(_)) => {
                self.minted_eff = true;
                Some(EffTail::Param(self.owner))
            }
            other => other.clone(),
        }
    }

    fn fold_row_tail(&mut self, tail: &Option<RowTail>) -> Option<RowTail> {
        match tail {
            Some(RowTail::Var(_)) => {
                self.minted_row = true;
                Some(RowTail::Param(self.owner))
            }
            other => other.clone(),
        }
    }
}

/// Nested shared/exclusive borrows collapse: a borrow is a permission
/// view, and viewing through two views is one view at the weaker
/// permission (`&(&mut T)` ≡ `&T`; ADR 0015 addendum). Collapse applies
/// only when both permissions are concrete — var/param perms wait for
/// defaulting.
pub(crate) fn collapse_borrow(perm: Perm, inner: Ty) -> Ty {
    if let Ty::Borrow(inner_perm, innermost) = &inner
        && matches!(perm, Perm::Shared | Perm::Exclusive)
        && matches!(inner_perm, Perm::Shared | Perm::Exclusive)
    {
        let collapsed = if perm.is_exclusive() && inner_perm.is_exclusive() {
            Perm::Exclusive
        } else {
            Perm::Shared
        };
        return collapse_borrow(collapsed, innermost.as_ref().clone());
    }
    Ty::Borrow(perm, Box::new(inner))
}

impl Ty {
    /// Whether any unification variable (type, effect/row tail, or perm)
    /// survives in this type — the module-boundary portability check.
    pub(crate) fn has_unification_vars(&self) -> bool {
        match self {
            Ty::Var(_) => true,
            Ty::Param(_) | Ty::Error => false,
            Ty::Nominal(_, args) | Ty::Tuple(args) => args.iter().any(Ty::has_unification_vars),
            Ty::Borrow(perm, inner) => matches!(perm, Perm::Var(_)) || inner.has_unification_vars(),
            Ty::Unique(inner) => inner.has_unification_vars(),
            Ty::Func(params, ret, eff) => {
                params.iter().any(Ty::has_unification_vars)
                    || ret.has_unification_vars()
                    || eff.has_unification_vars()
            }
            Ty::Record(row) => row.has_unification_vars(),
            Ty::Any { protocol, assoc } => {
                protocol.has_unification_vars()
                    || assoc.iter().any(|(_, ty)| ty.has_unification_vars())
            }
            Ty::Proj(base, protocol, _) => {
                base.has_unification_vars() || protocol.has_unification_vars()
            }
            Ty::Eff(eff) => eff.has_unification_vars(),
            Ty::Static(StaticValue::Int(int)) => int
                .terms
                .iter()
                .any(|(atom, _)| matches!(atom, StaticAtom::Var(_))),
            Ty::Static(StaticValue::Bool(_) | StaticValue::Case(..)) => false,
        }
    }
}

impl EffectRow {
    pub(crate) fn has_unification_vars(&self) -> bool {
        matches!(self.tail, Some(EffTail::Var(_)))
            || self
                .effects
                .iter()
                .any(|entry| entry.args.iter().any(Ty::has_unification_vars))
    }
}

impl Row {
    pub(crate) fn has_unification_vars(&self) -> bool {
        matches!(self.tail, Some(RowTail::Var(_)))
            || self.fields.iter().any(|(_, ty)| ty.has_unification_vars())
    }
}

impl Scheme {
    pub(crate) fn has_unification_vars(&self) -> bool {
        self.ty.has_unification_vars()
            || self.predicates.iter().any(Predicate::has_unification_vars)
    }
}

impl Predicate {
    pub(crate) fn has_unification_vars(&self) -> bool {
        match self {
            Predicate::TypeEq(a, b) => a.has_unification_vars() || b.has_unification_vars(),
            Predicate::EffectEq(a, b) => a.has_unification_vars() || b.has_unification_vars(),
            Predicate::RowEq(a, b) => a.has_unification_vars() || b.has_unification_vars(),
            Predicate::Conforms { ty, protocol } => {
                ty.has_unification_vars() || protocol.has_unification_vars()
            }
            Predicate::HasMember {
                receiver, member, ..
            } => receiver.has_unification_vars() || member.has_unification_vars(),
            Predicate::StaticCmp { lhs, rhs, .. } => {
                lhs.has_unification_vars() || rhs.has_unification_vars()
            }
        }
    }

    /// Export form of a predicate: leftover variables degrade exactly as
    /// they do in types (vars → Error, tails → owner-keyed params).
    pub fn sanitize_for_export(&self, owner: Symbol) -> Predicate {
        self.fold_with(&mut ExportSanitizer {
            owner,
            minted_eff: false,
            minted_row: false,
        })
    }
}

impl Predicate {
    pub fn render_mono(&self) -> String {
        render_predicate(self, &FxHashMap::default())
    }

    /// Apply a [`TyFold`] across every type, effect row, record row, and
    /// protocol reference this predicate contains — the one owner of the
    /// per-variant recursion, shared by every predicate rebuild.
    pub(crate) fn fold_with(&self, folder: &mut impl TyFold) -> Predicate {
        match self {
            Predicate::TypeEq(a, b) => Predicate::TypeEq(folder.fold_ty(a), folder.fold_ty(b)),
            Predicate::EffectEq(a, b) => {
                Predicate::EffectEq(folder.fold_eff(a), folder.fold_eff(b))
            }
            Predicate::RowEq(a, b) => Predicate::RowEq(folder.fold_row(a), folder.fold_row(b)),
            Predicate::Conforms { ty, protocol } => Predicate::Conforms {
                ty: folder.fold_ty(ty),
                protocol: folder.fold_protocol_ref(protocol),
            },
            Predicate::HasMember {
                receiver,
                label,
                member,
            } => Predicate::HasMember {
                receiver: folder.fold_ty(receiver),
                label: label.clone(),
                member: folder.fold_ty(member),
            },
            Predicate::StaticCmp { op, lhs, rhs } => Predicate::StaticCmp {
                op: *op,
                lhs: folder.fold_ty(lhs),
                rhs: folder.fold_ty(rhs),
            },
        }
    }

    pub fn substitute(
        &self,
        tys: &FxHashMap<Symbol, Ty>,
        effs: &FxHashMap<Symbol, EffTail>,
        rows: &FxHashMap<Symbol, RowTail>,
    ) -> Predicate {
        self.fold_with(&mut Substituter { tys, effs, rows })
    }

    /// Instantiation's permission-param leg for predicates: the exact
    /// mirror of [`Ty::substitute_perms`], so a predicate mentioning a
    /// quantified `Perm::Param` gets the same fresh variable the scheme
    /// type received (a rigid param left behind would never unify with
    /// the call site's perms).
    pub fn substitute_perms(&self, perms: &FxHashMap<Symbol, Perm>) -> Predicate {
        self.fold_with(&mut PermSubstituter { perms })
    }
}

/// Remap a symbol minted by the exporting module (ModuleId::Current from its
/// own point of view) to the importer's id for it; symbols referencing other
/// modules (core, transitive imports) keep theirs.
pub(crate) fn import_symbol(symbol: Symbol, target: crate::compiling::module::ModuleId) -> Symbol {
    if symbol.module_id() == Some(crate::compiling::module::ModuleId::Current) {
        symbol.import(target)
    } else {
        symbol
    }
}

impl Ty {
    /// Remap every embedded symbol for an importer (`Module::import_as`
    /// recursing through types).
    pub fn import_symbols(&self, target: crate::compiling::module::ModuleId) -> Ty {
        SymbolImporter { target }.fold_ty(self)
    }
}

impl EffectRow {
    pub fn import_symbols(&self, target: crate::compiling::module::ModuleId) -> EffectRow {
        SymbolImporter { target }.fold_eff(self)
    }
}

impl Row {
    pub fn import_symbols(&self, target: crate::compiling::module::ModuleId) -> Row {
        SymbolImporter { target }.fold_row(self)
    }
}

impl Predicate {
    pub fn import_symbols(&self, target: crate::compiling::module::ModuleId) -> Predicate {
        self.fold_with(&mut SymbolImporter { target })
    }
}

impl Scheme {
    pub fn import_symbols(&self, target: crate::compiling::module::ModuleId) -> Scheme {
        Scheme {
            params: self
                .params
                .iter()
                .map(|p| SchemeParam {
                    symbol: import_symbol(p.symbol, target),
                    kind: match &p.kind {
                        ParamKind::Type => ParamKind::Type,
                        ParamKind::Static(value_ty) => {
                            ParamKind::Static(value_ty.import_symbols(target))
                        }
                    },
                    default: p.default.as_ref().map(|d| d.import_symbols(target)),
                })
                .collect(),
            eff_params: self
                .eff_params
                .iter()
                .map(|s| import_symbol(*s, target))
                .collect(),
            row_params: self
                .row_params
                .iter()
                .map(|s| import_symbol(*s, target))
                .collect(),
            perm_params: self
                .perm_params
                .iter()
                .map(|s| import_symbol(*s, target))
                .collect(),
            predicates: self
                .predicates
                .iter()
                .map(|predicate| predicate.import_symbols(target))
                .collect(),
            ty: self.ty.import_symbols(target),
        }
    }
}

impl Ty {
    /// Prepare a type for export across a module boundary: unification
    /// variables index a solver store that does not travel, so any leftover
    /// type variable degrades to `Error` (truly unknown) and leftover row
    /// tails become rigid params keyed by the owning binder (an unknown but
    /// fixed row — unifiable as a rigid tail on the importing side).
    pub fn sanitize_for_export(&self, owner: Symbol) -> Ty {
        ExportSanitizer {
            owner,
            minted_eff: false,
            minted_row: false,
        }
        .fold_ty(self)
    }
}

impl Scheme {
    /// Export form of a whole scheme: sanitize the type, and register any
    /// owner-keyed row/effect param the sanitizer mints so instantiation
    /// freshens it on the importing side — a leftover tail variable means
    /// "whatever effects the caller allows", not a rigid row (the same
    /// convention as the catalog's annotation-derived signatures).
    pub fn sanitize_for_export(&self, owner: Symbol) -> Scheme {
        let mut sanitizer = ExportSanitizer {
            owner,
            minted_eff: false,
            minted_row: false,
        };
        let ty = sanitizer.fold_ty(&self.ty);
        let predicates = self
            .predicates
            .iter()
            .map(|predicate| predicate.sanitize_for_export(owner))
            .collect();
        let mut scheme = Scheme {
            ty,
            predicates,
            ..self.clone()
        };
        if sanitizer.minted_eff && !scheme.eff_params.contains(&owner) {
            scheme.eff_params.push(owner);
        }
        if sanitizer.minted_row && !scheme.row_params.contains(&owner) {
            scheme.row_params.push(owner);
        }
        scheme
    }
}

/// One-way structural match: bind every rigid `Param` in `pattern` to the
/// aligned part of `actual`, recursing through ALL type variants. Variables
/// and `Error` match anything; a re-bound param must stay consistent; binding
/// is occurs-checked. Returns false on a head mismatch. The single matcher for
/// conformance-head binding, member-owner binding, and GADT result refinement
/// (Chakravarty, Keller & Peyton Jones, ICFP 2005, instance reduction).
pub(crate) fn match_pattern(
    pattern: &Ty,
    actual: &Ty,
    bindings: &mut FxHashMap<Symbol, Ty>,
) -> bool {
    match_pattern_with_options(pattern, actual, bindings, true)
}

/// One-way structural match for full conformance-key components. Unlike
/// `match_pattern`, this does not erase a borrow on only the pattern side: a
/// conformance to `P<&Int>` must not also match a lookup for `P<Int>`.
pub(crate) fn match_key_pattern(
    pattern: &Ty,
    actual: &Ty,
    bindings: &mut FxHashMap<Symbol, Ty>,
) -> bool {
    match_pattern_with_options(pattern, actual, bindings, false)
}

fn match_pattern_with_options(
    pattern: &Ty,
    actual: &Ty,
    bindings: &mut FxHashMap<Symbol, Ty>,
    peel_pattern_borrows: bool,
) -> bool {
    match (pattern, actual) {
        (Ty::Error, _) | (_, Ty::Error) => true,
        // A rigid param binds to whatever sits opposite it, *including* a
        // unification variable (conformance heads match against a receiver that
        // still holds inference variables). This must precede the variable
        // wildcards below, or such a binding would be silently skipped.
        (Ty::Param(param), ty) => match_param(*param, ty, bindings, peel_pattern_borrows),
        (Ty::Var(_), _) | (_, Ty::Var(_)) | (_, Ty::Param(_)) => true,
        (Ty::Nominal(left, left_args), Ty::Nominal(right, right_args)) => {
            // Effect args (a kind-restricted suffix) are invisible to
            // conformance heads: `extend Wrapper` matches every instance
            // row. Compare the shared prefix when the excess is all-eff.
            let left_len = left_args
                .iter()
                .take_while(|a| !matches!(a, Ty::Eff(_)))
                .count();
            let right_len = right_args
                .iter()
                .take_while(|a| !matches!(a, Ty::Eff(_)))
                .count();
            left == right
                && left_len == right_len
                && left_args[..left_len]
                    .iter()
                    .zip(&right_args[..right_len])
                    .all(|(left, right)| {
                        match_pattern_with_options(left, right, bindings, peel_pattern_borrows)
                    })
        }
        // Concrete static arguments (ADR 0035) match by canonical
        // equality; a rigid static param in the pattern binds through the
        // `Param` arm above like any other parameter.
        (Ty::Static(left), Ty::Static(right)) => left == right,
        (Ty::Borrow(left_kind, left_inner), Ty::Borrow(right_kind, right_inner)) => {
            left_kind == right_kind
                && match_pattern_with_options(
                    left_inner,
                    right_inner,
                    bindings,
                    peel_pattern_borrows,
                )
        }
        // A borrow in the pattern is transparent against a non-borrow
        // actual: a witness may spell `T` where the requirement says `&T`
        // (borrow erasure, ADR 0014). One-sided — a param pattern binding
        // TO a borrow (`Element = &Int`) stays intact via `match_param`.
        (Ty::Borrow(_, left_inner), right) if peel_pattern_borrows => {
            match_pattern_with_options(left_inner, right, bindings, peel_pattern_borrows)
        }
        (Ty::Unique(left_inner), Ty::Unique(right_inner)) => {
            match_pattern_with_options(left_inner, right_inner, bindings, peel_pattern_borrows)
        }
        (Ty::Tuple(left_items), Ty::Tuple(right_items)) => {
            left_items.len() == right_items.len()
                && left_items.iter().zip(right_items).all(|(left, right)| {
                    match_pattern_with_options(left, right, bindings, peel_pattern_borrows)
                })
        }
        (Ty::Func(left_args, left_ret, _), Ty::Func(right_args, right_ret, _)) => {
            left_args.len() == right_args.len()
                && left_args.iter().zip(right_args).all(|(left, right)| {
                    match_pattern_with_options(left, right, bindings, peel_pattern_borrows)
                })
                && match_pattern_with_options(left_ret, right_ret, bindings, peel_pattern_borrows)
        }
        (Ty::Record(left), Ty::Record(right)) => {
            left.fields.len() == right.fields.len()
                && left.tail == right.tail
                && left.fields.iter().zip(&right.fields).all(
                    |((left_label, left_ty), (right_label, right_ty))| {
                        left_label == right_label
                            && match_pattern_with_options(
                                left_ty,
                                right_ty,
                                bindings,
                                peel_pattern_borrows,
                            )
                    },
                )
        }
        (
            Ty::Proj(left_base, left_protocol, left_assoc),
            Ty::Proj(right_base, right_protocol, right_assoc),
        ) => {
            left_protocol.protocol == right_protocol.protocol
                && left_protocol.args.len() == right_protocol.args.len()
                && left_protocol
                    .args
                    .iter()
                    .zip(&right_protocol.args)
                    .all(|(left, right)| {
                        match_pattern_with_options(left, right, bindings, peel_pattern_borrows)
                    })
                && left_assoc == right_assoc
                && match_pattern_with_options(left_base, right_base, bindings, peel_pattern_borrows)
        }
        (
            Ty::Any {
                protocol: left_protocol,
                assoc: left_assoc,
            },
            Ty::Any {
                protocol: right_protocol,
                assoc: right_assoc,
            },
        ) => {
            left_protocol.protocol == right_protocol.protocol
                && left_protocol.args.len() == right_protocol.args.len()
                && left_protocol
                    .args
                    .iter()
                    .zip(&right_protocol.args)
                    .all(|(left, right)| {
                        match_pattern_with_options(left, right, bindings, peel_pattern_borrows)
                    })
                && left_assoc.len() == right_assoc.len()
                && left_assoc.iter().zip(right_assoc).all(
                    |((left_symbol, left_ty), (right_symbol, right_ty))| {
                        left_symbol == right_symbol
                            && match_pattern_with_options(
                                left_ty,
                                right_ty,
                                bindings,
                                peel_pattern_borrows,
                            )
                    },
                )
        }
        _ => false,
    }
}

fn match_param(
    param: Symbol,
    ty: &Ty,
    bindings: &mut FxHashMap<Symbol, Ty>,
    peel_pattern_borrows: bool,
) -> bool {
    if matches!(ty, Ty::Param(other) if *other == param) {
        return true;
    }
    if pattern_occurs(param, ty, bindings) {
        return false;
    }
    if let Some(existing) = bindings.get(&param).cloned() {
        return match_pattern_with_options(&existing, ty, bindings, peel_pattern_borrows);
    }
    bindings.insert(param, ty.clone());
    true
}

fn pattern_occurs(param: Symbol, ty: &Ty, bindings: &FxHashMap<Symbol, Ty>) -> bool {
    match ty {
        Ty::Param(other) if *other == param => true,
        Ty::Param(other) => bindings
            .get(other)
            .is_some_and(|ty| pattern_occurs(param, ty, bindings)),
        Ty::Nominal(_, args) | Ty::Tuple(args) => {
            args.iter().any(|ty| pattern_occurs(param, ty, bindings))
        }
        Ty::Borrow(_, inner) => pattern_occurs(param, inner, bindings),
        Ty::Unique(inner) => pattern_occurs(param, inner, bindings),
        Ty::Func(args, ret, _) => {
            args.iter().any(|ty| pattern_occurs(param, ty, bindings))
                || pattern_occurs(param, ret, bindings)
        }
        Ty::Record(row) => row
            .fields
            .iter()
            .any(|(_, ty)| pattern_occurs(param, ty, bindings)),
        Ty::Any { protocol, assoc } => {
            protocol
                .args
                .iter()
                .any(|ty| pattern_occurs(param, ty, bindings))
                || assoc
                    .iter()
                    .any(|(_, ty)| pattern_occurs(param, ty, bindings))
        }
        Ty::Proj(base, protocol, _) => {
            pattern_occurs(param, base, bindings)
                || protocol
                    .args
                    .iter()
                    .any(|ty| pattern_occurs(param, ty, bindings))
        }
        Ty::Eff(eff) => eff.effects.iter().any(|entry| {
            entry
                .args
                .iter()
                .any(|ty| pattern_occurs(param, ty, bindings))
        }),
        Ty::Static(StaticValue::Int(int)) => int
            .terms
            .iter()
            .any(|(atom, _)| pattern_occurs(param, &atom.as_ty(), bindings)),
        Ty::Static(StaticValue::Bool(_) | StaticValue::Case(..)) => false,
        Ty::Var(_) | Ty::Error => false,
    }
}

/// The kind of a declared generic parameter: an ordinary type parameter,
/// or an ADR 0035 static value parameter carrying its declared value type.
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum ParamKind {
    Type,
    Static(Ty),
}

/// A quantified generic parameter: its symbol, its kind, and its declared
/// default (if any). The qualified context lives on `Scheme` as
/// predicates, not on individual parameters, matching Jones's
/// qualified-type shape while letting inline bounds and declaration
/// `where` share one P.
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct SchemeParam {
    pub symbol: Symbol,
    #[serde(default)]
    pub kind: ParamKind,
    #[serde(default)]
    pub default: Option<Ty>,
}

impl Default for ParamKind {
    fn default() -> Self {
        ParamKind::Type
    }
}

impl SchemeParam {
    /// An ordinary type parameter with no default.
    pub fn ty(symbol: Symbol) -> SchemeParam {
        SchemeParam {
            symbol,
            kind: ParamKind::Type,
            default: None,
        }
    }
}

/// A type scheme `forall params. P => type`. Monomorphic bindings are schemes
/// with no params and no predicates.
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct Scheme {
    pub params: Vec<SchemeParam>,
    pub eff_params: Vec<Symbol>,
    pub row_params: Vec<Symbol>,
    /// Quantified borrow-permission parameters: grade polymorphism over the
    /// {Shared, Exclusive} lattice, invisible in renders.
    pub perm_params: Vec<Symbol>,
    /// The qualified context P: declared bounds, inferred HasMember
    /// constraints, same-type equalities, and row/effect predicates.
    pub predicates: Vec<Predicate>,
    pub ty: Ty,
}

impl Scheme {
    pub fn mono(ty: Ty) -> Self {
        Scheme {
            params: vec![],
            predicates: vec![],
            eff_params: vec![],
            row_params: vec![],
            perm_params: vec![],
            ty,
        }
    }

    /// Render for display/tests: quantified type params are named
    /// positionally (T0, T1, …); static value parameters (ADR 0035) render
    /// with `static` and their declared value type; simple parameter
    /// conformances render inline, and the remaining qualified context
    /// renders after `where`.
    pub fn render(&self) -> String {
        let mut names = FxHashMap::default();
        for (i, param) in self.params.iter().enumerate() {
            names.insert(param.symbol, format!("T{i}"));
        }

        let mut inline_bounds: FxHashMap<Symbol, Vec<ProtocolRef>> = FxHashMap::default();
        let mut where_predicates = vec![];
        for predicate in &self.predicates {
            match predicate {
                Predicate::Conforms {
                    ty: Ty::Param(param),
                    protocol,
                } if self.params.iter().any(|p| p.symbol == *param) => {
                    inline_bounds
                        .entry(*param)
                        .or_default()
                        .push(protocol.clone());
                }
                _ => where_predicates.push(predicate),
            }
        }

        let mut body = render_ty(&self.ty, &names);
        if !where_predicates.is_empty() {
            let mut constraints: Vec<String> = where_predicates
                .iter()
                .map(|predicate| render_predicate(predicate, &names))
                .collect();
            constraints.sort();
            constraints.dedup();
            body = format!("{body} where {}", constraints.join(" && "));
        }
        if self.params.is_empty() {
            body
        } else {
            let params: Vec<String> = self
                .params
                .iter()
                .enumerate()
                .map(|(i, param)| {
                    if let ParamKind::Static(value_ty) = &param.kind {
                        return format!("static T{i}: {}", render_ty(value_ty, &names));
                    }
                    match inline_bounds.get(&param.symbol) {
                        Some(bounds) if !bounds.is_empty() => {
                            let mut bounds: Vec<String> = bounds
                                .iter()
                                .map(|b| render_protocol_ref(b, &names))
                                .collect();
                            bounds.sort();
                            bounds.dedup();
                            format!("T{i}: {}", bounds.join(" & "))
                        }
                        _ => format!("T{i}"),
                    }
                })
                .collect();
            format!("<{}>{}", params.join(", "), body)
        }
    }
}

impl Ty {
    /// Render a type with no quantified-parameter naming context.
    pub fn render_mono(&self) -> String {
        render_ty(self, &FxHashMap::default())
    }
}

pub(crate) fn render_ty(ty: &Ty, param_names: &FxHashMap<Symbol, String>) -> String {
    match ty {
        Ty::Var(v) => format!("?{}", v.0),
        Ty::Param(sym) => param_names
            .get(sym)
            .cloned()
            .unwrap_or_else(|| format!("{sym}")),
        Ty::Nominal(sym, args) => {
            let head = render_nominal_head(sym);
            if args.is_empty() {
                head
            } else {
                let args: Vec<String> = args.iter().map(|a| render_ty(a, param_names)).collect();
                format!("{head}<{}>", args.join(", "))
            }
        }
        // A solver perm var or quantified perm param renders as a plain `&`:
        // permission polymorphism stays invisible unless two concrete
        // permissions clash.
        Ty::Borrow(perm, inner) => {
            let prefix = if perm.is_exclusive() { "&mut " } else { "&" };
            format!("{prefix}{}", render_ty(inner, param_names))
        }
        Ty::Unique(inner) => format!("*{}", render_ty(inner, param_names)),
        Ty::Func(params, ret, eff) => {
            let params: Vec<String> = params.iter().map(|p| render_ty(p, param_names)).collect();
            let eff = render_effect_row(eff);
            format!(
                "({}) -> {}{}",
                params.join(", "),
                render_ty(ret, param_names),
                eff
            )
        }
        Ty::Tuple(items) => {
            let items: Vec<String> = items.iter().map(|i| render_ty(i, param_names)).collect();
            format!("({})", items.join(", "))
        }
        Ty::Record(row) => {
            let mut fields: Vec<String> = row
                .fields
                .iter()
                .map(|(l, t)| format!("{l}: {}", render_ty(t, param_names)))
                .collect();
            match &row.tail {
                Some(RowTail::Var(v)) => fields.push(format!("..?r{}", v.0)),
                Some(RowTail::Param(sym)) => fields.push(format!("..{sym}")),
                None => {}
            }
            format!("{{ {} }}", fields.join(", "))
        }
        Ty::Any { protocol, assoc } => {
            if assoc.is_empty() {
                format!("any {}", render_protocol_ref(protocol, param_names))
            } else {
                let bindings: Vec<String> = assoc
                    .iter()
                    .map(|(symbol, ty)| format!("{symbol} = {}", render_ty(ty, param_names)))
                    .collect();
                format!(
                    "any {}<{}>",
                    render_protocol_ref(protocol, param_names),
                    bindings.join(", ")
                )
            }
        }
        Ty::Proj(base, _, assoc) => {
            format!("{}.{assoc}", render_ty(base, param_names))
        }
        // An effect argument renders as its row (it is a row, not a type).
        Ty::Eff(eff) => {
            let rendered = render_effect_row(eff);
            if rendered.is_empty() {
                "'{}".to_string()
            } else {
                rendered.trim_start().to_string()
            }
        }
        Ty::Static(value) => render_static_value(value, param_names),
        Ty::Error => "<error>".to_string(),
    }
}

pub(crate) fn render_static_value(
    value: &StaticValue,
    param_names: &FxHashMap<Symbol, String>,
) -> String {
    match value {
        StaticValue::Int(int) => {
            let mut parts = vec![];
            if int.constant != 0.into() || int.terms.is_empty() {
                parts.push(int.constant.to_string());
            }
            for (atom, coeff) in &int.terms {
                let atom = render_ty(&atom.as_ty(), param_names);
                if *coeff == 1.into() {
                    parts.push(atom);
                } else if *coeff == (-1).into() {
                    parts.push(format!("-{atom}"));
                } else {
                    parts.push(format!("{coeff} * {atom}"));
                }
            }
            let mut rendered = String::new();
            for (i, part) in parts.iter().enumerate() {
                if i == 0 {
                    rendered.push_str(part);
                } else if let Some(negated) = part.strip_prefix('-') {
                    rendered.push_str(" - ");
                    rendered.push_str(negated);
                } else {
                    rendered.push_str(" + ");
                    rendered.push_str(part);
                }
            }
            rendered
        }
        StaticValue::Bool(value) => value.to_string(),
        StaticValue::Case(owner, case) => format!("{owner}.{case}"),
    }
}

pub(crate) fn render_protocol_ref(
    protocol: &ProtocolRef,
    param_names: &FxHashMap<Symbol, String>,
) -> String {
    let head = render_nominal_head(&protocol.protocol);
    if protocol.args.is_empty() {
        head
    } else {
        let args: Vec<String> = protocol
            .args
            .iter()
            .map(|arg| render_ty(arg, param_names))
            .collect();
        format!("{head}<{}>", args.join(", "))
    }
}

fn render_predicate(predicate: &Predicate, param_names: &FxHashMap<Symbol, String>) -> String {
    match predicate {
        Predicate::TypeEq(a, b) => {
            let mut rendered = [render_ty(a, param_names), render_ty(b, param_names)];
            rendered.sort();
            format!("{} == {}", rendered[0], rendered[1])
        }
        Predicate::EffectEq(a, b) => format!(
            "{} == {}",
            render_full_effect_row(a),
            render_full_effect_row(b)
        ),
        Predicate::RowEq(a, b) => format!(
            "{} == {}",
            render_ty(&Ty::Record(a.clone()), param_names),
            render_ty(&Ty::Record(b.clone()), param_names)
        ),
        Predicate::Conforms { ty, protocol } => {
            format!(
                "{}: {}",
                render_ty(ty, param_names),
                render_protocol_ref(protocol, param_names)
            )
        }
        Predicate::HasMember {
            receiver,
            label,
            member,
        } => format!(
            "{}.{}: {}",
            render_ty(receiver, param_names),
            label,
            render_ty(member, param_names)
        ),
        Predicate::StaticCmp { op, lhs, rhs } => format!(
            "{} {} {}",
            render_ty(lhs, param_names),
            op.as_str(),
            render_ty(rhs, param_names)
        ),
    }
}

pub(crate) fn render_entry(entry: &EffectEntry, param_names: &FxHashMap<Symbol, String>) -> String {
    if entry.args.is_empty() {
        return format!("'{}", entry.effect);
    }
    let args: Vec<String> = entry
        .args
        .iter()
        .map(|ty| render_ty(ty, param_names))
        .collect();
    format!("'{}<{}>", entry.effect, args.join(", "))
}

fn render_full_effect_row(eff: &EffectRow) -> String {
    let names = FxHashMap::default();
    let mut labels: Vec<String> = eff
        .effects
        .iter()
        .map(|entry| render_entry(entry, &names))
        .collect();
    match &eff.tail {
        Some(EffTail::Var(v)) => labels.push(format!("..?e{}", v.0)),
        Some(EffTail::Param(sym)) => labels.push(format!("..{sym}")),
        None => {}
    }
    format!("! <{}>", labels.join(", "))
}

/// Concrete effects render as `! <'a, 'b>`; pure rows and rows that are just
/// an (open or quantified) tail are elided — they say nothing concrete.
fn render_effect_row(eff: &EffectRow) -> String {
    if eff.effects.is_empty() {
        return String::new();
    }
    let names = FxHashMap::default();
    let labels: Vec<String> = eff
        .effects
        .iter()
        .map(|entry| render_entry(entry, &names))
        .collect();
    format!(" ! <{}>", labels.join(", "))
}

fn render_nominal_head(sym: &Symbol) -> String {
    if *sym == Symbol::Int {
        "Int".into()
    } else if *sym == Symbol::Float {
        "Float".into()
    } else if *sym == Symbol::Bool {
        "Bool".into()
    } else if *sym == Symbol::Void {
        "()".into()
    } else if *sym == Symbol::Never {
        "Never".into()
    } else if *sym == Symbol::String {
        "String".into()
    } else if *sym == Symbol::Character {
        "Character".into()
    } else if *sym == Symbol::Array {
        "Array".into()
    } else if *sym == Symbol::RawPtr {
        "RawPtr".into()
    } else if *sym == Symbol::Byte {
        "Byte".into()
    } else {
        format!("{sym}")
    }
}

#[cfg(test)]
mod traversal_tests {
    use super::*;

    #[test]
    fn nested_borrows_collapse_through_folds() {
        // & of & is & (ADR 0015 addendum): substitution exposing a nested
        // borrow collapses it, with the weaker permission winning.
        let mut subst = FxHashMap::default();
        subst.insert(
            Symbol::Bool,
            Ty::Borrow(Perm::Shared, Box::new(Ty::Nominal(Symbol::Int, vec![]))),
        );
        let outer = Ty::Borrow(Perm::Shared, Box::new(Ty::Param(Symbol::Bool)));
        let collapsed = outer.substitute(&subst, &Default::default(), &Default::default());
        assert_eq!(
            collapsed,
            Ty::Borrow(Perm::Shared, Box::new(Ty::Nominal(Symbol::Int, vec![])))
        );

        // Exclusive-over-shared caps at Shared.
        let outer = Ty::Borrow(Perm::Exclusive, Box::new(Ty::Param(Symbol::Bool)));
        let collapsed = outer.substitute(&subst, &Default::default(), &Default::default());
        assert_eq!(
            collapsed,
            Ty::Borrow(Perm::Shared, Box::new(Ty::Nominal(Symbol::Int, vec![])))
        );
    }

    #[test]
    fn match_pattern_peels_pattern_side_borrows() {
        // `&RHS` against `Int` binds RHS = Int: a witness may spell the
        // operand by value where the requirement borrows it (ADR 0014).
        let mut bindings = FxHashMap::default();
        assert!(match_pattern(
            &Ty::Borrow(Perm::Shared, Box::new(Ty::Param(Symbol::Bool))),
            &Ty::Nominal(Symbol::Int, vec![]),
            &mut bindings,
        ));
        assert_eq!(
            bindings.get(&Symbol::Bool),
            Some(&Ty::Nominal(Symbol::Int, vec![]))
        );

        // The other direction stays a whole-borrow bind: `Element`
        // against `&Int` binds Element = &Int (ArrayIterator's shape).
        let mut bindings = FxHashMap::default();
        let borrowed_int = Ty::Borrow(Perm::Shared, Box::new(Ty::Nominal(Symbol::Int, vec![])));
        assert!(match_pattern(
            &Ty::Param(Symbol::Bool),
            &borrowed_int,
            &mut bindings,
        ));
        assert_eq!(bindings.get(&Symbol::Bool), Some(&borrowed_int));
    }

    #[test]
    fn match_pattern_binds_params_nested_in_record_any_and_proj() {
        // These three variants were silently dropped by the old hand-rolled
        // matchers, so a param nested inside them never bound.
        let mut bindings = FxHashMap::default();

        // Record field: `{ x: A }` against `{ x: Float }` binds A = Float.
        assert!(match_pattern(
            &Ty::Record(Row {
                fields: vec![(Label::Named("x".into()), Ty::Param(Symbol::Bool))],
                tail: None,
            }),
            &Ty::Record(Row {
                fields: vec![(Label::Named("x".into()), Ty::Nominal(Symbol::Float, vec![]))],
                tail: None,
            }),
            &mut bindings,
        ));
        assert_eq!(
            bindings.get(&Symbol::Bool),
            Some(&Ty::Nominal(Symbol::Float, vec![]))
        );

        // Existential binding: `any P<K = B>` against `any P<K = Int>`.
        assert!(match_pattern(
            &Ty::Any {
                protocol: ProtocolRef::bare(Symbol::Int),
                assoc: vec![(Symbol::Float, Ty::Param(Symbol::String))],
            },
            &Ty::Any {
                protocol: ProtocolRef::bare(Symbol::Int),
                assoc: vec![(Symbol::Float, Ty::Nominal(Symbol::Int, vec![]))],
            },
            &mut bindings,
        ));
        assert_eq!(
            bindings.get(&Symbol::String),
            Some(&Ty::Nominal(Symbol::Int, vec![]))
        );

        // Projection base: `C.K` against `Int.K`.
        assert!(match_pattern(
            &Ty::Proj(
                Box::new(Ty::Param(Symbol::Void)),
                ProtocolRef::bare(Symbol::Int),
                Symbol::Float
            ),
            &Ty::Proj(
                Box::new(Ty::Nominal(Symbol::Int, vec![])),
                ProtocolRef::bare(Symbol::Int),
                Symbol::Float,
            ),
            &mut bindings,
        ));
        assert_eq!(
            bindings.get(&Symbol::Void),
            Some(&Ty::Nominal(Symbol::Int, vec![]))
        );
    }

    #[test]
    fn match_pattern_binds_a_rigid_param_to_a_unification_variable() {
        // Conformance heads match against a receiver that still holds inference
        // variables, so a rigid param must bind to a `Var` actual rather than
        // treat it as an unconstrained wildcard (the regression that forced two
        // matchers before this arm ordering was fixed).
        let mut bindings = FxHashMap::default();
        assert!(match_pattern(
            &Ty::Param(Symbol::Bool),
            &Ty::Var(TyVar(4)),
            &mut bindings,
        ));
        assert_eq!(bindings.get(&Symbol::Bool), Some(&Ty::Var(TyVar(4))));
    }

    #[test]
    fn match_pattern_occurs_check_refuses_a_cyclic_binding() {
        let mut bindings = FxHashMap::default();
        // A against List<A> must not create the infinite binding A = List<A>.
        assert!(!match_pattern(
            &Ty::Param(Symbol::Bool),
            &Ty::Nominal(Symbol::Int, vec![Ty::Param(Symbol::Bool)]),
            &mut bindings,
        ));
        assert!(bindings.is_empty());
    }

    #[test]
    fn tyfold_with_default_leaves_is_the_identity() {
        struct Identity;
        impl TyFold for Identity {}

        let ty = Ty::Func(
            vec![
                Ty::Var(TyVar(7)),
                Ty::Param(Symbol::Int),
                Ty::Nominal(Symbol::Float, vec![Ty::Param(Symbol::Bool)]),
                Ty::Record(Row {
                    fields: vec![(Label::Named("x".into()), Ty::Nominal(Symbol::Int, vec![]))],
                    tail: Some(RowTail::Param(Symbol::Bool)),
                }),
                Ty::Any {
                    protocol: ProtocolRef::bare(Symbol::Bool),
                    assoc: vec![(Symbol::Int, Ty::Nominal(Symbol::String, vec![]))],
                },
                Ty::Proj(
                    Box::new(Ty::Param(Symbol::Int)),
                    ProtocolRef::bare(Symbol::Bool),
                    Symbol::Float,
                ),
            ],
            Box::new(Ty::Tuple(vec![Ty::Error])),
            EffectRow {
                effects: vec![EffectEntry::label(Symbol::Int)],
                tail: Some(EffTail::Var(EffVar(3))),
            },
        );

        assert_eq!(Identity.fold_ty(&ty), ty);
    }

    #[test]
    fn ty_try_visit_reaches_any_associated_bindings_and_can_stop() {
        let ty = Ty::Any {
            protocol: ProtocolRef::bare(Symbol::Bool),
            assoc: vec![(
                Symbol::Int,
                Ty::Tuple(vec![Ty::Nominal(Symbol::Float, vec![])]),
            )],
        };

        let result = ty.try_visit(&mut |visited| match visited {
            Ty::Nominal(symbol, _) if *symbol == Symbol::Float => ControlFlow::Break(*symbol),
            _ => ControlFlow::Continue(()),
        });

        assert_eq!(result, ControlFlow::Break(Symbol::Float));
    }

    #[test]
    fn predicate_try_visit_reaches_member_types() {
        let predicate = Predicate::HasMember {
            receiver: Ty::Nominal(Symbol::Int, vec![]),
            label: Label::Named("show".into()),
            member: Ty::Func(
                vec![],
                Box::new(Ty::Nominal(Symbol::String, vec![])),
                EffectRow::pure(),
            ),
        };
        let mut seen_string = false;
        let result = predicate.try_visit(&mut |visited| {
            if matches!(visited, Ty::Nominal(symbol, _) if *symbol == Symbol::String) {
                seen_string = true;
            }
            ControlFlow::<()>::Continue(())
        });

        assert_eq!(result, ControlFlow::Continue(()));
        assert!(seen_string);
    }

    #[test]
    fn ty_try_zip_reaches_any_associated_bindings() {
        let left = Ty::Any {
            protocol: ProtocolRef::bare(Symbol::Bool),
            assoc: vec![(
                Symbol::Int,
                Ty::Tuple(vec![Ty::Nominal(Symbol::Float, vec![])]),
            )],
        };
        let right = Ty::Any {
            protocol: ProtocolRef::bare(Symbol::Bool),
            assoc: vec![(
                Symbol::Int,
                Ty::Tuple(vec![Ty::Nominal(Symbol::String, vec![])]),
            )],
        };

        let mut saw_leaf_pair = false;
        assert!(left.try_zip(&right, &mut |left, right| {
            if matches!(left, Ty::Nominal(symbol, _) if *symbol == Symbol::Float)
                && matches!(right, Ty::Nominal(symbol, _) if *symbol == Symbol::String)
            {
                saw_leaf_pair = true;
            }
            true
        }));
        assert!(saw_leaf_pair);
    }

    #[test]
    fn ty_try_zip_rejects_any_associated_binding_mismatch() {
        let left = Ty::Any {
            protocol: ProtocolRef::bare(Symbol::Bool),
            assoc: vec![(Symbol::Int, Ty::Nominal(Symbol::Float, vec![]))],
        };
        let right = Ty::Any {
            protocol: ProtocolRef::bare(Symbol::Bool),
            assoc: vec![(Symbol::String, Ty::Nominal(Symbol::Float, vec![]))],
        };

        assert!(!left.try_zip(&right, &mut |_, _| true));
    }
}
