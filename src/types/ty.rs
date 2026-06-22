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
//! Row-Polymorphic Effect Types* (MSR-TR-2013-79), restricted to label-only
//! entries: an effect's operation signature lives in the catalog, never in
//! the row.

use std::{collections::BTreeSet, ops::ControlFlow};

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

/// An effect row: a set of effect symbols plus an optional tail.
/// Operation signatures live in the catalog, not here (Leijen's Koka effect
/// labels, without the duplicate-label refinement: labels are a set).
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct EffectRow {
    pub effects: BTreeSet<Symbol>,
    pub tail: Option<EffTail>,
}

impl EffectRow {
    /// The pure, closed row `<>`.
    pub fn pure() -> Self {
        EffectRow {
            effects: BTreeSet::new(),
            tail: None,
        }
    }

    /// An empty open row `<|e>` — the usual state of a function under
    /// inference, so its effects can still grow.
    pub fn open(tail: EffVar) -> Self {
        EffectRow {
            effects: BTreeSet::new(),
            tail: Some(EffTail::Var(tail)),
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
    /// A function type with its latent effect row.
    Func(Vec<Ty>, Box<Ty>, EffectRow),
    Tuple(Vec<Ty>),
    Record(Row),
    /// A first-class protocol existential `any P<Assoc = T>`. This is an
    /// existential package in the Mitchell/Plotkin sense: hidden payload type,
    /// protocol evidence, and associated-type equality evidence. The vector is
    /// canonicalized by associated-type symbol.
    Any {
        protocol: Symbol,
        assoc: Vec<(Symbol, Ty)>,
    },
    /// An associated-type projection `base.Assoc` through a protocol — an
    /// associated type synonym application (Chakravarty, Keller & Peyton
    /// Jones, *Associated Type Synonyms*, ICFP 2005; `<T as Trait>::Assoc`
    /// in Rust terms). The solver normalizes it through the conformance
    /// table once `base`'s head is concrete; over a rigid base it is
    /// irreducible and equal only to itself (projections are NOT injective —
    /// OutsideIn(X) treats type functions as free symbols).
    Proj(Box<Ty>, Symbol, Symbol),
    /// Poison type for error recovery: equalities involving it succeed
    /// silently so one mistake doesn't cascade.
    Error,
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
    Conforms { ty: Ty, protocol: Symbol },
    /// A member-access predicate carried by schemes when the receiver head is
    /// not yet known; the record-predicate lineage is Gaster/Jones.
    HasMember {
        receiver: Ty,
        label: Label,
        member: Ty,
    },
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
            Predicate::Conforms { ty, .. } => ty.try_visit(visitor)?,
            Predicate::HasMember {
                receiver, member, ..
            } => {
                receiver.try_visit(visitor)?;
                member.try_visit(visitor)?;
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
            Ty::Func(params, ret, _) => {
                for param in params {
                    param.try_visit(visitor)?;
                }
                ret.try_visit(visitor)?;
            }
            Ty::Record(row) => row.try_visit(visitor)?,
            Ty::Any { assoc, .. } => {
                for (_, ty) in assoc {
                    ty.try_visit(visitor)?;
                }
            }
            Ty::Proj(base, ..) => base.try_visit(visitor)?,
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
                    assoc: left_assoc, ..
                },
                Ty::Any {
                    assoc: right_assoc, ..
                },
            ) => {
                left_assoc.len() == right_assoc.len()
                    && left_assoc.iter().zip(right_assoc).all(
                        |((left_symbol, left_ty), (right_symbol, right_ty))| {
                            left_symbol == right_symbol && left_ty.try_zip(right_ty, visitor)
                        },
                    )
            }
            (Ty::Proj(left_base, ..), Ty::Proj(right_base, ..)) => {
                left_base.try_zip(right_base, visitor)
            }
            (Ty::Var(_), Ty::Var(_)) | (Ty::Param(_), Ty::Param(_)) | (Ty::Error, Ty::Error) => {
                true
            }
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
            Ty::Func(params, ret, eff) => Ty::Func(
                params.iter().map(|p| self.fold_ty(p)).collect(),
                Box::new(self.fold_ty(ret)),
                self.fold_eff(eff),
            ),
            Ty::Tuple(items) => Ty::Tuple(items.iter().map(|i| self.fold_ty(i)).collect()),
            Ty::Record(row) => Ty::Record(self.fold_row(row)),
            Ty::Any { protocol, assoc } => Ty::Any {
                protocol: self.fold_symbol(*protocol),
                assoc: assoc
                    .iter()
                    .map(|(symbol, ty)| (self.fold_symbol(*symbol), self.fold_ty(ty)))
                    .collect(),
            },
            Ty::Proj(base, protocol, assoc) => Ty::Proj(
                Box::new(self.fold_ty(base)),
                self.fold_symbol(*protocol),
                self.fold_symbol(*assoc),
            ),
            Ty::Error => Ty::Error,
        }
    }

    fn fold_var(&mut self, var: TyVar) -> Ty {
        Ty::Var(var)
    }

    fn fold_symbol(&mut self, symbol: Symbol) -> Symbol {
        symbol
    }

    fn fold_param(&mut self, symbol: Symbol) -> Ty {
        Ty::Param(self.fold_symbol(symbol))
    }

    fn fold_eff(&mut self, eff: &EffectRow) -> EffectRow {
        EffectRow {
            effects: eff.effects.iter().map(|s| self.fold_symbol(*s)).collect(),
            tail: self.fold_eff_tail(&eff.tail),
        }
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
/// becomes a rigid param keyed by the owning binder.
struct ExportSanitizer {
    owner: Symbol,
}

impl TyFold for ExportSanitizer {
    fn fold_var(&mut self, _var: TyVar) -> Ty {
        Ty::Error
    }

    fn fold_eff_tail(&mut self, tail: &Option<EffTail>) -> Option<EffTail> {
        match tail {
            Some(EffTail::Var(_)) => Some(EffTail::Param(self.owner)),
            other => other.clone(),
        }
    }

    fn fold_row_tail(&mut self, tail: &Option<RowTail>) -> Option<RowTail> {
        match tail {
            Some(RowTail::Var(_)) => Some(RowTail::Param(self.owner)),
            other => other.clone(),
        }
    }
}

impl Predicate {
    pub fn render_mono(&self) -> String {
        render_predicate(self, &FxHashMap::default())
    }

    pub fn substitute(
        &self,
        tys: &FxHashMap<Symbol, Ty>,
        effs: &FxHashMap<Symbol, EffTail>,
        rows: &FxHashMap<Symbol, RowTail>,
    ) -> Predicate {
        let mut folder = Substituter { tys, effs, rows };
        match self {
            Predicate::TypeEq(a, b) => Predicate::TypeEq(folder.fold_ty(a), folder.fold_ty(b)),
            Predicate::EffectEq(a, b) => {
                Predicate::EffectEq(folder.fold_eff(a), folder.fold_eff(b))
            }
            Predicate::RowEq(a, b) => Predicate::RowEq(folder.fold_row(a), folder.fold_row(b)),
            Predicate::Conforms { ty, protocol } => Predicate::Conforms {
                ty: folder.fold_ty(ty),
                protocol: *protocol,
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
        }
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
        match self {
            Predicate::TypeEq(a, b) => {
                Predicate::TypeEq(a.import_symbols(target), b.import_symbols(target))
            }
            Predicate::EffectEq(a, b) => {
                Predicate::EffectEq(a.import_symbols(target), b.import_symbols(target))
            }
            Predicate::RowEq(a, b) => {
                Predicate::RowEq(a.import_symbols(target), b.import_symbols(target))
            }
            Predicate::Conforms { ty, protocol } => Predicate::Conforms {
                ty: ty.import_symbols(target),
                protocol: import_symbol(*protocol, target),
            },
            Predicate::HasMember {
                receiver,
                label,
                member,
            } => Predicate::HasMember {
                receiver: receiver.import_symbols(target),
                label: label.clone(),
                member: member.import_symbols(target),
            },
        }
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
        ExportSanitizer { owner }.fold_ty(self)
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
    match (pattern, actual) {
        (Ty::Error, _) | (_, Ty::Error) => true,
        // A rigid param binds to whatever sits opposite it, *including* a
        // unification variable (conformance heads match against a receiver that
        // still holds inference variables). This must precede the variable
        // wildcards below, or such a binding would be silently skipped.
        (Ty::Param(param), ty) => match_param(*param, ty, bindings),
        (Ty::Var(_), _) | (_, Ty::Var(_)) | (_, Ty::Param(_)) => true,
        (Ty::Nominal(left, left_args), Ty::Nominal(right, right_args)) => {
            left == right
                && left_args.len() == right_args.len()
                && left_args
                    .iter()
                    .zip(right_args)
                    .all(|(left, right)| match_pattern(left, right, bindings))
        }
        (Ty::Tuple(left_items), Ty::Tuple(right_items)) => {
            left_items.len() == right_items.len()
                && left_items
                    .iter()
                    .zip(right_items)
                    .all(|(left, right)| match_pattern(left, right, bindings))
        }
        (Ty::Func(left_args, left_ret, _), Ty::Func(right_args, right_ret, _)) => {
            left_args.len() == right_args.len()
                && left_args
                    .iter()
                    .zip(right_args)
                    .all(|(left, right)| match_pattern(left, right, bindings))
                && match_pattern(left_ret, right_ret, bindings)
        }
        (Ty::Record(left), Ty::Record(right)) => {
            left.fields.len() == right.fields.len()
                && left.tail == right.tail
                && left.fields.iter().zip(&right.fields).all(
                    |((left_label, left_ty), (right_label, right_ty))| {
                        left_label == right_label && match_pattern(left_ty, right_ty, bindings)
                    },
                )
        }
        (
            Ty::Proj(left_base, left_protocol, left_assoc),
            Ty::Proj(right_base, right_protocol, right_assoc),
        ) => {
            left_protocol == right_protocol
                && left_assoc == right_assoc
                && match_pattern(left_base, right_base, bindings)
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
            left_protocol == right_protocol
                && left_assoc.len() == right_assoc.len()
                && left_assoc.iter().zip(right_assoc).all(
                    |((left_symbol, left_ty), (right_symbol, right_ty))| {
                        left_symbol == right_symbol && match_pattern(left_ty, right_ty, bindings)
                    },
                )
        }
        _ => false,
    }
}

fn match_param(param: Symbol, ty: &Ty, bindings: &mut FxHashMap<Symbol, Ty>) -> bool {
    if matches!(ty, Ty::Param(other) if *other == param) {
        return true;
    }
    if pattern_occurs(param, ty, bindings) {
        return false;
    }
    if let Some(existing) = bindings.get(&param).cloned() {
        return match_pattern(&existing, ty, bindings);
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
        Ty::Func(args, ret, _) => {
            args.iter().any(|ty| pattern_occurs(param, ty, bindings))
                || pattern_occurs(param, ret, bindings)
        }
        Ty::Record(row) => row
            .fields
            .iter()
            .any(|(_, ty)| pattern_occurs(param, ty, bindings)),
        Ty::Any { assoc, .. } => assoc
            .iter()
            .any(|(_, ty)| pattern_occurs(param, ty, bindings)),
        Ty::Proj(base, _, _) => pattern_occurs(param, base, bindings),
        Ty::Var(_) | Ty::Error => false,
    }
}

/// A quantified type parameter. The qualified context lives on `Scheme` as
/// predicates, not on individual parameters, matching Jones's qualified-type
/// shape while letting inline bounds and declaration `where` share one P.
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct SchemeParam {
    pub symbol: Symbol,
}

/// A type scheme `forall params. P => type`. Monomorphic bindings are schemes
/// with no params and no predicates.
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct Scheme {
    pub params: Vec<SchemeParam>,
    pub eff_params: Vec<Symbol>,
    pub row_params: Vec<Symbol>,
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
            ty,
        }
    }

    /// Render for display/tests: quantified type params are named
    /// positionally (T0, T1, …); simple parameter conformances render inline,
    /// and the remaining qualified context renders after `where`.
    pub fn render(&self) -> String {
        let mut names = FxHashMap::default();
        for (i, param) in self.params.iter().enumerate() {
            names.insert(param.symbol, format!("T{i}"));
        }

        let mut inline_bounds: FxHashMap<Symbol, Vec<Symbol>> = FxHashMap::default();
        let mut where_predicates = vec![];
        for predicate in &self.predicates {
            match predicate {
                Predicate::Conforms {
                    ty: Ty::Param(param),
                    protocol,
                } if self.params.iter().any(|p| p.symbol == *param) => {
                    inline_bounds.entry(*param).or_default().push(*protocol);
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
                .map(|(i, param)| match inline_bounds.get(&param.symbol) {
                    Some(bounds) if !bounds.is_empty() => {
                        let mut bounds: Vec<String> =
                            bounds.iter().map(|b| format!("{b}")).collect();
                        bounds.sort();
                        bounds.dedup();
                        format!("T{i}: {}", bounds.join(" & "))
                    }
                    _ => format!("T{i}"),
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
                format!("any {}", render_nominal_head(protocol))
            } else {
                let bindings: Vec<String> = assoc
                    .iter()
                    .map(|(symbol, ty)| format!("{symbol} = {}", render_ty(ty, param_names)))
                    .collect();
                format!(
                    "any {}<{}>",
                    render_nominal_head(protocol),
                    bindings.join(", ")
                )
            }
        }
        Ty::Proj(base, _, assoc) => {
            format!("{}.{assoc}", render_ty(base, param_names))
        }
        Ty::Error => "<error>".to_string(),
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
            format!("{}: {protocol}", render_ty(ty, param_names))
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
    }
}

fn render_full_effect_row(eff: &EffectRow) -> String {
    let mut labels: Vec<String> = eff.effects.iter().map(|sym| format!("'{sym}")).collect();
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
    let labels: Vec<String> = eff.effects.iter().map(|sym| format!("'{sym}")).collect();
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
                protocol: Symbol::Int,
                assoc: vec![(Symbol::Float, Ty::Param(Symbol::String))],
            },
            &Ty::Any {
                protocol: Symbol::Int,
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
                Symbol::Int,
                Symbol::Float
            ),
            &Ty::Proj(
                Box::new(Ty::Nominal(Symbol::Int, vec![])),
                Symbol::Int,
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
                    protocol: Symbol::Bool,
                    assoc: vec![(Symbol::Int, Ty::Nominal(Symbol::String, vec![]))],
                },
                Ty::Proj(
                    Box::new(Ty::Param(Symbol::Int)),
                    Symbol::Bool,
                    Symbol::Float,
                ),
            ],
            Box::new(Ty::Tuple(vec![Ty::Error])),
            EffectRow {
                effects: [Symbol::Int].into_iter().collect(),
                tail: Some(EffTail::Var(EffVar(3))),
            },
        );

        assert_eq!(Identity.fold_ty(&ty), ty);
    }

    #[test]
    fn ty_try_visit_reaches_any_associated_bindings_and_can_stop() {
        let ty = Ty::Any {
            protocol: Symbol::Bool,
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
            protocol: Symbol::Bool,
            assoc: vec![(
                Symbol::Int,
                Ty::Tuple(vec![Ty::Nominal(Symbol::Float, vec![])]),
            )],
        };
        let right = Ty::Any {
            protocol: Symbol::Bool,
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
            protocol: Symbol::Bool,
            assoc: vec![(Symbol::Int, Ty::Nominal(Symbol::Float, vec![]))],
        };
        let right = Ty::Any {
            protocol: Symbol::Bool,
            assoc: vec![(Symbol::String, Ty::Nominal(Symbol::Float, vec![]))],
        };

        assert!(!left.try_zip(&right, &mut |_, _| true));
    }
}
