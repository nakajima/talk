//! Type representation for the Talk type system.
//!
//! Schemes are qualified types ∀ᾱ. P ⇒ τ (Jones, *A theory of qualified
//! types*, ESOP 1992): `SchemeParam.bounds` is the context P, restricted to
//! protocol predicates on quantified parameters. Quantified variables are
//! rigid `Ty::Param(Symbol)`s — first-class rigids keep GADT given-equalities
//! (milestone 8) out of the union-find entirely.
//!
//! Records are row types in the scoped-labels style (Leijen, *Extensible
//! Records with Scoped Labels*, Trends in FP 2005) — no lacks predicates.
//! Effect rows follow Koka (Leijen, *Koka: Programming with Row-polymorphic
//! Effect Types*, MSFP 2014), restricted to label-only entries: an effect's
//! operation signature lives in the catalog, never in the row.

use std::collections::BTreeSet;

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
}

/// An effect row: a set of effect symbols plus an optional tail.
/// Operation signatures live in the catalog, not here (Koka MSFP 2014's
/// effect labels, without the duplicate-label refinement — labels are a set).
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

impl Ty {
    pub fn unit() -> Ty {
        Ty::Nominal(Symbol::Void, vec![])
    }

    pub fn is_never(&self) -> bool {
        matches!(self, Ty::Nominal(sym, _) if *sym == Symbol::Never)
    }

    /// Substitute rigid `Param`s with types, and quantified row/effect tails
    /// with fresh tails. Used by scheme instantiation.
    pub fn substitute(
        &self,
        tys: &FxHashMap<Symbol, Ty>,
        effs: &FxHashMap<Symbol, EffTail>,
        rows: &FxHashMap<Symbol, RowTail>,
    ) -> Ty {
        match self {
            Ty::Var(v) => Ty::Var(*v),
            Ty::Param(sym) => tys.get(sym).cloned().unwrap_or(Ty::Param(*sym)),
            Ty::Nominal(sym, args) => Ty::Nominal(
                *sym,
                args.iter().map(|a| a.substitute(tys, effs, rows)).collect(),
            ),
            Ty::Func(params, ret, eff) => Ty::Func(
                params
                    .iter()
                    .map(|p| p.substitute(tys, effs, rows))
                    .collect(),
                Box::new(ret.substitute(tys, effs, rows)),
                substitute_eff(eff, effs),
            ),
            Ty::Tuple(items) => Ty::Tuple(
                items
                    .iter()
                    .map(|i| i.substitute(tys, effs, rows))
                    .collect(),
            ),
            Ty::Record(row) => {
                let mut fields: Vec<(Label, Ty)> = row
                    .fields
                    .iter()
                    .map(|(l, t)| (l.clone(), t.substitute(tys, effs, rows)))
                    .collect();
                let tail = match &row.tail {
                    // A row-parameter tail bound (in tys) to a concrete
                    // record splices its fields in — how monomorphization
                    // closes a row-polymorphic signature per call site.
                    Some(RowTail::Param(sym)) => match tys.get(sym) {
                        Some(Ty::Record(rest)) => {
                            for (label, ty) in &rest.fields {
                                fields.push((label.clone(), ty.substitute(tys, effs, rows)));
                            }
                            rest.tail.clone()
                        }
                        _ => Some(rows.get(sym).cloned().unwrap_or(RowTail::Param(*sym))),
                    },
                    other => other.clone(),
                };
                fields.sort_by(|(a, _), (b, _)| a.cmp(b));
                Ty::Record(Row { fields, tail })
            }
            Ty::Proj(base, protocol, assoc) => Ty::Proj(
                Box::new(base.substitute(tys, effs, rows)),
                *protocol,
                *assoc,
            ),
            Ty::Error => Ty::Error,
        }
    }
}

fn substitute_eff(eff: &EffectRow, effs: &FxHashMap<Symbol, EffTail>) -> EffectRow {
    let tail = match &eff.tail {
        Some(EffTail::Param(sym)) => Some(effs.get(sym).cloned().unwrap_or(EffTail::Param(*sym))),
        other => other.clone(),
    };
    EffectRow {
        effects: eff.effects.clone(),
        tail,
    }
}

/// Remap a symbol minted by the exporting module (ModuleId::Current from its
/// own point of view) to the importer's id for it; symbols referencing other
/// modules (core, transitive imports) keep theirs.
pub(crate) fn import_symbol(
    symbol: Symbol,
    target: crate::compiling::module::ModuleId,
) -> Symbol {
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
        match self {
            Ty::Var(v) => Ty::Var(*v),
            Ty::Param(sym) => Ty::Param(import_symbol(*sym, target)),
            Ty::Nominal(sym, args) => Ty::Nominal(
                import_symbol(*sym, target),
                args.iter().map(|a| a.import_symbols(target)).collect(),
            ),
            Ty::Func(params, ret, eff) => Ty::Func(
                params.iter().map(|p| p.import_symbols(target)).collect(),
                Box::new(ret.import_symbols(target)),
                eff.import_symbols(target),
            ),
            Ty::Tuple(items) => {
                Ty::Tuple(items.iter().map(|i| i.import_symbols(target)).collect())
            }
            Ty::Record(row) => Ty::Record(Row {
                fields: row
                    .fields
                    .iter()
                    .map(|(l, t)| (l.clone(), t.import_symbols(target)))
                    .collect(),
                tail: row.tail.as_ref().map(|tail| match tail {
                    RowTail::Var(v) => RowTail::Var(*v),
                    RowTail::Param(sym) => RowTail::Param(import_symbol(*sym, target)),
                }),
            }),
            Ty::Proj(base, protocol, assoc) => Ty::Proj(
                Box::new(base.import_symbols(target)),
                import_symbol(*protocol, target),
                import_symbol(*assoc, target),
            ),
            Ty::Error => Ty::Error,
        }
    }
}

impl EffectRow {
    pub fn import_symbols(&self, target: crate::compiling::module::ModuleId) -> EffectRow {
        EffectRow {
            effects: self
                .effects
                .iter()
                .map(|sym| import_symbol(*sym, target))
                .collect(),
            tail: self.tail.as_ref().map(|tail| match tail {
                EffTail::Var(v) => EffTail::Var(*v),
                EffTail::Param(sym) => EffTail::Param(import_symbol(*sym, target)),
            }),
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
                    bounds: p
                        .bounds
                        .iter()
                        .map(|b| Bound {
                            protocol: import_symbol(b.protocol, target),
                            assoc: b
                                .assoc
                                .iter()
                                .map(|(s, t)| {
                                    (import_symbol(*s, target), t.import_symbols(target))
                                })
                                .collect(),
                        })
                        .collect(),
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
            member_constraints: self
                .member_constraints
                .iter()
                .map(|mc| MemberConstraint {
                    receiver: mc.receiver.import_symbols(target),
                    label: mc.label.clone(),
                    member: mc.member.import_symbols(target),
                })
                .collect(),
            ty: self.ty.import_symbols(target),
        }
    }
}

/// One protocol obligation on a quantified parameter, together with the
/// associated-type bindings this use determined (Chakravarty, Keller &
/// Peyton Jones, *Associated Type Synonyms*, ICFP 2005). Keeping bindings on
/// the bound is the flattened form of a class constraint plus equality
/// constraints over its associated types.
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct Bound {
    pub protocol: Symbol,
    pub assoc: Vec<(Symbol, Ty)>,
}

impl Ty {
    /// Prepare a type for export across a module boundary: unification
    /// variables index a solver store that does not travel, so any leftover
    /// type variable degrades to `Error` (truly unknown) and leftover row
    /// tails become rigid params keyed by the owning binder (an unknown but
    /// fixed row — unifiable as a rigid tail on the importing side).
    pub fn sanitize_for_export(&self, owner: Symbol) -> Ty {
        match self {
            Ty::Var(_) => Ty::Error,
            Ty::Param(sym) => Ty::Param(*sym),
            Ty::Nominal(sym, args) => Ty::Nominal(
                *sym,
                args.iter().map(|a| a.sanitize_for_export(owner)).collect(),
            ),
            Ty::Func(params, ret, eff) => {
                let eff = EffectRow {
                    effects: eff.effects.clone(),
                    tail: match &eff.tail {
                        Some(EffTail::Var(_)) => Some(EffTail::Param(owner)),
                        other => other.clone(),
                    },
                };
                Ty::Func(
                    params.iter().map(|p| p.sanitize_for_export(owner)).collect(),
                    Box::new(ret.sanitize_for_export(owner)),
                    eff,
                )
            }
            Ty::Tuple(items) => Ty::Tuple(
                items.iter().map(|i| i.sanitize_for_export(owner)).collect(),
            ),
            Ty::Record(row) => Ty::Record(Row {
                fields: row
                    .fields
                    .iter()
                    .map(|(l, t)| (l.clone(), t.sanitize_for_export(owner)))
                    .collect(),
                tail: match &row.tail {
                    Some(RowTail::Var(_)) => Some(RowTail::Param(owner)),
                    other => other.clone(),
                },
            }),
            Ty::Proj(base, protocol, assoc) => Ty::Proj(
                Box::new(base.sanitize_for_export(owner)),
                *protocol,
                *assoc,
            ),
            Ty::Error => Ty::Error,
        }
    }
}

/// A quantified type parameter with its protocol bounds (the qualified-type
/// context P restricted to this parameter — Jones, ESOP 1992).
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct SchemeParam {
    pub symbol: Symbol,
    pub bounds: Vec<Bound>,
}

/// A type scheme ∀ᾱ. P ⇒ τ. Monomorphic bindings are schemes with no params.
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct Scheme {
    pub params: Vec<SchemeParam>,
    pub eff_params: Vec<Symbol>,
    pub row_params: Vec<Symbol>,
    /// Member uses the body could not discharge (`func g(x) { x.go() }`):
    /// qualified-type constraints over the scheme's parameters,
    /// re-emitted at each instantiation and discharged against the call's
    /// concrete receiver (Jones, *Qualified Types*, 1994).
    pub member_constraints: Vec<MemberConstraint>,
    pub ty: Ty,
}

/// One scheme-carried member obligation: `receiver` has a member
/// `label` of type `member` (types range over the scheme's parameters).
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct MemberConstraint {
    pub receiver: Ty,
    pub label: Label,
    pub member: Ty,
}

impl Scheme {
    pub fn mono(ty: Ty) -> Self {
        Scheme {
            params: vec![],
            member_constraints: vec![],
            eff_params: vec![],
            row_params: vec![],
            ty,
        }
    }

    /// Render for display/tests: quantified type params are named
    /// positionally (T0, T1, …); pure or quantified-tail effect rows are
    /// elided.
    pub fn render(&self) -> String {
        let mut names = FxHashMap::default();
        for (i, param) in self.params.iter().enumerate() {
            names.insert(param.symbol, format!("T{i}"));
        }
        let mut body = render_ty(&self.ty, &names);
        if !self.member_constraints.is_empty() {
            let constraints: Vec<String> = self
                .member_constraints
                .iter()
                .map(|c| {
                    format!(
                        "{}.{}: {}",
                        render_ty(&c.receiver, &names),
                        c.label,
                        render_ty(&c.member, &names)
                    )
                })
                .collect();
            body = format!("{body} where {}", constraints.join(", "));
        }
        if self.params.is_empty() {
            body
        } else {
            let params: Vec<String> = self
                .params
                .iter()
                .enumerate()
                .map(|(i, param)| {
                    if param.bounds.is_empty() {
                        format!("T{i}")
                    } else {
                        let bounds: Vec<String> = param
                            .bounds
                            .iter()
                            .map(|b| format!("{}", b.protocol))
                            .collect();
                        format!("T{i}: {}", bounds.join(" + "))
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
        Ty::Func(params, ret, eff) => {
            let params: Vec<String> = params.iter().map(|p| render_ty(p, param_names)).collect();
            let eff = render_effect_row(eff);
            format!("({}) -> {}{}", params.join(", "), render_ty(ret, param_names), eff)
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
        Ty::Proj(base, _, assoc) => {
            format!("{}.{assoc}", render_ty(base, param_names))
        }
        Ty::Error => "<error>".to_string(),
    }
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
