//! Match coverage: exhaustiveness (is there a value no arm handles?) and
//! reachability (can any value reach each arm?). Both are the *usefulness*
//! question of Maranget, *Warnings for pattern matching* (JFP 2007): given
//! the rows above, is there a value this pattern row matches that they
//! miss? A match is exhaustive when a catch-all row appended below every
//! arm would be useless (section 5); an arm is unreachable when its own row is
//! useless against the arms above it (section 6). The matrix machinery uses
//! specialization S(c, P) and the default matrix D(P) (section 3.1) to answer the
//! coverage question over checked types and report example values for anything
//! missed. For GADTs, constructor universes are
//! filtered by satisfiability of the constructor result against the scrutinee
//! type, matching the type-directed applicability condition from Peyton
//! Jones, Vytiniotis, Weirich, and Washburn (ICFP 2006).

use rustc_hash::FxHashMap;

use crate::label::Label;
use crate::name_resolution::symbol::Symbol;
use crate::node_id::NodeID;
use crate::node_kinds::pattern::{Pattern, PatternKind, RecordFieldPatternKind};
use crate::types::catalog::TypeCatalog;
use crate::types::ty::Ty;

/// What checking one `match` found.
pub struct MatchReport {
    /// Example values no arm handles, rendered as patterns (`.blue`,
    /// `.some(false)`); empty means the match is exhaustive.
    pub missing: Vec<String>,
    /// Arms that can never run (the arms above them already match every
    /// value they could), by the arm's pattern node.
    pub unreachable_arms: Vec<NodeID>,
}

/// At most this many example values are reported for one match.
const WITNESS_CAP: usize = 3;

/// Check one `match`: `scrutinee` is the solved (zonked) type being
/// matched, `arms` the arm patterns in source order.
pub fn check_match(catalog: &TypeCatalog, scrutinee: &Ty, arms: &[&Pattern]) -> MatchReport {
    let coverage = Coverage { catalog };
    let rows: Vec<Vec<Pat>> = arms
        .iter()
        .map(|p| vec![coverage.lower(p, scrutinee)])
        .collect();
    let tys = vec![scrutinee.clone()];

    let mut unreachable_arms = vec![];
    for (i, arm) in arms.iter().enumerate() {
        let Some(row) = rows.get(i) else { continue };
        if coverage.useful(&rows[..i], &tys, row, 1).is_empty() {
            unreachable_arms.push(arm.id);
        }
    }

    let missing = coverage
        .useful(&rows, &tys, &[Pat::Wild], WITNESS_CAP)
        .iter()
        .filter_map(|witness| witness.first().map(render))
        .collect();

    MatchReport {
        missing,
        unreachable_arms,
    }
}

/// A pattern reduced to what coverage cares about: a constructor with
/// sub-patterns, a catch-all (wildcards and binders both match
/// everything), or alternatives.
#[derive(Clone, Debug, PartialEq)]
enum Pat {
    Wild,
    Ctor(Ctor, Vec<Pat>),
    Or(Vec<Pat>),
}

#[derive(Clone, Debug, PartialEq)]
enum Ctor {
    Bool(bool),
    Int(i128),
    /// Float literals compare by their source text — two spellings of the
    /// same value count as different patterns, which only ever
    /// under-reports reachability, never coverage.
    Float(String),
    Character(String),
    Str(String),
    /// One enum case: the enum's symbol and the case's name.
    Variant(Symbol, String),
    Tuple(usize),
    /// A record with exactly these (sorted) fields.
    Record(Vec<Label>),
}

struct Coverage<'a> {
    catalog: &'a TypeCatalog,
}

impl Coverage<'_> {
    fn pattern_ty(ty: &Ty) -> &Ty {
        match ty {
            Ty::Borrow(_, inner) => Self::pattern_ty(inner),
            other => other,
        }
    }

    /// Reduce an AST pattern at the given column type. Anything this
    /// analysis doesn't understand becomes a catch-all — over-approximating
    /// what a pattern matches can only silence reports, never invent them.
    fn lower(&self, pattern: &Pattern, ty: &Ty) -> Pat {
        let ty = Self::pattern_ty(ty);
        match &pattern.kind {
            PatternKind::Wildcard | PatternKind::Bind(_) => Pat::Wild,
            PatternKind::LiteralTrue => Pat::Ctor(Ctor::Bool(true), vec![]),
            PatternKind::LiteralFalse => Pat::Ctor(Ctor::Bool(false), vec![]),
            PatternKind::LiteralInt(text) => match text.replace('_', "").parse::<i128>() {
                Ok(value) => Pat::Ctor(Ctor::Int(value), vec![]),
                Err(_) => Pat::Wild,
            },
            PatternKind::LiteralFloat(text) => Pat::Ctor(Ctor::Float(text.clone()), vec![]),
            PatternKind::LiteralCharacter(text) => match crate::parsing::lexing::unescape(text) {
                Ok(value) => Pat::Ctor(Ctor::Character(value), vec![]),
                Err(_) => Pat::Wild,
            },
            PatternKind::LiteralString(text) => match crate::parsing::lexing::unescape(text) {
                Ok(value) => Pat::Ctor(Ctor::Str(value), vec![]),
                Err(_) => Pat::Wild,
            },
            PatternKind::Or(items) => Pat::Or(items.iter().map(|p| self.lower(p, ty)).collect()),
            PatternKind::Tuple(items) => {
                let mut item_tys = match ty {
                    Ty::Tuple(tys) => tys.clone(),
                    _ => vec![],
                };
                item_tys.resize(items.len(), Ty::Error);
                let args = items
                    .iter()
                    .zip(&item_tys)
                    .map(|(p, t)| self.lower(p, t))
                    .collect();
                Pat::Ctor(Ctor::Tuple(items.len()), args)
            }
            PatternKind::Variant {
                enum_name,
                variant_name,
                fields,
                ..
            } => {
                let enum_symbol = match enum_name {
                    Some(name) => name.symbol().ok(),
                    None => match ty {
                        Ty::Nominal(symbol, _) => Some(*symbol),
                        _ => None,
                    },
                };
                // A case name the catalog doesn't know already errored as
                // an unknown member; treating it as a catch-all keeps that
                // from cascading into a bogus coverage report.
                let known = enum_symbol.is_some_and(|s| {
                    self.catalog
                        .enums
                        .get(&s)
                        .is_some_and(|info| info.variants.contains_key(variant_name))
                });
                let Some(enum_symbol) = enum_symbol.filter(|_| known) else {
                    return Pat::Wild;
                };
                let ctor = Ctor::Variant(enum_symbol, variant_name.clone());
                let arity = self.arity(&ctor);
                let field_tys = self.ctor_field_tys(&ctor, ty);
                let mut args: Vec<Pat> = fields
                    .iter()
                    .zip(&field_tys)
                    .map(|(p, t)| self.lower(p, t))
                    .collect();
                args.resize(arity, Pat::Wild);
                Pat::Ctor(ctor, args)
            }
            PatternKind::Record { fields } => {
                let labels = match ty {
                    Ty::Record(row) => row.fields.iter().map(|(l, _)| l.clone()).collect(),
                    _ => {
                        let mut labels: Vec<Label> = fields
                            .iter()
                            .filter_map(|f| match &f.kind {
                                RecordFieldPatternKind::Bind(name)
                                | RecordFieldPatternKind::Equals { name, .. } => {
                                    Some(Label::Named(name.name_str()))
                                }
                                RecordFieldPatternKind::Rest => None,
                            })
                            .collect();
                        labels.sort();
                        labels
                    }
                };
                let field_tys: FxHashMap<&Label, &Ty> = match ty {
                    Ty::Record(row) => row.fields.iter().map(|(l, t)| (l, t)).collect(),
                    _ => FxHashMap::default(),
                };
                let mut by_label: FxHashMap<Label, Pat> = FxHashMap::default();
                for field in fields {
                    match &field.kind {
                        RecordFieldPatternKind::Bind(name) => {
                            by_label.insert(Label::Named(name.name_str()), Pat::Wild);
                        }
                        RecordFieldPatternKind::Equals { name, value, .. } => {
                            let label = Label::Named(name.name_str());
                            let value_ty = field_tys.get(&label).copied().unwrap_or(&Ty::Error);
                            by_label.insert(label, self.lower(value, value_ty));
                        }
                        RecordFieldPatternKind::Rest => {}
                    }
                }
                let args = labels
                    .iter()
                    .map(|l| by_label.remove(l).unwrap_or(Pat::Wild))
                    .collect();
                Pat::Ctor(Ctor::Record(labels), args)
            }
            PatternKind::Struct { .. } => Pat::Wild,
        }
    }

    fn ctor_possible(&self, ctor: &Ctor, ty: &Ty) -> bool {
        let ty = Self::pattern_ty(ty);
        match ctor {
            Ctor::Bool(_) => matches!(ty, Ty::Nominal(symbol, _) if *symbol == Symbol::Bool),
            Ctor::Int(_) | Ctor::Float(_) => true,
            Ctor::Character(_) => {
                matches!(ty, Ty::Nominal(symbol, _) if *symbol == Symbol::Character)
            }
            Ctor::Str(_) => matches!(
                ty,
                Ty::Nominal(symbol, _)
                    if *symbol == Symbol::String || *symbol == Symbol::Substring
            ),
            Ctor::Tuple(n) => matches!(ty, Ty::Tuple(items) if items.len() == *n),
            Ctor::Record(labels) => {
                matches!(ty, Ty::Record(row) if row.fields.len() == labels.len())
            }
            Ctor::Variant(enum_symbol, name) => {
                self.variant_instantiation(*enum_symbol, name, ty).is_some()
            }
        }
    }

    fn variant_instantiation(
        &self,
        enum_symbol: Symbol,
        name: &str,
        ty: &Ty,
    ) -> Option<crate::types::variant::VariantInstantiation> {
        let ty = Self::pattern_ty(ty);
        let Ty::Nominal(symbol, args) = ty else {
            return None;
        };
        if *symbol != enum_symbol {
            return None;
        }
        let info = self.catalog.enums.get(&enum_symbol)?;
        let variant = info.variants.get(name)?;
        let tys: FxHashMap<Symbol, Ty> = info
            .params
            .iter()
            .map(|param| param.symbol)
            .zip(args.clone())
            .collect();
        let no_effs = FxHashMap::default();
        let no_rows = FxHashMap::default();
        variant
            .instantiate(&tys, &no_effs, &no_rows)
            .refined_by_result(ty)
    }

    fn arity(&self, ctor: &Ctor) -> usize {
        match ctor {
            Ctor::Bool(_) | Ctor::Int(_) | Ctor::Float(_) | Ctor::Character(_) | Ctor::Str(_) => 0,
            Ctor::Tuple(n) => *n,
            Ctor::Record(labels) => labels.len(),
            Ctor::Variant(enum_symbol, name) => self
                .catalog
                .enums
                .get(enum_symbol)
                .and_then(|info| info.variants.get(name))
                .map(|variant| variant.argument_types().len())
                .unwrap_or(0),
        }
    }

    /// The column types a constructor's sub-patterns match at, given the
    /// constructor's own column type.
    fn ctor_field_tys(&self, ctor: &Ctor, ty: &Ty) -> Vec<Ty> {
        let ty = Self::pattern_ty(ty);
        match ctor {
            Ctor::Bool(_) | Ctor::Int(_) | Ctor::Float(_) | Ctor::Character(_) | Ctor::Str(_) => {
                vec![]
            }
            Ctor::Tuple(n) => {
                let mut tys = match ty {
                    Ty::Tuple(items) => items.clone(),
                    _ => vec![],
                };
                tys.resize(*n, Ty::Error);
                tys
            }
            Ctor::Record(labels) => {
                let fields: FxHashMap<&Label, &Ty> = match ty {
                    Ty::Record(row) => row.fields.iter().map(|(l, t)| (l, t)).collect(),
                    _ => FxHashMap::default(),
                };
                labels
                    .iter()
                    .map(|l| fields.get(l).copied().cloned().unwrap_or(Ty::Error))
                    .collect()
            }
            Ctor::Variant(enum_symbol, name) => self
                .variant_instantiation(*enum_symbol, name, ty)
                .map(|instantiation| instantiation.argument_types)
                .unwrap_or_default(),
        }
    }

    /// Every constructor of the column's type, when the type has a known,
    /// finite set: Bool, enums, and the single-constructor tuple/record
    /// types. `None` for everything else (Int, String, type variables, …)
    /// — those are only ever covered by a catch-all.
    fn universe(&self, ty: &Ty) -> Option<Vec<Ctor>> {
        let ty = Self::pattern_ty(ty);
        match ty {
            Ty::Nominal(symbol, _) if *symbol == Symbol::Bool => {
                Some(vec![Ctor::Bool(false), Ctor::Bool(true)])
            }
            Ty::Nominal(symbol, _) => {
                let info = self.catalog.enums.get(symbol)?;
                Some(
                    info.variants
                        .keys()
                        .map(|name| Ctor::Variant(*symbol, name.clone()))
                        .filter(|ctor| self.ctor_possible(ctor, ty))
                        .collect(),
                )
            }
            Ty::Tuple(items) => Some(vec![Ctor::Tuple(items.len())]),
            Ty::Record(row) => Some(vec![Ctor::Record(
                row.fields.iter().map(|(l, _)| l.clone()).collect(),
            )]),
            _ => None,
        }
    }

    /// S(c, P) for one row (§3.1): keep it if it can match `c`, replacing
    /// the head with its sub-patterns. Or-heads expand to a row per
    /// alternative.
    fn specialize(&self, row: &[Pat], ctor: &Ctor) -> Vec<Vec<Pat>> {
        let Some((head, rest)) = row.split_first() else {
            return vec![];
        };
        match head {
            Pat::Wild => {
                let mut out = vec![Pat::Wild; self.arity(ctor)];
                out.extend_from_slice(rest);
                vec![out]
            }
            Pat::Ctor(c, args) if c == ctor => {
                let mut out = args.clone();
                out.resize(self.arity(ctor), Pat::Wild);
                out.extend_from_slice(rest);
                vec![out]
            }
            Pat::Ctor(..) => vec![],
            Pat::Or(alts) => alts
                .iter()
                .flat_map(|alt| {
                    let mut row = vec![alt.clone()];
                    row.extend_from_slice(rest);
                    self.specialize(&row, ctor)
                })
                .collect(),
        }
    }

    /// D(P) for one row (§3.1): the rows that still apply when the value's
    /// head constructor is not in the column.
    fn default_row(row: &[Pat]) -> Vec<Vec<Pat>> {
        let Some((head, rest)) = row.split_first() else {
            return vec![];
        };
        match head {
            Pat::Wild => vec![rest.to_vec()],
            Pat::Ctor(..) => vec![],
            Pat::Or(alts) => alts
                .iter()
                .flat_map(|alt| {
                    let mut row = vec![alt.clone()];
                    row.extend_from_slice(rest);
                    Self::default_row(&row)
                })
                .collect(),
        }
    }

    /// The constructors mentioned in the first column.
    fn column_ctors(rows: &[Vec<Pat>]) -> Vec<Ctor> {
        fn add(pat: &Pat, out: &mut Vec<Ctor>) {
            match pat {
                Pat::Wild => {}
                Pat::Ctor(c, _) => {
                    if !out.contains(c) {
                        out.push(c.clone());
                    }
                }
                Pat::Or(alts) => {
                    for alt in alts {
                        add(alt, out);
                    }
                }
            }
        }
        let mut out = vec![];
        for row in rows {
            if let Some(head) = row.first() {
                add(head, &mut out);
            }
        }
        out
    }

    /// Maranget's U (§3.1) extended to return example values (the witness
    /// construction of §5): is there a value `q` matches that no row in
    /// `rows` matches? Returns up to `cap` such values as pattern rows;
    /// empty means `q` is useless.
    fn useful(&self, rows: &[Vec<Pat>], tys: &[Ty], q: &[Pat], cap: usize) -> Vec<Vec<Pat>> {
        let Some((q_head, q_rest)) = q.split_first() else {
            // No columns left: q matches everything here, so it is useful
            // exactly when no row got here first.
            return if rows.is_empty() {
                vec![vec![]]
            } else {
                vec![]
            };
        };
        let (ty_head, ty_rest) = match tys.split_first() {
            Some((head, rest)) => (head.clone(), rest),
            None => (Ty::Error, &[] as &[Ty]),
        };
        match q_head {
            Pat::Or(alts) => {
                let mut out: Vec<Vec<Pat>> = vec![];
                for alt in alts {
                    if out.len() >= cap {
                        break;
                    }
                    let mut q = vec![alt.clone()];
                    q.extend_from_slice(q_rest);
                    out.extend(self.useful(rows, tys, &q, cap - out.len()));
                }
                out
            }
            Pat::Ctor(ctor, args) => {
                if !self.ctor_possible(ctor, &ty_head) {
                    return vec![];
                }
                let mut q = args.clone();
                q.resize(self.arity(ctor), Pat::Wild);
                q.extend_from_slice(q_rest);
                self.useful_under(rows, &ty_head, ty_rest, ctor, &q, cap)
            }
            Pat::Wild => {
                let seen = Self::column_ctors(rows);
                let universe = self.universe(&ty_head);
                match &universe {
                    // Every constructor of the type is mentioned: a value
                    // missed here must be missed under one of them.
                    Some(all) if all.iter().all(|c| seen.contains(c)) => {
                        let mut out: Vec<Vec<Pat>> = vec![];
                        for ctor in all {
                            if out.len() >= cap {
                                break;
                            }
                            let mut q = vec![Pat::Wild; self.arity(ctor)];
                            q.extend_from_slice(q_rest);
                            out.extend(self.useful_under(
                                rows,
                                &ty_head,
                                ty_rest,
                                ctor,
                                &q,
                                cap - out.len(),
                            ));
                        }
                        out
                    }
                    // Some constructor is unmentioned (or the type has
                    // infinitely many): values built from it fall through
                    // to the default matrix.
                    _ => {
                        let d_rows: Vec<Vec<Pat>> =
                            rows.iter().flat_map(|r| Self::default_row(r)).collect();
                        let tails = self.useful(&d_rows, ty_rest, q_rest, cap);
                        if tails.is_empty() {
                            return vec![];
                        }
                        // Name the missing heads when the type's
                        // constructors are known; `_` otherwise.
                        let heads: Vec<Pat> = match &universe {
                            Some(all) => all
                                .iter()
                                .filter(|c| !seen.contains(c))
                                .map(|c| Pat::Ctor(c.clone(), vec![Pat::Wild; self.arity(c)]))
                                .collect(),
                            None => vec![Pat::Wild],
                        };
                        let mut out: Vec<Vec<Pat>> = vec![];
                        'heads: for head in heads {
                            for tail in &tails {
                                if out.len() >= cap {
                                    break 'heads;
                                }
                                let mut witness = vec![head.clone()];
                                witness.extend_from_slice(tail);
                                out.push(witness);
                            }
                        }
                        out
                    }
                }
            }
        }
    }

    /// One constructor's branch of `useful`: specialize the matrix and
    /// query for `ctor`, recurse, and rebuild the constructor around each
    /// witness that comes back.
    fn useful_under(
        &self,
        rows: &[Vec<Pat>],
        ty_head: &Ty,
        ty_rest: &[Ty],
        ctor: &Ctor,
        q: &[Pat],
        cap: usize,
    ) -> Vec<Vec<Pat>> {
        let s_rows: Vec<Vec<Pat>> = rows.iter().flat_map(|r| self.specialize(r, ctor)).collect();
        let mut s_tys = self.ctor_field_tys(ctor, ty_head);
        s_tys.extend_from_slice(ty_rest);
        self.useful(&s_rows, &s_tys, q, cap)
            .into_iter()
            .map(|witness| rebuild(ctor, self.arity(ctor), witness))
            .collect()
    }
}

/// Fold a witness's first `arity` columns back under their constructor.
fn rebuild(ctor: &Ctor, arity: usize, mut witness: Vec<Pat>) -> Vec<Pat> {
    if witness.len() < arity {
        witness.resize(arity, Pat::Wild);
    }
    let rest = witness.split_off(arity);
    let mut out = vec![Pat::Ctor(ctor.clone(), witness)];
    out.extend(rest);
    out
}

/// Render a witness the way the user would write it as a pattern.
fn render(pat: &Pat) -> String {
    let list = |pats: &[Pat]| pats.iter().map(render).collect::<Vec<_>>().join(", ");
    match pat {
        Pat::Wild => "_".into(),
        Pat::Or(alts) => alts.iter().map(render).collect::<Vec<_>>().join(" | "),
        Pat::Ctor(ctor, args) => match ctor {
            Ctor::Bool(value) => value.to_string(),
            Ctor::Int(value) => value.to_string(),
            Ctor::Float(text) => text.clone(),
            Ctor::Character(text) => format!("'{text}'"),
            Ctor::Str(text) => format!("{text:?}"),
            Ctor::Variant(_, name) if args.is_empty() => format!(".{name}"),
            Ctor::Variant(_, name) => format!(".{name}({})", list(args)),
            Ctor::Tuple(_) => format!("({})", list(args)),
            Ctor::Record(labels) => {
                let fields: Vec<String> = labels
                    .iter()
                    .zip(args)
                    .map(|(label, arg)| format!("{label}: {}", render(arg)))
                    .collect();
                format!("{{ {} }}", fields.join(", "))
            }
        },
    }
}
