//! Pattern-match compilation to decision trees.
//!
//! A faithful implementation of Luc Maranget, *Compiling Pattern Matching to
//! Good Decision Trees*, ML Workshop 2008: a pattern matrix over a vector of
//! subjects ("occurrences"), consumed column by column. Variant columns
//! dispatch with one `switch` over `get_tag` (the paper's constructor
//! split, §2.2 — specialization S(c, P) per constructor, default matrix
//! D(P) for the rest); literal columns test with an equality chain (the
//! constant switch restricted to constants that occur); or-patterns expand
//! by row duplication (§2.2); irrefutable aggregate columns (tuples,
//! records) expand in place without branching. Column choice is the
//! leftmost refutable column of the first row (the baseline heuristic the
//! paper measures the others against, §7.1).
//!
//! Arm bodies are lowered exactly once, into a continuation taking the
//! arm's binders as a tuple — default rows reach the same arm from several
//! switch cases, and sharing leaves through join points is the paper's
//! "maximal sharing" of output states (§5); in CPS a join point is just a
//! function (Maurer, Downen, Ariola & Peyton Jones, *Compiling without
//! Continuations*, PLDI 2017).
//!
//! The matrix carries each occurrence's *checker* type alongside its λ_G
//! value: payload and field types come from the catalog through the
//! checker's instantiations, which λ_G's argument-erased `Variant` type no
//! longer names.

use rustc_hash::FxHashMap;

use crate::lambda_g::expr::{CmpOp, ExprId, Op};
use crate::lambda_g::program::Label;
use crate::name_resolution::symbol::Symbol;
use crate::node_kinds::{
    match_arm::MatchArm,
    pattern::{Pattern, PatternKind, RecordFieldPatternKind},
};
use crate::types::ty::Ty as CheckTy;

use super::{Binding, Ctx, Lowering};

/// A matrix column's subject: a pure λ_G value plus its checker type.
#[derive(Clone)]
struct Occurrence {
    value: ExprId,
    ty: CheckTy,
}

/// A row's pattern cell: a source pattern, or a wildcard introduced by
/// specialization (default rows, consumed binds, record-shorthand binds).
#[derive(Clone, Copy)]
enum Pat<'p> {
    Wild,
    Source(&'p Pattern),
}

impl Pat<'_> {
    /// Wildcards and binds match anything; binds are recorded into the row
    /// when their column is consumed.
    fn is_irrefutable(self) -> bool {
        match self {
            Pat::Wild => true,
            Pat::Source(p) => matches!(p.kind, PatternKind::Wildcard | PatternKind::Bind(_)),
        }
    }
}

#[derive(Clone)]
struct Row<'p> {
    pats: Vec<Pat<'p>>,
    /// Binders whose columns have been consumed: symbol → bound value.
    binds: Vec<(Symbol, ExprId)>,
    /// Index of the source arm this row came from.
    arm: usize,
}

impl<'p> Row<'p> {
    /// Drop `column`, recording a bind if the cell was a binder.
    fn without_column(&self, column: usize, occ: &Occurrence) -> Row<'p> {
        let mut row = self.clone();
        let pat = row.pats.remove(column);
        if let Pat::Source(p) = pat
            && let PatternKind::Bind(name) = &p.kind
            && let Ok(symbol) = name.symbol()
        {
            row.binds.push((symbol, occ.value));
        }
        row
    }

    /// Replace `column` with `cells`, recording a bind if the cell was a
    /// binder (the irrefutable half of specialization: a wildcard row is
    /// compatible with every constructor).
    fn with_column_expanded(
        &self,
        column: usize,
        occ: &Occurrence,
        cells: Vec<Pat<'p>>,
    ) -> Row<'p> {
        let mut row = self.without_column(column, occ);
        row.pats.splice(column..column, cells);
        row
    }
}

/// One arm's join point, created at the first leaf that reaches it and
/// shared by every later one.
struct ArmTarget {
    binders: Vec<Symbol>,
    label: Option<Label>,
}

/// Compile a `match` whose scrutinee is already lowered to the pure value
/// `value` (checker type `scrutinee_ty`), delivering each arm's value to
/// `k`. Returns the ⊥-typed decision tree.
pub(super) fn compile_match(
    lowering: &mut Lowering<'_>,
    value: ExprId,
    scrutinee_ty: CheckTy,
    arms: &[MatchArm],
    ctx: &Ctx,
    k: ExprId,
) -> ExprId {
    let targets = arms
        .iter()
        .map(|arm| {
            // Canonical binder order for the arm's join point; or-pattern
            // alternatives bind the same names, so dedup keeps the first.
            let mut binders: Vec<Symbol> = vec![];
            for (_, symbol) in arm.pattern.collect_binders() {
                if !binders.contains(&symbol) {
                    binders.push(symbol);
                }
            }
            ArmTarget {
                binders,
                label: None,
            }
        })
        .collect();
    let rows = arms
        .iter()
        .enumerate()
        .map(|(arm, a)| Row {
            pats: vec![Pat::Source(&a.pattern)],
            binds: vec![],
            arm,
        })
        .collect();
    let occs = vec![Occurrence {
        value,
        ty: scrutinee_ty,
    }];
    MatchCompiler {
        lowering,
        ctx,
        k,
        arms,
        targets,
        trap: None,
    }
    .compile(occs, rows)
}

struct MatchCompiler<'l, 'a, 'p> {
    lowering: &'l mut Lowering<'a>,
    ctx: &'l Ctx,
    /// The continuation every arm's value flows to.
    k: ExprId,
    arms: &'p [MatchArm],
    targets: Vec<ArmTarget>,
    /// The shared no-row-matched target (bodyless, so both engines trap) —
    /// reachable only if a non-exhaustive match slips past the checker.
    trap: Option<Label>,
}

impl<'p> MatchCompiler<'_, '_, 'p> {
    /// CC(o⃗, P → A) — the paper's compilation scheme (§3, Fig. 5).
    fn compile(&mut self, occs: Vec<Occurrence>, rows: Vec<Row<'p>>) -> ExprId {
        // Empty matrix: no row can match.
        let Some(first) = rows.first() else {
            return self.trap_jump();
        };
        // First row all-irrefutable: it matches (Fig. 5, case 1).
        let Some(column) = first.pats.iter().position(|p| !p.is_irrefutable()) else {
            let row = first.clone();
            return self.leaf(&occs, row);
        };
        // Or-patterns in the selected column expand by row duplication
        // before the column is examined (§2.2).
        let has_or = rows.iter().any(|row| {
            matches!(row.pats[column], Pat::Source(p) if matches!(p.kind, PatternKind::Or(_)))
        });
        if has_or {
            let expanded = expand_or(rows, column);
            return self.compile(occs, expanded);
        }
        let Pat::Source(head) = rows[0].pats[column] else {
            // position() above only selects refutable (source) cells.
            self.lowering
                .diagnostics
                .push("lowering: pattern matrix invariant broken".into());
            return self.trap_jump();
        };
        match &head.kind {
            PatternKind::Variant { .. } => self.variant_column(occs, rows, column),
            PatternKind::LiteralInt(_)
            | PatternKind::LiteralFloat(_)
            | PatternKind::LiteralTrue
            | PatternKind::LiteralFalse => self.literal_column(occs, rows, column, head),
            PatternKind::Tuple(_) => self.tuple_column(occs, rows, column),
            PatternKind::Record { .. } => self.record_column(occs, rows, column),
            other => {
                self.lowering.diagnostics.push(format!(
                    "lowering: pattern not yet supported: {other:?}"
                ));
                self.trap_jump()
            }
        }
    }

    // ----- Leaves -----------------------------------------------------------

    /// The first row matches: gather its binds and jump to its arm's join
    /// point with the bound values.
    fn leaf(&mut self, occs: &[Occurrence], row: Row<'p>) -> ExprId {
        let mut binds: FxHashMap<Symbol, ExprId> = row.binds.iter().copied().collect();
        for (pat, occ) in row.pats.iter().zip(occs) {
            if let Pat::Source(p) = pat
                && let PatternKind::Bind(name) = &p.kind
                && let Ok(symbol) = name.symbol()
            {
                binds.insert(symbol, occ.value);
            }
        }
        let binders = self.targets[row.arm].binders.clone();
        let mut values = Vec::with_capacity(binders.len());
        for symbol in &binders {
            match binds.get(symbol) {
                Some(&value) => values.push(value),
                None => {
                    self.lowering.diagnostics.push(format!(
                        "lowering: pattern alternative does not bind {symbol} \
                         (alternatives must bind the same names)"
                    ));
                    values.push(self.lowering.p.void());
                }
            }
        }
        let label = match self.targets[row.arm].label {
            Some(label) => label,
            None => self.make_arm(row.arm, &binders, &values),
        };
        let arg = self.lowering.p.tuple(&values);
        let func = self.lowering.p.func_ref(label);
        self.lowering.p.app(func, arg)
    }

    /// Lower the arm's body once, as a join point taking its binders.
    fn make_arm(&mut self, arm: usize, binders: &[Symbol], values: &[ExprId]) -> Label {
        let tys: Vec<_> = values
            .iter()
            .map(|v| self.lowering.p.expr_ty(*v))
            .collect();
        let dom = self.lowering.p.ty_tuple(&tys);
        let bot = self.lowering.p.ty_bot();
        let label = self.lowering.p.func("arm", dom, bot);
        self.targets[arm].label = Some(label);

        let var = self.lowering.p.var(label);
        let mut inner = self.ctx.clone();
        // Mutated binders are assignment-converted like any local (ORBIT —
        // Kranz et al., 1986).
        let mut celled: Vec<(Symbol, ExprId)> = vec![];
        for (i, symbol) in binders.iter().enumerate() {
            let value = self.lowering.p.extract(var, i as u32);
            if inner.cellable.contains(symbol) {
                celled.push((*symbol, value));
            } else {
                inner.env.insert(*symbol, Binding::Value(value));
            }
        }
        let body_block = &self.arms[arm].body;
        let k = self.k;
        let body = self
            .lowering
            .with_cells(&celled, &mut inner, |this, inner| {
                this.lower_block(body_block, inner, k)
            });
        self.lowering.p.set_body(label, body);
        label
    }

    // ----- Variant columns (switch over get_tag) ------------------------------

    fn variant_column(
        &mut self,
        occs: Vec<Occurrence>,
        rows: Vec<Row<'p>>,
        column: usize,
    ) -> ExprId {
        let occ = occs[column].clone();
        let CheckTy::Nominal(enum_symbol, enum_args) = &occ.ty else {
            self.lowering.diagnostics.push(format!(
                "lowering: variant pattern on a non-enum scrutinee {:?}",
                occ.ty
            ));
            return self.trap_jump();
        };
        let Some(info) = self.lowering.enum_info(*enum_symbol) else {
            self.lowering.diagnostics.push(format!(
                "lowering: no enum catalog entry for {enum_symbol}"
            ));
            return self.trap_jump();
        };
        let subst: FxHashMap<Symbol, CheckTy> = info
            .params
            .iter()
            .copied()
            .zip(enum_args.iter().cloned())
            .collect();

        let void_ty = self.lowering.p.ty_void();
        let bot = self.lowering.p.ty_bot();
        let trap = self.trap_label();
        let trap_ref = self.lowering.p.func_ref(trap);

        // One switch arm per declared variant, in tag (declaration) order:
        // S(c, P) for each constructor c (Fig. 5, case 2). Tags absent
        // from the matrix specialize to an empty matrix, which is the trap.
        let mut arm_refs = Vec::with_capacity(info.variants.len());
        for (variant_name, variant) in info.variants.iter() {
            let payload_occs: Vec<Occurrence> = variant
                .payloads
                .iter()
                .enumerate()
                .map(|(i, payload)| {
                    let payload_ty =
                        payload.substitute(&subst, &Default::default(), &Default::default());
                    let lam_ty = self.lowering.map_ty(&payload_ty);
                    let value =
                        self.lowering
                            .p
                            .primop(Op::GetPayload(i as u32), &[occ.value], lam_ty);
                    Occurrence {
                        value,
                        ty: payload_ty,
                    }
                })
                .collect();

            let mut spec_rows: Vec<Row<'p>> = vec![];
            for row in &rows {
                if row.pats[column].is_irrefutable() {
                    let wilds = vec![Pat::Wild; payload_occs.len()];
                    spec_rows.push(row.with_column_expanded(column, &occ, wilds));
                    continue;
                }
                let Pat::Source(p) = row.pats[column] else {
                    continue;
                };
                let PatternKind::Variant {
                    variant_name: row_variant,
                    fields,
                    ..
                } = &p.kind
                else {
                    continue;
                };
                if row_variant != variant_name || fields.len() != payload_occs.len() {
                    continue;
                }
                let cells: Vec<Pat<'p>> = fields.iter().map(Pat::Source).collect();
                spec_rows.push(row.with_column_expanded(column, &occ, cells));
            }

            if spec_rows.is_empty() {
                arm_refs.push(trap_ref);
                continue;
            }
            let mut spec_occs = occs.clone();
            spec_occs.splice(column..column + 1, payload_occs);
            let body = self.compile(spec_occs, spec_rows);
            let case = self
                .lowering
                .p
                .func(&format!("case_{variant_name}"), void_ty, bot);
            self.lowering.p.set_body(case, body);
            arm_refs.push(self.lowering.p.func_ref(case));
        }

        let i64_ty = self.lowering.p.ty_i64();
        let tag = self.lowering.p.primop(Op::GetTag, &[occ.value], i64_ty);
        self.lowering.p.switch(tag, &arm_refs, trap_ref, bot)
    }

    // ----- Literal columns (equality chain) -----------------------------------

    fn literal_column(
        &mut self,
        occs: Vec<Occurrence>,
        rows: Vec<Row<'p>>,
        column: usize,
        head: &'p Pattern,
    ) -> ExprId {
        let occ = occs[column].clone();
        let Some(constant) = self.literal_const(head) else {
            return self.trap_jump();
        };

        // S(c, P): rows matching this constant lose the column; the rest —
        // other constants impossible here, wildcards still possible — form
        // the chain's else side, D-style (Fig. 5, case 2 over constants).
        let mut then_rows: Vec<Row<'p>> = vec![];
        let mut else_rows: Vec<Row<'p>> = vec![];
        for row in &rows {
            if row.pats[column].is_irrefutable() {
                then_rows.push(row.without_column(column, &occ));
                else_rows.push(row.clone());
                continue;
            }
            let Pat::Source(p) = row.pats[column] else {
                continue;
            };
            match self.literal_const(p) {
                Some(c) if c == constant => then_rows.push(row.without_column(column, &occ)),
                Some(_) => else_rows.push(row.clone()),
                None => {}
            }
        }

        let mut then_occs = occs.clone();
        then_occs.remove(column);
        let then_body = self.compile(then_occs, then_rows);
        let else_body = self.compile(occs, else_rows);
        let cond = self.lowering.p.cmp(CmpOp::Eq, occ.value, constant);
        self.lowering.branch_value(cond, then_body, else_body)
    }

    /// The λ_G constant a literal pattern tests against. Hash-consing makes
    /// ExprId equality literal equality (`1` and `01` intern to one node).
    fn literal_const(&mut self, pattern: &Pattern) -> Option<ExprId> {
        match &pattern.kind {
            PatternKind::LiteralInt(text) => match text.parse() {
                Ok(v) => Some(self.lowering.p.int(v)),
                Err(_) => {
                    self.lowering
                        .diagnostics
                        .push("lowering: unparseable int literal pattern".into());
                    None
                }
            },
            PatternKind::LiteralFloat(text) => match text.parse() {
                Ok(v) => Some(self.lowering.p.float(v)),
                Err(_) => {
                    self.lowering
                        .diagnostics
                        .push("lowering: unparseable float literal pattern".into());
                    None
                }
            },
            PatternKind::LiteralTrue => Some(self.lowering.p.bool(true)),
            PatternKind::LiteralFalse => Some(self.lowering.p.bool(false)),
            _ => None,
        }
    }

    // ----- Irrefutable aggregate columns (expand in place, no branching) ------

    fn tuple_column(
        &mut self,
        occs: Vec<Occurrence>,
        rows: Vec<Row<'p>>,
        column: usize,
    ) -> ExprId {
        let occ = occs[column].clone();
        let CheckTy::Tuple(items) = &occ.ty else {
            self.lowering.diagnostics.push(format!(
                "lowering: tuple pattern on a non-tuple scrutinee {:?}",
                occ.ty
            ));
            return self.trap_jump();
        };
        let sub_occs: Vec<Occurrence> = items
            .iter()
            .enumerate()
            .map(|(i, ty)| Occurrence {
                value: self.lowering.p.extract(occ.value, i as u32),
                ty: ty.clone(),
            })
            .collect();

        let mut expanded: Vec<Row<'p>> = vec![];
        for row in &rows {
            if row.pats[column].is_irrefutable() {
                let wilds = vec![Pat::Wild; sub_occs.len()];
                expanded.push(row.with_column_expanded(column, &occ, wilds));
                continue;
            }
            let Pat::Source(p) = row.pats[column] else {
                continue;
            };
            let PatternKind::Tuple(subs) = &p.kind else {
                continue;
            };
            if subs.len() != sub_occs.len() {
                continue;
            }
            let cells: Vec<Pat<'p>> = subs.iter().map(Pat::Source).collect();
            expanded.push(row.with_column_expanded(column, &occ, cells));
        }
        let mut new_occs = occs;
        new_occs.splice(column..column + 1, sub_occs);
        self.compile(new_occs, expanded)
    }

    fn record_column(
        &mut self,
        occs: Vec<Occurrence>,
        rows: Vec<Row<'p>>,
        column: usize,
    ) -> ExprId {
        let occ = occs[column].clone();
        let CheckTy::Record(row_ty) = &occ.ty else {
            self.lowering.diagnostics.push(format!(
                "lowering: record pattern on a non-record scrutinee {:?}",
                occ.ty
            ));
            return self.trap_jump();
        };
        if row_ty.tail.is_some() {
            self.lowering.diagnostics.push(
                "lowering: record pattern on an open row (not yet supported)".into(),
            );
            return self.trap_jump();
        }
        // One sub-occurrence per row field, in the row's canonical
        // (label-sorted) order — the same layout record literals build.
        let labels: Vec<String> = row_ty.fields.iter().map(|(l, _)| l.to_string()).collect();
        let field_tys: Vec<CheckTy> = row_ty.fields.iter().map(|(_, t)| t.clone()).collect();
        let sub_occs: Vec<Occurrence> = field_tys
            .iter()
            .enumerate()
            .map(|(i, ty)| Occurrence {
                value: self.lowering.p.extract(occ.value, i as u32),
                ty: ty.clone(),
            })
            .collect();

        let mut expanded: Vec<Row<'p>> = vec![];
        for row in &rows {
            if row.pats[column].is_irrefutable() {
                let wilds = vec![Pat::Wild; sub_occs.len()];
                expanded.push(row.with_column_expanded(column, &occ, wilds));
                continue;
            }
            let Pat::Source(p) = row.pats[column] else {
                continue;
            };
            let PatternKind::Record { fields } = &p.kind else {
                continue;
            };
            // Match pattern fields to row positions by label; absent
            // labels (covered by `..` or a sub-pattern-free shorthand) are
            // wildcards; shorthand binds record immediately.
            let mut new_row = row.without_column(column, &occ);
            let mut cells: Vec<Pat<'p>> = Vec::with_capacity(sub_occs.len());
            for (i, label) in labels.iter().enumerate() {
                let cell = fields.iter().find_map(|field| match &field.kind {
                    RecordFieldPatternKind::Bind(name) if name.name_str() == *label => {
                        if let Ok(symbol) = name.symbol() {
                            new_row.binds.push((symbol, sub_occs[i].value));
                        }
                        Some(Pat::Wild)
                    }
                    // `y: pat` binds `y` to the field *and* matches the
                    // sub-pattern (the checker binds both names).
                    RecordFieldPatternKind::Equals { name, value, .. }
                        if name.name_str() == *label =>
                    {
                        if let Ok(symbol) = name.symbol() {
                            new_row.binds.push((symbol, sub_occs[i].value));
                        }
                        Some(Pat::Source(value))
                    }
                    _ => None,
                });
                cells.push(cell.unwrap_or(Pat::Wild));
            }
            new_row.pats.splice(column..column, cells);
            expanded.push(new_row);
        }
        let mut new_occs = occs;
        new_occs.splice(column..column + 1, sub_occs);
        self.compile(new_occs, expanded)
    }

    // ----- The no-match trap ---------------------------------------------------

    /// The shared bodyless target: the scheduler emits `Trap` for a
    /// bodyless block and the reference evaluator reports an unset body —
    /// honest failure on a match the checker should have proven exhaustive.
    fn trap_label(&mut self) -> Label {
        if let Some(label) = self.trap {
            return label;
        }
        let void_ty = self.lowering.p.ty_void();
        let bot = self.lowering.p.ty_bot();
        let label = self.lowering.p.func("match_failed", void_ty, bot);
        self.trap = Some(label);
        label
    }

    fn trap_jump(&mut self) -> ExprId {
        let label = self.trap_label();
        let func = self.lowering.p.func_ref(label);
        let void = self.lowering.p.void();
        self.lowering.p.app(func, void)
    }
}

/// Collect the binders of an *irrefutable* pattern against an
/// already-lowered value (destructuring `let`): Bind takes the value,
/// tuples and closed records project with Extract (records are tuples in
/// canonical label order — see `map_ty`). Refutable sub-patterns are
/// diagnosed: a `let` cannot fail.
pub(super) fn collect_irrefutable_binds(
    lowering: &mut Lowering<'_>,
    pattern: &Pattern,
    value: ExprId,
    ty: &CheckTy,
    out: &mut Vec<(Symbol, ExprId)>,
) {
    match &pattern.kind {
        PatternKind::Wildcard => {}
        PatternKind::Bind(name) => {
            if let Ok(symbol) = name.symbol() {
                out.push((symbol, value));
            }
        }
        PatternKind::Tuple(subs) => {
            let CheckTy::Tuple(items) = ty else {
                lowering.diagnostics.push(format!(
                    "lowering: tuple pattern on a non-tuple let value {ty:?}"
                ));
                return;
            };
            for (i, (sub, item_ty)) in subs.iter().zip(items).enumerate() {
                let item = lowering.p.extract(value, i as u32);
                collect_irrefutable_binds(lowering, sub, item, item_ty, out);
            }
        }
        PatternKind::Record { fields } => {
            let CheckTy::Record(row) = ty else {
                lowering.diagnostics.push(format!(
                    "lowering: record pattern on a non-record let value {ty:?}"
                ));
                return;
            };
            if row.tail.is_some() {
                lowering
                    .diagnostics
                    .push("lowering: record pattern on an open row (not yet supported)".into());
                return;
            }
            for field in fields {
                let (name, sub) = match &field.kind {
                    RecordFieldPatternKind::Bind(name) => (name, None),
                    RecordFieldPatternKind::Equals { name, value, .. } => (name, Some(value)),
                    RecordFieldPatternKind::Rest => continue,
                };
                let label = name.name_str();
                let Some(index) = row
                    .fields
                    .iter()
                    .position(|(l, _)| l.to_string() == label)
                else {
                    lowering.diagnostics.push(format!(
                        "lowering: record pattern field '{label}' is not in the row"
                    ));
                    continue;
                };
                let field_value = lowering.p.extract(value, index as u32);
                if let Ok(symbol) = name.symbol() {
                    out.push((symbol, field_value));
                }
                if let Some(sub) = sub {
                    let field_ty = row.fields[index].1.clone();
                    collect_irrefutable_binds(lowering, sub, field_value, &field_ty, out);
                }
            }
        }
        other => {
            lowering.diagnostics.push(format!(
                "lowering: refutable pattern in a let (match on it instead): {other:?}"
            ));
        }
    }
}

/// Or-pattern row expansion (§2.2): each alternative becomes its own row,
/// same arm. Nested alternatives expand on the next visit to the column.
fn expand_or<'p>(rows: Vec<Row<'p>>, column: usize) -> Vec<Row<'p>> {
    let mut out = Vec::with_capacity(rows.len());
    for row in rows {
        let Pat::Source(p) = row.pats[column] else {
            out.push(row);
            continue;
        };
        let PatternKind::Or(alternatives) = &p.kind else {
            out.push(row);
            continue;
        };
        for alternative in alternatives {
            let mut expanded = row.clone();
            expanded.pats[column] = Pat::Source(alternative);
            out.push(expanded);
        }
    }
    out
}
