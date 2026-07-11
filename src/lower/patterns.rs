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

use crate::lambda_g::expr::{CmpOp, Const, ExprId, Op, TyKind};
use crate::lambda_g::program::Label;
use crate::name_resolution::symbol::Symbol;
use crate::typed_ast::{MatchArm, Pattern, PatternKind, RecordFieldPatternKind};
use crate::types::ty::Ty as CheckTy;

use super::{Binding, Ctx, EvidenceBinding, Lowering, ScaffoldArms};

/// A matrix column's subject: a pure λ_G value plus its checker type.
#[derive(Clone)]
struct Occurrence {
    value: ExprId,
    /// The type visible to pattern shape checking. A borrow at this
    /// occurrence is erased, but borrows nested below aggregates remain
    /// until those child occurrences are projected.
    ty: CheckTy,
    /// Whether reaching this occurrence crossed a borrow. Borrowed
    /// occurrences are aliases: neither wildcards nor binders own a drop.
    borrowed: bool,
}

impl Occurrence {
    fn new(value: ExprId, mut ty: CheckTy, mut borrowed: bool) -> Self {
        loop {
            match ty {
                CheckTy::Borrow(_, inner) => {
                    borrowed = true;
                    ty = *inner;
                }
                CheckTy::Unique(inner) => ty = *inner,
                _ => {
                    return Occurrence {
                        value,
                        ty,
                        borrowed,
                    };
                }
            }
        }
    }
}

/// What ownership action a synthetic wildcard cell represents at a leaf.
#[derive(Clone, Copy)]
enum WildcardCell {
    /// A source discard owns this occurrence and must release it.
    Drop,
    /// The occurrence is owned through an already-recorded binder.
    Ignore,
}

/// A row's pattern cell: a source pattern, or a wildcard introduced by
/// specialization (default rows, consumed binds, record-shorthand binds).
#[derive(Clone, Copy)]
enum Pat<'p> {
    Wild(WildcardCell),
    Source(&'p Pattern),
}

#[derive(Clone, Debug, PartialEq)]
enum PatternLiteral {
    Int(i64),
    Float(u64),
    Bool(bool),
    Character(Vec<u8>),
    Str(Vec<u8>),
}

impl<'p> Pat<'p> {
    /// Wildcards and binds match anything; binds are recorded into the row
    /// when their column is consumed.
    fn is_irrefutable(self) -> bool {
        match self {
            Pat::Wild(_) => true,
            Pat::Source(p) => matches!(p.kind, PatternKind::Wildcard | PatternKind::Bind(_)),
        }
    }

    fn expanded_wildcard(self) -> Pat<'p> {
        match self {
            Pat::Wild(kind) => Pat::Wild(kind),
            Pat::Source(pattern) if matches!(pattern.kind, PatternKind::Bind(_)) => {
                Pat::Wild(WildcardCell::Ignore)
            }
            Pat::Source(_) => Pat::Wild(WildcardCell::Drop),
        }
    }
}

#[derive(Clone)]
struct Row<'p> {
    pats: Vec<Pat<'p>>,
    /// Binders whose columns have been consumed: symbol, value, and whether
    /// the projection aliases borrowed storage.
    binds: Vec<(Symbol, ExprId, bool)>,
    /// Runtime dictionaries brought into scope by consumed GADT constructors.
    evidence: Vec<((Symbol, Symbol), EvidenceBinding)>,
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
            row.binds.push((symbol, occ.value, occ.borrowed));
        }
        row
    }

    fn with_evidence(&self, evidence: &[((Symbol, Symbol), EvidenceBinding)]) -> Row<'p> {
        let mut row = self.clone();
        for (key, binding) in evidence {
            if !row.evidence.iter().any(|(existing, _)| existing == key) {
                row.evidence.push((*key, *binding));
            }
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
    binder_borrows: Vec<bool>,
    evidence: Vec<(Symbol, Symbol)>,
    label: Option<Label>,
}

/// Compile a `match` whose scrutinee is already lowered to the pure value
/// `value` (checker type `scrutinee_ty`), delivering each arm's value to
/// `k`. Returns the ⊥-typed decision tree.
#[allow(clippy::too_many_arguments)]
pub(super) fn compile_match(
    lowering: &mut Lowering<'_>,
    value: ExprId,
    scrutinee_ty: CheckTy,
    arms: &[MatchArm],
    scaffold_arms: Option<ScaffoldArms>,
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
                binder_borrows: vec![],
                evidence: vec![],
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
            evidence: vec![],
            arm,
        })
        .collect();
    let occs = vec![Occurrence::new(value, scrutinee_ty, false)];
    MatchCompiler {
        lowering,
        ctx,
        k,
        arms,
        scaffold_arms,
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
    /// The arms' scaffold blocks in the body being lowered, when this match
    /// is embedded there: arm bodies lower from these instead of standalone
    /// bodies.
    scaffold_arms: Option<ScaffoldArms>,
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
            | PatternKind::LiteralCharacter(_)
            | PatternKind::LiteralString(_)
            | PatternKind::LiteralTrue
            | PatternKind::LiteralFalse => self.literal_column(occs, rows, column, head),
            PatternKind::Tuple(_) => self.tuple_column(occs, rows, column),
            PatternKind::Record { .. } => self.record_column(occs, rows, column),
            other => {
                self.lowering
                    .diagnostics
                    .push(format!("lowering: pattern not yet supported: {other:?}"));
                self.trap_jump()
            }
        }
    }

    // ----- Leaves -----------------------------------------------------------

    /// The first row matches: gather its binds and jump to its arm's join
    /// point with the bound values.
    fn leaf(&mut self, occs: &[Occurrence], row: Row<'p>) -> ExprId {
        let mut binds: FxHashMap<Symbol, (ExprId, bool)> = row
            .binds
            .iter()
            .map(|(symbol, value, borrowed)| (*symbol, (*value, *borrowed)))
            .collect();
        for (pat, occ) in row.pats.iter().zip(occs) {
            if let Pat::Source(p) = pat
                && let PatternKind::Bind(name) = &p.kind
                && let Ok(symbol) = name.symbol()
            {
                binds.insert(symbol, (occ.value, occ.borrowed));
            }
        }
        let binders = self.targets[row.arm].binders.clone();
        let mut values = Vec::with_capacity(binders.len());
        let mut binder_borrows = Vec::with_capacity(binders.len());
        for symbol in &binders {
            match binds.get(symbol) {
                Some(&(value, borrowed)) => {
                    values.push(value);
                    binder_borrows.push(borrowed);
                }
                None => {
                    self.lowering.diagnostics.push(format!(
                        "lowering: pattern alternative does not bind {symbol} \
                         (alternatives must bind the same names)"
                    ));
                    values.push(self.lowering.p.void());
                    binder_borrows.push(false);
                }
            }
        }
        let evidence_by_key: FxHashMap<(Symbol, Symbol), EvidenceBinding> =
            row.evidence.iter().copied().collect();
        let mut evidence_values = vec![];
        let label = match self.targets[row.arm].label {
            Some(label) => {
                if self.targets[row.arm].binder_borrows != binder_borrows {
                    self.lowering
                        .diagnostics
                        .push("lowering: pattern alternatives disagree on binder ownership".into());
                }
                for key in &self.targets[row.arm].evidence {
                    match evidence_by_key.get(key) {
                        Some(binding) => evidence_values.push(binding.table),
                        None => {
                            self.lowering
                                .diagnostics
                                .push(format!("lowering: missing GADT evidence for {key:?}"));
                        }
                    }
                }
                label
            }
            None => {
                evidence_values.extend(row.evidence.iter().map(|(_, binding)| binding.table));
                self.make_arm(row.arm, &binders, &values, &binder_borrows, &row.evidence)
            }
        };
        values.extend(evidence_values);
        let arg = self.lowering.p.tuple(&values);
        let func = self.lowering.p.func_ref(label);
        let mut body = self.lowering.p.app(func, arg);
        for (pat, occ) in row.pats.iter().zip(occs).rev() {
            let should_drop = !occ.borrowed
                && match pat {
                    Pat::Wild(WildcardCell::Drop) => true,
                    Pat::Wild(WildcardCell::Ignore) => false,
                    Pat::Source(pattern) => matches!(pattern.kind, PatternKind::Wildcard),
                };
            if should_drop {
                body = self
                    .lowering
                    .lower_drop_value_then(self.ctx, occ.value, &occ.ty, body);
            }
        }
        body
    }

    /// Lower the arm's body once, as a join point taking its binders.
    fn make_arm(
        &mut self,
        arm: usize,
        binders: &[Symbol],
        values: &[ExprId],
        binder_borrows: &[bool],
        evidence: &[((Symbol, Symbol), EvidenceBinding)],
    ) -> Label {
        let mut tys: Vec<_> = values.iter().map(|v| self.lowering.p.expr_ty(*v)).collect();
        tys.extend(
            evidence
                .iter()
                .map(|(_, binding)| self.lowering.p.expr_ty(binding.table)),
        );
        let dom = self.lowering.p.ty_tuple(&tys);
        let bot = self.lowering.p.ty_bot();
        let label = self.lowering.p.func("arm", dom, bot);
        self.targets[arm].label = Some(label);
        self.targets[arm].binder_borrows = binder_borrows.to_vec();
        self.targets[arm].evidence = evidence.iter().map(|(key, _)| *key).collect();

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
        for (i, (key, binding)) in evidence.iter().enumerate() {
            let table = self.lowering.p.extract(var, (binders.len() + i) as u32);
            inner.local_evidence.insert(
                *key,
                EvidenceBinding {
                    protocol: binding.protocol,
                    table,
                },
            );
        }
        let body_block = &self.arms[arm].body;
        // Only binders projected entirely through owned occurrences take an
        // arm-scope drop. Borrowed projections remain aliases even when the
        // outer scrutinee itself is an owned aggregate.
        let pattern_types = self.lowering.units[self.ctx.unit].types;
        for (_, symbol, ty) in
            crate::lower::mir::arm_release_binders(pattern_types, &self.arms[arm].pattern)
        {
            let borrowed = binders
                .iter()
                .position(|binder| *binder == symbol)
                .and_then(|index| binder_borrows.get(index))
                .copied()
                .unwrap_or(false);
            if binders.contains(&symbol) && !borrowed {
                inner.drop_stack.push(crate::lower::DropBinding {
                    symbol,
                    key_path: crate::lower::Place::root(symbol),
                    ty,
                    dynamic_flags: vec![],
                });
            }
        }
        let k = self.k;
        // The arm body lowers from its scaffold block in the enclosing body
        // when this match is embedded there (breaks/continues/returns inside
        // it are real CFG edges); a standalone body otherwise.
        let scaffold_block = self
            .scaffold_arms
            .as_ref()
            .and_then(|scaffold| Some((*scaffold.blocks.get(arm)?, scaffold.join)));
        let body = self
            .lowering
            .with_cells(&celled, &mut inner, |this, inner| {
                if let Some((arm_block, join)) = scaffold_block
                    && let Some(done) = this.lower_arm_from_scaffold(arm_block, join, inner, k)
                {
                    return done;
                }
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
            self.lowering
                .diagnostics
                .push(format!("lowering: no enum catalog entry for {enum_symbol}"));
            return self.trap_jump();
        };
        let subst: FxHashMap<Symbol, CheckTy> = info
            .params
            .iter()
            .copied()
            .zip(enum_args.iter().cloned())
            .collect();
        let no_effs = FxHashMap::default();
        let no_rows = FxHashMap::default();

        let void_ty = self.lowering.p.ty_void();
        let bot = self.lowering.p.ty_bot();
        let trap = self.trap_label();
        let trap_ref = self.lowering.p.func_ref(trap);

        // One switch arm per declared variant, in tag (declaration) order:
        // S(c, P) for each constructor c (Fig. 5, case 2). Tags absent
        // from the matrix specialize to an empty matrix, which is the trap.
        let mut arm_refs = Vec::with_capacity(info.variants.len());
        for (variant_name, variant) in info.variants.iter() {
            let Some(instantiation) = variant
                .instantiate(&subst, &no_effs, &no_rows)
                .refined_by_result(&occ.ty)
            else {
                arm_refs.push(trap_ref);
                continue;
            };
            let payload_occs: Vec<Occurrence> = instantiation
                .argument_types
                .iter()
                .enumerate()
                .map(|(i, payload_ty)| {
                    let lam_ty = self.lowering.map_ty(payload_ty);
                    let value =
                        self.lowering
                            .p
                            .primop(Op::GetPayload(i as u32), &[occ.value], lam_ty);
                    Occurrence::new(value, payload_ty.clone(), occ.borrowed)
                })
                .collect();
            let gadt_evidence = self.lowering.variant_pattern_evidence(
                variant,
                &instantiation,
                occ.value,
                payload_occs.len(),
                self.ctx.unit,
            );

            let mut spec_rows: Vec<Row<'p>> = vec![];
            for row in &rows {
                if row.pats[column].is_irrefutable() {
                    let wilds = vec![row.pats[column].expanded_wildcard(); payload_occs.len()];
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
                spec_rows.push(
                    row.with_column_expanded(column, &occ, cells)
                        .with_evidence(&gadt_evidence),
                );
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
        let Some(literal) = self.pattern_literal(head) else {
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
            match self.pattern_literal(p) {
                Some(candidate) if candidate == literal => {
                    then_rows.push(row.without_column(column, &occ));
                }
                Some(_) => else_rows.push(row.clone()),
                None => {}
            }
        }

        let mut then_occs = occs.clone();
        then_occs.remove(column);
        let then_body = self.compile(then_occs, then_rows);
        let else_body = self.compile(occs, else_rows);
        match literal {
            PatternLiteral::Int(value) => {
                let constant = self.lowering.p.int(value);
                let cond = self.lowering.p.cmp(CmpOp::Eq, occ.value, constant);
                self.lowering.branch_value(cond, then_body, else_body)
            }
            PatternLiteral::Float(bits) => {
                let constant = self.lowering.p.float(f64::from_bits(bits));
                let cond = self.lowering.p.cmp(CmpOp::Eq, occ.value, constant);
                self.lowering.branch_value(cond, then_body, else_body)
            }
            PatternLiteral::Bool(value) => {
                let constant = self.lowering.p.bool(value);
                let cond = self.lowering.p.cmp(CmpOp::Eq, occ.value, constant);
                self.lowering.branch_value(cond, then_body, else_body)
            }
            PatternLiteral::Character(bytes) => {
                self.character_literal_branch(&occ, &bytes, then_body, else_body)
            }
            PatternLiteral::Str(bytes) => {
                self.string_literal_branch(&occ, &bytes, then_body, else_body)
            }
        }
    }

    fn pattern_literal(&mut self, pattern: &Pattern) -> Option<PatternLiteral> {
        match &pattern.kind {
            PatternKind::LiteralInt(text) => match text.parse() {
                Ok(value) => Some(PatternLiteral::Int(value)),
                Err(_) => {
                    self.lowering
                        .diagnostics
                        .push("lowering: unparseable int literal pattern".into());
                    None
                }
            },
            PatternKind::LiteralFloat(text) => match text.parse::<f64>() {
                Ok(value) => Some(PatternLiteral::Float(value.to_bits())),
                Err(_) => {
                    self.lowering
                        .diagnostics
                        .push("lowering: unparseable float literal pattern".into());
                    None
                }
            },
            PatternKind::LiteralCharacter(text) => match crate::parsing::lexing::unescape(text) {
                Ok(value) => Some(PatternLiteral::Character(value.into_bytes())),
                Err(_) => {
                    self.lowering
                        .diagnostics
                        .push("lowering: character literal pattern with invalid escape".into());
                    None
                }
            },
            PatternKind::LiteralString(text) => match crate::parsing::lexing::unescape(text) {
                Ok(value) => Some(PatternLiteral::Str(value.into_bytes())),
                Err(_) => {
                    self.lowering
                        .diagnostics
                        .push("lowering: string literal pattern with invalid escape".into());
                    None
                }
            },
            PatternKind::LiteralTrue => Some(PatternLiteral::Bool(true)),
            PatternKind::LiteralFalse => Some(PatternLiteral::Bool(false)),
            _ => None,
        }
    }

    fn character_literal_branch(
        &mut self,
        occ: &Occurrence,
        bytes: &[u8],
        then_body: ExprId,
        else_body: ExprId,
    ) -> ExprId {
        let CheckTy::Nominal(character_symbol, _) = &occ.ty else {
            self.lowering
                .diagnostics
                .push("lowering: character pattern on a non-Character value".into());
            return self.trap_jump();
        };
        let metadata = self
            .lowering
            .units
            .iter()
            .find_map(|unit| unit.types.catalog.structs.get(character_symbol))
            .and_then(|character| {
                let storage_index = character.fields.get_index_of("storage")? as u32;
                let start_index = character.fields.get_index_of("start")? as u32;
                let length_index = character.fields.get_index_of("byte_count")? as u32;
                let (_, storage_ty) = character.fields.get("storage")?;
                let CheckTy::Nominal(storage_symbol, _) = storage_ty else {
                    return None;
                };
                let storage = self
                    .lowering
                    .units
                    .iter()
                    .find_map(|unit| unit.types.catalog.structs.get(storage_symbol))?;
                let base_index = storage.fields.get_index_of("base")? as u32;
                Some((
                    storage_index,
                    start_index,
                    length_index,
                    storage_ty.clone(),
                    base_index,
                ))
            });
        let Some((storage_index, start_index, length_index, storage_ty, base_index)) = metadata
        else {
            self.lowering.diagnostics.push(
                "lowering: Character pattern requires storage, start, and byte_count fields".into(),
            );
            return self.trap_jump();
        };

        let storage_lam_ty = self.lowering.map_ty(&storage_ty);
        let storage =
            self.lowering
                .p
                .primop(Op::GetField(storage_index), &[occ.value], storage_lam_ty);
        let ptr_ty = self.lowering.p.ty_ptr();
        let base = self
            .lowering
            .p
            .primop(Op::GetField(base_index), &[storage], ptr_ty);
        let i64_ty = self.lowering.p.ty_i64();
        let start = self
            .lowering
            .p
            .primop(Op::GetField(start_index), &[occ.value], i64_ty);
        let length = self
            .lowering
            .p
            .primop(Op::GetField(length_index), &[occ.value], i64_ty);

        let mut matched = then_body;
        for (index, expected) in bytes.iter().copied().enumerate().rev() {
            let offset = if index == 0 {
                start
            } else {
                let index = self.lowering.p.int(index as i64);
                self.lowering.p.add(start, index)
            };
            let ptr = self.lowering.p.add(base, offset);
            let byte_ty = self.lowering.p.ty(TyKind::Byte);
            let actual = self.lowering.p.primop(Op::Load, &[ptr], byte_ty);
            let expected = self.lowering.p.constant(Const::Byte(expected), byte_ty);
            let cond = self.lowering.p.cmp(CmpOp::Eq, actual, expected);
            matched = self.lowering.branch_value(cond, matched, else_body);
        }
        let expected_length = self.lowering.p.int(bytes.len() as i64);
        let length_matches = self.lowering.p.cmp(CmpOp::Eq, length, expected_length);
        self.lowering
            .branch_value(length_matches, matched, else_body)
    }

    /// Match a `String` scrutinee against a literal's bytes: a byte_count
    /// check guarding a byte-equality chain over the string's buffer, the
    /// same shape as `character_literal_branch`.
    fn string_literal_branch(
        &mut self,
        occ: &Occurrence,
        bytes: &[u8],
        then_body: ExprId,
        else_body: ExprId,
    ) -> ExprId {
        let CheckTy::Nominal(string_symbol, _) = &occ.ty else {
            self.lowering
                .diagnostics
                .push("lowering: string pattern on a non-String value".into());
            return self.trap_jump();
        };
        let metadata = self
            .lowering
            .units
            .iter()
            .find_map(|unit| unit.types.catalog.structs.get(string_symbol))
            .and_then(|string| {
                let storage_index = string.fields.get_index_of("storage")? as u32;
                let length_index = string.fields.get_index_of("byte_count")? as u32;
                let (_, storage_ty) = string.fields.get("storage")?;
                let CheckTy::Nominal(storage_symbol, _) = storage_ty else {
                    return None;
                };
                let storage = self
                    .lowering
                    .units
                    .iter()
                    .find_map(|unit| unit.types.catalog.structs.get(storage_symbol))?;
                let base_index = storage.fields.get_index_of("base")? as u32;
                Some((storage_index, length_index, storage_ty.clone(), base_index))
            });
        let Some((storage_index, length_index, storage_ty, base_index)) = metadata else {
            self.lowering
                .diagnostics
                .push("lowering: String pattern requires storage and byte_count fields".into());
            return self.trap_jump();
        };

        let storage_lam_ty = self.lowering.map_ty(&storage_ty);
        let storage =
            self.lowering
                .p
                .primop(Op::GetField(storage_index), &[occ.value], storage_lam_ty);
        let ptr_ty = self.lowering.p.ty_ptr();
        let base = self
            .lowering
            .p
            .primop(Op::GetField(base_index), &[storage], ptr_ty);
        let i64_ty = self.lowering.p.ty_i64();
        let length = self
            .lowering
            .p
            .primop(Op::GetField(length_index), &[occ.value], i64_ty);

        let mut matched = then_body;
        for (index, expected) in bytes.iter().copied().enumerate().rev() {
            let offset = self.lowering.p.int(index as i64);
            let ptr = self.lowering.p.add(base, offset);
            let byte_ty = self.lowering.p.ty(TyKind::Byte);
            let actual = self.lowering.p.primop(Op::Load, &[ptr], byte_ty);
            let expected = self.lowering.p.constant(Const::Byte(expected), byte_ty);
            let cond = self.lowering.p.cmp(CmpOp::Eq, actual, expected);
            matched = self.lowering.branch_value(cond, matched, else_body);
        }
        let expected_length = self.lowering.p.int(bytes.len() as i64);
        let length_matches = self.lowering.p.cmp(CmpOp::Eq, length, expected_length);
        self.lowering
            .branch_value(length_matches, matched, else_body)
    }

    // ----- Irrefutable aggregate columns (expand in place, no branching) ------

    fn tuple_column(&mut self, occs: Vec<Occurrence>, rows: Vec<Row<'p>>, column: usize) -> ExprId {
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
            .map(|(i, ty)| {
                Occurrence::new(
                    self.lowering.p.extract(occ.value, i as u32),
                    ty.clone(),
                    occ.borrowed,
                )
            })
            .collect();

        let mut expanded: Vec<Row<'p>> = vec![];
        for row in &rows {
            if row.pats[column].is_irrefutable() {
                let wilds = vec![row.pats[column].expanded_wildcard(); sub_occs.len()];
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
            self.lowering
                .diagnostics
                .push("lowering: record pattern on an open row (not yet supported)".into());
            return self.trap_jump();
        }
        // One sub-occurrence per row field, in the row's canonical
        // (label-sorted) order — the same layout record literals build.
        let labels: Vec<String> = row_ty.fields.iter().map(|(l, _)| l.to_string()).collect();
        let field_tys: Vec<CheckTy> = row_ty.fields.iter().map(|(_, t)| t.clone()).collect();
        let sub_occs: Vec<Occurrence> = field_tys
            .iter()
            .enumerate()
            .map(|(i, ty)| {
                Occurrence::new(
                    self.lowering.p.extract(occ.value, i as u32),
                    ty.clone(),
                    occ.borrowed,
                )
            })
            .collect();

        let mut expanded: Vec<Row<'p>> = vec![];
        for row in &rows {
            if row.pats[column].is_irrefutable() {
                let wilds = vec![row.pats[column].expanded_wildcard(); sub_occs.len()];
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
                            new_row
                                .binds
                                .push((symbol, sub_occs[i].value, sub_occs[i].borrowed));
                        }
                        Some(Pat::Wild(WildcardCell::Ignore))
                    }
                    // `y: pat` binds `y` to the field *and* matches the
                    // sub-pattern (the checker binds both names).
                    RecordFieldPatternKind::Equals { name, value, .. }
                        if name.name_str() == *label =>
                    {
                        if let Ok(symbol) = name.symbol() {
                            new_row
                                .binds
                                .push((symbol, sub_occs[i].value, sub_occs[i].borrowed));
                        }
                        Some(Pat::Source(value))
                    }
                    _ => None,
                });
                cells.push(cell.unwrap_or(Pat::Wild(WildcardCell::Drop)));
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
                let Some(index) = row.fields.iter().position(|(l, _)| l.to_string() == label)
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
