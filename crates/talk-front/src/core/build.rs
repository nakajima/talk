//! AST → typed-program tree lowering. Consumes the name-resolved, type-checked
//! AST and produces the owned typed tree: NodeID-preserving, and with each
//! expression's type baked onto its node (read once from the checker's tables).
//! All real desugaring already happened in `name_resolution/transforms/`, so the
//! dropped surface forms (`Unary`/`Binary`/`For`/`Incomplete`) must not appear —
//! they panic loudly if they somehow do.

use crate::core;
use crate::name_resolution::symbol::Symbol;
use crate::node::Node;
use crate::node_kinds::{decl, expr, pattern, stmt};
use crate::parsing::ast::{AST, NameResolved};
use crate::types::TypeOutput;

/// Lower one name-resolved, type-checked source file to a `TypedFile`.
pub fn build_file(
    ast: &AST<NameResolved>,
    types: &TypeOutput,
    elaboration: &crate::types::output::Elaboration,
) -> core::TypedFile {
    // Elaborated-node ids continue below the checker's descending mint
    // (`synthetic_floors`), so neither range meets the parser's.
    let floor = elaboration
        .synthetic_floors
        .get(&ast.file_id)
        .copied()
        .unwrap_or(u32::MAX);
    TypedTreeBuilder {
        types,
        elaboration,
        synthetic_next: std::cell::Cell::new(floor),
        grafted: std::cell::RefCell::new(Vec::new()),
    }
    .file(ast)
}

struct TypedTreeBuilder<'a> {
    types: &'a TypeOutput,
    /// The checker's per-occurrence decisions, consumed here — each entry
    /// bakes onto its tree node and is never published (ADR 0057).
    elaboration: &'a crate::types::output::Elaboration,
    /// Descending id mint for elaborated nodes (`elaborate_for`).
    synthetic_next: std::cell::Cell<u32>,
    /// (inner, wrapper) id pairs recorded at graft sites — see
    /// [`core::TypedFile::grafted`].
    grafted: std::cell::RefCell<Vec<(crate::node_id::NodeID, crate::node_id::NodeID)>>,
}

/// The checked float value. The lexer only produces parseable float
/// spellings, so this cannot fail on a checked tree.
fn float_literal(text: &str) -> core::FloatValue {
    core::FloatValue(
        text.replace('_', "")
            .parse()
            .expect("lexed float literal parses as f64"),
    )
}

/// The literal's value with escapes processed. The lexer already
/// rejected invalid escapes, so this cannot fail on a checked tree.
fn unescape(text: &str) -> String {
    crate::parsing::lexing::unescape(text).expect("lexer-validated escape sequences")
}

/// A frame-local symbol: bindable in some function frame, so a use
/// outside its binding frame is a capture. Globals and type-level
/// symbols never capture.
fn is_frame_local(symbol: &Symbol) -> bool {
    matches!(
        symbol,
        Symbol::DeclaredLocal(_) | Symbol::PatternBindLocal(_) | Symbol::ParamLocal(_)
    )
}

/// One walk computing a frame root's lexical facts (ADR 0038): free
/// variables in first-use order, symbols referenced under nested
/// function values, and the assigned∩nested cell set. `depth` counts
/// nested function boundaries; binder collection is flat — symbols are
/// unique per binder, so a symbol bound anywhere in the frame's subtree
/// (including a hoisted func-valued `let` used before its declaration)
/// is not free.
fn frame_facts(block: &core::Block, params: &[core::Parameter]) -> core::FrameFacts {
    use core::{DeclKind, ExprKind, PatternKind};
    use derive_visitor::{Drive, Visitor};

    #[derive(Visitor)]
    #[visitor(
        core::Expr(enter, exit),
        core::Decl(enter, exit),
        core::Stmt(enter),
        core::Pattern(enter),
        core::Parameter(enter)
    )]
    struct Scan {
        depth: usize,
        bound: rustc_hash::FxHashSet<Symbol>,
        used: Vec<Symbol>,
        assigned: rustc_hash::FxHashSet<Symbol>,
        nested: rustc_hash::FxHashSet<Symbol>,
    }
    impl Scan {
        fn enter_expr(&mut self, expr: &core::Expr) {
            match &expr.kind {
                ExprKind::Func(_) => self.depth += 1,
                ExprKind::Variable(crate::name::Name::Resolved(symbol, _)) => {
                    if self.depth > 0 {
                        self.nested.insert(*symbol);
                    }
                    if is_frame_local(symbol) && !self.used.contains(symbol) {
                        self.used.push(*symbol);
                    }
                }
                _ => {}
            }
        }
        fn exit_expr(&mut self, expr: &core::Expr) {
            if matches!(expr.kind, ExprKind::Func(_)) {
                self.depth -= 1;
            }
        }
        fn enter_decl(&mut self, decl: &core::Decl) {
            // A named local function is a nested frame like a func
            // expression (its recursion reference counts as nested).
            if matches!(decl.kind, DeclKind::Func(_)) {
                self.depth += 1;
            }
        }
        fn exit_decl(&mut self, decl: &core::Decl) {
            if matches!(decl.kind, DeclKind::Func(_)) {
                self.depth -= 1;
            }
        }
        fn enter_stmt(&mut self, stmt: &core::Stmt) {
            if let core::StmtKind::Assignment(lhs, _) = &stmt.kind
                && let ExprKind::Variable(crate::name::Name::Resolved(symbol, _)) = &lhs.kind
            {
                self.assigned.insert(*symbol);
            }
        }
        fn enter_pattern(&mut self, pattern: &core::Pattern) {
            if let PatternKind::Bind(crate::name::Name::Resolved(symbol, _)) = &pattern.kind {
                self.bound.insert(*symbol);
            }
        }
        fn enter_parameter(&mut self, param: &core::Parameter) {
            if let crate::name::Name::Resolved(symbol, _) = &param.name {
                self.bound.insert(*symbol);
            }
        }
    }

    let mut scan = Scan {
        depth: 0,
        bound: rustc_hash::FxHashSet::default(),
        used: Vec::new(),
        assigned: rustc_hash::FxHashSet::default(),
        nested: rustc_hash::FxHashSet::default(),
    };
    for param in params {
        if let crate::name::Name::Resolved(symbol, _) = &param.name {
            scan.bound.insert(*symbol);
        }
    }
    block.drive(&mut scan);

    core::FrameFacts {
        captured: scan
            .used
            .into_iter()
            .filter(|symbol| !scan.bound.contains(symbol))
            .collect(),
        celled: scan.assigned.intersection(&scan.nested).copied().collect(),
        nested_refs: scan.nested,
        assigned: scan.assigned,
    }
}

impl TypedTreeBuilder<'_> {
    /// The checked 64-bit value of an integer literal (LIT-01). A file
    /// with an out-of-range literal is blocked before the tree builds, so
    /// a missing or invalid entry is an invariant failure.
    fn int_literal(&self, id: crate::node_id::NodeID) -> i64 {
        match self.elaboration.integer_literals.get(&id) {
            Some(crate::types::output::CheckedIntegerLiteral::Value(value)) => *value,
            other => unreachable!("integer literal {id:?} lacks a checked value: {other:?}"),
        }
    }

    fn file(&self, ast: &AST<NameResolved>) -> core::TypedFile {
        let roots = self.roots(&ast.roots);
        core::TypedFile {
            file_id: ast.file_id,
            roots,
            grafted: self.grafted.take(),
        }
    }

    fn roots(&self, roots: &[Node]) -> Vec<core::Node> {
        let mut built: Vec<core::Node> = roots.iter().map(|n| self.node(n)).collect();
        // A top-level `func name` declaration desugars to `let name =
        // <func>`; stamp the binding as the callable's identity
        // (ADR 0038) so lowering reads the fact instead of
        // re-recognizing the declaration shape.
        for node in &mut built {
            if let core::Node::Decl(decl) = node
                && let core::DeclKind::Let {
                    lhs,
                    rhs: Some(rhs),
                    ..
                } = &mut decl.kind
                && let core::PatternKind::Bind(name) = &lhs.kind
                && let core::ExprKind::Func(func) = &mut rhs.kind
            {
                func.bound_as = name.symbol().ok();
            }
        }
        built
    }

    fn node(&self, node: &Node) -> core::Node {
        match node {
            Node::Decl(d) => core::Node::Decl(self.decl(d)),
            Node::Stmt(s) => core::Node::Stmt(self.stmt(s)),
            Node::Expr(e) => core::Node::Expr(self.expr(e)),
            other => unreachable!("unexpected node in typed-program lowering position: {other:?}"),
        }
    }

    // ----- Expressions -----------------------------------------------------

    fn expr(&self, e: &expr::Expr) -> core::Expr {
        let built = self.expr_unconverted(e);
        self.apply_into_coercion(e.id, built)
    }

    /// Wrap a checker-coerced expression in its synthesized `.into()`
    /// call (implicit `Into` conversion): the value crossed into a slot
    /// of a different monotype and typing committed the one declared
    /// row. The wrapper is an ordinary member call at fresh elaborated
    /// ids — MIR dispatches it exactly like a source-written `.into()`.
    fn apply_into_coercion(&self, id: crate::node_id::NodeID, built: core::Expr) -> core::Expr {
        let Some(coercion) = self.elaboration.into_coercions.get(&id) else {
            return built;
        };
        let span = built.span;
        let file = id.0;
        let target = coercion.target.erase_eff_args();
        let callee = core::Expr {
            id: self.syn_id(file),
            kind: core::ExprKind::Member(
                Some(Box::new(built)),
                crate::label::Label::Named("into".into()),
            ),
            span,
            ownership: Default::default(),
            ty: core::ValueTy::from_finalized(crate::types::ty::Ty::Func(
                vec![],
                Box::new(target.clone()),
                crate::types::ty::EffectRow::pure(),
            )),
            member_resolution: Some(coercion.resolution.clone()),
            specialization: None,
            witness_layout: None,
            instantiation: None,
            existential_pack: None,
            selected_callable: None,
        };
        core::Expr {
            id: self.syn_id(file),
            kind: core::ExprKind::Call {
                callee: Box::new(callee),
                type_args: vec![],
                args: vec![],
            },
            span,
            ownership: Default::default(),
            ty: core::ValueTy::from_finalized(target),
            member_resolution: None,
            specialization: None,
            witness_layout: None,
            instantiation: None,
            existential_pack: None,
            selected_callable: None,
        }
    }

    fn expr_unconverted(&self, e: &expr::Expr) -> core::Expr {
        // Coercion erasure: `inner as T` did its work in the checker; the
        // value is the inner expression. Likewise a parenthesized
        // expression, which parses as a 1-tuple. The outer node's
        // annotations describe the same value, so they overlay the inner's
        // — the ascribed type, an existential pack, a clone coercion —
        // under the outer node's id and span (the position the checker
        // annotated).
        match &e.kind {
            expr::ExprKind::As(inner, _) => return self.graft(e, inner),
            expr::ExprKind::Tuple(items) if items.len() == 1 => {
                return self.graft(e, &items[0]);
            }
            expr::ExprKind::Propagate(_) | expr::ExprKind::ForceUnwrap(..) => {
                let plan = self
                    .elaboration
                    .propagation_plans
                    .get(&e.id)
                    .unwrap_or_else(|| panic!("checked postfix expression {:?} has no plan", e.id));
                return self.graft(e, &plan.lowered);
            }
            // Variant construction: the checker resolves `.some(x)` at the
            // call node (checking mode) and `Optional.some(x)` at the
            // member callee node; either way the resolution is the variant
            // symbol. The constructor instantiation (GADT evidence) lives
            // at the resolution node, so it overlays the call node's.
            expr::ExprKind::Call { callee, args, .. } => {
                if let Some((site, enum_symbol, tag, variant_symbol)) = [callee.id, e.id]
                    .into_iter()
                    .find_map(|id| self.variant_resolution(id))
                {
                    let mut built = self.expr_with_kind(
                        e,
                        core::ExprKind::Con {
                            enum_symbol,
                            tag,
                            variant_symbol,
                            args: args.iter().map(|a| self.expr(&a.value)).collect(),
                        },
                    );
                    if let Some(instantiation) = self.elaboration.instantiations.get(&site) {
                        built.instantiation = Some(instantiation.clone());
                    }
                    // The construction IS the member resolution; the callee
                    // node it was recorded at has no tree counterpart, so
                    // editor queries there alias to this node.
                    built.member_resolution = Some(crate::types::output::MemberResolution::Direct(
                        variant_symbol,
                    ));
                    self.grafted.borrow_mut().push((callee.id, e.id));
                    return built;
                }
            }
            // A payload-less variant named bare (`.none`, `Optional.none`)
            // is a constructed value. Payload-carrying variants named bare
            // are function values and stay `Member`.
            expr::ExprKind::Member(..) => {
                if let Some((_, enum_symbol, tag, variant_symbol)) = self.variant_resolution(e.id)
                    && self
                        .types
                        .catalog
                        .enums
                        .get(&enum_symbol)
                        .and_then(|info| info.variants.get_index(tag as usize))
                        .is_some_and(|(_, v)| v.argument_types().is_empty())
                {
                    return self.expr_with_kind(
                        e,
                        core::ExprKind::Con {
                            enum_symbol,
                            tag,
                            variant_symbol,
                            args: vec![],
                        },
                    );
                }
            }
            _ => {}
        }
        self.plain_expr(e)
    }

    /// The enum variant a node's member resolution names, if any:
    /// (resolution node, enum, tag, variant symbol).
    fn variant_resolution(
        &self,
        id: crate::node_id::NodeID,
    ) -> Option<(crate::node_id::NodeID, Symbol, u16, Symbol)> {
        let crate::types::output::MemberResolution::Direct(symbol) =
            self.elaboration.member_resolutions.get(&id)?
        else {
            return None;
        };
        let Symbol::Variant(_) = *symbol else {
            return None;
        };
        for (enum_symbol, info) in &self.types.catalog.enums {
            if let Some(index) = info.variants.values().position(|v| v.symbol == *symbol) {
                return Some((id, *enum_symbol, index as u16, *symbol));
            }
        }
        None
    }

    fn plain_expr(&self, e: &expr::Expr) -> core::Expr {
        self.expr_with_kind(e, self.expr_kind(e))
    }

    fn expr_with_kind(&self, e: &expr::Expr, kind: core::ExprKind) -> core::Expr {
        let explicit_clone = matches!(kind, core::ExprKind::Clone(_));
        core::Expr {
            id: e.id,
            kind,
            span: e.span,
            ownership: core::ExprOwnership {
                auto_clone: explicit_clone || self.elaboration.coerce_clones.contains(&e.id),
            },
            // The type checker assigns every expression a type; a hole can
            // only arise downstream of an error diagnostic (which normally
            // blocks the file, but an unattributed solver error blocks
            // nothing), so it bakes as the poison type rather than a panic.
            // `erase_eff_args`: effect args on nominal heads are
            // type-checker internals and are not part of CoreProgram.
            ty: core::ValueTy::from_finalized(
                self.elaboration
                    .node_types
                    .get(&e.id)
                    .map(|ty| ty.erase_eff_args())
                    .unwrap_or(crate::types::ty::Ty::Error),
            ),
            member_resolution: self.elaboration.member_resolutions.get(&e.id).cloned(),
            specialization: self.elaboration.field_specializations.get(&e.id).cloned(),
            witness_layout: self.elaboration.witness_layouts.get(&e.id).cloned(),
            instantiation: self.elaboration.instantiations.get(&e.id).cloned(),
            existential_pack: self.elaboration.existential_packs.get(&e.id).cloned(),
            selected_callable: self.elaboration.selected_callables.get(&e.id).copied(),
        }
    }

    fn boxed(&self, e: &expr::Expr) -> Box<core::Expr> {
        Box::new(self.expr(e))
    }

    fn is_marker_clone_requirement(&self, symbol: Symbol) -> bool {
        [Symbol::Copy, Symbol::Clone]
            .into_iter()
            .filter_map(|protocol| self.types.catalog.requirement_in(protocol, "clone"))
            .any(|(_, requirement)| requirement.symbol == symbol)
    }

    /// Build `inner` in place of the erased wrapper `e`, overlaying the
    /// wrapper's annotations (they describe the same value).
    fn graft(&self, e: &expr::Expr, inner: &expr::Expr) -> core::Expr {
        let mut built = self.expr(inner);
        self.grafted.borrow_mut().push((built.id, e.id));
        built.id = e.id;
        built.span = e.span;
        built.ownership.auto_clone |= self.elaboration.coerce_clones.contains(&e.id);
        if let Some(ty) = self.elaboration.node_types.get(&e.id) {
            built.ty.replace(ty.erase_eff_args());
        }
        if let Some(pack) = self.elaboration.existential_packs.get(&e.id) {
            built.existential_pack = Some(pack.clone());
        }
        built
    }

    fn expr_kind(&self, e: &expr::Expr) -> core::ExprKind {
        match &e.kind {
            expr::ExprKind::Unreachable => {
                unreachable!("unreachable expressions are desugared to the panic effect")
            }
            expr::ExprKind::MacroCall { .. } | expr::ExprKind::SyntaxQuote { .. } => {
                unreachable!("macro syntax is eliminated before typed-program build")
            }
            expr::ExprKind::InlineIR(ir) => {
                // Typing validated the instruction and published its
                // checked op; an invalid instruction blocked the file.
                let kind = self
                    .elaboration
                    .checked_ir
                    .get(&e.id)
                    .expect("typed facts invariant: inline IR carries its checked operation")
                    .clone();
                core::ExprKind::InlineIR(core::InlineIRInstruction {
                    id: ir.id,
                    span: ir.span,
                    binds: ir.binds.iter().map(|b| self.expr(b)).collect(),
                    kind,
                })
            }
            expr::ExprKind::As(..) => {
                unreachable!("As is erased in expr(); expr_kind never sees it")
            }
            expr::ExprKind::CallEffect {
                effect_name,
                type_args,
                args,
                ..
            } => core::ExprKind::CallEffect {
                effect_name: effect_name.clone(),
                type_args: type_args.clone(),
                args: args.iter().map(|a| self.call_arg(a)).collect(),
                contract: self
                    .elaboration
                    .effect_contracts
                    .get(&e.id)
                    .expect("typed facts invariant: a perform carries its effect contract")
                    .clone(),
            },
            expr::ExprKind::LiteralArray(items) => {
                core::ExprKind::LiteralArray(items.iter().map(|i| self.expr(i)).collect())
            }
            expr::ExprKind::LiteralInt(_) => {
                core::ExprKind::Lit(core::Literal::Int(self.int_literal(e.id)))
            }
            expr::ExprKind::LiteralFloat(s) => {
                core::ExprKind::Lit(core::Literal::Float(float_literal(s)))
            }
            expr::ExprKind::LiteralTrue => core::ExprKind::Lit(core::Literal::Bool(true)),
            expr::ExprKind::LiteralFalse => core::ExprKind::Lit(core::Literal::Bool(false)),
            expr::ExprKind::LiteralString(s) => {
                core::ExprKind::Lit(core::Literal::String(unescape(s)))
            }
            expr::ExprKind::LiteralCharacter(s) => {
                core::ExprKind::Lit(core::Literal::Character(unescape(s)))
            }
            expr::ExprKind::Tuple(items) => {
                core::ExprKind::Tuple(items.iter().map(|i| self.expr(i)).collect())
            }
            expr::ExprKind::Block(block) => core::ExprKind::Block(self.block(block)),
            expr::ExprKind::Unsafe(block) => core::ExprKind::Unsafe(self.block(block)),
            expr::ExprKind::Call {
                callee,
                type_args,
                args,
                trailing_block,
                ..
            } => {
                let clone_requirement = match self.elaboration.member_resolutions.get(&callee.id) {
                    Some(crate::types::output::MemberResolution::Direct(symbol)) => {
                        self.is_marker_clone_requirement(*symbol)
                    }
                    _ => false,
                };
                if clone_requirement
                    && args.is_empty()
                    && trailing_block.is_none()
                    && let expr::ExprKind::Member(Some(receiver), _, _) = &callee.kind
                {
                    core::ExprKind::Clone(self.boxed(receiver))
                } else {
                    core::ExprKind::Call {
                        callee: self.boxed(callee),
                        type_args: type_args.clone(),
                        args: args.iter().map(|a| self.call_arg(a)).collect(),
                    }
                }
            }
            expr::ExprKind::Member(recv, label, _span) => {
                // Field read vs method/variant, decided once here: a member
                // that resolves to a stored field is a projection.
                if let Some(receiver) = recv
                    && let Some(field) = crate::types::output::stored_field_symbol(
                        &self.types.catalog,
                        &self.types.schemes,
                        self.elaboration.member_resolutions.get(&e.id),
                    )
                {
                    core::ExprKind::Proj(self.boxed(receiver), label.clone(), field)
                } else {
                    core::ExprKind::Member(recv.as_ref().map(|r| self.boxed(r)), label.clone())
                }
            }
            expr::ExprKind::Func(func) => core::ExprKind::Func(Box::new(self.func(func))),
            expr::ExprKind::Variable(name) => core::ExprKind::Variable(name.clone()),
            expr::ExprKind::Constructor(name, ..) => core::ExprKind::Constructor(name.clone()),
            expr::ExprKind::If(..) => {
                unreachable!("if expressions are desugared to match before typed-program build")
            }
            expr::ExprKind::Match(scrut, arms) => core::ExprKind::Match(
                self.boxed(scrut),
                arms.iter().map(|a| self.match_arm(a)).collect(),
            ),
            expr::ExprKind::RecordLiteral { fields, spread } => {
                // A spreadless literal with a closed row whose fields are
                // written in the row's canonical (label-sorted) order is a
                // tuple as-is. Out-of-order literals stay RecordLiteral:
                // field values must evaluate in source order, and only the
                // RecordLiteral lowering permutes at assembly time.
                if spread.is_none()
                    && let Some(crate::types::ty::Ty::Record(row)) =
                        self.elaboration.node_types.get(&e.id)
                    && row.tail.is_none()
                    && row.fields.len() == fields.len()
                    && row
                        .fields
                        .iter()
                        .zip(fields.iter())
                        .all(|((label, _), f)| f.label.name_str() == label.to_string())
                {
                    core::ExprKind::Tuple(fields.iter().map(|f| self.expr(&f.value)).collect())
                } else {
                    core::ExprKind::RecordLiteral {
                        fields: fields.iter().map(|f| self.record_field(f)).collect(),
                        spread: spread.as_ref().map(|s| self.boxed(s)),
                    }
                }
            }
            expr::ExprKind::Propagate(..) | expr::ExprKind::ForceUnwrap(..) => {
                unreachable!(
                    "postfix expressions are elaborated in expr(); expr_kind never sees them"
                )
            }
            expr::ExprKind::Unary(..) | expr::ExprKind::Binary(..) => {
                unreachable!(
                    "Unary/Binary should be desugared by LowerOperators before typed-program build"
                )
            }
            expr::ExprKind::Subscript(..) => {
                unreachable!(
                    "Subscript should be desugared by LowerSubscripts before typed-program build"
                )
            }
            expr::ExprKind::Incomplete(_) => {
                unreachable!("Incomplete expressions cannot be lowered to typed-program tree")
            }
        }
    }

    fn call_arg(&self, a: &crate::node_kinds::call_arg::CallArg) -> core::CallArg {
        core::CallArg {
            id: a.id,
            label: a.label.clone(),
            value: self.expr(&a.value),
            mode: a.mode,
        }
    }

    fn record_field(&self, f: &crate::node_kinds::record_field::RecordField) -> core::RecordField {
        core::RecordField {
            id: f.id,
            label: f.label.clone(),
            value: self.expr(&f.value),
        }
    }

    fn match_arm(&self, arm: &crate::node_kinds::match_arm::MatchArm) -> core::MatchArm {
        core::MatchArm {
            id: arm.id,
            pattern: self.pattern(&arm.pattern),
            body: self.block(&arm.body),
        }
    }

    // ----- Patterns --------------------------------------------------------

    fn pattern(&self, p: &pattern::Pattern) -> core::Pattern {
        // The occurrence type: recorded per pattern node during checking;
        // plain `let` binders skip `check_pattern` (they bind through the
        // monomorphic environment or a top-level scheme), so a bare Bind
        // falls back to its symbol's published type.
        let ty = self
            .elaboration
            .pattern_tys
            .get(&p.id)
            .cloned()
            .or_else(|| {
                let pattern::PatternKind::Bind(name) = &p.kind else {
                    return None;
                };
                let symbol = name.symbol().ok()?;
                self.types
                    .binder_ty(symbol)
                    .cloned()
                    .or_else(|| self.types.schemes.get(&symbol).map(|s| s.ty.clone()))
            });
        core::Pattern {
            id: p.id,
            kind: self.pattern_kind(p),
            span: p.span,
            ty: ty.map(core::ValueTy::from_finalized),
        }
    }

    fn pattern_kind(&self, p: &pattern::Pattern) -> core::PatternKind {
        match &p.kind {
            pattern::PatternKind::LiteralInt(_) => {
                core::PatternKind::LiteralInt(self.int_literal(p.id))
            }
            pattern::PatternKind::LiteralFloat(s) => {
                core::PatternKind::LiteralFloat(float_literal(s))
            }
            pattern::PatternKind::LiteralCharacter(s) => {
                core::PatternKind::LiteralCharacter(unescape(s))
            }
            pattern::PatternKind::LiteralString(s) => core::PatternKind::LiteralString(unescape(s)),
            pattern::PatternKind::LiteralTrue => core::PatternKind::LiteralTrue,
            pattern::PatternKind::LiteralFalse => core::PatternKind::LiteralFalse,
            pattern::PatternKind::Bind(name) => core::PatternKind::Bind(name.clone()),
            pattern::PatternKind::Tuple(ps) => {
                core::PatternKind::Tuple(ps.iter().map(|p| self.pattern(p)).collect())
            }
            pattern::PatternKind::Or(ps) => {
                core::PatternKind::Or(ps.iter().map(|p| self.pattern(p)).collect())
            }
            pattern::PatternKind::Wildcard => core::PatternKind::Wildcard,
            pattern::PatternKind::MacroCall { .. } => {
                unreachable!("macro invocations are expanded before typed-program build")
            }
            pattern::PatternKind::Variant {
                enum_name,
                variant_name,
                fields,
                ..
            } => core::PatternKind::Variant {
                enum_name: enum_name.clone(),
                variant_name: variant_name.clone(),
                resolved: match self.elaboration.member_resolutions.get(&p.id) {
                    Some(crate::types::output::MemberResolution::Direct(variant)) => Some(*variant),
                    _ => None,
                },
                fields: fields.iter().map(|p| self.pattern(p)).collect(),
            },
            pattern::PatternKind::Record { fields } => {
                let built: Vec<core::RecordFieldPattern> = fields
                    .iter()
                    .map(|f| self.record_field_pattern(f))
                    .collect();
                // Slot field references arrive as node ids; translate to
                // indices into `fields` for direct access.
                let slots = self
                    .elaboration
                    .record_pattern_slots
                    .get(&p.id)
                    .map(|slots| {
                        slots
                            .iter()
                            .map(|(ty, sub)| {
                                let index = sub
                                    .and_then(|id| built.iter().position(|field| field.id == id));
                                (core::ValueTy::from_finalized(ty.clone()), index)
                            })
                            .collect()
                    });
                core::PatternKind::Record {
                    fields: built,
                    slots,
                }
            }
            pattern::PatternKind::Struct {
                struct_name,
                fields,
                field_names,
                rest,
                // Explicit head args are consumed by the checker.
                struct_generics: _,
            } => {
                let built: Vec<core::Pattern> = fields
                    .iter()
                    .map(|n| match n {
                        Node::Pattern(p) => self.pattern(p),
                        other => unreachable!("struct pattern field is not a pattern: {other:?}"),
                    })
                    .collect();
                // Slot sub-pattern references arrive as node ids;
                // translate to indices into `fields` for direct access.
                let slots = self
                    .elaboration
                    .struct_pattern_slots
                    .get(&p.id)
                    .map(|slots| {
                        slots
                            .iter()
                            .map(|(ty, sub)| {
                                let index = sub
                                    .and_then(|id| built.iter().position(|field| field.id == id));
                                (core::ValueTy::from_finalized(ty.clone()), index)
                            })
                            .collect()
                    })
                    .unwrap_or_default();
                core::PatternKind::Struct {
                    struct_name: struct_name.clone(),
                    fields: built,
                    field_names: field_names.clone(),
                    rest: *rest,
                    slots,
                }
            }
        }
    }

    fn record_field_pattern(&self, f: &pattern::RecordFieldPattern) -> core::RecordFieldPattern {
        let kind = match &f.kind {
            pattern::RecordFieldPatternKind::Bind(name) => {
                core::RecordFieldPatternKind::Bind(name.clone())
            }
            pattern::RecordFieldPatternKind::Equals { name, value, .. } => {
                core::RecordFieldPatternKind::Equals {
                    name: name.clone(),
                    value: self.pattern(value),
                }
            }
            pattern::RecordFieldPatternKind::Rest => core::RecordFieldPatternKind::Rest,
        };
        core::RecordFieldPattern {
            id: f.id,
            kind,
            ty: self
                .elaboration
                .pattern_tys
                .get(&f.id)
                .cloned()
                .map(core::ValueTy::from_finalized),
        }
    }

    // ----- Blocks and statements -------------------------------------------

    fn block(&self, b: &crate::node_kinds::block::Block) -> core::Block {
        core::Block {
            id: b.id,
            args: self.params(&b.args),
            body: self.roots(&b.body),
            span: b.span,
            frame: None,
        }
    }

    /// A frame-root block — a function or initializer body, or a handler
    /// clause: publish the frame's capture and cell facts (ADR 0038).
    /// `params` are the frame's own parameters (bound, never captured);
    /// a handler clause's live on the block itself.
    fn frame_block(
        &self,
        b: &crate::node_kinds::block::Block,
        params: &[core::Parameter],
    ) -> core::Block {
        let mut block = self.block(b);
        block.frame = Some(frame_facts(&block, params));
        block
    }

    fn stmt(&self, s: &stmt::Stmt) -> core::Stmt {
        core::Stmt {
            id: s.id,
            kind: self.stmt_kind(s.id, &s.kind),
            span: s.span,
        }
    }

    fn stmt_kind(&self, stmt_id: crate::node_id::NodeID, k: &stmt::StmtKind) -> core::StmtKind {
        match k {
            stmt::StmtKind::Expr(e) => core::StmtKind::Expr(self.expr(e)),
            stmt::StmtKind::If(cond, then, els) => core::StmtKind::If(
                self.expr(cond),
                self.block(then),
                els.as_ref().map(|b| self.block(b)),
            ),
            stmt::StmtKind::Return(e) => core::StmtKind::Return(e.as_ref().map(|e| self.expr(e))),
            stmt::StmtKind::Break => core::StmtKind::Break,
            stmt::StmtKind::Assignment(lhs, rhs) => {
                core::StmtKind::Assignment(self.boxed(lhs), self.boxed(rhs))
            }
            stmt::StmtKind::Loop(cond, body) => {
                core::StmtKind::Loop(cond.as_ref().map(|e| self.expr(e)), self.block(body))
            }
            stmt::StmtKind::Continue => core::StmtKind::Continue,
            stmt::StmtKind::Resume(e) => core::StmtKind::Resume(e.as_ref().map(|e| self.expr(e))),
            stmt::StmtKind::Handling {
                effect_name, body, ..
            } => core::StmtKind::Handling {
                effect_name: effect_name.clone(),
                // A clause is a frame; its parameters are the block's args.
                body: self.frame_block(body, &[]),
                contract: self
                    .elaboration
                    .effect_contracts
                    .get(&stmt_id)
                    .expect("typed facts invariant: a handler carries its effect contract")
                    .clone(),
            },
            stmt::StmtKind::For { .. } => self.elaborate_for(stmt_id, k),
        }
    }

    /// Elaborate a first-class `for` into ordinary typed nodes once, so the
    /// final CoreProgram contains its semantic form:
    ///
    /// ```text
    /// {                                       // scope: hidden locals die here
    ///     let __for_src = <source>            // rvalue/consume sources only
    ///     let __for_iter = <recv>.iter()      // into_iter/iter_mut by mode
    ///     loop {
    ///         match __for_iter.next() {
    ///             .some(pattern) -> { <body> [__for_iter._store_current(pattern)] },
    ///             .none -> break
    ///         }
    ///     }
    /// }
    /// ```
    ///
    /// The `iter()`/`next()`/mut-store calls are rebuilt at
    /// the checker's ForPlan ids, so their member resolutions and
    /// instantiations bake on exactly like source-written calls. A `for`
    /// with no plan was rejected by typing, so only its source expression
    /// survives in the typed tree.
    fn elaborate_for(&self, stmt_id: crate::node_id::NodeID, k: &stmt::StmtKind) -> core::StmtKind {
        use crate::node_kinds::call_arg::ArgMode;
        let stmt::StmtKind::For {
            iterable,
            source_mode,
            pattern,
            body,
            hidden_source,
            hidden_iter,
            ..
        } = k
        else {
            unreachable!("elaborate_for on a non-for statement");
        };
        let Some(plan) = self.elaboration.for_plans.get(&stmt_id) else {
            return core::StmtKind::Expr(self.expr(iterable));
        };
        let span = iterable.span;
        let file = stmt_id.0;
        let consume = matches!(source_mode, Some(ArgMode::Consume));
        let mutate = matches!(source_mode, Some(ArgMode::Mut));
        let iter_label = if consume {
            "into_iter"
        } else if mutate {
            "iter_mut"
        } else {
            "iter"
        };
        let source = self.expr(iterable);
        let mut nodes: Vec<core::Node> = vec![];

        // A named source is borrowed as written; an rvalue source — or a
        // `consume`-marked one — binds to the hidden source local so its
        // buffers get ordinary scope-exit drops when the loop ends. `mut`
        // iteration borrows its source in place for the hidden iterator's
        // scope.
        let needs_bind =
            consume || (!mutate && !matches!(source.kind, core::ExprKind::Variable(_)));
        let iter_receiver = if needs_bind {
            let source_ty = source.ty.as_ty().clone();
            nodes.push(core::Node::Decl(self.syn_let(
                file,
                span,
                hidden_source.clone(),
                source.clone(),
                source_mode.filter(|_| consume),
            )));
            self.syn_variable(self.syn_id(file), span, hidden_source.clone(), source_ty)
        } else {
            source.clone()
        };

        // let __for_iter = <recv>.iter()
        let iter_call = self.syn_member_call(
            plan.iter_call_id,
            plan.iter_callee_id,
            span,
            iter_receiver,
            iter_label,
            vec![],
        );
        nodes.push(core::Node::Decl(self.syn_let(
            file,
            span,
            hidden_iter.clone(),
            iter_call,
            None,
        )));

        // loop { match __for_iter.next() { .some(pattern) body, .none break } }
        let iterator_ty = plan.iterator_ty.erase_eff_args();
        let next_receiver = self.syn_variable(
            self.syn_id(file),
            span,
            hidden_iter.clone(),
            iterator_ty.clone(),
        );
        let next_call = self.syn_member_call(
            plan.next_call_id,
            plan.next_callee_id,
            span,
            next_receiver,
            "next",
            vec![],
        );

        // Mut iteration stores the (possibly reassigned) binder back into
        // the current iterator slot at the end of each normal iteration.
        let mut arm_body = self.block(body);
        if mutate && let pattern::PatternKind::Bind(binder_name) = &pattern.kind {
            let binder_read = self.syn_variable(
                plan.mut_store_arg_id,
                pattern.span,
                binder_name.clone(),
                plan.element_ty.erase_eff_args(),
            );
            let wb_receiver = self.syn_variable(
                self.syn_id(file),
                span,
                hidden_iter.clone(),
                iterator_ty.clone(),
            );
            let store_call = self.syn_member_call(
                plan.mut_store_call_id,
                plan.mut_store_callee_id,
                span,
                wb_receiver,
                "_store_current",
                vec![core::CallArg {
                    id: plan.mut_store_arg_id,
                    label: crate::label::Label::Positional(0),
                    value: binder_read,
                    mode: None,
                }],
            );
            arm_body.body.push(core::Node::Stmt(core::Stmt {
                id: self.syn_id(file),
                span,
                kind: core::StmtKind::Expr(store_call),
            }));
        }
        let some_arm = core::MatchArm {
            id: self.syn_id(file),
            pattern: core::Pattern {
                id: self.syn_id(file),
                span: pattern.span,
                ty: None,
                kind: core::PatternKind::Variant {
                    enum_name: None,
                    variant_name: "some".to_string(),
                    resolved: None,
                    fields: vec![self.pattern(pattern)],
                },
            },
            body: arm_body,
        };
        let none_arm = core::MatchArm {
            id: self.syn_id(file),
            pattern: core::Pattern {
                id: self.syn_id(file),
                span,
                ty: None,
                kind: core::PatternKind::Variant {
                    enum_name: None,
                    variant_name: "none".to_string(),
                    resolved: None,
                    fields: vec![],
                },
            },
            body: core::Block {
                id: self.syn_id(file),
                args: vec![],
                span,
                body: vec![core::Node::Stmt(core::Stmt {
                    id: self.syn_id(file),
                    span,
                    kind: core::StmtKind::Break,
                })],
                frame: None,
            },
        };
        let match_expr = core::Expr {
            id: self.syn_id(file),
            kind: core::ExprKind::Match(Box::new(next_call), vec![some_arm, none_arm]),
            span,
            ownership: Default::default(),
            ty: core::ValueTy::from_finalized(plan.body_ty.erase_eff_args()),
            member_resolution: None,
            specialization: None,
            witness_layout: None,
            instantiation: None,
            existential_pack: None,
            selected_callable: None,
        };
        nodes.push(core::Node::Stmt(core::Stmt {
            id: self.syn_id(file),
            span,
            kind: core::StmtKind::Loop(
                None,
                core::Block {
                    id: self.syn_id(file),
                    args: vec![],
                    span,
                    body: vec![core::Node::Stmt(core::Stmt {
                        id: self.syn_id(file),
                        span,
                        kind: core::StmtKind::Expr(match_expr),
                    })],
                    frame: None,
                },
            ),
        }));

        core::StmtKind::Expr(core::Expr {
            id: self.syn_id(file),
            kind: core::ExprKind::Block(core::Block {
                id: self.syn_id(file),
                args: vec![],
                span,
                body: nodes,
                frame: None,
            }),
            span,
            ownership: Default::default(),
            ty: core::ValueTy::from_finalized(crate::types::ty::Ty::unit()),
            member_resolution: None,
            specialization: None,
            witness_layout: None,
            instantiation: None,
            existential_pack: None,
            selected_callable: None,
        })
    }

    /// Mint a fresh id for an elaborated node, descending from `u32::MAX`
    /// (parser ids ascend from zero, so the ranges never meet).
    fn syn_id(&self, file: crate::node_id::FileID) -> crate::node_id::NodeID {
        let next = self.synthetic_next.get() - 1;
        self.synthetic_next.set(next);
        crate::node_id::NodeID(file, next)
    }

    fn syn_variable(
        &self,
        id: crate::node_id::NodeID,
        span: crate::span::Span,
        name: crate::name::Name,
        ty: crate::types::ty::Ty,
    ) -> core::Expr {
        core::Expr {
            id,
            kind: core::ExprKind::Variable(name),
            span,
            ownership: Default::default(),
            ty: core::ValueTy::from_finalized(ty),
            member_resolution: None,
            specialization: None,
            witness_layout: None,
            instantiation: None,
            existential_pack: None,
            selected_callable: None,
        }
    }

    /// A method call rebuilt at the checker's ids: types, member
    /// resolutions, and instantiations bake on from the same tables as
    /// source-written calls.
    fn syn_member_call(
        &self,
        call_id: crate::node_id::NodeID,
        callee_id: crate::node_id::NodeID,
        span: crate::span::Span,
        receiver: core::Expr,
        label: &str,
        args: Vec<core::CallArg>,
    ) -> core::Expr {
        let baked_ty = |id: &crate::node_id::NodeID| {
            self.elaboration
                .node_types
                .get(id)
                .map(|ty| ty.erase_eff_args())
                .unwrap_or(crate::types::ty::Ty::Error)
        };
        let callee = core::Expr {
            id: callee_id,
            kind: core::ExprKind::Member(
                Some(Box::new(receiver)),
                crate::label::Label::Named(label.into()),
            ),
            span,
            ownership: Default::default(),
            ty: core::ValueTy::from_finalized(baked_ty(&callee_id)),
            member_resolution: self.elaboration.member_resolutions.get(&callee_id).cloned(),
            specialization: None,
            witness_layout: None,
            instantiation: self.elaboration.instantiations.get(&callee_id).cloned(),
            existential_pack: None,
            selected_callable: self.elaboration.selected_callables.get(&callee_id).copied(),
        };
        core::Expr {
            id: call_id,
            kind: core::ExprKind::Call {
                callee: Box::new(callee),
                type_args: vec![],
                args,
            },
            span,
            ownership: Default::default(),
            ty: core::ValueTy::from_finalized(baked_ty(&call_id)),
            member_resolution: self.elaboration.member_resolutions.get(&call_id).cloned(),
            specialization: None,
            witness_layout: None,
            instantiation: self.elaboration.instantiations.get(&call_id).cloned(),
            existential_pack: None,
            selected_callable: self.elaboration.selected_callables.get(&call_id).copied(),
        }
    }

    fn syn_let(
        &self,
        file: crate::node_id::FileID,
        span: crate::span::Span,
        name: crate::name::Name,
        rhs: core::Expr,
        source_mode: Option<crate::node_kinds::call_arg::ArgMode>,
    ) -> core::Decl {
        core::Decl {
            id: self.syn_id(file),
            span,
            visibility: crate::node_kinds::decl::Visibility::Private,
            kind: core::DeclKind::Let {
                lhs: core::Pattern {
                    id: self.syn_id(file),
                    span,
                    kind: core::PatternKind::Bind(name),
                    ty: None,
                },
                type_annotation: None,
                rhs: Some(rhs),
                source_mode,
            },
        }
    }

    // ----- Functions and declarations --------------------------------------

    fn param(&self, p: &crate::node_kinds::parameter::Parameter) -> core::Parameter {
        core::Parameter {
            id: p.id,
            name: p.name.clone(),
            name_span: p.name_span,
            type_annotation: p.type_annotation.clone(),
            span: p.span,
            ty: self
                .elaboration
                .node_types
                .get(&p.id)
                .map(|ty| core::ValueTy::from_finalized(ty.erase_eff_args())),
        }
    }

    fn params(&self, ps: &[crate::node_kinds::parameter::Parameter]) -> Vec<core::Parameter> {
        ps.iter().map(|p| self.param(p)).collect()
    }

    fn func(&self, f: &crate::node_kinds::func::Func) -> core::Func {
        let scheme = f
            .name
            .symbol()
            .ok()
            .and_then(|symbol| self.types.schemes.get(&symbol))
            .cloned()
            .or_else(|| {
                self.elaboration
                    .node_types
                    .get(&f.id)
                    .cloned()
                    .map(|ty| match ty {
                        // A rank-N field literal: the field's own scheme
                        // is baked as the function's scheme, so lowering
                        // compiles it per projection instantiation like
                        // any other polymorphic callable.
                        crate::types::ty::Ty::Forall(scheme) => *scheme,
                        other => crate::types::ty::Scheme::mono(other),
                    })
            })
            .unwrap_or_else(|| crate::types::ty::Scheme::mono(crate::types::ty::Ty::Error));
        let params = self.params(&f.params);
        let body = self.frame_block(&f.body, &params);
        core::Func {
            specialization: self.elaboration.field_specializations.get(&f.id).cloned(),
            id: f.id,
            name: f.name.clone(),
            effects: f.effects.clone(),
            scheme,
            receiver: crate::node_kinds::decl::ReceiverMode::None,
            bound_as: None,
            generics: f.generics.clone(),
            captures: f.captures.clone(),
            where_clause: f.where_clause.clone(),
            params,
            body,
            ret: f.ret.clone(),
            attributes: f.attributes.clone(),
        }
    }

    fn body(&self, b: &crate::node_kinds::body::Body) -> core::Body {
        core::Body {
            id: b.id,
            decls: b.decls.iter().map(|d| self.decl(d)).collect(),
            span: b.span,
        }
    }

    fn decl(&self, d: &decl::Decl) -> core::Decl {
        core::Decl {
            id: d.id,
            kind: self.decl_kind(&d.kind),
            span: d.span,
            visibility: d.visibility,
        }
    }

    fn decl_kind(&self, k: &decl::DeclKind) -> core::DeclKind {
        match k {
            decl::DeclKind::Macro { .. } => {
                unreachable!("macro declarations are removed before typed-program build")
            }
            decl::DeclKind::MacroCall { .. } => {
                unreachable!("macro invocations are expanded before typed-program build")
            }
            decl::DeclKind::Wrapper { .. } => {
                unreachable!("wrapper macros are expanded before typed-program build")
            }
            decl::DeclKind::Import(import) => core::DeclKind::Import(import.clone()),
            decl::DeclKind::Effect {
                name,
                generics,
                where_clause,
                params,
                ret,
                ..
            } => core::DeclKind::Effect {
                name: name.clone(),
                generics: generics.clone(),
                where_clause: where_clause.clone(),
                params: self.params(params),
                ret: ret.clone(),
            },
            decl::DeclKind::Struct {
                name,
                generics,
                where_clause,
                body,
                ..
            } => core::DeclKind::Struct {
                name: name.clone(),
                generics: generics.clone(),
                where_clause: where_clause.clone(),
                body: self.body(body),
            },
            decl::DeclKind::Let {
                lhs,
                type_annotation,
                rhs,
            } => core::DeclKind::Let {
                lhs: self.pattern(lhs),
                type_annotation: type_annotation.clone(),
                rhs: rhs.as_ref().map(|e| self.expr(e)),
                source_mode: None,
            },
            decl::DeclKind::Protocol {
                name,
                generics,
                where_clause,
                body,
                conformances,
                ..
            } => core::DeclKind::Protocol {
                name: name.clone(),
                generics: generics.clone(),
                where_clause: where_clause.clone(),
                body: self.body(body),
                conformances: conformances.clone(),
            },
            decl::DeclKind::Init { name, params, body } => {
                let params = self.params(params);
                let body = self.frame_block(body, &params);
                core::DeclKind::Init {
                    name: name.clone(),
                    params,
                    body,
                }
            }
            decl::DeclKind::Property {
                name,
                is_static,
                type_annotation,
                default_value,
                ..
            } => core::DeclKind::Property {
                name: name.clone(),
                is_static: *is_static,
                type_annotation: type_annotation.clone(),
                default_value: default_value.as_ref().map(|e| self.expr(e)),
            },
            decl::DeclKind::Method {
                func,
                is_static,
                receiver_mode,
            } => {
                let mut func = self.func(func);
                func.receiver = *receiver_mode;
                core::DeclKind::Method {
                    func: Box::new(func),
                    is_static: *is_static,
                    receiver_mode: *receiver_mode,
                }
            }
            decl::DeclKind::Associated {
                generic,
                where_clause,
            } => core::DeclKind::Associated {
                generic: generic.clone(),
                where_clause: where_clause.clone(),
            },
            decl::DeclKind::Func(func) => core::DeclKind::Func(self.func(func)),
            decl::DeclKind::Extend {
                binders,
                head,
                conformances,
                where_clause,
                body,
            } => core::DeclKind::Extend {
                binders: binders.clone(),
                head: head.clone(),
                conformances: conformances.clone(),
                where_clause: where_clause.clone(),
                body: self.body(body),
            },
            decl::DeclKind::Enum {
                name,
                generics,
                where_clause,
                body,
                ..
            } => core::DeclKind::Enum {
                name: name.clone(),
                generics: generics.clone(),
                where_clause: where_clause.clone(),
                body: self.body(body),
            },
            decl::DeclKind::EnumVariant {
                name,
                generics,
                payloads,
                payload_labels,
                result,
                ..
            } => core::DeclKind::EnumVariant {
                name: name.clone(),
                generics: generics.clone(),
                payloads: payloads.clone(),
                payload_labels: payload_labels.clone(),
                result: result.clone(),
            },
            decl::DeclKind::FuncSignature(sig) => core::DeclKind::FuncSignature(sig.clone()),
            decl::DeclKind::MethodRequirement {
                signature,
                receiver_mode,
            } => core::DeclKind::MethodRequirement {
                signature: signature.clone(),
                receiver_mode: *receiver_mode,
            },
            decl::DeclKind::InitRequirement { signature } => core::DeclKind::InitRequirement {
                signature: signature.clone(),
            },
            decl::DeclKind::TypeAlias(name, _span, ty) => {
                core::DeclKind::TypeAlias(name.clone(), ty.clone())
            }
        }
    }
}
