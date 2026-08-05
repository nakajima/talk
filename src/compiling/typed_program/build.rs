//! AST → typed-program tree lowering. Consumes the name-resolved, type-checked
//! AST and produces the owned typed tree: NodeID-preserving, and with each
//! expression's type baked onto its node (read once from the checker's tables).
//! All real desugaring already happened in `name_resolution/transforms/`, so the
//! dropped surface forms (`Unary`/`Binary`/`For`/`Incomplete`) must not appear —
//! they panic loudly if they somehow do.

use crate::name_resolution::symbol::Symbol;
use crate::node::Node;
use crate::node_kinds::{decl, expr, pattern, stmt};
use crate::parsing::ast::{AST, NameResolved};
use crate::typed_ast;
use crate::types::TypeOutput;

/// Lower one name-resolved, type-checked source file to a `TypedFile`.
pub fn build_file(ast: &AST<NameResolved>, types: &TypeOutput) -> typed_ast::TypedFile {
    // Elaborated-node ids continue below the checker's descending mint
    // (`synthetic_floors`), so neither range meets the parser's.
    let floor = types
        .synthetic_floors
        .get(&ast.file_id)
        .copied()
        .unwrap_or(u32::MAX);
    TypedTreeBuilder {
        types,
        synthetic_next: std::cell::Cell::new(floor),
    }
    .file(ast)
}

struct TypedTreeBuilder<'a> {
    types: &'a TypeOutput,
    /// Descending id mint for elaborated nodes (`elaborate_for`).
    synthetic_next: std::cell::Cell<u32>,
}

/// The checked float value. The lexer only produces parseable float
/// spellings, so this cannot fail on a checked tree.
fn float_literal(text: &str) -> typed_ast::FloatValue {
    typed_ast::FloatValue(
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
fn frame_facts(block: &typed_ast::Block, params: &[typed_ast::Parameter]) -> typed_ast::FrameFacts {
    use derive_visitor::{Drive, Visitor};
    use typed_ast::{DeclKind, ExprKind, PatternKind};

    #[derive(Visitor)]
    #[visitor(
        typed_ast::Expr(enter, exit),
        typed_ast::Decl(enter, exit),
        typed_ast::Stmt(enter),
        typed_ast::Pattern(enter),
        typed_ast::Parameter(enter)
    )]
    struct Scan {
        depth: usize,
        bound: rustc_hash::FxHashSet<Symbol>,
        used: Vec<Symbol>,
        assigned: rustc_hash::FxHashSet<Symbol>,
        nested: rustc_hash::FxHashSet<Symbol>,
    }
    impl Scan {
        fn enter_expr(&mut self, expr: &typed_ast::Expr) {
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
        fn exit_expr(&mut self, expr: &typed_ast::Expr) {
            if matches!(expr.kind, ExprKind::Func(_)) {
                self.depth -= 1;
            }
        }
        fn enter_decl(&mut self, decl: &typed_ast::Decl) {
            // A named local function is a nested frame like a func
            // expression (its recursion reference counts as nested).
            if matches!(decl.kind, DeclKind::Func(_)) {
                self.depth += 1;
            }
        }
        fn exit_decl(&mut self, decl: &typed_ast::Decl) {
            if matches!(decl.kind, DeclKind::Func(_)) {
                self.depth -= 1;
            }
        }
        fn enter_stmt(&mut self, stmt: &typed_ast::Stmt) {
            if let typed_ast::StmtKind::Assignment(lhs, _) = &stmt.kind
                && let ExprKind::Variable(crate::name::Name::Resolved(symbol, _)) = &lhs.kind
            {
                self.assigned.insert(*symbol);
            }
        }
        fn enter_pattern(&mut self, pattern: &typed_ast::Pattern) {
            if let PatternKind::Bind(crate::name::Name::Resolved(symbol, _)) = &pattern.kind {
                self.bound.insert(*symbol);
            }
        }
        fn enter_parameter(&mut self, param: &typed_ast::Parameter) {
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

    typed_ast::FrameFacts {
        captured: scan
            .used
            .into_iter()
            .filter(|symbol| !scan.bound.contains(symbol))
            .collect(),
        celled: scan.assigned.intersection(&scan.nested).copied().collect(),
        nested_refs: scan.nested,
    }
}

impl TypedTreeBuilder<'_> {
    /// The checked 64-bit value of an integer literal (LIT-01). A file
    /// with an out-of-range literal is blocked before the tree builds, so
    /// a missing or invalid entry is an invariant failure.
    fn int_literal(&self, id: crate::node_id::NodeID) -> i64 {
        match self.types.integer_literals.get(&id) {
            Some(crate::types::output::CheckedIntegerLiteral::Value(value)) => *value,
            other => unreachable!("integer literal {id:?} lacks a checked value: {other:?}"),
        }
    }

    fn file(&self, ast: &AST<NameResolved>) -> typed_ast::TypedFile {
        typed_ast::TypedFile {
            file_id: ast.file_id,
            roots: self.roots(&ast.roots),
        }
    }

    fn roots(&self, roots: &[Node]) -> Vec<typed_ast::Node> {
        let mut built: Vec<typed_ast::Node> = roots.iter().map(|n| self.node(n)).collect();
        // A top-level `func name` declaration desugars to `let name =
        // <func>`; stamp the binding as the callable's identity
        // (ADR 0038) so lowering reads the fact instead of
        // re-recognizing the declaration shape.
        for node in &mut built {
            if let typed_ast::Node::Decl(decl) = node
                && let typed_ast::DeclKind::Let {
                    lhs,
                    rhs: Some(rhs),
                    ..
                } = &mut decl.kind
                && let typed_ast::PatternKind::Bind(name) = &lhs.kind
                && let typed_ast::ExprKind::Func(func) = &mut rhs.kind
            {
                func.bound_as = name.symbol().ok();
            }
        }
        built
    }

    fn node(&self, node: &Node) -> typed_ast::Node {
        match node {
            Node::Decl(d) => typed_ast::Node::Decl(self.decl(d)),
            Node::Stmt(s) => typed_ast::Node::Stmt(self.stmt(s)),
            Node::Expr(e) => typed_ast::Node::Expr(self.expr(e)),
            other => unreachable!("unexpected node in typed-program lowering position: {other:?}"),
        }
    }

    // ----- Expressions -----------------------------------------------------

    fn expr(&self, e: &expr::Expr) -> typed_ast::Expr {
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
                let plan =
                    self.types.propagation_plans.get(&e.id).unwrap_or_else(|| {
                        panic!("checked postfix expression {:?} has no plan", e.id)
                    });
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
                        typed_ast::ExprKind::Con {
                            enum_symbol,
                            tag,
                            variant_symbol,
                            args: args.iter().map(|a| self.expr(&a.value)).collect(),
                        },
                    );
                    if let Some(instantiation) = self.types.instantiations.get(&site) {
                        built.instantiation = Some(instantiation.clone());
                    }
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
                        typed_ast::ExprKind::Con {
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
            self.types.member_resolutions.get(&id)?
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

    fn plain_expr(&self, e: &expr::Expr) -> typed_ast::Expr {
        self.expr_with_kind(e, self.expr_kind(e))
    }

    fn expr_with_kind(&self, e: &expr::Expr, kind: typed_ast::ExprKind) -> typed_ast::Expr {
        let explicit_clone = matches!(kind, typed_ast::ExprKind::Clone(_));
        typed_ast::Expr {
            id: e.id,
            kind,
            span: e.span,
            ownership: typed_ast::ExprOwnership {
                auto_clone: explicit_clone || self.types.coerce_clones.contains(&e.id),
            },
            // The type checker assigns every expression a type; a hole can
            // only arise downstream of an error diagnostic (which normally
            // blocks the file, but an unattributed solver error blocks
            // nothing), so it bakes as the poison type rather than a panic.
            // `erase_eff_args`: effect args on nominal heads are
            // type-checker internals and are not part of TypedProgram.
            ty: self
                .types
                .node_types
                .get(&e.id)
                .map(|ty| ty.erase_eff_args())
                .unwrap_or(crate::types::ty::Ty::Error),
            member_resolution: self.types.member_resolutions.get(&e.id).cloned(),
            specialization: self.types.field_specializations.get(&e.id).cloned(),
            witness_layout: self.types.witness_layouts.get(&e.id).cloned(),
            instantiation: self.types.instantiations.get(&e.id).cloned(),
            existential_pack: self.types.existential_packs.get(&e.id).cloned(),
        }
    }

    fn boxed(&self, e: &expr::Expr) -> Box<typed_ast::Expr> {
        Box::new(self.expr(e))
    }

    fn is_marker_clone_requirement(&self, symbol: Symbol) -> bool {
        [Symbol::Copy, Symbol::CheapClone]
            .into_iter()
            .filter_map(|protocol| self.types.catalog.requirement_in(protocol, "clone"))
            .any(|(_, requirement)| requirement.symbol == symbol)
    }

    /// Build `inner` in place of the erased wrapper `e`, overlaying the
    /// wrapper's annotations (they describe the same value).
    fn graft(&self, e: &expr::Expr, inner: &expr::Expr) -> typed_ast::Expr {
        let mut built = self.expr(inner);
        built.id = e.id;
        built.span = e.span;
        built.ownership.auto_clone |= self.types.coerce_clones.contains(&e.id);
        if let Some(ty) = self.types.node_types.get(&e.id) {
            built.ty = ty.erase_eff_args();
        }
        if let Some(pack) = self.types.existential_packs.get(&e.id) {
            built.existential_pack = Some(pack.clone());
        }
        built
    }

    fn expr_kind(&self, e: &expr::Expr) -> typed_ast::ExprKind {
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
                    .types
                    .checked_ir
                    .get(&e.id)
                    .expect("typed facts invariant: inline IR carries its checked operation")
                    .clone();
                typed_ast::ExprKind::InlineIR(typed_ast::InlineIRInstruction {
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
            } => typed_ast::ExprKind::CallEffect {
                effect_name: effect_name.clone(),
                type_args: type_args.clone(),
                args: args.iter().map(|a| self.call_arg(a)).collect(),
                contract: self
                    .types
                    .effect_contracts
                    .get(&e.id)
                    .expect("typed facts invariant: a perform carries its effect contract")
                    .clone(),
            },
            expr::ExprKind::LiteralArray(items) => {
                typed_ast::ExprKind::LiteralArray(items.iter().map(|i| self.expr(i)).collect())
            }
            expr::ExprKind::LiteralInt(_) => {
                typed_ast::ExprKind::Lit(typed_ast::Literal::Int(self.int_literal(e.id)))
            }
            expr::ExprKind::LiteralFloat(s) => {
                typed_ast::ExprKind::Lit(typed_ast::Literal::Float(float_literal(s)))
            }
            expr::ExprKind::LiteralTrue => typed_ast::ExprKind::Lit(typed_ast::Literal::Bool(true)),
            expr::ExprKind::LiteralFalse => {
                typed_ast::ExprKind::Lit(typed_ast::Literal::Bool(false))
            }
            expr::ExprKind::LiteralString(s) => {
                typed_ast::ExprKind::Lit(typed_ast::Literal::String(unescape(s)))
            }
            expr::ExprKind::LiteralCharacter(s) => {
                typed_ast::ExprKind::Lit(typed_ast::Literal::Character(unescape(s)))
            }
            expr::ExprKind::Tuple(items) => {
                typed_ast::ExprKind::Tuple(items.iter().map(|i| self.expr(i)).collect())
            }
            expr::ExprKind::Block(block) => typed_ast::ExprKind::Block(self.block(block)),
            expr::ExprKind::Unsafe(block) => typed_ast::ExprKind::Unsafe(self.block(block)),
            expr::ExprKind::Call {
                callee,
                type_args,
                args,
                trailing_block,
                ..
            } => {
                let clone_requirement = match self.types.member_resolutions.get(&callee.id) {
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
                    typed_ast::ExprKind::Clone(self.boxed(receiver))
                } else {
                    typed_ast::ExprKind::Call {
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
                        self.types.member_resolutions.get(&e.id),
                    )
                {
                    typed_ast::ExprKind::Proj(self.boxed(receiver), label.clone(), field)
                } else {
                    typed_ast::ExprKind::Member(recv.as_ref().map(|r| self.boxed(r)), label.clone())
                }
            }
            expr::ExprKind::Func(func) => typed_ast::ExprKind::Func(Box::new(self.func(func))),
            expr::ExprKind::Variable(name) => typed_ast::ExprKind::Variable(name.clone()),
            expr::ExprKind::Constructor(name, ..) => typed_ast::ExprKind::Constructor(name.clone()),
            expr::ExprKind::If(..) => {
                unreachable!("if expressions are desugared to match before typed-program build")
            }
            expr::ExprKind::Match(scrut, arms) => typed_ast::ExprKind::Match(
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
                        self.types.node_types.get(&e.id)
                    && row.tail.is_none()
                    && row.fields.len() == fields.len()
                    && row
                        .fields
                        .iter()
                        .zip(fields.iter())
                        .all(|((label, _), f)| f.label.name_str() == label.to_string())
                {
                    typed_ast::ExprKind::Tuple(fields.iter().map(|f| self.expr(&f.value)).collect())
                } else {
                    typed_ast::ExprKind::RecordLiteral {
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

    fn call_arg(&self, a: &crate::node_kinds::call_arg::CallArg) -> typed_ast::CallArg {
        typed_ast::CallArg {
            id: a.id,
            label: a.label.clone(),
            value: self.expr(&a.value),
            mode: a.mode,
        }
    }

    fn record_field(
        &self,
        f: &crate::node_kinds::record_field::RecordField,
    ) -> typed_ast::RecordField {
        typed_ast::RecordField {
            id: f.id,
            label: f.label.clone(),
            value: self.expr(&f.value),
        }
    }

    fn match_arm(&self, arm: &crate::node_kinds::match_arm::MatchArm) -> typed_ast::MatchArm {
        typed_ast::MatchArm {
            id: arm.id,
            pattern: self.pattern(&arm.pattern),
            body: self.block(&arm.body),
        }
    }

    // ----- Patterns --------------------------------------------------------

    fn pattern(&self, p: &pattern::Pattern) -> typed_ast::Pattern {
        // The occurrence type: recorded per pattern node during checking;
        // plain `let` binders skip `check_pattern` (they bind through the
        // monomorphic environment or a top-level scheme), so a bare Bind
        // falls back to its symbol's published type.
        let ty = self.types.pattern_tys.get(&p.id).cloned().or_else(|| {
            let pattern::PatternKind::Bind(name) = &p.kind else {
                return None;
            };
            let symbol = name.symbol().ok()?;
            self.types
                .binder_ty(symbol)
                .cloned()
                .or_else(|| self.types.schemes.get(&symbol).map(|s| s.ty.clone()))
        });
        typed_ast::Pattern {
            id: p.id,
            kind: self.pattern_kind(p),
            span: p.span,
            ty,
        }
    }

    fn pattern_kind(&self, p: &pattern::Pattern) -> typed_ast::PatternKind {
        match &p.kind {
            pattern::PatternKind::LiteralInt(_) => {
                typed_ast::PatternKind::LiteralInt(self.int_literal(p.id))
            }
            pattern::PatternKind::LiteralFloat(s) => {
                typed_ast::PatternKind::LiteralFloat(float_literal(s))
            }
            pattern::PatternKind::LiteralCharacter(s) => {
                typed_ast::PatternKind::LiteralCharacter(unescape(s))
            }
            pattern::PatternKind::LiteralString(s) => {
                typed_ast::PatternKind::LiteralString(unescape(s))
            }
            pattern::PatternKind::LiteralTrue => typed_ast::PatternKind::LiteralTrue,
            pattern::PatternKind::LiteralFalse => typed_ast::PatternKind::LiteralFalse,
            pattern::PatternKind::Bind(name) => typed_ast::PatternKind::Bind(name.clone()),
            pattern::PatternKind::Tuple(ps) => {
                typed_ast::PatternKind::Tuple(ps.iter().map(|p| self.pattern(p)).collect())
            }
            pattern::PatternKind::Or(ps) => {
                typed_ast::PatternKind::Or(ps.iter().map(|p| self.pattern(p)).collect())
            }
            pattern::PatternKind::Wildcard => typed_ast::PatternKind::Wildcard,
            pattern::PatternKind::Variant {
                enum_name,
                variant_name,
                fields,
                ..
            } => typed_ast::PatternKind::Variant {
                enum_name: enum_name.clone(),
                variant_name: variant_name.clone(),
                resolved: match self.types.member_resolutions.get(&p.id) {
                    Some(crate::types::output::MemberResolution::Direct(variant)) => Some(*variant),
                    _ => None,
                },
                fields: fields.iter().map(|p| self.pattern(p)).collect(),
            },
            pattern::PatternKind::Record { fields } => {
                let built: Vec<typed_ast::RecordFieldPattern> = fields
                    .iter()
                    .map(|f| self.record_field_pattern(f))
                    .collect();
                // Slot field references arrive as node ids; translate to
                // indices into `fields` for direct access.
                let slots = self.types.record_pattern_slots.get(&p.id).map(|slots| {
                    slots
                        .iter()
                        .map(|(ty, sub)| {
                            let index =
                                sub.and_then(|id| built.iter().position(|field| field.id == id));
                            (ty.clone(), index)
                        })
                        .collect()
                });
                typed_ast::PatternKind::Record {
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
                let built: Vec<typed_ast::Pattern> = fields
                    .iter()
                    .map(|n| match n {
                        Node::Pattern(p) => self.pattern(p),
                        other => unreachable!("struct pattern field is not a pattern: {other:?}"),
                    })
                    .collect();
                // Slot sub-pattern references arrive as node ids;
                // translate to indices into `fields` for direct access.
                let slots = self
                    .types
                    .struct_pattern_slots
                    .get(&p.id)
                    .map(|slots| {
                        slots
                            .iter()
                            .map(|(ty, sub)| {
                                let index = sub
                                    .and_then(|id| built.iter().position(|field| field.id == id));
                                (ty.clone(), index)
                            })
                            .collect()
                    })
                    .unwrap_or_default();
                typed_ast::PatternKind::Struct {
                    struct_name: struct_name.clone(),
                    fields: built,
                    field_names: field_names.clone(),
                    rest: *rest,
                    slots,
                }
            }
        }
    }

    fn record_field_pattern(
        &self,
        f: &pattern::RecordFieldPattern,
    ) -> typed_ast::RecordFieldPattern {
        let kind = match &f.kind {
            pattern::RecordFieldPatternKind::Bind(name) => {
                typed_ast::RecordFieldPatternKind::Bind(name.clone())
            }
            pattern::RecordFieldPatternKind::Equals { name, value, .. } => {
                typed_ast::RecordFieldPatternKind::Equals {
                    name: name.clone(),
                    value: self.pattern(value),
                }
            }
            pattern::RecordFieldPatternKind::Rest => typed_ast::RecordFieldPatternKind::Rest,
        };
        typed_ast::RecordFieldPattern {
            id: f.id,
            kind,
            ty: self.types.pattern_tys.get(&f.id).cloned(),
        }
    }

    // ----- Blocks and statements -------------------------------------------

    fn block(&self, b: &crate::node_kinds::block::Block) -> typed_ast::Block {
        typed_ast::Block {
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
        params: &[typed_ast::Parameter],
    ) -> typed_ast::Block {
        let mut block = self.block(b);
        block.frame = Some(frame_facts(&block, params));
        block
    }

    fn stmt(&self, s: &stmt::Stmt) -> typed_ast::Stmt {
        typed_ast::Stmt {
            id: s.id,
            kind: self.stmt_kind(s.id, &s.kind),
            span: s.span,
        }
    }

    fn stmt_kind(
        &self,
        stmt_id: crate::node_id::NodeID,
        k: &stmt::StmtKind,
    ) -> typed_ast::StmtKind {
        match k {
            stmt::StmtKind::Expr(e) => typed_ast::StmtKind::Expr(self.expr(e)),
            stmt::StmtKind::If(cond, then, els) => typed_ast::StmtKind::If(
                self.expr(cond),
                self.block(then),
                els.as_ref().map(|b| self.block(b)),
            ),
            stmt::StmtKind::Return(e) => {
                typed_ast::StmtKind::Return(e.as_ref().map(|e| self.expr(e)))
            }
            stmt::StmtKind::Break => typed_ast::StmtKind::Break,
            stmt::StmtKind::Assignment(lhs, rhs) => {
                typed_ast::StmtKind::Assignment(self.boxed(lhs), self.boxed(rhs))
            }
            stmt::StmtKind::Loop(cond, body) => {
                typed_ast::StmtKind::Loop(cond.as_ref().map(|e| self.expr(e)), self.block(body))
            }
            stmt::StmtKind::Continue => typed_ast::StmtKind::Continue,
            stmt::StmtKind::Resume(e) => {
                typed_ast::StmtKind::Resume(e.as_ref().map(|e| self.expr(e)))
            }
            stmt::StmtKind::Handling {
                effect_name, body, ..
            } => typed_ast::StmtKind::Handling {
                effect_name: effect_name.clone(),
                // A clause is a frame; its parameters are the block's args.
                body: self.frame_block(body, &[]),
                contract: self
                    .types
                    .effect_contracts
                    .get(&stmt_id)
                    .expect("typed facts invariant: a handler carries its effect contract")
                    .clone(),
            },
            stmt::StmtKind::For { .. } => self.elaborate_for(stmt_id, k),
        }
    }

    /// Elaborate a first-class `for` into ordinary typed nodes once, so the
    /// final TypedProgram contains its semantic form:
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
    fn elaborate_for(
        &self,
        stmt_id: crate::node_id::NodeID,
        k: &stmt::StmtKind,
    ) -> typed_ast::StmtKind {
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
        let Some(plan) = self.types.for_plans.get(&stmt_id) else {
            return typed_ast::StmtKind::Expr(self.expr(iterable));
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
        let mut nodes: Vec<typed_ast::Node> = vec![];

        // A named source is borrowed as written; an rvalue source — or a
        // `consume`-marked one — binds to the hidden source local so its
        // buffers get ordinary scope-exit drops when the loop ends. `mut`
        // iteration borrows its source in place for the hidden iterator's
        // scope.
        let needs_bind =
            consume || (!mutate && !matches!(source.kind, typed_ast::ExprKind::Variable(_)));
        let iter_receiver = if needs_bind {
            let source_ty = source.ty.clone();
            nodes.push(typed_ast::Node::Decl(self.syn_let(
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
        nodes.push(typed_ast::Node::Decl(self.syn_let(
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
                vec![typed_ast::CallArg {
                    id: plan.mut_store_arg_id,
                    label: crate::label::Label::Positional(0),
                    value: binder_read,
                    mode: None,
                }],
            );
            arm_body.body.push(typed_ast::Node::Stmt(typed_ast::Stmt {
                id: self.syn_id(file),
                span,
                kind: typed_ast::StmtKind::Expr(store_call),
            }));
        }
        let some_arm = typed_ast::MatchArm {
            id: self.syn_id(file),
            pattern: typed_ast::Pattern {
                id: self.syn_id(file),
                span: pattern.span,
                ty: None,
                kind: typed_ast::PatternKind::Variant {
                    enum_name: None,
                    variant_name: "some".to_string(),
                    resolved: None,
                    fields: vec![self.pattern(pattern)],
                },
            },
            body: arm_body,
        };
        let none_arm = typed_ast::MatchArm {
            id: self.syn_id(file),
            pattern: typed_ast::Pattern {
                id: self.syn_id(file),
                span,
                ty: None,
                kind: typed_ast::PatternKind::Variant {
                    enum_name: None,
                    variant_name: "none".to_string(),
                    resolved: None,
                    fields: vec![],
                },
            },
            body: typed_ast::Block {
                id: self.syn_id(file),
                args: vec![],
                span,
                body: vec![typed_ast::Node::Stmt(typed_ast::Stmt {
                    id: self.syn_id(file),
                    span,
                    kind: typed_ast::StmtKind::Break,
                })],
                frame: None,
            },
        };
        let match_expr = typed_ast::Expr {
            id: self.syn_id(file),
            kind: typed_ast::ExprKind::Match(Box::new(next_call), vec![some_arm, none_arm]),
            span,
            ownership: Default::default(),
            ty: plan.body_ty.erase_eff_args(),
            member_resolution: None,
            specialization: None,
            witness_layout: None,
            instantiation: None,
            existential_pack: None,
        };
        nodes.push(typed_ast::Node::Stmt(typed_ast::Stmt {
            id: self.syn_id(file),
            span,
            kind: typed_ast::StmtKind::Loop(
                None,
                typed_ast::Block {
                    id: self.syn_id(file),
                    args: vec![],
                    span,
                    body: vec![typed_ast::Node::Stmt(typed_ast::Stmt {
                        id: self.syn_id(file),
                        span,
                        kind: typed_ast::StmtKind::Expr(match_expr),
                    })],
                    frame: None,
                },
            ),
        }));

        typed_ast::StmtKind::Expr(typed_ast::Expr {
            id: self.syn_id(file),
            kind: typed_ast::ExprKind::Block(typed_ast::Block {
                id: self.syn_id(file),
                args: vec![],
                span,
                body: nodes,
                frame: None,
            }),
            span,
            ownership: Default::default(),
            ty: crate::types::ty::Ty::unit(),
            member_resolution: None,
            specialization: None,
            witness_layout: None,
            instantiation: None,
            existential_pack: None,
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
    ) -> typed_ast::Expr {
        typed_ast::Expr {
            id,
            kind: typed_ast::ExprKind::Variable(name),
            span,
            ownership: Default::default(),
            ty,
            member_resolution: None,
            specialization: None,
            witness_layout: None,
            instantiation: None,
            existential_pack: None,
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
        receiver: typed_ast::Expr,
        label: &str,
        args: Vec<typed_ast::CallArg>,
    ) -> typed_ast::Expr {
        let baked_ty = |id: &crate::node_id::NodeID| {
            self.types
                .node_types
                .get(id)
                .map(|ty| ty.erase_eff_args())
                .unwrap_or(crate::types::ty::Ty::Error)
        };
        let callee = typed_ast::Expr {
            id: callee_id,
            kind: typed_ast::ExprKind::Member(
                Some(Box::new(receiver)),
                crate::label::Label::Named(label.into()),
            ),
            span,
            ownership: Default::default(),
            ty: baked_ty(&callee_id),
            member_resolution: self.types.member_resolutions.get(&callee_id).cloned(),
            specialization: None,
            witness_layout: None,
            instantiation: self.types.instantiations.get(&callee_id).cloned(),
            existential_pack: None,
        };
        typed_ast::Expr {
            id: call_id,
            kind: typed_ast::ExprKind::Call {
                callee: Box::new(callee),
                type_args: vec![],
                args,
            },
            span,
            ownership: Default::default(),
            ty: baked_ty(&call_id),
            member_resolution: self.types.member_resolutions.get(&call_id).cloned(),
            specialization: None,
            witness_layout: None,
            instantiation: self.types.instantiations.get(&call_id).cloned(),
            existential_pack: None,
        }
    }

    fn syn_let(
        &self,
        file: crate::node_id::FileID,
        span: crate::span::Span,
        name: crate::name::Name,
        rhs: typed_ast::Expr,
        source_mode: Option<crate::node_kinds::call_arg::ArgMode>,
    ) -> typed_ast::Decl {
        typed_ast::Decl {
            id: self.syn_id(file),
            span,
            visibility: crate::node_kinds::decl::Visibility::Private,
            kind: typed_ast::DeclKind::Let {
                lhs: typed_ast::Pattern {
                    id: self.syn_id(file),
                    span,
                    kind: typed_ast::PatternKind::Bind(name),
                    ty: None,
                },
                type_annotation: None,
                rhs: Some(rhs),
                source_mode,
            },
        }
    }

    // ----- Functions and declarations --------------------------------------

    fn param(&self, p: &crate::node_kinds::parameter::Parameter) -> typed_ast::Parameter {
        typed_ast::Parameter {
            id: p.id,
            name: p.name.clone(),
            name_span: p.name_span,
            type_annotation: p.type_annotation.clone(),
            span: p.span,
            ty: self
                .types
                .node_types
                .get(&p.id)
                .map(|ty| ty.erase_eff_args()),
        }
    }

    fn params(&self, ps: &[crate::node_kinds::parameter::Parameter]) -> Vec<typed_ast::Parameter> {
        ps.iter().map(|p| self.param(p)).collect()
    }

    fn func(&self, f: &crate::node_kinds::func::Func) -> typed_ast::Func {
        let scheme = f
            .name
            .symbol()
            .ok()
            .and_then(|symbol| self.types.schemes.get(&symbol))
            .cloned()
            .or_else(|| {
                self.types
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
        typed_ast::Func {
            specialization: self.types.field_specializations.get(&f.id).cloned(),
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

    fn body(&self, b: &crate::node_kinds::body::Body) -> typed_ast::Body {
        typed_ast::Body {
            id: b.id,
            decls: b.decls.iter().map(|d| self.decl(d)).collect(),
            span: b.span,
        }
    }

    fn decl(&self, d: &decl::Decl) -> typed_ast::Decl {
        typed_ast::Decl {
            id: d.id,
            kind: self.decl_kind(&d.kind),
            span: d.span,
            visibility: d.visibility,
        }
    }

    fn decl_kind(&self, k: &decl::DeclKind) -> typed_ast::DeclKind {
        match k {
            decl::DeclKind::Macro { .. } => {
                unreachable!("macro declarations are removed before typed-program build")
            }
            decl::DeclKind::Import(import) => typed_ast::DeclKind::Import(import.clone()),
            decl::DeclKind::Effect {
                name,
                generics,
                where_clause,
                params,
                ret,
                ..
            } => typed_ast::DeclKind::Effect {
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
            } => typed_ast::DeclKind::Struct {
                name: name.clone(),
                generics: generics.clone(),
                where_clause: where_clause.clone(),
                body: self.body(body),
            },
            decl::DeclKind::Let {
                lhs,
                type_annotation,
                rhs,
            } => typed_ast::DeclKind::Let {
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
            } => typed_ast::DeclKind::Protocol {
                name: name.clone(),
                generics: generics.clone(),
                where_clause: where_clause.clone(),
                body: self.body(body),
                conformances: conformances.clone(),
            },
            decl::DeclKind::Init { name, params, body } => {
                let params = self.params(params);
                let body = self.frame_block(body, &params);
                typed_ast::DeclKind::Init {
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
            } => typed_ast::DeclKind::Property {
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
                typed_ast::DeclKind::Method {
                    func: Box::new(func),
                    is_static: *is_static,
                    receiver_mode: *receiver_mode,
                }
            }
            decl::DeclKind::Associated {
                generic,
                where_clause,
            } => typed_ast::DeclKind::Associated {
                generic: generic.clone(),
                where_clause: where_clause.clone(),
            },
            decl::DeclKind::Func(func) => typed_ast::DeclKind::Func(self.func(func)),
            decl::DeclKind::Extend {
                binders,
                head,
                conformances,
                where_clause,
                body,
            } => typed_ast::DeclKind::Extend {
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
            } => typed_ast::DeclKind::Enum {
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
            } => typed_ast::DeclKind::EnumVariant {
                name: name.clone(),
                generics: generics.clone(),
                payloads: payloads.clone(),
                payload_labels: payload_labels.clone(),
                result: result.clone(),
            },
            decl::DeclKind::FuncSignature(sig) => typed_ast::DeclKind::FuncSignature(sig.clone()),
            decl::DeclKind::MethodRequirement {
                signature,
                receiver_mode,
            } => typed_ast::DeclKind::MethodRequirement {
                signature: signature.clone(),
                receiver_mode: *receiver_mode,
            },
            decl::DeclKind::InitRequirement { signature } => typed_ast::DeclKind::InitRequirement {
                signature: signature.clone(),
            },
            decl::DeclKind::TypeAlias(name, _span, ty) => {
                typed_ast::DeclKind::TypeAlias(name.clone(), ty.clone())
            }
        }
    }
}
