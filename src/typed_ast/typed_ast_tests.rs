use crate::compiling::driver::{Driver, DriverConfig, Source};
use crate::node::Node;
use crate::node_id::NodeID;
use crate::typed_ast;

/// Type-check `source` and pair each file's AST roots with the typed tree the
/// type checker produced.
fn lower(source: &str) -> Vec<(Vec<Node>, Vec<typed_ast::Node>)> {
    let resolved = Driver::new_bare(
        vec![Source::from(source)],
        DriverConfig::new("TypedAstTest"),
    )
    .parse()
    .expect("parse")
    .resolve_names()
    .expect("resolve");
    // `type_check` consumes the AST into the typed compiler tree, so capture the AST roots here
    // to pair them against the typed compiler tree roots.
    let asts = resolved.phase.asts.clone();
    let typed = resolved.type_check();
    assert!(
        !typed.has_errors(),
        "unexpected type errors: {:?}",
        typed.diagnostics()
    );
    asts.iter()
        .filter_map(|(source, ast)| {
            typed
                .phase
                .program
                .files()
                .get(source)
                .map(|file| (ast.roots.clone(), file.roots.clone()))
        })
        .collect()
}

/// Every typed expression id, recursively.
fn hir_expr_ids(nodes: &[typed_ast::Node]) -> Vec<NodeID> {
    let mut ids = Vec::new();
    for node in nodes {
        match node {
            typed_ast::Node::Expr(e) => collect_expr(e, &mut ids),
            typed_ast::Node::Stmt(s) => collect_stmt(s, &mut ids),
            typed_ast::Node::Decl(d) => collect_decl(d, &mut ids),
        }
    }
    ids
}

fn collect_expr(e: &typed_ast::Expr, ids: &mut Vec<NodeID>) {
    ids.push(e.id);
    use typed_ast::ExprKind as K;
    match &e.kind {
        K::InlineIR(ir) => ir.binds.iter().for_each(|b| collect_expr(b, ids)),
        K::CallEffect { args, .. } => args.iter().for_each(|a| collect_expr(&a.value, ids)),
        K::LiteralArray(xs) | K::Tuple(xs) | K::Con { args: xs, .. } => {
            xs.iter().for_each(|x| collect_expr(x, ids))
        }
        K::Block(b) | K::Unsafe(b) => collect_block(b, ids),
        K::Call { callee, args, .. } => {
            collect_expr(callee, ids);
            args.iter().for_each(|a| collect_expr(&a.value, ids));
        }
        K::Member(recv, _) => {
            if let Some(r) = recv {
                collect_expr(r, ids);
            }
        }
        K::Proj(recv, ..) | K::Clone(recv) => collect_expr(recv, ids),
        K::Func(f) => collect_block(&f.body, ids),
        K::Match(s, arms) => {
            collect_expr(s, ids);
            arms.iter().for_each(|a| collect_block(&a.body, ids));
        }
        K::RecordLiteral { fields, spread } => {
            fields.iter().for_each(|f| collect_expr(&f.value, ids));
            if let Some(s) = spread {
                collect_expr(s, ids);
            }
        }
        K::Lit(_) | K::Variable(_) | K::Constructor(_) | K::Temp(_) => {}
    }
}

fn collect_stmt(s: &typed_ast::Stmt, ids: &mut Vec<NodeID>) {
    use typed_ast::StmtKind as K;
    match &s.kind {
        K::Expr(e) => collect_expr(e, ids),
        K::If(c, t, e2) => {
            collect_expr(c, ids);
            collect_block(t, ids);
            if let Some(b) = e2 {
                collect_block(b, ids);
            }
        }
        K::Return(e) | K::Resume(e) => {
            if let Some(e) = e {
                collect_expr(e, ids);
            }
        }
        K::Break | K::Continue => {}
        K::Assignment(l, r) => {
            collect_expr(l, ids);
            collect_expr(r, ids);
        }
        K::Loop(c, b) => {
            if let Some(c) = c {
                collect_expr(c, ids);
            }
            collect_block(b, ids);
        }
        K::Handling { body, .. } => collect_block(body, ids),
    }
}

fn collect_block(b: &typed_ast::Block, ids: &mut Vec<NodeID>) {
    ids.extend(hir_expr_ids(&b.body));
}

fn collect_decl(d: &typed_ast::Decl, ids: &mut Vec<NodeID>) {
    use typed_ast::DeclKind as K;
    match &d.kind {
        K::Let { rhs: Some(rhs), .. } => collect_expr(rhs, ids),
        K::Init { body, .. } => collect_block(body, ids),
        K::Method { func, .. } => collect_block(&func.body, ids),
        K::Func(f) => collect_block(&f.body, ids),
        K::Property {
            default_value: Some(value),
            ..
        } => collect_expr(value, ids),
        K::Struct { body, .. }
        | K::Protocol { body, .. }
        | K::Extend { body, .. }
        | K::Enum { body, .. } => body.decls.iter().for_each(|d| collect_decl(d, ids)),
        _ => {}
    }
}

#[test]
fn lowers_a_construct_diverse_program_without_panicking() {
    // Exercises: structs, methods, generics, closures (captures), match, records,
    // arrays, tuples, control flow, assignment, loops, effects/handlers.
    // Verbatim from a passing types test: enum + generics + method (self receiver)
    // + source-level `match` (Pattern -> body) + variant construction + method call.
    let source = "
            enum Fizz<T> {
                case foo(T), bar(T)

                func unwrap() {
                    match self {
                        Fizz.foo(t) -> t,
                        Fizz.bar(t) -> t
                    }
                }
            }

            Fizz.foo(123).unwrap()
            ";
    for (_ast_roots, hir_nodes) in lower(source) {
        // Building the typed compiler tree for real code must not hit any panic arm
        // (Unary/Binary/For/Incomplete must already be desugared).
        assert!(!hir_nodes.is_empty());
    }
}

#[test]
fn functions_carry_their_finalized_effect_scheme() {
    use derive_visitor::Drive;

    let source = "// no-core\neffect 'a() -> ()\nfunc f() 'a -> () { () }";
    let mut effect_counts = vec![];
    for (_, hir_nodes) in lower(source) {
        let mut collect = derive_visitor::visitor_enter_fn(|func: &typed_ast::Func| {
            if func.name.name_str() == "f"
                && let crate::types::ty::Ty::Func(_, _, effects) = &func.scheme.ty
            {
                effect_counts.push(effects.effects.len());
            }
        });
        for node in &hir_nodes {
            node.drive(&mut collect);
        }
    }
    assert_eq!(effect_counts, vec![1]);
}

#[test]
fn preserves_node_ids_one_to_one() {
    let source = "func f(x: Int) -> Int {\n\tlet y = x\n\ty\n}\nf(x: 2)";
    for (ast_roots, hir_nodes) in lower(source) {
        let mut ast_ids = ast_expr_ids(&ast_roots);
        let mut hir_ids = hir_expr_ids(&hir_nodes);
        ast_ids.sort();
        hir_ids.sort();
        assert_eq!(
            ast_ids, hir_ids,
            "Typed compiler tree must preserve exactly the AST's expression NodeIDs"
        );
        assert!(!hir_ids.is_empty());
    }
}

#[test]
fn or_pattern_binders_collect_once() {
    // `.a(s) | .b(s)` binds one `s`: consumers register scope locals (and
    // schedule drops) per binder, so a duplicate would double-drop.
    let source = "enum E {\n\tcase a(Int)\n\tcase b(Int)\n}\nfunc f(e: E) -> Int {\n\tmatch e {\n\t\t.a(s) | .b(s) -> s,\n\t}\n}";
    let mut or_binders = None;
    for (_, hir_nodes) in lower(source) {
        visit_patterns(&hir_nodes, &mut |pattern: &typed_ast::Pattern| {
            if matches!(pattern.kind, typed_ast::PatternKind::Or(_)) {
                or_binders = Some(pattern.collect_binders());
            }
        });
    }
    let binders = or_binders.expect("source contains an or-pattern");
    assert_eq!(
        binders.len(),
        1,
        "the shared binder must be collected once, got {binders:?}"
    );
}

#[test]
fn literals_carry_canonical_values() {
    use derive_visitor::Drive;

    // The typed tree publishes checked literal values — underscores
    // stripped, escapes processed — so lowering never reparses source
    // text (ADR 0038).
    let source = "// no-core\nlet n = 1_000\nlet f = 2_5.5\nlet s = \"a\\nb\"\n()";
    let mut literals = vec![];
    for (_, hir_nodes) in lower(source) {
        let mut collect = derive_visitor::visitor_enter_fn(|expr: &typed_ast::Expr| {
            if let typed_ast::ExprKind::Lit(literal) = &expr.kind {
                literals.push(literal.clone());
            }
        });
        for node in &hir_nodes {
            node.drive(&mut collect);
        }
    }
    assert!(
        literals.contains(&typed_ast::Literal::Int(1000)),
        "expected the checked integer value: {literals:?}"
    );
    assert!(
        literals.contains(&typed_ast::Literal::Float(typed_ast::FloatValue(25.5))),
        "expected the checked float value: {literals:?}"
    );
    assert!(
        literals.contains(&typed_ast::Literal::String("a\nb".into())),
        "expected the unescaped string value: {literals:?}"
    );
}

#[test]
fn pattern_literals_carry_canonical_values() {
    let source =
        "// no-core\nfunc f(n: Int) -> Int {\n\tmatch n {\n\t\t1_0 -> 1,\n\t\t_ -> 0,\n\t}\n}";
    let mut ints = vec![];
    for (_, hir_nodes) in lower(source) {
        visit_patterns(&hir_nodes, &mut |pattern: &typed_ast::Pattern| {
            if let typed_ast::PatternKind::LiteralInt(value) = &pattern.kind {
                ints.push(*value);
            }
        });
    }
    assert_eq!(ints, vec![10], "expected the checked pattern value");
}

#[test]
fn handler_clause_binders_carry_their_checked_types() {
    use derive_visitor::Drive;

    // Clause binders take the effect's declared parameter types; the
    // typed tree publishes them on the parameter nodes (ADR 0038) so
    // lowering never reloads the effect signature for binder types.
    let source = "// no-core\neffect 'ask(question: Int) -> Int\n#handle 'ask { q in\n\t'continue q\n}\n'ask(question: 1)\n()";
    let mut clause_param_tys = vec![];
    for (_, hir_nodes) in lower(source) {
        let mut collect = derive_visitor::visitor_enter_fn(|stmt: &typed_ast::Stmt| {
            if let typed_ast::StmtKind::Handling { body, .. } = &stmt.kind {
                clause_param_tys.extend(body.args.iter().map(|param| param.ty.clone()));
            }
        });
        for node in &hir_nodes {
            node.drive(&mut collect);
        }
    }
    assert_eq!(clause_param_tys.len(), 1, "one clause binder");
    assert!(
        clause_param_tys[0].is_some(),
        "the binder carries the effect's checked parameter type"
    );
}

#[test]
fn record_patterns_carry_row_layout_slots() {
    // A record pattern publishes one slot per row field in the row's
    // layout order — the slot type and the covering written field
    // (ADR 0038). Lowering builds cells from these instead of matching
    // labels against a decomposed row.
    let source =
        "// no-core\nlet rec = { b: true, a: 1 }\nlet n = match rec {\n\t{ a, .. } -> a,\n}\n()";
    let mut slot_sets = vec![];
    for (_, hir_nodes) in lower(source) {
        visit_patterns(&hir_nodes, &mut |pattern: &typed_ast::Pattern| {
            if let typed_ast::PatternKind::Record { slots, .. } = &pattern.kind {
                slot_sets.push(slots.clone());
            }
        });
    }
    assert_eq!(slot_sets.len(), 1, "one record pattern");
    let slots = slot_sets[0]
        .as_ref()
        .expect("a closed row publishes its layout");
    assert_eq!(slots.len(), 2, "one slot per row field: {slots:?}");
    let covered: Vec<bool> = slots.iter().map(|(_, sub)| sub.is_some()).collect();
    assert_eq!(
        covered.iter().filter(|c| **c).count(),
        1,
        "exactly the written field is covered: {slots:?}"
    );
}

#[test]
fn struct_patterns_carry_declaration_order_slots() {
    // A struct pattern publishes one slot per stored field in
    // declaration order — the instantiated field type and which written
    // sub-pattern covers it (ADR 0038). Lowering builds its cells from
    // these instead of re-substituting catalog field types.
    let source = "// no-core\nstruct P {\n\tlet x: Int\n\tlet y: Bool\n}\nfunc f(p: P) -> Bool {\n\tmatch p {\n\t\tP { y: flag, .. } -> flag,\n\t}\n}";
    let mut slot_sets = vec![];
    for (_, hir_nodes) in lower(source) {
        visit_patterns(&hir_nodes, &mut |pattern: &typed_ast::Pattern| {
            if let typed_ast::PatternKind::Struct { slots, .. } = &pattern.kind {
                slot_sets.push(slots.clone());
            }
        });
    }
    assert_eq!(slot_sets.len(), 1, "one struct pattern");
    let slots = &slot_sets[0];
    assert_eq!(slots.len(), 2, "one slot per stored field: {slots:?}");
    assert!(
        format!("{:?}", slots[0].0).contains("Int") && slots[0].1.is_none(),
        "x is left to `..`: {slots:?}"
    );
    assert!(
        format!("{:?}", slots[1].0).contains("Bool") && slots[1].1 == Some(0),
        "y is covered by the written sub-pattern: {slots:?}"
    );
}

#[test]
fn patterns_carry_their_checked_occurrence_types() {
    // Every checked pattern occurrence carries its type (ADR 0038):
    // lowering reads binder and component types off the tree instead of
    // re-decomposing scrutinee types.
    let source = "// no-core\nlet (a, b) = (1, true)\n()";
    let mut bind_tys = vec![];
    for (_, hir_nodes) in lower(source) {
        visit_patterns(&hir_nodes, &mut |pattern: &typed_ast::Pattern| {
            if matches!(pattern.kind, typed_ast::PatternKind::Bind(_)) {
                bind_tys.push(pattern.ty.clone());
            }
        });
    }
    assert_eq!(bind_tys.len(), 2, "two binders");
    assert!(
        bind_tys.iter().all(|ty| ty.is_some()),
        "every source binder carries its checked type: {bind_tys:?}"
    );
    let rendered: Vec<String> = bind_tys
        .iter()
        .map(|ty| format!("{:?}", ty.as_ref().unwrap()))
        .collect();
    assert!(
        rendered[0].contains("Int") && rendered[1].contains("Bool"),
        "component types come from the checked tuple: {rendered:?}"
    );
}

#[test]
fn effect_sites_carry_their_contracts() {
    use derive_visitor::Drive;

    // Perform sites and handlers both carry the effect's checked
    // contract (ADR 0038): declared parameter types and the type-generic
    // layout, so lowering never reloads effect signatures.
    let source = "// no-core\neffect 'ask(question: Int) -> Int\n#handle 'ask { q in\n\t'continue q\n}\n'ask(question: 1)\n()";
    let mut call_contracts = vec![];
    let mut handler_contracts = vec![];
    for (_, hir_nodes) in lower(source) {
        let mut collect_calls = derive_visitor::visitor_enter_fn(|expr: &typed_ast::Expr| {
            if let typed_ast::ExprKind::CallEffect { contract, .. } = &expr.kind {
                call_contracts.push(contract.clone());
            }
        });
        let mut collect_handlers = derive_visitor::visitor_enter_fn(|stmt: &typed_ast::Stmt| {
            if let typed_ast::StmtKind::Handling { contract, .. } = &stmt.kind {
                handler_contracts.push(contract.clone());
            }
        });
        for node in &hir_nodes {
            node.drive(&mut collect_calls);
            node.drive(&mut collect_handlers);
        }
    }
    assert_eq!(call_contracts.len(), 1, "one perform site");
    assert_eq!(
        call_contracts[0].params.len(),
        1,
        "the perform carries the declared parameter: {call_contracts:?}"
    );
    assert_eq!(handler_contracts.len(), 1, "one handler");
    assert_eq!(
        handler_contracts[0].params.len(),
        1,
        "the handler carries the declared parameter: {handler_contracts:?}"
    );
}

#[test]
fn variant_patterns_carry_their_resolution() {
    // Typing resolves a variant pattern's constructor; the typed tree
    // bakes that identity on the pattern node (ADR 0038), so lowering
    // never resolves variants by name against the catalog.
    let source = "enum E {\n\tcase a(Int)\n\tcase b(Int)\n}\nfunc f(e: E) -> Int {\n\tmatch e {\n\t\t.a(s) -> s,\n\t\t.b(s) -> s,\n\t}\n}";
    let mut resolutions = vec![];
    for (_, hir_nodes) in lower(source) {
        visit_patterns(&hir_nodes, &mut |pattern: &typed_ast::Pattern| {
            if let typed_ast::PatternKind::Variant { resolved, .. } = &pattern.kind {
                resolutions.push(*resolved);
            }
        });
    }
    assert_eq!(resolutions.len(), 2, "two variant patterns");
    assert!(
        resolutions.iter().all(|resolved| resolved.is_some()),
        "every source variant pattern carries its checked constructor: {resolutions:?}"
    );
}

#[test]
fn frame_roots_carry_capture_and_cell_facts() {
    use derive_visitor::Drive;

    // Frame-root blocks publish free variables and assignment-conversion
    // sets (ADR 0038): lowering builds closure environments and cells
    // from these without re-walking the tree.
    let source = "// no-core\nfunc outer() -> Int {\n\tlet x = 1\n\tlet bump = func() -> () {\n\t\tx = x\n\t}\n\tbump()\n\tx\n}";
    let mut frames = vec![];
    for (_, hir_nodes) in lower(source) {
        let mut collect = derive_visitor::visitor_enter_fn(|func: &typed_ast::Func| {
            frames.push((func.name.name_str(), func.body.frame.clone()));
        });
        for node in &hir_nodes {
            node.drive(&mut collect);
        }
    }
    let outer = frames
        .iter()
        .find(|(name, _)| name == "outer")
        .and_then(|(_, frame)| frame.clone())
        .expect("outer carries frame facts");
    let closure = frames
        .iter()
        .find(|(name, _)| name != "outer")
        .and_then(|(_, frame)| frame.clone())
        .expect("the closure carries frame facts");
    assert_eq!(
        closure.captured.len(),
        1,
        "the closure captures exactly `x`: {closure:?}"
    );
    let x = closure.captured[0];
    assert!(
        outer.nested_refs.contains(&x),
        "`x` is referenced under a nested function: {outer:?}"
    );
    assert!(
        outer.celled.contains(&x),
        "`x` is assigned in the frame and shared with the closure: {outer:?}"
    );
    assert!(
        outer.captured.is_empty(),
        "a top-level function has no free variables: {outer:?}"
    );
}

fn visit_patterns(nodes: &[typed_ast::Node], f: &mut impl FnMut(&typed_ast::Pattern)) {
    use derive_visitor::{Drive, Visitor};

    struct Collect<'a, F>(&'a mut F);
    impl<F: FnMut(&typed_ast::Pattern)> Visitor for Collect<'_, F> {
        fn visit(&mut self, item: &dyn std::any::Any, event: derive_visitor::Event) {
            if matches!(event, derive_visitor::Event::Enter)
                && let Some(pattern) = item.downcast_ref::<typed_ast::Pattern>()
            {
                (self.0)(pattern);
            }
        }
    }
    let mut collect = Collect(f);
    for node in nodes {
        node.drive(&mut collect);
    }
}

/// Collect AST `Expr` ids via the derive_visitor `Drive` walk (the `Expr` node is
/// visited even though its `id` field is `#[drive(skip)]`).
fn ast_expr_ids(roots: &[Node]) -> Vec<NodeID> {
    use derive_visitor::{Drive, Visitor};

    #[derive(Default)]
    struct Collect {
        ids: Vec<NodeID>,
    }
    impl Visitor for Collect {
        fn visit(&mut self, item: &dyn std::any::Any, event: derive_visitor::Event) {
            if matches!(event, derive_visitor::Event::Enter)
                && let Some(expr) = item.downcast_ref::<crate::node_kinds::expr::Expr>()
            {
                self.ids.push(expr.id);
            }
        }
    }
    let mut collect = Collect::default();
    for root in roots {
        root.drive(&mut collect);
    }
    collect.ids
}
