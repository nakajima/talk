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
        K::Block(b) => collect_block(b, ids),
        K::Call {
            callee,
            args,
            trailing_block,
            ..
        } => {
            collect_expr(callee, ids);
            args.iter().for_each(|a| collect_expr(&a.value, ids));
            if let Some(b) = trailing_block {
                collect_block(b, ids);
            }
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
        K::Return(e) | K::Continue(e) => {
            if let Some(e) = e {
                collect_expr(e, ids);
            }
        }
        K::Break => {}
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
