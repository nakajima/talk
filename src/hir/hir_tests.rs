use crate::compiling::driver::{Driver, DriverConfig, Source};
use crate::hir;
use crate::node::Node;
use crate::node_id::NodeID;

/// Type-check `source` and pair each file's AST roots with the HIR the
/// type-checker lowered them to (`Typed.hir`).
fn lower(source: &str) -> Vec<(Vec<Node>, Vec<hir::Node>)> {
    let typed = Driver::new_bare(vec![Source::from(source)], DriverConfig::new("HirTest"))
        .parse()
        .expect("parse")
        .resolve_names()
        .expect("resolve")
        .type_check();
    assert!(
        !typed.has_errors(),
        "unexpected type errors: {:?}",
        typed.diagnostics()
    );
    typed
        .phase
        .asts
        .iter()
        .filter_map(|(source, ast)| {
            typed
                .phase
                .hir
                .get(source)
                .map(|file| (ast.roots.clone(), file.roots.clone()))
        })
        .collect()
}

/// Every `hir::Expr` id, recursively.
fn hir_expr_ids(nodes: &[hir::Node]) -> Vec<NodeID> {
    let mut ids = Vec::new();
    for node in nodes {
        match node {
            hir::Node::Expr(e) => collect_expr(e, &mut ids),
            hir::Node::Stmt(s) => collect_stmt(s, &mut ids),
            hir::Node::Decl(d) => collect_decl(d, &mut ids),
        }
    }
    ids
}

fn collect_expr(e: &hir::Expr, ids: &mut Vec<NodeID>) {
    ids.push(e.id);
    use hir::ExprKind as K;
    match &e.kind {
        K::InlineIR(ir) => ir.binds.iter().for_each(|b| collect_expr(b, ids)),
        K::As(inner, _) => collect_expr(inner, ids),
        K::CallEffect { args, .. } => args.iter().for_each(|a| collect_expr(&a.value, ids)),
        K::LiteralArray(xs) | K::Tuple(xs) => xs.iter().for_each(|x| collect_expr(x, ids)),
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
        K::Func(f) => collect_block(&f.body, ids),
        K::If(c, t, e2) => {
            collect_expr(c, ids);
            collect_block(t, ids);
            collect_block(e2, ids);
        }
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
        K::LiteralInt(_)
        | K::LiteralFloat(_)
        | K::LiteralTrue
        | K::LiteralFalse
        | K::LiteralString(_)
        | K::Variable(_)
        | K::Constructor(_)
        | K::RowVariable(_) => {}
    }
}

fn collect_stmt(s: &hir::Stmt, ids: &mut Vec<NodeID>) {
    use hir::StmtKind as K;
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

fn collect_block(b: &hir::Block, ids: &mut Vec<NodeID>) {
    ids.extend(hir_expr_ids(&b.body));
}

fn collect_decl(d: &hir::Decl, ids: &mut Vec<NodeID>) {
    use hir::DeclKind as K;
    match &d.kind {
        K::Let { rhs, .. } => {
            if let Some(rhs) = rhs {
                collect_expr(rhs, ids);
            }
        }
        K::Init { body, .. } => collect_block(body, ids),
        K::Method { func, .. } => collect_block(&func.body, ids),
        K::Func(f) => collect_block(&f.body, ids),
        K::Property { default_value, .. } => {
            if let Some(v) = default_value {
                collect_expr(v, ids);
            }
        }
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
        // Building HIR for real code must not hit any panic arm
        // (Unary/Binary/For/Incomplete must already be desugared).
        assert!(!hir_nodes.is_empty());
    }
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
            "HIR must preserve exactly the AST's expression NodeIDs"
        );
        assert!(!hir_ids.is_empty());
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
