#[cfg(test)]
mod tests {
    fn graph_nodes(code: &'static str) -> (Vec<NodeID>, FxHashSet<NodeID>) {
        let ast = resolve(code);
        (
            ast.roots.iter().map(|r| r.node_id()).collect(),
            ast.phase
                .dependency_graph // <-- rename if your field is different
                .nodes()
                .collect(),
        )
    }

    fn graph_edges(code: &'static str) -> (Vec<NodeID>, FxHashSet<(NodeID, NodeID)>) {
        let ast = resolve(code);
        (
            ast.roots.iter().map(|r| r.node_id()).collect(),
            ast.phase
                .dependency_graph // <-- rename if your field is different
                .all_edges()
                .map(|(u, v, _)| (u, v))
                .collect(),
        )
    }

    #[test]
    fn graph_records_orphan_function_as_node() {
        let (ids, ns) = graph_nodes(
            r#"
        func a() { 0 }
    "#,
        );
        assert!(ns.contains(&ids[0]), "{ns:?}");
        let (_, es) = graph_edges(r#"func a(){ 0 }"#);
        assert!(es.is_empty(), "{es:?}");
    }

    #[test]
    fn graph_linear_dependency_creates_single_edge() {
        let (ids, es) = graph_edges(
            r#"
        func a(){ b() }
        func b(){ 0 }
    "#,
        );
        assert_eq!(es, FxHashSet::from_iter([(ids[0], ids[1])]), "{es:?}");
    }

    #[test]
    fn graph_mutual_recursion_creates_cycle_edges() {
        let (ids, es) = graph_edges(
            r#"
        func odd(){ even() }
        func even(){ odd() }
    "#,
        );
        assert_eq!(
            es,
            FxHashSet::from_iter([(ids[0], ids[1]), (ids[1], ids[0])]),
            "{es:?}"
        );
    }

    #[test]
    fn graph_ignores_locals_and_types() {
        // Using parameters/locals or type names must NOT introduce edges.
        let (_, es) = graph_edges(
            r#"
        struct Person { let age: Int }
        func f(x: Person) { let y = x; 123 }
        func g(){ 0 }
    "#,
        );
        assert!(es.is_empty(), "{es:?}");
    }

    #[test]
    fn graph_dedups_multiple_calls_to_same_target() {
        let (ids, es) = graph_edges(
            r#"
        func a(){ b(); b() }
        func b(){ 0 }
    "#,
        );
        assert_eq!(es, FxHashSet::from_iter([(ids[0], ids[1])]), "{es:?}");
    }

    #[test]
    #[ignore = "we dont have builtin funcs yet"]
    fn graph_ignores_builtins() {
        // Calls to builtins (no DeclId) must not create edges.
        let (_, es) = graph_edges(
            r#"
        func f(){ print(1) }
    "#,
        );
        assert!(es.is_empty(), "{es:?}");
    }

    #[test]
    fn graph_no_edge_for_property_projection() {
        // Field access is a projection, not a term ref; no edges.
        let (_, es) = graph_edges(
            r#"
        struct P { let v: Int }
        func f(p: P) { p.v }
    "#,
        );
        assert!(es.is_empty(), "{es:?}");
    }

    // If your resolver resolves method member calls to a DeclId in the body walk,
    // you can enable this. If not yet, skip this test for now.
    #[test]
    fn graph_records_method_to_method_edge() {
        let (_, es) = graph_edges(
            r#"
        struct S {
            func a(){ self.b() }
            func b(){ 0 }
        }
    "#,
        );
        // Expect a -> b (IDs consistent with your existing numbering)
        assert_eq!(es, FxHashSet::from_iter([(NodeID(2), NodeID(3))]), "{es:?}");
    }

    // If you register init bodies as nodes and resolve their calls, enable this too.
    #[test]
    fn graph_records_init_to_function_edge() {
        let (_, es) = graph_edges(
            r#"
        func h(){ 0 }
        struct S { init(){ h() } }
    "#,
        );
        // init -> h (adjust IDs if needed)
        assert_eq!(es, FxHashSet::from_iter([(NodeID(3), NodeID(1))]), "{es:?}");
    }
}
