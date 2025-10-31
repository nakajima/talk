#[cfg(test)]
pub mod tests {
    use crate::name_resolution::{name_resolver_tests::tests::resolve, symbol::Symbol};

    #[test]
    fn registers_edges_for_global_func_calls() {
        let types = resolve(
            "
            func a() { 123 }
            func b() { a() ; a() } // Twice to make sure we don't have dups
          ",
        );

        // b references a...
        assert_eq!(
            vec![Symbol::Global(1.into())],
            types
                .phase
                .scc_graph
                .neighbors_for(&Symbol::Global(2.into()))
        );

        // but a does not reference b
        assert!(
            types
                .phase
                .scc_graph
                .neighbors_for(&Symbol::Global(1.into()))
                .is_empty()
        );
    }

    #[test]
    fn registers_mutual_recursion_edges_for_global_func_calls() {
        let types = resolve(
            "
            func a() { b() }
            func b() { a() }
          ",
        );

        assert_eq!(
            vec![Symbol::Global(2.into())],
            types
                .phase
                .scc_graph
                .neighbors_for(&Symbol::Global(1.into()))
        );

        assert_eq!(
            vec![Symbol::Global(1.into())],
            types
                .phase
                .scc_graph
                .neighbors_for(&Symbol::Global(2.into()))
        );
    }

    #[test]
    fn graph_ignores_builtins() {
        let types = resolve(
            "
            func f(){ __IR(\"add $? int 1 2\") }
          ",
        );

        assert!(
            types
                .phase
                .scc_graph
                .neighbors_for(&Symbol::Global(1.into()))
                .is_empty()
        );
    }

    #[test]
    fn contains_node_for_structs() {
        // We handle all instance methods for a struct in one go so we don't need to add individual nodes
        // for instance methods
        let types = resolve(
            r#"
        struct Person {
            func first()  { self.second() }
            func second() { self.first() }
        }
        "#,
        );

        assert_eq!(
            types.phase.scc_graph.groups(),
            vec![vec![Symbol::Struct(1.into())]],
        );
    }

    #[test]
    fn creates_edge_for_type_with_instance_method_calling_global() {
        let types = resolve(
            r#"
        func fizz() {}
        struct Person {
            func first() { fizz() }
        }
        "#,
        );

        assert_eq!(
            vec![Symbol::Global(1.into())],
            types
                .phase
                .scc_graph
                .neighbors_for(&Symbol::Struct(1.into()))
        );
    }

    #[test]
    fn static_methods_are_under_struct() {
        let types = resolve(
            r#"
        struct Person {
            static func first()  { Person.second() }
            static func second() { Person.first() }
        }
        "#,
        );

        assert_eq!(
            types.phase.scc_graph.groups(),
            vec![vec![Symbol::Struct(1.into())],],
        );
    }

    #[test]
    fn static_methods_can_reference_globals() {
        let types = resolve(
            r#"
          func helper() {}
          struct Person {
              static func create() { helper() }
          }
          "#,
        );

        assert_eq!(
            vec![Symbol::Global(1.into())],
            types
                .phase
                .scc_graph
                .neighbors_for(&Symbol::Struct(1.into()))
        );
    }
}
