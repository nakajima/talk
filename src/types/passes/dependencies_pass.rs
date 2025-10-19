use derive_visitor::{Drive, Visitor};
use petgraph::prelude::DiGraphMap;
use rustc_hash::FxHashMap;

use crate::{
    ast::AST,
    compiling::module::ModuleId,
    label::Label,
    name::Name,
    name_resolution::{
        name_resolver::NameResolved,
        symbol::{
            AssociatedTypeId, DeclaredLocalId, GlobalId, InstanceMethodId, MethodRequirementId,
            ProtocolId, StaticMethodId, Symbol,
        },
    },
    node_id::NodeID,
    node_kinds::{
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        func::Func,
        pattern::{Pattern, PatternKind},
    },
    span::Span,
    types::infer_ty::InferTy,
};

#[derive(Debug, Clone, PartialEq)]
pub enum ConformanceRequirement {
    UnfulfilledInstanceMethod(MethodRequirementId),
    FulfilledInstanceMethod(InstanceMethodId),
}

impl ConformanceRequirement {
    pub fn import(self, module_id: ModuleId) -> ConformanceRequirement {
        match self {
            ConformanceRequirement::UnfulfilledInstanceMethod(id) => {
                ConformanceRequirement::UnfulfilledInstanceMethod(id.import(module_id))
            }
            ConformanceRequirement::FulfilledInstanceMethod(id) => {
                ConformanceRequirement::FulfilledInstanceMethod(id.import(module_id))
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Conformance {
    pub conforming_id: Symbol,
    pub protocol_id: ProtocolId,
    pub requirements: FxHashMap<Label, ConformanceRequirement>,
    pub associated_types: FxHashMap<AssociatedTypeId, InferTy>,
    pub span: Span,
}

#[derive(Debug, Default, Clone)]
pub struct SCCResolved {
    pub graph: DiGraphMap<Binder, ()>,
    pub annotation_map: FxHashMap<Binder, NodeID>,
    pub rhs_map: FxHashMap<Binder, NodeID>,
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Ord, Eq, Hash)]
pub enum Binder {
    Global(GlobalId),
    LocalDecl(DeclaredLocalId),
    InstanceMethod(InstanceMethodId),
    StaticMethod(StaticMethodId),
}

impl From<Binder> for Symbol {
    fn from(value: Binder) -> Self {
        match value {
            Binder::Global(id) => Symbol::Global(id),
            Binder::LocalDecl(id) => Symbol::DeclaredLocal(id),
            Binder::InstanceMethod(id) => Symbol::InstanceMethod(id),
            Binder::StaticMethod(id) => Symbol::StaticMethod(id),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Ord, Eq, Hash)]
pub enum BoundRHS {
    Expr(NodeID),
    Func(NodeID),
}

impl BoundRHS {
    fn id(&self) -> NodeID {
        match self {
            Self::Expr(id) => *id,
            Self::Func(id) => *id,
        }
    }
}

#[derive(Debug, Visitor)]
#[visitor(Decl(enter, exit), Expr(enter))]
pub struct DependenciesPass<'a> {
    scc: &'a mut SCCResolved,
    binder_stack: Vec<(NodeID, Binder)>,
    module_id: ModuleId,
}

impl<'a> DependenciesPass<'a> {
    pub fn drive(ast: &mut AST<NameResolved>, scc: &mut SCCResolved, module_id: ModuleId) {
        let mut pass = DependenciesPass {
            scc,
            binder_stack: Default::default(),
            module_id,
        };

        for root in ast.roots.iter() {
            root.drive(&mut pass);
        }
    }

    fn enter_decl(&mut self, decl: &Decl) {
        let (sym, annotation_id, rhs_id) = match &decl.kind {
            DeclKind::Let {
                lhs:
                    Pattern {
                        kind: PatternKind::Bind(Name::Resolved(sym, _)),
                        ..
                    },
                type_annotation,
                value: Some(rhs),
                ..
            } => (
                sym,
                type_annotation.as_ref().map(|t| t.id),
                BoundRHS::Expr(rhs.id),
            ),
            DeclKind::Method {
                func:
                    box Func {
                        name: Name::Resolved(sym, _),
                        ..
                    },
                ..
            } => (sym, None, BoundRHS::Func(decl.id)),
            _ => {
                return;
            }
        };

        // Skip symbols from external modules - they're already typed
        if sym.module_id().is_some_and(|id| id != self.module_id) {
            return;
        }

        match sym {
            Symbol::Global(global_id) => {
                let binder = Binder::Global(*global_id);
                self.scc.graph.add_node(binder);

                if let Some(id) = annotation_id {
                    self.scc.annotation_map.insert(binder, id);
                }

                self.scc.rhs_map.insert(binder, rhs_id.id());
                self.binder_stack.push((decl.id, binder));
            }
            Symbol::DeclaredLocal(declared_local_id) => {
                let binder = Binder::LocalDecl(*declared_local_id);
                self.scc.graph.add_node(binder);
                self.scc.rhs_map.insert(binder, rhs_id.id());
                self.binder_stack.push((decl.id, binder));
            }
            Symbol::InstanceMethod(method_id) => {
                let binder = Binder::InstanceMethod(*method_id);
                self.scc.graph.add_node(binder);
                self.scc.rhs_map.insert(binder, rhs_id.id());
                self.binder_stack.push((decl.id, binder));
            }
            Symbol::StaticMethod(method_id) => {
                let binder = Binder::StaticMethod(*method_id);
                self.scc.graph.add_node(binder);
                self.scc.rhs_map.insert(binder, rhs_id.id());
                self.binder_stack.push((decl.id, binder));
            }
            _ => unreachable!(),
        }
    }

    fn exit_decl(&mut self, decl: &Decl) {
        let Some((node_id, _)) = self.binder_stack.last() else {
            return;
        };

        if decl.id == *node_id {
            self.binder_stack.pop();
        }
    }

    fn enter_expr(&mut self, expr: &Expr) {
        if let ExprKind::Variable(Name::Resolved(sym, _)) = &expr.kind {
            self.handle_symbol(sym);
        }
    }

    fn handle_symbol(&mut self, sym: &Symbol) {
        match sym {
            Symbol::Global(global_id) => {
                let binder = Binder::Global(*global_id);

                if let Some((_, scope_binder)) = self.binder_stack.last() {
                    self.scc.graph.add_edge(*scope_binder, binder, ());
                }
            }
            Symbol::DeclaredLocal(declared_local_id) => {
                let binder = Binder::LocalDecl(*declared_local_id);

                if let Some((_, scope_binder)) = self.binder_stack.last() {
                    self.scc.graph.add_edge(*scope_binder, binder, ());
                }
            }
            Symbol::StaticMethod(id) => {
                let binder = Binder::StaticMethod(*id);

                if let Some((_, scope_binder)) = self.binder_stack.last() {
                    self.scc.graph.add_edge(*scope_binder, binder, ());
                }
            }
            Symbol::InstanceMethod(id) => {
                let binder = Binder::InstanceMethod(*id);

                if let Some((_, scope_binder)) = self.binder_stack.last() {
                    self.scc.graph.add_edge(*scope_binder, binder, ());
                }
            }
            _ => (),
        }
    }
}

#[cfg(test)]
pub mod tests {
    use rustc_hash::FxHashSet;

    use crate::{
        ast::AST,
        compiling::module::ModuleId,
        name_resolution::{name_resolver::NameResolved, symbol::GlobalId},
        types::{
            passes::{
                dependencies_pass::{Binder, DependenciesPass, SCCResolved},
                type_resolve_pass::tests::type_header_resolve_pass,
            },
            type_session::TypeSession,
        },
    };

    pub fn resolve_dependencies(
        code: &'static str,
    ) -> (AST<NameResolved>, SCCResolved, TypeSession) {
        let (mut ast, session) = type_header_resolve_pass(code);
        let mut scc = SCCResolved::default();
        DependenciesPass::drive(&mut ast, &mut scc, ModuleId::default());

        (ast, scc, session)
    }

    fn graph_nodes(code: &'static str) -> Vec<Binder> {
        let (_, scc, _) = resolve_dependencies(code);
        let mut nodes: Vec<Binder> = scc.graph.nodes().collect();
        nodes.sort();
        nodes
    }

    fn graph_edges(code: &'static str) -> FxHashSet<(Binder, Binder)> {
        let (_, scc, _) = resolve_dependencies(code);
        scc.graph.all_edges().map(|(u, v, _)| (u, v)).collect()
    }

    #[test]
    fn graph_records_orphan_function_as_node() {
        let ns = graph_nodes(
            r#"
        func a() { 0 }
    "#,
        );
        assert!(ns.contains(&Binder::Global(GlobalId::from(1))), "{ns:?}");
        let es = graph_edges(r#"func a(){ 0 }"#);
        assert!(es.is_empty(), "{es:?}");
    }

    #[test]
    fn graph_linear_dependency_creates_single_edge() {
        let es = graph_edges(
            r#"
        func a(){ b() }
        func b(){ 0 }
    "#,
        );
        assert_eq!(
            es,
            FxHashSet::from_iter([(
                Binder::Global(GlobalId::from(1)),
                Binder::Global(GlobalId::from(2))
            )]),
            "{es:?}"
        );
    }

    #[test]
    fn graph_mutual_recursion_creates_cycle_edges() {
        let es = graph_edges(
            r#"
        func odd(){ even() }
        func even(){ odd() }
    "#,
        );
        assert_eq!(
            es,
            FxHashSet::from_iter([
                (
                    Binder::Global(GlobalId::from(1)),
                    Binder::Global(GlobalId::from(2))
                ),
                (
                    Binder::Global(GlobalId::from(2)),
                    Binder::Global(GlobalId::from(1))
                )
            ]),
            "{es:?}"
        );
    }

    #[test]
    fn graph_ignores_locals_and_types() {
        // Using parameters/locals or type names must NOT introduce edges.
        let es = graph_edges(
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
        let es = graph_edges(
            r#"
        func a(){ b(); b() }
        func b(){ 0 }
    "#,
        );
        assert_eq!(
            es,
            FxHashSet::from_iter([(
                Binder::Global(GlobalId::from(1)),
                Binder::Global(GlobalId::from(2))
            )]),
            "{es:?}"
        );
    }

    #[test]
    #[ignore = "we dont have builtin funcs yet"]
    fn graph_ignores_builtins() {
        // Calls to builtins (no DeclId) must not create edges.
        let es = graph_edges(
            r#"
        func f(){ print(1) }
    "#,
        );
        assert!(es.is_empty(), "{es:?}");
    }

    #[test]
    fn graph_no_edge_for_property_projection() {
        // Field access is a projection, not a term ref; no edges.
        let es = graph_edges(
            r#"
        struct P { let v: Int }
        func f(p: P) { p.v }
    "#,
        );
        assert!(es.is_empty(), "{es:?}");
    }

    #[test]
    fn graph_static_methods_mutual_recursion_creates_cycle_edges() {
        let edges = graph_edges(
            r#"
        struct Person {
            static func first()  { second() }
            static func second() { first() }
        }
        "#,
        );

        use super::Binder;
        use crate::name_resolution::symbol::StaticMethodId;

        let expected = FxHashSet::from_iter([
            (
                Binder::StaticMethod(StaticMethodId::from(1)),
                Binder::StaticMethod(StaticMethodId::from(2)),
            ),
            (
                Binder::StaticMethod(StaticMethodId::from(2)),
                Binder::StaticMethod(StaticMethodId::from(1)),
            ),
        ]);

        assert_eq!(edges, expected, "{edges:?}");
    }

    #[test]
    #[ignore = "need to handle members"]
    fn graph_instance_methods_mutual_recursion_creates_cycle_edges() {
        let edges = graph_edges(
            r#"
        struct Counter {
            func first()  { self.second() }
            func second() { self.first()  }
        }
        "#,
        );

        use super::Binder;
        use crate::name_resolution::symbol::InstanceMethodId;

        let expected = FxHashSet::from_iter([
            (
                Binder::InstanceMethod(InstanceMethodId::from(1)),
                Binder::InstanceMethod(InstanceMethodId::from(2)),
            ),
            (
                Binder::InstanceMethod(InstanceMethodId::from(2)),
                Binder::InstanceMethod(InstanceMethodId::from(1)),
            ),
        ]);

        assert_eq!(edges, expected, "{edges:?}");
    }

    #[test]
    #[ignore = "need to handle members"]
    fn graph_global_calls_static_method_creates_edge() {
        let edges = graph_edges(
            r#"
        struct Math {
            static func provide() { 123 }
        }
        func use() { Math.provide() }
        "#,
        );

        use super::Binder;
        use crate::name_resolution::symbol::{GlobalId, StaticMethodId};

        let expected = FxHashSet::from_iter([(
            Binder::Global(GlobalId::from(1)),
            Binder::StaticMethod(StaticMethodId::from(1)),
        )]);

        assert_eq!(edges, expected, "{edges:?}");
    }

    #[test]
    #[ignore = "need to handle members"]
    fn graph_member_static_call_creates_edge() {
        let edges = graph_edges(
            r#"
        struct Person {
            static func get() { 123 }
        }
        func use() { Person.get() }
        "#,
        );

        use super::Binder;
        use crate::name_resolution::symbol::{GlobalId, StaticMethodId};

        let expected = FxHashSet::from_iter([(
            Binder::Global(GlobalId::from(1)),
            Binder::StaticMethod(StaticMethodId::from(1)),
        )]);

        assert_eq!(edges, expected, "{edges:?}");
    }

    #[test]
    #[ignore = "need to handle members"]
    fn graph_member_instance_call_creates_edge() {
        let edges = graph_edges(
            r#"
        struct Chain {
            func a() { self.b() }
            func b() { 0 }
        }
        "#,
        );

        use super::Binder;
        use crate::name_resolution::symbol::InstanceMethodId;

        let expected = FxHashSet::from_iter([(
            Binder::InstanceMethod(InstanceMethodId::from(1)),
            Binder::InstanceMethod(InstanceMethodId::from(2)),
        )]);

        assert_eq!(edges, expected, "{edges:?}");
    }
}
