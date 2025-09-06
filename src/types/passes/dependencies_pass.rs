use derive_visitor::{Drive, Visitor};
use petgraph::prelude::DiGraphMap;
use rustc_hash::FxHashMap;

use crate::{
    ast::AST,
    label::Label,
    name::Name,
    name_resolution::{
        name_resolver::NameResolved,
        symbol::{DeclaredLocalId, GlobalId, Symbol, TypeId},
    },
    node_id::NodeID,
    node_kinds::{
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        func::Func,
        pattern::{Pattern, PatternKind},
    },
    types::{
        passes::{inference_pass::Inferenced, type_header_resolve_pass::HeadersResolved},
        ty::Ty,
        type_session::{TypeDef, TypeSession, TypingPhase},
    },
};

#[derive(Debug, Clone)]
pub struct SCCResolved {
    pub graph: DiGraphMap<Binder, ()>,
    pub rhs_map: FxHashMap<Binder, NodeID>,
    pub type_constructors: FxHashMap<TypeId, TypeDef<Ty>>,
    pub protocols: FxHashMap<TypeId, TypeDef<Ty>>,
}

impl TypingPhase for SCCResolved {
    type Next = Inferenced;
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Ord, Eq, Hash)]
pub enum Binder {
    Global(GlobalId),
    LocalDecl(DeclaredLocalId),
}

impl From<Binder> for Symbol {
    fn from(value: Binder) -> Self {
        match value {
            Binder::Global(id) => Symbol::Global(id),
            Binder::LocalDecl(id) => Symbol::DeclaredLocal(id),
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
pub struct DependenciesPass {
    pub graph: DiGraphMap<Binder, ()>,
    pub rhs_map: FxHashMap<Binder, NodeID>,
    binder_stack: Vec<(NodeID, Binder)>,
}

impl DependenciesPass {
    pub fn drive(
        mut session: TypeSession<HeadersResolved>,
        ast: &mut AST<NameResolved>,
    ) -> TypeSession<SCCResolved> {
        let mut pass = DependenciesPass {
            graph: Default::default(),
            rhs_map: Default::default(),
            binder_stack: Default::default(),
        };

        for root in ast.roots.iter() {
            root.drive(&mut pass);
        }

        let type_constructors = std::mem::take(&mut session.phase.type_constructors);
        let protocols = std::mem::take(&mut session.phase.protocols);

        let phase = SCCResolved {
            graph: pass.graph,
            rhs_map: pass.rhs_map,
            type_constructors,
            protocols,
        };

        session.advance(phase)
    }

    fn enter_decl(&mut self, decl: &Decl) {
        let (sym, rhs_id) = match &decl.kind {
            DeclKind::Let {
                lhs:
                    Pattern {
                        kind: PatternKind::Bind(Name::Resolved(sym, _)),
                        ..
                    },
                value: Some(rhs),
                ..
            } => (sym, BoundRHS::Expr(rhs.id)),
            DeclKind::Method {
                func:
                    box func @ Func {
                        name: Name::Resolved(sym, _),
                        ..
                    },
                ..
            } => (sym, BoundRHS::Func(func.id)),

            _ => return,
        };

        match sym {
            Symbol::Global(global_id) => {
                let binder = Binder::Global(*global_id);
                self.graph.add_node(binder);

                self.rhs_map.insert(binder, rhs_id.id());
                self.binder_stack.push((decl.id, binder));
            }
            Symbol::DeclaredLocal(declared_local_id) => {
                let binder = Binder::LocalDecl(*declared_local_id);
                self.graph.add_node(binder);
                self.rhs_map.insert(binder, rhs_id.id());
                self.binder_stack.push((decl.id, binder));
            }
            _ => (),
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
        match &expr.kind {
            ExprKind::Member(
                Some(box Expr {
                    kind: ExprKind::Variable(Name::_Self),
                    ..
                }),
                Label::Named(_name),
            ) => (),
            ExprKind::Variable(Name::Resolved(sym, _)) => match sym {
                Symbol::Global(global_id) => {
                    let binder = Binder::Global(*global_id);

                    if let Some((_, scope_binder)) = self.binder_stack.last() {
                        self.graph.add_edge(*scope_binder, binder, ());
                    }
                }
                Symbol::DeclaredLocal(declared_local_id) => {
                    let binder = Binder::LocalDecl(*declared_local_id);

                    if let Some((_, scope_binder)) = self.binder_stack.last() {
                        self.graph.add_edge(*scope_binder, binder, ());
                    }
                }
                _ => (),
            },
            _ => (),
        }
    }
}

#[cfg(test)]
pub mod tests {
    use rustc_hash::FxHashSet;

    use crate::{
        ast::AST,
        name_resolution::{name_resolver::NameResolved, symbol::GlobalId},
        types::{
            passes::{
                dependencies_pass::{Binder, DependenciesPass, SCCResolved},
                type_header_resolve_pass::tests::type_header_resolve_pass_err,
            },
            type_session::TypeSession,
        },
    };

    pub fn resolve_dependencies(
        code: &'static str,
    ) -> (AST<NameResolved>, TypeSession<SCCResolved>) {
        let (mut ast, session) = type_header_resolve_pass_err(code).unwrap();
        let session = DependenciesPass::drive(session, &mut ast);
        (ast, session)
    }

    fn graph_nodes(code: &'static str) -> Vec<Binder> {
        let (_, session) = resolve_dependencies(code);
        let mut nodes: Vec<Binder> = session.phase.graph.nodes().collect();
        nodes.sort();
        nodes
    }

    fn graph_edges(code: &'static str) -> FxHashSet<(Binder, Binder)> {
        let (_, session) = resolve_dependencies(code);
        session
            .phase
            .graph
            .all_edges()
            .map(|(u, v, _)| (u, v))
            .collect()
    }

    #[test]
    fn graph_records_orphan_function_as_node() {
        let ns = graph_nodes(
            r#"
        func a() { 0 }
    "#,
        );
        assert!(ns.contains(&Binder::Global(GlobalId(1))), "{ns:?}");
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
            FxHashSet::from_iter([(Binder::Global(GlobalId(1)), Binder::Global(GlobalId(2)))]),
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
                (Binder::Global(GlobalId(1)), Binder::Global(GlobalId(2))),
                (Binder::Global(GlobalId(2)), Binder::Global(GlobalId(1)))
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
            FxHashSet::from_iter([(Binder::Global(GlobalId(1)), Binder::Global(GlobalId(2)))]),
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

    // If your resolver resolves method member calls to a DeclId in the body walk,
    // you can enable this. If not yet, skip this test for now.
    #[test]
    #[ignore = "wip"]
    fn graph_records_method_to_method_edge() {
        let es = graph_edges(
            r#"
        struct S {
            func a(){ self.b() }
            func b(){ 0 }
        }
    "#,
        );
        // Expect a -> b (IDs consistent with your existing numbering)
        assert_eq!(
            es,
            FxHashSet::from_iter([(Binder::Global(GlobalId(1)), Binder::Global(GlobalId(2)))]),
            "{es:?}"
        );
    }

    // If you register init bodies as nodes and resolve their calls, enable this too.
    #[test]
    #[ignore = "wip"]
    fn graph_records_init_to_function_edge() {
        let es = graph_edges(
            r#"
        func h(){ 0 }
        struct S { init(){ h() } }
    "#,
        );
        // init -> h (adjust IDs if needed)
        assert_eq!(
            es,
            FxHashSet::from_iter([(Binder::Global(GlobalId(1)), Binder::Global(GlobalId(2)))]),
            "{es:?}"
        );
    }
}
