use std::fmt::Debug;

use derive_visitor::Visitor;
use petgraph::prelude::DiGraphMap;
use rustc_hash::FxHashMap;
use tracing::instrument;

use crate::{
    ast::AST,
    name::Name,
    name_resolution::{
        name_resolver::NameResolved,
        symbol::{DeclId, Symbol},
    },
    node_kinds::{
        decl::{Decl, DeclKind},
        func::Func,
    },
    types::{
        ty::Ty,
        type_error::TypeError,
        type_header_resolve_pass::HeadersResolved,
        type_session::{TypeDef, TypeSession, TypingPhase},
    },
};

#[derive(Clone, Debug)]
pub struct SCCLeveled {
    pub scc_graph: DiGraphMap<DeclId, ()>,
    pub type_constructors: FxHashMap<DeclId, TypeDef<Ty>>,
    pub protocols: FxHashMap<DeclId, TypeDef<Ty>>,
}

impl TypingPhase for SCCLeveled {
    type Next = SCCLeveled;
}

pub struct BindingGroup {
    pub decls: Vec<DeclId>,
    pub level: u32,
}

#[derive(Debug, Visitor)]
#[visitor(Decl(enter))]
pub struct SCCPass {
    session: TypeSession<HeadersResolved>,
    graph: DiGraphMap<DeclId, ()>,
}

impl SCCPass {
    pub fn drive(
        ast: &mut AST<NameResolved>,
        session: TypeSession<HeadersResolved>,
    ) -> Result<(&mut AST<NameResolved>, TypeSession<SCCLeveled>), TypeError> {
        let pass = SCCPass {
            session,
            graph: DiGraphMap::new(),
        };

        pass.solve(ast)
    }

    fn solve(
        mut self,
        ast: &mut AST<NameResolved>,
    ) -> Result<(&mut AST<NameResolved>, TypeSession<SCCLeveled>), TypeError> {
        let type_constructors = std::mem::take(&mut self.session.phase.type_constructors);
        let protocols = std::mem::take(&mut self.session.phase.protocols);

        Ok((
            ast,
            self.session.advance(SCCLeveled {
                scc_graph: self.graph,
                type_constructors,
                protocols,
            }),
        ))
    }

    #[instrument]
    fn enter_decl(&mut self, decl: &Decl) {
        match &decl.kind {
            DeclKind::Struct {
                name: Name::Resolved(Symbol::Type(decl_id), _),
                ..
            } => {
                self.graph.add_node(*decl_id);
            } // We treat these as callable
            DeclKind::Let { .. } => todo!(),
            DeclKind::Init {
                name: Name::Resolved(Symbol::Type(decl_id), _),
                ..
            } => {
                self.graph.add_node(*decl_id);
            }
            DeclKind::Method {
                func:
                    box Func {
                        name: Name::Resolved(Symbol::Value(decl_id), _),
                        ..
                    },
                ..
            } => {
                self.graph.add_node(*decl_id);
            }
            DeclKind::Associated { .. } => todo!(),
            DeclKind::Func(Func {
                name: Name::Resolved(Symbol::Value(decl_id), _),
                ..
            }) => {
                self.graph.add_node(*decl_id);
            }
            DeclKind::Extend { .. } => todo!(),
            DeclKind::Enum { .. } => todo!(),
            DeclKind::EnumVariant(..) => todo!(),
            DeclKind::FuncSignature(..) => todo!(),
            DeclKind::MethodRequirement(..) => todo!(),
            _ => (),
        };
    }
}

#[cfg(test)]
pub mod tests {
    use crate::{
        name_resolution::symbol::DeclId,
        types::{scc_pass::SCCPass, type_header_resolve_pass::tests::type_header_resolve_pass_err},
    };
    use petgraph::algo::tarjan_scc;

    #[macro_export]
    macro_rules! assert_same_elements {
        ($lhs:expr, $rhs:expr) => {
            let lhs = &mut $lhs;
            lhs.sort();
            let rhs = &mut $rhs;
            rhs.sort();
            assert_eq!(lhs, rhs, "elements not equal: {lhs:?} <> {rhs:?}")
        };
    }

    fn groups(src: &'static str) -> Vec<Vec<DeclId>> {
        let (mut ast, session) = type_header_resolve_pass_err(src).unwrap();
        let (ast, _session) = SCCPass::drive(&mut ast, session).unwrap();
        tarjan_scc(&ast.phase.dependency_graph)
    }

    #[test]
    fn mutual_recursion_top_level_in_one_group() {
        let mut got = groups(
            r#"
            func odd(n) { even(n - 1) }
            func even(n){ odd(n - 1) }
        "#,
        );

        // Expect exactly one SCC with both decls (DeclId(1)=odd, DeclId(2)=even per your resolver)
        assert_eq!(got.len(), 1, "{got:?}");
        assert_same_elements!(got[0], vec![DeclId(1), DeclId(2)]);
    }

    #[test]
    fn ignores_param_and_local_symbols_as_edges() {
        let got = groups(
            r#"
            func f(x) { 
                let y = x
                123
            }
            func g(){ 0 }
        "#,
        );

        // f does not depend on g; there should be two singleton groups.
        // If your pass incorrectly adds edges for Symbol::Local, this will fail.
        assert_eq!(got, vec![vec![DeclId(1)], vec![DeclId(2)]], "{got:?}");
    }

    #[test]
    fn ignores_type_names_in_edges() {
        let got = groups(
            r#"
            struct Person { let age: Int }
            func f(){ 0 }
            func g(){ f() }
        "#,
        );

        // The presence of 'Person' (type) must not affect term graph.
        assert_eq!(got, vec![vec![DeclId(2)], vec![DeclId(3)]], "{got:?}");
    }

    #[test]
    fn dedups_edges_and_ignores_self_edges() {
        let got = groups(
            r#"
            func a(){ b(); b(); a } // mention, but no call
            func b(){ 0 }
        "#,
        );

        // Still just {b}, then {a}. If you keep duplicates or add self-edges, SCC or ordering can wobble.
        assert_eq!(got, vec![vec![DeclId(2)], vec![DeclId(1)]], "{got:?}");
    }

    #[test]
    fn member_calls_still_create_edge_to_function_symbol() {
        // If your resolver desugars or resolves method calls to a DeclId, this should add an edge.
        let got = groups(
            r#"
            struct S { }
            func h(){ 0 }
            func f(){ self.h() } // or just h() depending on your resolution rules
        "#,
        );

        // Expect h before f
        assert_eq!(got, vec![vec![DeclId(2)], vec![DeclId(3)]], "{got:?}");
    }

    #[test]
    #[ignore = "no builtin print yet"]
    fn no_spurious_edge_from_builtins() {
        let got = groups(
            r#"
            func f(){ print(1) }  // 'print' is a builtin, not a DeclId node
            func g(){ }
        "#,
        );

        // Two independent singletons; if you created an edge to a phantom DeclId, topo order will differ.
        assert_eq!(got, vec![vec![DeclId(1)], vec![DeclId(2)]], "{got:?}");
    }

    #[test]
    fn nested_mutual_recursion_becomes_group_when_generalize_locals_true() {
        let got = groups(
            r#"
            func outer(){
                func g(){ h() }
                func h(){ g() }
                0
            }
        "#,
        );

        // Sort members in each group for stable compare
        let mut groups_sorted: Vec<Vec<DeclId>> = got
            .into_iter()
            .map(|mut g| {
                g.sort_by_key(|d| d.0);
                g
            })
            .collect();

        // Expect two groups: one singleton {outer}, and one {g,h}.
        groups_sorted.sort_by_key(|g| g.len()); // singleton first

        assert_eq!(groups_sorted.len(), 2, "{groups_sorted:?}");
        assert_eq!(
            groups_sorted[0],
            vec![DeclId(1)],
            "outer should be its own group"
        );

        // Adjust these IDs to your resolver’s numbering if different:
        // with your other tests, locals often come as DeclId(2) and DeclId(3).
        let gh = &groups_sorted[1];
        assert_eq!(
            gh,
            &vec![DeclId(2), DeclId(3)],
            "g and h should form one SCC"
        );
    }

    #[test]
    fn deterministic_group_member_ordering() {
        let got1 = groups(
            r#"
            func a(){ c() }
            func b(){ c() }
            func c(){ 0 }
        "#,
        );
        let got2 = groups(
            r#"
            func a(){ c() }
            func b(){ c() }
            func c(){ 0 }
        "#,
        );

        // Ensure stable member ordering inside a group (e.g., sort by DeclId).
        assert_eq!(
            got1, got2,
            "non-deterministic SCC/member order: {got1:?} vs {got2:?}"
        );
        assert_eq!(
            got1,
            vec![vec![DeclId(3)], vec![DeclId(1)], vec![DeclId(2)]],
            "{got1:?}"
        );
    }

    #[test]
    fn cycle_via_three_nodes() {
        let got = groups(
            r#"
            func a(){ b() }
            func b(){ c() }
            func c(){ a() }
        "#,
        );
        let mut group = got[0].clone();
        group.sort();
        assert_eq!(got.len(), 1, "{got:?}");
        assert_eq!(got[0], vec![DeclId(3), DeclId(2), DeclId(1)], "{got:?}");
    }
}
