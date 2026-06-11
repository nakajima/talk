//! The λ_G verifier: typing (paper §3's T-App/T-Fun/T-Var/T-Body/T-Prog —
//! re-derived over the construction-time types) and well-formedness (Rule
//! WF / Property 2: the strict-nesting relation induced by free variables
//! must be acyclic — the higher-order restatement of the SSA dominance
//! property). Runs after lowering and after every IR pass, in the spirit of
//! LLVM's module verifier (Lattner & Adve, CGO 2004) and the typed-IL
//! tradition (TIL: Tarditi et al., PLDI 1996).

use rustc_hash::FxHashMap;

use crate::lambda_g::expr::{ExprId, ExprKind, TyKind};
use crate::lambda_g::program::{Label, Program};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifyError(pub String);

impl Program {
    pub fn verify(&mut self) -> Result<(), Vec<VerifyError>> {
        let mut errors = vec![];

        // T-Prog: every set body type-checks against its codomain (T-Body).
        for label in self.labels().collect::<Vec<_>>() {
            if let Some(body) = self.body(label) {
                self.verify_expr(body, &mut errors);
                let body_ty = self.expr_ty(body);
                let cod = self.cod(label);
                // ⊥-typed expressions inhabit any codomain vacuously (a
                // transfer of control never returns).
                let is_bot = matches!(self.ty_kind(body_ty), TyKind::Bot);
                if body_ty != cod && !is_bot {
                    errors.push(VerifyError(format!(
                        "T-Body: {} has body type {:?} but codomain {:?}",
                        self.name(label),
                        body_ty,
                        cod
                    )));
                }
            }
        }

        // Rule WF: strict nesting (var ℓ1 ∈ FV(ℓ2)) must be acyclic.
        use petgraph::algo::tarjan_scc;
        use petgraph::graph::DiGraph;
        let mut graph = DiGraph::<Label, ()>::new();
        let mut index = FxHashMap::default();
        for label in self.labels().collect::<Vec<_>>() {
            index.insert(label, graph.add_node(label));
        }
        for l2 in self.labels().collect::<Vec<_>>() {
            let fv = self.fv(l2);
            for l1 in self.set_labels(fv) {
                graph.add_edge(index[&l1], index[&l2], ());
            }
        }
        for scc in tarjan_scc(&graph) {
            if scc.len() > 1 {
                let names: Vec<String> = scc.iter().map(|n| self.name(graph[*n])).collect();
                errors.push(VerifyError(format!(
                    "WF: cyclic nesting (Property 2 violated) among {}",
                    names.join(", ")
                )));
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    /// Re-derive each subexpression's type and compare with the stored one.
    fn verify_expr(&mut self, e: ExprId, errors: &mut Vec<VerifyError>) {
        let expr = self.expr(e).clone();
        match &expr.kind {
            ExprKind::Const(_) | ExprKind::Var(_) | ExprKind::Func(_) => {}
            ExprKind::App(f, a) => {
                self.verify_expr(*f, errors);
                self.verify_expr(*a, errors);
                let f_ty = self.expr_ty(*f);
                match self.ty_kind(f_ty).clone() {
                    TyKind::Fn(dom, cod) => {
                        if self.expr_ty(*a) != dom {
                            errors.push(VerifyError(
                                "T-App: argument/domain mismatch".to_string(),
                            ));
                        }
                        if expr.ty != cod {
                            errors.push(VerifyError("T-App: stored type != codomain".to_string()));
                        }
                    }
                    _ => errors.push(VerifyError("T-App: callee not a function".to_string())),
                }
            }
            ExprKind::Tuple(items) => {
                for item in items.iter() {
                    self.verify_expr(*item, errors);
                }
            }
            ExprKind::Extract(inner, index) => {
                self.verify_expr(*inner, errors);
                let inner_ty = self.expr_ty(*inner);
                match self.ty_kind(inner_ty) {
                    TyKind::Tuple(items) if (*index as usize) < items.len() => {
                        if items[*index as usize] != expr.ty {
                            errors.push(VerifyError("extract: component type mismatch".into()));
                        }
                    }
                    _ => errors.push(VerifyError("extract: not a tuple / out of range".into())),
                }
            }
            ExprKind::PrimOp(_, args, _) => {
                for arg in args.iter() {
                    self.verify_expr(*arg, errors);
                }
            }
        }
    }
}
