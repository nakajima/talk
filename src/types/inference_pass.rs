use derive_visitor::{Drive, Visitor};
use petgraph::algo::kosaraju_scc;
use rustc_hash::FxHashMap;
use tracing::instrument;

use crate::{
    ast::{AST, ASTPhase},
    diagnostic::Diagnostic,
    id_generator::IDGenerator,
    name::Name,
    name_resolution::{
        name_resolver::NameResolved,
        symbol::{DeclId, Symbol},
    },
    node::Node,
    node_id::NodeID,
    node_kinds::{
        block::Block,
        expr::{Expr, ExprKind},
        stmt::{Stmt, StmtKind},
    },
    types::{
        constraints::{Constraint, ConstraintCause, Equals},
        ty::{Level, MetaId, Ty},
        type_error::TypeError,
        type_header_resolve_pass::HeadersResolved,
        type_session::{TypeDef, TypeSession},
    },
};

pub type Substitutions = FxHashMap<MetaId, Ty>;

#[derive(Debug)]
pub struct BindingGroup {
    node_ids: Vec<NodeID>,
    level: Level,
}

#[derive(Debug, Clone)]
pub struct Scheme {
    pub foralls: Vec<MetaId>,
    pub ty: Ty,
}

#[derive(Debug, Clone)]
pub enum EnvEntry {
    Mono(Ty),
    Scheme(Scheme),
}

#[derive(Debug, Default)]
pub struct TermEnv(FxHashMap<Symbol, EnvEntry>);

impl TermEnv {
    fn insert_mono(&mut self, symbol: Symbol, ty: Ty) {
        self.0.insert(symbol, EnvEntry::Mono(ty));
    }
    fn promote(&mut self, symbol: Symbol, sch: Scheme) {
        self.0.insert(symbol, EnvEntry::Scheme(sch));
    }
    fn get(&self, symbol: &Symbol) -> Option<&EnvEntry> {
        self.0.get(symbol)
    }
}

#[derive(Debug)]
pub struct InferenceSolution {
    pub diagnostics: Vec<Diagnostic<TypeError>>,
    pub types_by_node: FxHashMap<NodeID, Ty>,
}

#[derive(Debug)]
pub struct InferencePass {
    ast: AST<NameResolved>,
    _type_constructors: FxHashMap<DeclId, TypeDef<Ty>>,
    _protocols: FxHashMap<DeclId, TypeDef<Ty>>,
    types_by_node: FxHashMap<NodeID, Ty>,
    metavars: IDGenerator,
    term_env: TermEnv,
}

#[derive(Debug)]
pub struct Wants(Vec<Constraint>);
impl Wants {
    pub fn equals(&mut self, lhs: Ty, rhs: Ty, cause: ConstraintCause) {
        self.0.push(Constraint::Equals(Equals { lhs, rhs, cause }));
    }
}

impl InferencePass {
    pub fn perform(
        session: TypeSession<HeadersResolved>,
        ast: AST<NameResolved>,
    ) -> InferenceResult {
        let groups = kosaraju_scc(&ast.phase.dependency_graph);
        let mut pass = InferencePass {
            ast,
            _type_constructors: session.phase.type_constructors,
            _protocols: session.phase.protocols,
            types_by_node: Default::default(),
            metavars: Default::default(),
            term_env: Default::default(),
        };

        for decl_ids in groups {
            let group = BindingGroup {
                node_ids: decl_ids,
                level: Level(1),
            };

            let wants = pass.infer_group(&group);
            let subs = pass.solve(wants);
            pass.promote_group(&group, &subs);
        }

        pass.annotate_uses_after_inference();

        InferenceResult {
            ast: pass.into_typed_ast(),
            diagnostics: vec![], // populate from solve() if you report errors
        }
    }

    #[instrument(skip(self))]
    fn infer_group(&mut self, group: &BindingGroup) -> Wants {
        let mut wants = Wants(Default::default());
        let inner_level = group.level.next();

        for &decl_id in &group.node_ids {
            let m = Ty::MetaVar {
                id: self.metavars.next_id(),
                level: inner_level,
            };

            self.term_env.insert_mono(Symbol::Value(decl_id), m);
        }

        // 2) synth each RHS and tie to provisional
        for &decl_id in &group.node_ids {
            let symbol = Symbol::Value(decl_id);
            let rhs_expr_id = self.ast.phase.decl_rhs.get(&decl_id).copied().unwrap();
            let rhs_expr = self.ast.find(rhs_expr_id).clone();

            let got = self.infer_node(&rhs_expr.unwrap(), inner_level, &mut wants);
            self.types_by_node.insert(rhs_expr_id, got.clone());

            let tv = match self.term_env.get(&symbol).unwrap() {
                EnvEntry::Mono(t) => t.clone(),
                _ => unreachable!(),
            };

            wants.equals(got, tv, ConstraintCause::Internal);
        }

        wants
    }

    #[instrument(skip(self))]
    fn solve(&mut self, wants: Wants) -> Substitutions {
        let mut substitutions = Substitutions::default();
        for want in wants.0 {
            match want {
                Constraint::Equals(equals) => self
                    .unify(&equals.lhs, &equals.rhs, &mut substitutions)
                    .unwrap(),
            };
        }

        substitutions
    }

    #[instrument(skip(self))]
    fn annotate_uses_after_inference(&mut self) {
        let mut visitor = AnnotateUsesAfterInferenceVisitor {
            term_env: &mut self.term_env,
            types_by_node: &mut self.types_by_node,
        };

        for root in &self.ast.roots {
            root.drive(&mut visitor);
        }
    }

    #[instrument(skip(self))]
    fn promote_group(&mut self, group: &BindingGroup, subs: &Substitutions) {
        for &did in &group.node_ids {
            let sym = Symbol::Value(did);
            if let Some(EnvEntry::Mono(tv)) = self.term_env.get(&sym).cloned() {
                let mut subs_clone = subs.clone();
                let applied = self.apply(tv, &mut subs_clone);
                self.term_env.promote(
                    sym,
                    Scheme {
                        foralls: vec![],
                        ty: applied,
                    },
                );
            }
        }
    }

    #[instrument(skip(self))]
    fn unify(
        &mut self,
        lhs: &Ty,
        rhs: &Ty,
        substitutions: &mut Substitutions,
    ) -> Result<bool, TypeError> {
        let lhs = self.apply(lhs.clone(), substitutions);
        let rhs = self.apply(rhs.clone(), substitutions);

        // Hole(NodeID),
        // Rigid(DeclId),
        // MetaVar { id: MetaId, level: Level },
        // Primitive(Primitive),
        // TypeConstructor { name: Name, kind: TypeDefKind },
        // TypeApplication(Box<Ty>, Box<Ty>),
        match (&lhs, &rhs) {
            (Ty::Primitive(lhs), Ty::Primitive(rhs)) => {
                if lhs == rhs {
                    Ok(false)
                } else {
                    Err(TypeError::InvalidUnification(
                        Ty::Primitive(*lhs),
                        Ty::Primitive(*rhs),
                    ))
                }
            }
            (
                Ty::TypeApplication(box lhs_rec, box lhs_arg),
                Ty::TypeApplication(box rhs_rec, box rhs_arg),
            ) => Ok(self.unify(lhs_rec, rhs_rec, substitutions)?
                || self.unify(lhs_arg, rhs_arg, substitutions)?),
            (ty, Ty::MetaVar { id, .. }) | (Ty::MetaVar { id, .. }, ty) => {
                substitutions.insert(*id, ty.clone());
                Ok(true)
            }
            (_, Ty::Rigid(_)) | (Ty::Rigid(_), _) => Err(TypeError::InvalidUnification(lhs, rhs)),
            _ => todo!(),
        }
    }

    #[allow(clippy::only_used_in_recursion)]
    fn apply(&self, ty: Ty, substitutions: &mut Substitutions) -> Ty {
        match ty {
            Ty::Hole(..) => ty,
            Ty::Rigid(..) => ty,
            Ty::MetaVar { id, .. } => substitutions.get(&id).cloned().unwrap_or(ty),
            Ty::Primitive(..) => ty,
            Ty::TypeConstructor { .. } => todo!(),
            Ty::TypeApplication(box lhs, box rhs) => Ty::TypeApplication(
                self.apply(lhs, substitutions).into(),
                self.apply(rhs, substitutions).into(),
            ),
        }
    }

    fn into_typed_ast(self) -> AST<Typed> {
        AST {
            path: self.ast.path,
            meta: self.ast.meta,
            roots: self.ast.roots, // same nodes
            diagnostics: self.ast.diagnostics,
            phase: Typed {
                _types_by_node: self.types_by_node,
            },
        }
    }

    fn infer_node(&mut self, node: &Node, _level: Level, _wants: &mut Wants) -> Ty {
        match node {
            Node::Expr(expr) => self.infer_expr(expr),
            Node::Stmt(stmt) => self.infer_stmt(stmt),
            Node::Block(block) => self.infer_block(block),
            _ => todo!("don't know how to handle {node:?}"),
        }
    }

    fn infer_block(&mut self, block: &Block) -> Ty {
        // Very simple semantics: return the type of the last expression statement, else Void.
        let mut last_ty = Ty::Void;
        for node in &block.body {
            if let Node::Stmt(stmt) = node {
                last_ty = self.infer_stmt(stmt);
            }
        }
        last_ty
    }

    fn infer_expr(&mut self, expr: &Expr) -> Ty {
        match &expr.kind {
            ExprKind::Incomplete(..) => todo!(),
            ExprKind::LiteralArray(..) => todo!(),
            ExprKind::LiteralInt(_) => Ty::Int,
            ExprKind::LiteralFloat(_) => Ty::Float,
            ExprKind::LiteralTrue => Ty::Bool,
            ExprKind::LiteralFalse => Ty::Bool,
            ExprKind::Variable(Name::Resolved(sym, _)) => {
                let ty = match self.term_env.get(sym).cloned() {
                    Some(EnvEntry::Scheme(s)) => self.instantiate(&s, /*current*/ Level(1)), // or pass through
                    Some(EnvEntry::Mono(t)) => t.clone(),
                    None => panic!("unbound variable {:?}", sym),
                };
                // record the type for this expression node
                self.types_by_node.insert(expr.id, ty.clone());
                ty
            }
            ExprKind::LiteralString(_) => todo!(),
            ExprKind::Unary(..) => todo!(),
            ExprKind::Binary(..) => todo!(),
            ExprKind::Tuple(..) => todo!(),
            ExprKind::Block(..) => todo!(),
            ExprKind::Call { .. } => todo!(),
            ExprKind::Member(..) => todo!(),
            ExprKind::Func { .. } => todo!(),
            ExprKind::If(..) => todo!(),
            ExprKind::Match(..) => todo!(),
            ExprKind::PatternVariant(..) => todo!(),
            ExprKind::RecordLiteral(..) => todo!(),
            ExprKind::RowVariable(..) => todo!(),
            ExprKind::Spread(..) => todo!(),
            _ => todo!(),
        }
    }

    fn infer_stmt(&mut self, stmt: &Stmt) -> Ty {
        match &stmt.kind {
            StmtKind::Expr(expr) => self.infer_expr(expr),
            StmtKind::If(..) => Ty::Void,
            StmtKind::Return(..) => todo!(),
            StmtKind::Break => Ty::Void,
            StmtKind::Assignment(..) => Ty::Void,
            StmtKind::Loop(..) => Ty::Void,
        }
    }

    fn instantiate(&mut self, s: &Scheme, _level: Level) -> Ty {
        // MVP: schemes are monomorphic (foralls = []), so:
        s.ty.clone()
        // Later: map each MetaId in s.foralls to fresh Ty::MetaVar at `level`
    }
}

#[derive(Visitor)]
#[visitor(Expr(enter))]
struct AnnotateUsesAfterInferenceVisitor<'a> {
    term_env: &'a TermEnv,
    types_by_node: &'a mut FxHashMap<NodeID, Ty>,
}
impl<'a> AnnotateUsesAfterInferenceVisitor<'a> {
    #[instrument(skip(self))]
    fn enter_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Variable(Name::Resolved(name, _)) => match self.term_env.get(name) {
                Some(EnvEntry::Mono(ty)) => {
                    self.types_by_node.insert(expr.id, ty.clone());
                }
                Some(EnvEntry::Scheme(scheme)) => {
                    self.types_by_node.insert(expr.id, scheme.ty.clone());
                }
                _ => tracing::warn!("no type found for use of {:?}", expr),
            },
            ExprKind::Block(..) => todo!(),
            _ => (),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Typed {
    _types_by_node: FxHashMap<NodeID, Ty>,
}
impl ASTPhase for Typed {}

pub struct InferenceResult {
    pub ast: AST<Typed>,
    pub diagnostics: Vec<Diagnostic<TypeError>>,
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::types::type_header_resolve_pass::tests::type_header_resolve_pass_err;

    fn typecheck(code: &'static str) -> InferenceResult {
        let (ast, session) = type_header_resolve_pass_err(code).unwrap();
        InferencePass::perform(session, ast)
    }

    #[test]
    fn types_int() {
        let types = typecheck("let a = 123; a");
        assert_eq!(
            *types
                .ast
                .phase
                ._types_by_node
                .get(&types.ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Int
        );
    }

    #[test]
    fn types_float() {
        let types = typecheck("let a = 1.23; a");
        assert_eq!(
            *types
                .ast
                .phase
                ._types_by_node
                .get(&types.ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Float
        );
    }

    #[test]
    fn types_bool() {
        let types = typecheck("let a = true; a ; let b = false ; b");
        assert_eq!(
            *types
                .ast
                .phase
                ._types_by_node
                .get(&types.ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Bool
        );
        assert_eq!(
            *types
                .ast
                .phase
                ._types_by_node
                .get(&types.ast.roots[3].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Bool
        );
    }

    #[test]
    fn types_identity() {
        let types = typecheck(
            "
        func identity(x) { x }
        identity(123)
        identity(true)
        ",
        );
        assert_eq!(
            *types
                .ast
                .phase
                ._types_by_node
                .get(&types.ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Int
        );
        assert_eq!(
            *types
                .ast
                .phase
                ._types_by_node
                .get(&types.ast.roots[2].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Bool
        );
    }
}
