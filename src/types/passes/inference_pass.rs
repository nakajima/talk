use derive_visitor::{Drive, Visitor};
use petgraph::algo::kosaraju_scc;
use rustc_hash::{FxHashMap, FxHashSet};
use tracing::instrument;

use crate::{
    ast::{AST, ASTPhase},
    diagnostic::Diagnostic,
    id_generator::IDGenerator,
    name::Name,
    name_resolution::{
        name_resolver::NameResolved,
        symbol::{Symbol, TypeId},
    },
    node::Node,
    node_id::NodeID,
    node_kinds::{
        block::Block,
        call_arg::CallArg,
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        func::Func,
        pattern::{Pattern, PatternKind},
        stmt::{Stmt, StmtKind},
        type_annotation::TypeAnnotation,
    },
    types::{
        constraints::{Constraint, ConstraintCause, Equals},
        passes::dependencies_pass::{Binder, SCCResolved},
        ty::{Level, MetaId, Ty},
        type_error::TypeError,
        type_operations::{apply, unify},
        type_session::{TypeDef, TypeSession, TypingPhase},
    },
};

pub type Substitutions = FxHashMap<MetaId, Ty>;

#[derive(Debug, PartialEq, Clone)]
pub struct Inferenced {
    pub type_constructors: FxHashMap<TypeId, TypeDef<Ty>>,
    pub protocols: FxHashMap<TypeId, TypeDef<Ty>>,
    pub types_by_node: FxHashMap<NodeID, Ty>,
}

impl TypingPhase for Inferenced {
    type Next = Inferenced;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct MetaTag {
    pub id: MetaId,
    pub level: Level,
}

#[derive(Debug)]
pub struct BindingGroup {
    binders: Vec<Binder>,
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

#[derive(Debug)]
pub struct TermEnv {
    frames: Vec<FxHashMap<Symbol, EnvEntry>>,
}

impl Default for TermEnv {
    fn default() -> Self {
        Self {
            frames: vec![FxHashMap::default()],
        }
    }
}

impl TermEnv {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push(&mut self) {
        self.frames.push(FxHashMap::default());
    }
    pub fn pop(&mut self) {
        self.frames.pop().expect("pop on empty env");
    }

    pub fn insert_mono(&mut self, sym: Symbol, ty: Ty) {
        self.frames
            .last_mut()
            .unwrap()
            .insert(sym, EnvEntry::Mono(ty));
    }
    pub fn promote(&mut self, sym: Symbol, sch: Scheme) {
        // promote into the *root* frame so it’s visible everywhere (for binders)
        self.frames[0].insert(sym, EnvEntry::Scheme(sch));
    }
    pub fn lookup(&self, sym: &Symbol) -> Option<&EnvEntry> {
        for frame in self.frames.iter().rev() {
            if let Some(e) = frame.get(sym) {
                return Some(e);
            }
        }
        None
    }
}

#[derive(Debug)]
pub struct InferenceSolution {
    pub diagnostics: Vec<Diagnostic<TypeError>>,
    pub types_by_node: FxHashMap<NodeID, Ty>,
}

#[derive(Debug)]
pub struct InferencePass<'a> {
    ast: &'a mut AST<NameResolved>,
    types_by_node: FxHashMap<NodeID, Ty>,
    metavars: IDGenerator,
    term_env: TermEnv,
    rhs_map: FxHashMap<Binder, NodeID>,
}

#[derive(Debug)]
pub struct Wants(Vec<Constraint>);
impl Wants {
    pub fn equals(&mut self, lhs: Ty, rhs: Ty, cause: ConstraintCause) {
        self.0.push(Constraint::Equals(Equals { lhs, rhs, cause }));
    }
}

impl<'a> InferencePass<'a> {
    pub fn perform(
        mut session: TypeSession<SCCResolved>,
        ast: &'a mut AST<NameResolved>,
    ) -> TypeSession<Inferenced> {
        let groups = kosaraju_scc(&session.phase.graph);
        let mut pass = InferencePass {
            ast,
            types_by_node: Default::default(),
            metavars: Default::default(),
            term_env: TermEnv::new(),
            rhs_map: session.phase.rhs_map.clone(),
        };

        // Handle binders first
        for binders in groups {
            let group = BindingGroup {
                binders,
                level: Level(1),
            };

            let wants = pass.infer_group(&group);
            let subs = pass.solve(wants);
            pass.promote_group(&group, &subs);
            pass.apply_to_self(&subs);
        }

        let roots = std::mem::take(&mut pass.ast.roots);

        for root in roots.iter() {
            // if !matches!(root, Node::Stmt(_)) {
            //     continue;
            // }

            let mut wants = Wants(vec![]);
            let ty = pass.infer_node(root, Level(1), &mut wants);
            pass.types_by_node.insert(root.node_id(), ty);
            let subs = pass.solve(wants);
            pass.apply_to_self(&subs);
        }

        _ = std::mem::replace(&mut pass.ast.roots, roots);

        pass.annotate_uses_after_inference();

        let type_constructors = std::mem::take(&mut session.phase.type_constructors);
        let protocols = std::mem::take(&mut session.phase.protocols);

        let phase = Inferenced {
            type_constructors,
            protocols,
            types_by_node: pass.types_by_node,
        };

        session.advance(phase)
    }

    #[instrument(skip(self))]
    fn infer_group(&mut self, group: &BindingGroup) -> Wants {
        let mut wants = Wants(Default::default());
        let inner_level = group.level.next();

        for &binder in &group.binders {
            let m = Ty::MetaVar {
                id: self.metavars.next_id(),
                level: inner_level,
            };

            tracing::trace!("binding {binder:?} placeholder");

            self.term_env.insert_mono(binder.into(), m);
        }

        for &binder in &group.binders {
            let symbol = Symbol::from(binder);
            let Some(rhs_expr_id) = self.rhs_map.get(&binder).copied() else {
                println!("Did not get rhs for {binder:?}");
                continue;
            };

            let rhs_expr = self.ast.find(rhs_expr_id).clone();

            let got = self.infer_node(&rhs_expr.unwrap(), inner_level, &mut wants);
            self.types_by_node.insert(rhs_expr_id, got.clone());

            let tv = match self.term_env.lookup(&symbol).unwrap() {
                EnvEntry::Mono(t) => t.clone(),
                _ => unreachable!(),
            };

            wants.equals(got, tv, ConstraintCause::Internal);
        }

        wants
    }

    #[instrument(skip(self))]
    fn apply_to_self(&mut self, substitutions: &Substitutions) {
        for (_, ty) in self.types_by_node.iter_mut() {
            if matches!(ty, Ty::Primitive(_)) {
                continue;
            }

            *ty = apply(ty.clone(), substitutions);
        }
    }

    #[instrument(skip(self))]
    fn solve(&mut self, wants: Wants) -> Substitutions {
        let mut substitutions = Substitutions::default();
        for want in wants.0 {
            match want {
                Constraint::Equals(equals) => {
                    unify(&equals.lhs, &equals.rhs, &mut substitutions).unwrap()
                }
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
        for &binder in &group.binders {
            let sym = Symbol::from(binder);

            match self.term_env.lookup(&sym).cloned() {
                Some(EnvEntry::Mono(ty)) => {
                    let applied = apply(ty, subs);
                    let scheme = self.generalize(group.level, applied);
                    self.term_env.promote(sym, scheme);
                }
                Some(EnvEntry::Scheme(_scheme)) => {}
                None => panic!("didn't find {sym:?} in term env"),
            }
        }
    }

    #[instrument(skip(self))]
    fn generalize(&self, inner: Level, ty: Ty) -> Scheme {
        // collect metas in ty
        let mut metas = FxHashSet::default();
        collect_metas(&ty, &mut metas);
        // keep only metas born at or above inner
        let foralls: Vec<MetaId> = metas
            .into_iter()
            .filter(|m| m.level >= inner)
            .map(|m| m.id)
            .collect();
        Scheme { foralls, ty }
    }

    #[instrument(skip(self))]
    fn infer_node(&mut self, node: &Node, level: Level, wants: &mut Wants) -> Ty {
        match node {
            Node::Expr(expr) => self.infer_expr(expr, level, wants),
            Node::Stmt(stmt) => self.infer_stmt(stmt, level, wants),
            Node::Decl(decl) => self.infer_decl(decl, level, wants),
            Node::Block(block) => self.infer_block(block, level, wants),
            _ => todo!("don't know how to handle {node:?}"),
        }
    }

    #[instrument(skip(self))]
    fn infer_decl(&mut self, decl: &Decl, level: Level, wants: &mut Wants) -> Ty {
        match &decl.kind {
            DeclKind::Let { lhs, .. } => {
                let Pattern { id, kind, .. } = &lhs;

                match kind {
                    PatternKind::Bind(Name::Resolved(sym, _)) => {
                        let ty = match self.term_env.lookup(sym).unwrap() {
                            EnvEntry::Mono(ty) => ty.clone(),
                            EnvEntry::Scheme(scheme) => scheme.ty.clone(),
                        };

                        self.types_by_node.insert(*id, ty.clone());

                        ty
                    }
                    _ => todo!(),
                }
            }
            _ => todo!("unhandled: {decl:?}"),
        }
    }

    #[instrument(skip(self))]
    fn infer_block(&mut self, block: &Block, level: Level, wants: &mut Wants) -> Ty {
        // Very simple semantics: return the type of the last expression statement, else Void.
        let mut last_ty = Ty::Void;
        for node in &block.body {
            if let Node::Stmt(stmt) = node {
                last_ty = self.infer_stmt(stmt, level, wants);
            }
        }
        last_ty
    }

    #[instrument(skip(self))]
    fn infer_expr(&mut self, expr: &Expr, level: Level, wants: &mut Wants) -> Ty {
        let ty = match &expr.kind {
            ExprKind::Incomplete(..) => todo!(),
            ExprKind::LiteralArray(..) => todo!(),
            ExprKind::LiteralInt(_) => Ty::Int,
            ExprKind::LiteralFloat(_) => Ty::Float,
            ExprKind::LiteralTrue => Ty::Bool,
            ExprKind::LiteralFalse => Ty::Bool,
            ExprKind::Variable(Name::Resolved(sym, _)) => {
                match self.term_env.lookup(sym).cloned() {
                    Some(EnvEntry::Scheme(s)) => self.instantiate(&s, level), // or pass through
                    Some(EnvEntry::Mono(t)) => t.clone(),
                    None => panic!("unbound variable {:?}", sym),
                }
            }
            ExprKind::LiteralString(_) => todo!(),
            ExprKind::Unary(..) => todo!(),
            ExprKind::Binary(..) => todo!(),
            ExprKind::Tuple(items) => Ty::Tuple(
                items
                    .iter()
                    .map(|t| self.infer_expr(t, level, wants))
                    .collect(),
            ),
            ExprKind::Block(..) => todo!(),
            ExprKind::Call {
                callee,
                type_args,
                args,
            } => self.infer_call(callee, type_args, args, level, wants),
            ExprKind::Member(..) => todo!(),
            ExprKind::Func(func) => self.infer_func(func, level, wants),
            ExprKind::If(..) => todo!(),
            ExprKind::Match(..) => todo!(),
            ExprKind::PatternVariant(..) => todo!(),
            ExprKind::RecordLiteral(..) => todo!(),
            ExprKind::RowVariable(..) => todo!(),
            ExprKind::Spread(..) => todo!(),
            _ => todo!(),
        };

        // record the type for this expression node
        self.types_by_node.insert(expr.id, ty.clone());
        ty
    }

    #[instrument(skip(self))]
    fn infer_call(
        &mut self,
        callee: &Expr,
        type_args: &[TypeAnnotation],
        args: &[CallArg],
        level: Level,
        wants: &mut Wants,
    ) -> Ty {
        let callee_ty = self.infer_expr(callee, level, wants);
        let mut arg_tys = Vec::with_capacity(args.len());
        for _ in args {
            arg_tys.push(Ty::MetaVar {
                id: self.metavars.next_id(),
                level,
            });
        }
        let returns = Ty::MetaVar {
            id: self.metavars.next_id(),
            level,
        };

        wants.equals(
            callee_ty,
            curry(arg_tys.clone(), returns.clone()),
            ConstraintCause::Call(callee.id),
        );

        for (a, aty) in args.iter().zip(arg_tys) {
            let got = self.infer_expr(&a.value, level, wants);
            wants.equals(got, aty, ConstraintCause::Internal);
        }

        returns
    }

    #[instrument(skip(self))]
    fn infer_func(&mut self, func: &Func, level: Level, wants: &mut Wants) -> Ty {
        let mut param_tys: Vec<Ty> = Vec::with_capacity(func.params.len());
        for _ in &func.params {
            param_tys.push(Ty::MetaVar {
                id: self.metavars.next_id(),
                level,
            });
        }
        let ret_ty = Ty::MetaVar {
            id: self.metavars.next_id(),
            level,
        };

        for (p, ty) in func.params.iter().zip(param_tys.iter()) {
            let Name::Resolved(sym, _) = &p.name else {
                panic!("unresolved param");
            };
            self.term_env.insert_mono(*sym, ty.clone());
        }

        let body_ty = self.infer_block(&func.body, level, wants);
        wants.equals(body_ty, ret_ty.clone(), ConstraintCause::Internal);

        curry(param_tys, ret_ty)
    }

    #[instrument(skip(self))]
    fn infer_stmt(&mut self, stmt: &Stmt, level: Level, wants: &mut Wants) -> Ty {
        match &stmt.kind {
            StmtKind::Expr(expr) => self.infer_expr(expr, level, wants),
            StmtKind::If(..) => Ty::Void,
            StmtKind::Return(..) => todo!(),
            StmtKind::Break => Ty::Void,
            StmtKind::Assignment(..) => Ty::Void,
            StmtKind::Loop(..) => Ty::Void,
        }
    }

    #[instrument(skip(self))]
    fn instantiate(&mut self, scheme: &Scheme, level: Level) -> Ty {
        // Map each quantified meta id to a fresh meta at this use-site level
        let mut substitutions = Substitutions::default();

        for meta in &scheme.foralls {
            substitutions.insert(
                *meta,
                Ty::MetaVar {
                    id: self.metavars.next_id(),
                    level,
                },
            );
        }
        apply(scheme.ty.clone(), &substitutions)
    }
}

fn curry<I: IntoIterator<Item = Ty>>(params: I, ret: Ty) -> Ty {
    params
        .into_iter()
        .collect::<Vec<_>>()
        .into_iter()
        .rfold(ret, |acc, p| Ty::Func(Box::new(p), Box::new(acc)))
}

pub fn collect_metas(ty: &Ty, out: &mut FxHashSet<MetaTag>) {
    match ty {
        Ty::MetaVar { id, level } => {
            out.insert(MetaTag {
                id: *id,
                level: *level,
            });
        }
        Ty::Func(dom, codom) => {
            collect_metas(dom, out);
            collect_metas(codom, out);
        }
        Ty::TypeApplication(fun, arg) => {
            collect_metas(fun, out);
            collect_metas(arg, out);
        }
        Ty::Tuple(items) => {
            for item in items {
                collect_metas(item, out);
            }
        }
        Ty::Primitive(_) | Ty::Rigid(_) | Ty::Hole(_) | Ty::TypeConstructor { .. } => {}
    }
}

#[derive(Visitor)]
#[visitor(Expr(enter))]
struct AnnotateUsesAfterInferenceVisitor<'a> {
    term_env: &'a TermEnv,
    types_by_node: &'a mut FxHashMap<NodeID, Ty>,
}
impl<'a> AnnotateUsesAfterInferenceVisitor<'a> {
    fn enter_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Variable(Name::Resolved(name, _)) => match self.term_env.lookup(name) {
                Some(EnvEntry::Mono(ty)) => {
                    tracing::trace!("annotating {name:?}");
                    self.types_by_node.insert(expr.id, ty.clone());
                }
                Some(EnvEntry::Scheme(scheme)) => {
                    tracing::trace!("annotating {name:?}");
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
    use crate::types::passes::dependencies_pass::tests::resolve_dependencies;

    fn typecheck(code: &'static str) -> (AST<NameResolved>, TypeSession<Inferenced>) {
        let (mut ast, session) = resolve_dependencies(code);
        let session = InferencePass::perform(session, &mut ast);
        (ast, session)
    }

    #[test]
    fn types_int() {
        let (ast, session) = typecheck("let a = 123; a");
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Int
        );
    }

    #[test]
    fn types_float() {
        let (ast, session) = typecheck("let a = 1.23; a");
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Float
        );
    }

    #[test]
    fn types_bool() {
        let (ast, session) = typecheck("let a = true; a ; let b = false ; b");
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Bool
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[3].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Bool
        );
    }

    #[test]
    fn types_identity() {
        let (ast, session) = typecheck(
            "
        func identity(x) { x }
        identity(123)
        identity(true)
        ",
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Int
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[2].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Bool
        );
    }

    #[test]
    fn types_call_let() {
        let (ast, session) = typecheck(
            "
        func id(x) { x }
        let a = id(123)
        let b = id(1.23)
        a
        b
        ",
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[3].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Int
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[4].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Float
        );
    }

    #[test]
    fn types_nested_identity() {
        let (ast, session) = typecheck(
            "
        func identity(x) { x }
        identity(identity(123))
        identity(identity(true))
        ",
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Int
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[2].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Bool
        );
    }

    #[test]
    fn types_multiple_args() {
        let (ast, session) = typecheck(
            "
        func makeTuple(x, y) {
            (x, y)
        }

        makeTuple(123, true)
            ",
        );

        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Tuple(vec![Ty::Int, Ty::Bool])
        );
    }

    #[test]
    fn types_tuple_value() {
        let (ast, session) = typecheck(
            "
        let z = (123, true)
        z
        ",
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Tuple(vec![Ty::Int, Ty::Bool])
        );
    }

    #[test]
    #[ignore = "waiting on rows"]
    fn types_tuple_assignment() {
        let (ast, session) = typecheck(
            "
        let z = (123, 1.23)
        let (x, y) = z
        ",
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Int
        );
    }
}
