//! The λ_G program: a flat map from labels to functions "floating in a
//! soup" (Leißa & Griebler §2.2, Fig. 2). Each function introduces exactly
//! one variable identified by its own label (paper §7 "Binders" — function
//! and binder share an identifier, eliminating synchronization bugs).
//! Bodies may be unset (↑) to tie recursive knots during construction and
//! substitution (paper Eq. 18); bodies are mutable, expressions are not.
//!
//! Every mutation maintains the users sets (UF, paper Eq. 11) and
//! transitively invalidates memoized free-variable information (§3.1.1
//! "Users & Invalidation") — the only reverse dependency the framework
//! needs (no def-use chains).

use rustc_hash::FxHashMap;

use crate::lambda_g::expr::{CmpOp, Const, Expr, ExprId, ExprKind, Op, TyId, TyKind};
use crate::lambda_g::sets::{SetArena, SetId};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Label(pub u32);

#[derive(Clone, Debug)]
pub(crate) struct FunctionData {
    pub dom: TyId,
    pub cod: TyId,
    pub body: Option<ExprId>,
    /// UF(ℓ): functions whose bodies reference ℓ (paper Eq. 11).
    pub users: Vec<Label>,
    /// 0 = free-variable cache invalid (paper §3.1.1).
    pub mark: u64,
    pub fv: SetId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstructionError(pub String);

pub struct Program {
    tys: Vec<TyKind>,
    ty_intern: FxHashMap<TyKind, TyId>,
    exprs: Vec<Expr>,
    expr_intern: FxHashMap<ExprKind, ExprId>,
    pub(crate) funcs: Vec<FunctionData>,
    names: Vec<String>,
    by_name: FxHashMap<String, Label>,
    pub(crate) sets: SetArena,
    /// The fixed-point iteration counter (paper §3.1.1).
    pub(crate) run: u64,
    /// Static memory (string literal bytes), referenced by StaticPtr.
    pub static_mem: Vec<u8>,
}

impl Default for Program {
    fn default() -> Self {
        Self::new()
    }
}

impl Program {
    pub fn new() -> Self {
        Program {
            tys: vec![],
            ty_intern: FxHashMap::default(),
            exprs: vec![],
            expr_intern: FxHashMap::default(),
            funcs: vec![],
            names: vec![],
            by_name: FxHashMap::default(),
            sets: SetArena::new(),
            run: 0,
            static_mem: vec![],
        }
    }

    // ----- Types ---------------------------------------------------------

    pub fn ty(&mut self, kind: TyKind) -> TyId {
        if let Some(&id) = self.ty_intern.get(&kind) {
            return id;
        }
        let id = TyId(self.tys.len() as u32);
        self.tys.push(kind.clone());
        self.ty_intern.insert(kind, id);
        id
    }

    pub fn ty_kind(&self, id: TyId) -> &TyKind {
        &self.tys[id.0 as usize]
    }

    pub fn ty_i64(&mut self) -> TyId {
        self.ty(TyKind::I64)
    }
    pub fn ty_f64(&mut self) -> TyId {
        self.ty(TyKind::F64)
    }
    pub fn ty_bool(&mut self) -> TyId {
        self.ty(TyKind::Bool)
    }
    pub fn ty_void(&mut self) -> TyId {
        self.ty(TyKind::Void)
    }
    pub fn ty_bot(&mut self) -> TyId {
        self.ty(TyKind::Bot)
    }
    pub fn ty_ptr(&mut self) -> TyId {
        self.ty(TyKind::Ptr)
    }
    pub fn ty_tuple(&mut self, items: &[TyId]) -> TyId {
        self.ty(TyKind::Tuple(items.into()))
    }
    pub fn ty_fn(&mut self, dom: TyId, cod: TyId) -> TyId {
        self.ty(TyKind::Fn(dom, cod))
    }
    pub fn ty_cell(&mut self, inner: TyId) -> TyId {
        self.ty(TyKind::Cell(inner))
    }

    // ----- Functions -----------------------------------------------------

    /// Create a function with an unset body (↑) — partial construction for
    /// knot-tying (paper §2.2).
    pub fn func(&mut self, name: &str, dom: TyId, cod: TyId) -> Label {
        let label = Label(self.funcs.len() as u32);
        self.funcs.push(FunctionData {
            dom,
            cod,
            body: None,
            users: vec![],
            mark: 0,
            fv: SetId::EMPTY,
        });
        let unique = if self.by_name.contains_key(name) {
            format!("{name}#{}", label.0)
        } else {
            name.to_string()
        };
        self.by_name.insert(unique.clone(), label);
        self.names.push(unique);
        label
    }

    pub fn func_count(&self) -> usize {
        self.funcs.len()
    }

    pub fn name(&self, label: Label) -> String {
        self.names[label.0 as usize].clone()
    }

    pub fn label_named(&self, name: &str) -> Option<Label> {
        self.by_name.get(name).copied()
    }

    pub fn body(&self, label: Label) -> Option<ExprId> {
        self.funcs[label.0 as usize].body
    }

    pub fn dom(&self, label: Label) -> TyId {
        self.funcs[label.0 as usize].dom
    }

    pub fn cod(&self, label: Label) -> TyId {
        self.funcs[label.0 as usize].cod
    }

    pub fn labels(&self) -> impl Iterator<Item = Label> {
        (0..self.funcs.len() as u32).map(Label)
    }

    /// Set (or replace) a body. Maintains UF edges and transitively
    /// invalidates the free-variable caches of everything that depends on
    /// this function (paper §3.1.1 "Users & Invalidation").
    pub fn set_body(&mut self, label: Label, body: ExprId) {
        if let Some(old) = self.funcs[label.0 as usize].body {
            let old_lf = self.exprs[old.0 as usize].lf;
            for &m in self.sets.labels(old_lf).to_vec().iter() {
                self.funcs[m.0 as usize].users.retain(|u| *u != label);
            }
        }
        self.funcs[label.0 as usize].body = Some(body);
        let lf = self.exprs[body.0 as usize].lf;
        for &m in self.sets.labels(lf).to_vec().iter() {
            let users = &mut self.funcs[m.0 as usize].users;
            if !users.contains(&label) {
                users.push(label);
            }
        }
        self.invalidate(label);
    }

    /// Transitive cache invalidation through users sets (paper §3.1.1).
    pub(crate) fn invalidate(&mut self, label: Label) {
        let mut stack = vec![label];
        while let Some(l) = stack.pop() {
            let func = &mut self.funcs[l.0 as usize];
            if func.mark == 0 && l != label {
                continue;
            }
            func.mark = 0;
            func.fv = SetId::EMPTY;
            stack.extend(func.users.iter().copied());
        }
    }

    // ----- Expressions (interned; typed at construction, T-rules) --------

    pub fn expr(&self, id: ExprId) -> &Expr {
        &self.exprs[id.0 as usize]
    }

    pub fn expr_ty(&self, id: ExprId) -> TyId {
        self.exprs[id.0 as usize].ty
    }

    fn intern_expr(&mut self, kind: ExprKind, ty: TyId, lv: SetId, lf: SetId) -> ExprId {
        if let Some(&id) = self.expr_intern.get(&kind) {
            return id;
        }
        let id = ExprId(self.exprs.len() as u32);
        self.exprs.push(Expr {
            kind: kind.clone(),
            ty,
            lv,
            lf,
        });
        self.expr_intern.insert(kind, id);
        id
    }

    pub fn constant(&mut self, c: Const, ty: TyId) -> ExprId {
        self.intern_expr(ExprKind::Const(c), ty, SetId::EMPTY, SetId::EMPTY)
    }

    pub fn int(&mut self, v: i64) -> ExprId {
        let ty = self.ty_i64();
        self.constant(Const::I64(v), ty)
    }

    pub fn float(&mut self, v: f64) -> ExprId {
        let ty = self.ty_f64();
        self.constant(Const::F64(v.to_bits()), ty)
    }

    pub fn bool(&mut self, v: bool) -> ExprId {
        let ty = self.ty_bool();
        self.constant(Const::Bool(v), ty)
    }

    pub fn void(&mut self) -> ExprId {
        let ty = self.ty_void();
        self.constant(Const::Void, ty)
    }

    /// ℓ — T-Fun: type is dom → cod.
    pub fn func_ref(&mut self, label: Label) -> ExprId {
        let func = &self.funcs[label.0 as usize];
        let (dom, cod) = (func.dom, func.cod);
        let ty = self.ty_fn(dom, cod);
        let lf = self.sets.singleton(label);
        self.intern_expr(ExprKind::Func(label), ty, SetId::EMPTY, lf)
    }

    /// var ℓ — T-Var: type is ℓ's domain.
    pub fn var(&mut self, label: Label) -> ExprId {
        let ty = self.funcs[label.0 as usize].dom;
        let lv = self.sets.singleton(label);
        self.intern_expr(ExprKind::Var(label), ty, lv, SetId::EMPTY)
    }

    /// T-App.
    pub fn try_app(&mut self, f: ExprId, a: ExprId) -> Result<ExprId, ConstructionError> {
        let f_ty = self.expr_ty(f);
        let TyKind::Fn(dom, cod) = *self.ty_kind(f_ty) else {
            return Err(ConstructionError(format!(
                "T-App: callee is not a function (ty {f_ty:?})"
            )));
        };
        let a_ty = self.expr_ty(a);
        if a_ty != dom {
            return Err(ConstructionError(format!(
                "T-App: argument type {} does not match domain {} (callee {}, arg {})",
                self.render_ty(a_ty),
                self.render_ty(dom),
                self.render_expr(f),
                self.render_expr(a),
            )));
        }
        let lv = self.merge_lv(&[f, a]);
        let lf = self.merge_lf(&[f, a]);
        Ok(self.intern_expr(ExprKind::App(f, a), cod, lv, lf))
    }

    pub fn app(&mut self, f: ExprId, a: ExprId) -> ExprId {
        match self.try_app(f, a) {
            Ok(id) => id,
            // A construction-type error is a lowerer bug: the checker
            // accepted the program, so the IR we build from it must be
            // well-typed (preservation through lowering).
            Err(e) => unreachable!("λ_G construction: {}", e.0),
        }
    }

    pub fn tuple(&mut self, items: &[ExprId]) -> ExprId {
        let tys: Vec<TyId> = items.iter().map(|i| self.expr_ty(*i)).collect();
        let ty = self.ty_tuple(&tys);
        let lv = self.merge_lv(items);
        let lf = self.merge_lf(items);
        self.intern_expr(ExprKind::Tuple(items.into()), ty, lv, lf)
    }

    pub fn extract(&mut self, e: ExprId, index: u32) -> ExprId {
        let e_ty = self.expr_ty(e);
        let TyKind::Tuple(items) = self.ty_kind(e_ty) else {
            unreachable!("λ_G construction: extract from non-tuple type");
        };
        let ty = items[index as usize];
        let (lv, lf) = (self.exprs[e.0 as usize].lv, self.exprs[e.0 as usize].lf);
        self.intern_expr(ExprKind::Extract(e, index), ty, lv, lf)
    }

    pub fn primop(&mut self, op: Op, args: &[ExprId], ty: TyId) -> ExprId {
        let lv = self.merge_lv(args);
        let lf = self.merge_lf(args);
        self.intern_expr(ExprKind::PrimOp(op, args.into(), ty), ty, lv, lf)
    }

    pub fn add(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let ty = self.expr_ty(a);
        self.primop(Op::Add, &[a, b], ty)
    }

    pub fn sub(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let ty = self.expr_ty(a);
        self.primop(Op::Sub, &[a, b], ty)
    }

    pub fn mul(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let ty = self.expr_ty(a);
        self.primop(Op::Mul, &[a, b], ty)
    }

    pub fn div(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let ty = self.expr_ty(a);
        self.primop(Op::Div, &[a, b], ty)
    }

    pub fn cmp(&mut self, op: CmpOp, a: ExprId, b: ExprId) -> ExprId {
        let ty = self.ty_bool();
        self.primop(Op::Cmp(op), &[a, b], ty)
    }

    /// br(cond, t, f) where t, f : [] → R — the paper's br_T builtin (§2.2)
    /// as a primop. The result type is R (⊥ for branches between
    /// continuations).
    pub fn br(&mut self, cond: ExprId, then_e: ExprId, else_e: ExprId, thunk_ty: TyId) -> ExprId {
        let TyKind::Fn(_, result) = *self.ty_kind(thunk_ty) else {
            unreachable!("λ_G construction: br thunks must have function type");
        };
        self.primop(Op::Br, &[cond, then_e, else_e], result)
    }

    pub fn switch(&mut self, tag: ExprId, arms: &[ExprId], default: ExprId, result: TyId) -> ExprId {
        let mut args = vec![tag];
        args.extend_from_slice(arms);
        args.push(default);
        self.primop(Op::Switch, &args, result)
    }

    fn merge_lv(&mut self, items: &[ExprId]) -> SetId {
        let mut acc = SetId::EMPTY;
        for &item in items {
            let lv = self.exprs[item.0 as usize].lv;
            acc = self.sets.union(acc, lv);
        }
        acc
    }

    fn merge_lf(&mut self, items: &[ExprId]) -> SetId {
        let mut acc = SetId::EMPTY;
        for &item in items {
            let lf = self.exprs[item.0 as usize].lf;
            acc = self.sets.union(acc, lf);
        }
        acc
    }

    // ----- Set helpers for callers/tests ---------------------------------

    pub fn set_labels(&self, set: SetId) -> Vec<Label> {
        self.sets.labels(set).to_vec()
    }

    pub fn fv_is_cached(&self, label: Label) -> bool {
        self.funcs[label.0 as usize].mark != 0
    }
}
