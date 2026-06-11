//! Textual rendering in the paper's surface style:
//! `hi ↦ λ int → ⊥. br(i1 < n, bi, xi)` — used by `show_ir` and golden
//! tests. Sharing is printed inline (the underlying graph hash-conses; the
//! paper's examples read "as if all let-bound variables had been inlined",
//! §3).

use crate::lambda_g::expr::{Const, ExprId, ExprKind, Op, TyId, TyKind};
use crate::lambda_g::program::{Label, Program};

impl Program {
    pub fn render(&self) -> String {
        let mut out = String::new();
        for label in self.labels() {
            out.push_str(&self.render_func(label));
            out.push('\n');
        }
        out
    }

    pub fn render_func(&self, label: Label) -> String {
        let dom = self.render_ty(self.dom(label));
        let cod = self.render_ty(self.cod(label));
        let body = match self.body(label) {
            Some(b) => self.render_expr(b),
            None => "↑".to_string(),
        };
        format!("{} ↦ λ {} → {}. {}", self.name(label), dom, cod, body)
    }

    pub fn render_ty(&self, ty: TyId) -> String {
        match self.ty_kind(ty) {
            TyKind::I64 => "int".into(),
            TyKind::F64 => "float".into(),
            TyKind::Bool => "bool".into(),
            TyKind::Byte => "byte".into(),
            TyKind::Ptr => "ptr".into(),
            TyKind::Void => "()".into(),
            TyKind::Bot => "⊥".into(),
            TyKind::Tuple(items) => {
                let inner: Vec<String> = items.iter().map(|t| self.render_ty(*t)).collect();
                format!("[{}]", inner.join(", "))
            }
            TyKind::Fn(d, c) => format!("{} → {}", self.render_ty(*d), self.render_ty(*c)),
            TyKind::Boxed(sym) => format!("boxed({sym})"),
            TyKind::Variant(sym) => format!("variant({sym})"),
            TyKind::Cell(inner) => format!("cell({})", self.render_ty(*inner)),
        }
    }

    pub fn render_expr(&self, e: ExprId) -> String {
        match &self.expr(e).kind {
            ExprKind::Const(c) => match c {
                Const::I64(v) => format!("{v}"),
                Const::F64(bits) => format!("{}", f64::from_bits(*bits)),
                Const::Bool(v) => format!("{v}"),
                Const::Byte(v) => format!("{v}b"),
                Const::Void => "()".into(),
                Const::StaticPtr(off) => format!("static+{off}"),
                Const::Slot(index) => format!("slot#{index}"),
            },
            ExprKind::Func(l) => self.name(*l),
            ExprKind::Var(l) => format!("var {}", self.name(*l)),
            ExprKind::App(f, a) => format!("{} {}", self.render_expr(*f), self.render_expr(*a)),
            ExprKind::Tuple(items) => {
                let inner: Vec<String> = items.iter().map(|i| self.render_expr(*i)).collect();
                format!("({})", inner.join(", "))
            }
            ExprKind::Extract(inner, index) => format!("{}.{index}", self.render_expr(*inner)),
            ExprKind::PrimOp(op, args, _) => {
                let inner: Vec<String> = args.iter().map(|a| self.render_expr(*a)).collect();
                format!("{}({})", render_op(*op), inner.join(", "))
            }
        }
    }
}

fn render_op(op: Op) -> String {
    format!("{op:?}").to_lowercase()
}
