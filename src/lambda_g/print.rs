//! Textual rendering for humans (`talk lower`, the playground's show_ir,
//! and IR snapshot tests): each function prints as
//! `func name(param types) { body }` — plain function syntax. Sharing is
//! printed inline (the underlying graph hash-conses; the rendering reads
//! as if every shared subexpression had been written out).

use crate::lambda_g::expr::{Const, ExprId, ExprKind, Op, TyId, TyKind};
use crate::lambda_g::nest::NestingTree;
use crate::lambda_g::program::{Label, Program};

/// ANSI styles for terminal rendering — the REPL highlighter's palette
/// (`src/cli/repl.rs`). `plain()` renders nothing, so tests and the
/// playground see clean text.
#[derive(Clone, Copy)]
pub struct Styles {
    pub keyword: &'static str,
    pub func: &'static str,
    pub ty: &'static str,
    pub num: &'static str,
    pub string: &'static str,
    pub op: &'static str,
    pub reset: &'static str,
}

impl Styles {
    pub fn plain() -> Self {
        Styles {
            keyword: "",
            func: "",
            ty: "",
            num: "",
            string: "",
            op: "",
            reset: "",
        }
    }

    pub fn ansi() -> Self {
        Styles {
            keyword: "\x1b[1;35m",
            func: "\x1b[1;33m",
            ty: "\x1b[1;34m",
            num: "\x1b[36m",
            string: "\x1b[32m",
            op: "\x1b[35m",
            reset: "\x1b[0m",
        }
    }

    /// Pick by destination: colors on a terminal unless NO_COLOR is set.
    pub fn auto() -> Self {
        use std::io::IsTerminal;
        if std::io::stdout().is_terminal() && std::env::var_os("NO_COLOR").is_none() {
            Styles::ansi()
        } else {
            Styles::plain()
        }
    }
}

impl Program {
    /// Whole-program rendering: functions nest under the function whose
    /// variable they use (the nesting tree), so a function's helper
    /// continuations read like local functions. (`&mut`: building the
    /// tree fills the free-variable caches; no term changes.)
    pub fn render(&mut self) -> String {
        self.render_styled(&Styles::plain())
    }

    pub fn render_ansi(&mut self) -> String {
        self.render_styled(&Styles::ansi())
    }

    pub fn render_styled(&mut self, s: &Styles) -> String {
        let tree = self.nesting_forest();
        let mut out = String::new();
        let mut first = true;
        for root in tree.children(None) {
            if !first {
                out.push('\n');
            }
            first = false;
            self.render_nested(root, &tree, 0, &mut out, s);
        }
        out
    }

    fn render_nested(
        &self,
        label: Label,
        tree: &NestingTree,
        depth: usize,
        out: &mut String,
        s: &Styles,
    ) {
        let indent = "  ".repeat(depth);
        let (header, result) = self.signature(label, s);
        out.push_str(&format!(
            "{indent}{}func{} {header}{result} {{\n",
            s.keyword, s.reset
        ));
        let body = match self.body(label) {
            Some(b) => self.expr_text(b, s),
            None => format!("{}unset{}", s.keyword, s.reset),
        };
        out.push_str(&format!("{indent}  {body}\n"));
        for child in tree.children(Some(label)) {
            out.push('\n');
            self.render_nested(child, tree, depth + 1, out, s);
        }
        out.push_str(&format!("{indent}}}\n"));
    }

    pub fn render_func(&self, label: Label) -> String {
        let s = Styles::plain();
        let (header, result) = self.signature(label, &s);
        let body = match self.body(label) {
            Some(b) => self.expr_text(b, &s),
            None => "unset".to_string(),
        };
        format!("func {header}{result} {{ {body} }}")
    }

    /// `name(params)` and the (almost always empty) result suffix. The
    /// domain tuple is the parameter list; almost every function's
    /// codomain is "never returns" (calls don't come back in this IR),
    /// so a result type is only printed in the odd case it has one.
    fn signature(&self, label: Label, s: &Styles) -> (String, String) {
        let styled_ty = |t: TyId| format!("{}{}{}", s.ty, self.render_ty(t), s.reset);
        let params = match self.ty_kind(self.dom(label)) {
            TyKind::Tuple(items) => {
                let inner: Vec<String> = items
                    .iter()
                    .enumerate()
                    .map(|(i, t)| match self.param_name(label, i as u32) {
                        Some(name) => format!("{name}: {}", styled_ty(*t)),
                        None => styled_ty(*t),
                    })
                    .collect();
                inner.join(", ")
            }
            _ => match self.param_name(label, 0) {
                Some(name) => format!("{name}: {}", styled_ty(self.dom(label))),
                None => styled_ty(self.dom(label)),
            },
        };
        let result = match self.ty_kind(self.cod(label)) {
            TyKind::Bot => String::new(),
            _ => format!(" -> {}", styled_ty(self.cod(label))),
        };
        (
            format!("{}{}{}({params})", s.func, self.name(label), s.reset),
            result,
        )
    }

    pub fn render_ty(&self, ty: TyId) -> String {
        match self.ty_kind(ty) {
            TyKind::I64 => "int".into(),
            TyKind::F64 => "float".into(),
            TyKind::Bool => "bool".into(),
            TyKind::Byte => "byte".into(),
            TyKind::Ptr => "ptr".into(),
            TyKind::Void => "()".into(),
            TyKind::Bot => "never".into(),
            TyKind::Tuple(items) => {
                let inner: Vec<String> = items.iter().map(|t| self.render_ty(*t)).collect();
                format!("({})", inner.join(", "))
            }
            TyKind::Fn(d, c) => {
                let params = match self.ty_kind(*d) {
                    TyKind::Tuple(items) => {
                        let inner: Vec<String> = items.iter().map(|t| self.render_ty(*t)).collect();
                        inner.join(", ")
                    }
                    _ => self.render_ty(*d),
                };
                match self.ty_kind(*c) {
                    TyKind::Bot => format!("fn({params})"),
                    _ => format!("fn({params}) -> {}", self.render_ty(*c)),
                }
            }
            TyKind::Boxed(sym) => format!("boxed({})", self.render_symbol(sym)),
            TyKind::Variant(sym) => format!("variant({})", self.render_symbol(sym)),
            TyKind::Existential(sym) => format!("existential({})", self.render_symbol(sym)),
            TyKind::Erased => "erased".into(),
            TyKind::Cell(inner) => format!("cell({})", self.render_ty(*inner)),
        }
    }

    pub fn render_expr(&self, e: ExprId) -> String {
        self.expr_text(e, &Styles::plain())
    }

    fn expr_text(&self, e: ExprId, s: &Styles) -> String {
        match &self.expr(e).kind {
            ExprKind::Const(c) => {
                let text = match c {
                    Const::I64(v) => format!("{v}"),
                    Const::F64(bits) => format!("{}", f64::from_bits(*bits)),
                    Const::Bool(v) => format!("{v}"),
                    Const::Byte(v) => format!("{v}b"),
                    Const::Void => return "()".into(),
                    Const::StaticPtr(off) => format!("static+{off}"),
                    Const::Slot(index) => format!("slot#{index}"),
                };
                format!("{}{text}{}", s.num, s.reset)
            }
            ExprKind::Func(l) => format!("{}{}{}", s.func, self.name(*l), s.reset),
            ExprKind::Var(l) => format!("var {}", self.name(*l)),
            // A call: tuple arguments print as the argument list.
            ExprKind::App(f, a) => {
                let callee = self.expr_text(*f, s);
                match &self.expr(*a).kind {
                    ExprKind::Tuple(items) => {
                        let inner: Vec<String> =
                            items.iter().map(|i| self.expr_text(*i, s)).collect();
                        format!("{callee}({})", inner.join(", "))
                    }
                    _ => format!("{callee}({})", self.expr_text(*a, s)),
                }
            }
            ExprKind::Tuple(items) => {
                let inner: Vec<String> = items.iter().map(|i| self.expr_text(*i, s)).collect();
                format!("({})", inner.join(", "))
            }
            ExprKind::Extract(inner, index) => {
                // A parameter reference prints by name when the function
                // recorded one.
                if let ExprKind::Var(l) = &self.expr(*inner).kind
                    && let Some(param) = self.param_name(*l, *index)
                {
                    return format!("var {}.{param}", self.name(*l));
                }
                format!("{}.{index}", self.expr_text(*inner, s))
            }
            ExprKind::PrimOp(op, args, _) => {
                let mut parts = self.op_payload(op, s);
                parts.extend(args.iter().map(|a| self.expr_text(*a, s)));
                // A `record_new(String, static+N, len, …)` shows the
                // literal bytes the pointer refers to.
                if matches!(op, Op::RecordNew(_))
                    && let Some(text) = self.static_text(args)
                {
                    let payload = self.op_payload(op, s).len();
                    parts[payload] =
                        format!("{} {}({text:?}){}", parts[payload], s.string, s.reset);
                }
                format!("{}{}{}({})", s.op, op_name(op), s.reset, parts.join(", "))
            }
        }
    }

    /// The static bytes a `[static pointer, length, …]` argument list
    /// points at, when they are printable text.
    fn static_text(&self, args: &[ExprId]) -> Option<String> {
        let [ptr, len, ..] = args else { return None };
        let ExprKind::Const(Const::StaticPtr(off)) = &self.expr(*ptr).kind else {
            return None;
        };
        let ExprKind::Const(Const::I64(len)) = &self.expr(*len).kind else {
            return None;
        };
        let start = *off as usize;
        let end = start.checked_add(usize::try_from(*len).ok()?)?;
        let bytes = self.static_mem.get(start..end)?;
        let text = std::str::from_utf8(bytes).ok()?;
        // Escaped rendering keeps newlines/tabs readable; anything with
        // other control bytes is not a text literal.
        text.chars()
            .all(|c| !c.is_control() || c.is_whitespace())
            .then(|| text.to_string())
    }

    /// A symbol's display name when the lowerer recorded one; the raw
    /// symbol otherwise.
    fn render_symbol(&self, sym: &crate::name_resolution::symbol::Symbol) -> String {
        match self.symbol_names.get(sym) {
            Some(name) => name.clone(),
            None => sym.to_string(),
        }
    }

    /// Static operands an op carries in its variant (the struct symbol,
    /// the field index, …), printed ahead of the value arguments.
    fn op_payload(&self, op: &Op, s: &Styles) -> Vec<String> {
        let styled_sym = |sym| format!("{}{}{}", s.ty, self.render_symbol(sym), s.reset);
        match op {
            Op::RecordNew(sym) | Op::ExistentialPack(sym) => vec![styled_sym(sym)],
            Op::VariantNew(sym, tag) => vec![styled_sym(sym), tag.to_string()],
            Op::GetField(i) | Op::SetField(i) | Op::GetPayload(i) | Op::ExistentialWitness(i) => {
                vec![i.to_string()]
            }
            _ => vec![],
        }
    }
}

/// The op's name in snake_case (`record_new`, `io_write`, `cmp_lt`).
fn op_name(op: &Op) -> String {
    match op {
        Op::Cmp(c) => format!("cmp_{c:?}").to_lowercase(),
        Op::RecordNew(_) => "record_new".into(),
        Op::VariantNew(..) => "variant_new".into(),
        Op::GetField(_) => "get_field".into(),
        Op::SetField(_) => "set_field".into(),
        Op::GetPayload(_) => "get_payload".into(),
        Op::ExistentialPack(_) => "existential_pack".into(),
        Op::ExistentialWitness(_) => "existential_witness".into(),
        Op::ExistentialPayload => "existential_payload".into(),
        other => snake(&format!("{other:?}")),
    }
}

fn snake(name: &str) -> String {
    let mut out = String::new();
    for (i, ch) in name.chars().enumerate() {
        if ch.is_uppercase() {
            if i > 0 {
                out.push('_');
            }
            out.extend(ch.to_lowercase());
        } else {
            out.push(ch);
        }
    }
    out
}
