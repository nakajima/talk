//! Raw-pointer surface gating: outside the core module, expressions whose
//! type mentions `RawPtr` and inline IR require a lexical `@unsafe` block or
//! a function whose checked effect row contains the intrinsic `'unsafe`
//! effect. The gate fails closed before ownership analysis runs.

use std::ops::ControlFlow;

use super::{BackendError, ProgramInput};
use crate::name_resolution::symbol::Symbol;
use crate::typed_ast::{self, Expr, Func};
use crate::types::ty::Ty;

pub(super) fn check(programs: &[ProgramInput<'_>]) -> Result<(), BackendError> {
    for input in programs {
        if input.module == crate::compiling::module::ModuleId::Core {
            continue;
        }
        for (_, file) in input.program.files() {
            let mut visitor = UnsafeVisitor {
                error: None,
                contexts: vec![0],
            };
            for root in &file.roots {
                use derive_visitor::Drive;
                root.drive(&mut visitor);
            }
            if let Some(error) = visitor.error {
                return Err(error);
            }
        }
    }
    Ok(())
}

#[derive(derive_visitor::Visitor)]
#[visitor(Expr(enter, exit), Func(enter, exit))]
struct UnsafeVisitor {
    error: Option<BackendError>,
    // One independent context per function. A nested function does not
    // inherit an enclosing block's lexical unsafe authority.
    contexts: Vec<usize>,
}

impl UnsafeVisitor {
    fn enter_func(&mut self, func: &typed_ast::Func) {
        let requires_unsafe = matches!(
            &func.scheme.ty,
            Ty::Func(_, _, effects)
                if effects
                    .effects
                    .iter()
                    .any(|entry| entry.effect == Symbol::Unsafe)
        );
        self.contexts.push(usize::from(requires_unsafe));
    }

    fn exit_func(&mut self, _func: &typed_ast::Func) {
        self.contexts.pop();
    }

    fn enter_expr(&mut self, expr: &typed_ast::Expr) {
        if matches!(expr.kind, typed_ast::ExprKind::Unsafe(_)) {
            // The wrapper itself is checked in the outer context so a raw
            // pointer cannot escape merely by being the block's result.
            if self.error.is_none() && !self.allows_unsafe() && mentions_raw_ptr(&expr.ty) {
                self.raw_ptr_error(expr);
            }
            *self
                .contexts
                .last_mut()
                .expect("unsafe visitor always has a context") += 1;
            return;
        }

        if self.error.is_some() || matches!(expr.kind, typed_ast::ExprKind::Func(_)) {
            return;
        }
        if self.allows_unsafe() {
            return;
        }
        if matches!(expr.kind, typed_ast::ExprKind::InlineIR(_)) {
            self.error = Some(BackendError::new(
                "inline IR requires `@unsafe { ... }` or an enclosing `'unsafe` function".into(),
                expr.span,
            ));
            return;
        }
        if mentions_raw_ptr(&expr.ty) {
            self.raw_ptr_error(expr);
        }
    }

    fn exit_expr(&mut self, expr: &typed_ast::Expr) {
        if matches!(expr.kind, typed_ast::ExprKind::Unsafe(_)) {
            *self
                .contexts
                .last_mut()
                .expect("unsafe visitor always has a context") -= 1;
        }
    }

    fn allows_unsafe(&self) -> bool {
        self.contexts.last().is_some_and(|depth| *depth > 0)
    }

    fn raw_ptr_error(&mut self, expr: &typed_ast::Expr) {
        self.error = Some(BackendError::new(
            format!(
                "`{}` requires `@unsafe {{ ... }}` or an enclosing `'unsafe` function",
                expr.ty.render_mono()
            ),
            expr.span,
        ));
    }
}

fn mentions_raw_ptr(ty: &Ty) -> bool {
    ty.try_visit(&mut |t| match t {
        Ty::Nominal(symbol, _) if *symbol == Symbol::RawPtr => ControlFlow::Break(()),
        _ => ControlFlow::Continue(()),
    })
    .is_break()
}
