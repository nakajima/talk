//! Raw-pointer surface gating, restored from the reference checker:
//! outside the core module, any expression whose type mentions `RawPtr` —
//! and any inline IR — is only legal in a source file containing a line
//! that is exactly `// unsafe`. The gate fails closed before any
//! ownership analysis runs; it is one of the four error categories the
//! implicit-sharing decision keeps (docs/ownership-rethink-plan.md).

use std::ops::ControlFlow;

use super::{BackendError, ProgramInput};
use crate::compiling::driver::Source;
use crate::name_resolution::symbol::Symbol;
use crate::typed_ast;
use crate::types::ty::Ty;

pub(super) fn check(programs: &[ProgramInput<'_>]) -> Result<(), BackendError> {
    for input in programs {
        if input.module == crate::compiling::module::ModuleId::Core {
            continue;
        }
        for (source, file) in input.program.files() {
            if source_allows_unsafe(source) {
                continue;
            }
            let mut visitor = RawPtrVisitor { error: None };
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

/// A source opts into raw pointers with a line that is exactly `// unsafe`.
fn source_allows_unsafe(source: &Source) -> bool {
    source
        .read()
        .map(|text| text.lines().any(|line| line.trim() == "// unsafe"))
        .unwrap_or(false)
}

#[derive(derive_visitor::Visitor)]
#[visitor(typed_ast::Expr(enter))]
struct RawPtrVisitor {
    error: Option<BackendError>,
}

impl RawPtrVisitor {
    fn enter_expr(&mut self, expr: &typed_ast::Expr) {
        if self.error.is_some() {
            return;
        }
        if let typed_ast::ExprKind::InlineIR(_) = &expr.kind {
            self.error = Some(BackendError::new(
                "inline IR is only available in core or sources marked '// unsafe'".into(),
                expr.span,
            ));
            return;
        }
        if mentions_raw_ptr(&expr.ty) {
            self.error = Some(BackendError::new(
                format!(
                    "`{}` is only available in core or sources marked '// unsafe'",
                    expr.ty.render_mono()
                ),
                expr.span,
            ));
        }
    }
}

fn mentions_raw_ptr(ty: &Ty) -> bool {
    ty.try_visit(&mut |t| match t {
        Ty::Nominal(symbol, _) if *symbol == Symbol::RawPtr => ControlFlow::Break(()),
        _ => ControlFlow::Continue(()),
    })
    .is_break()
}
