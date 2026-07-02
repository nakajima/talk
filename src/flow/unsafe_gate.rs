//! Raw-pointer surface gating, ported from the legacy checker: outside the
//! core module, any expression whose type mentions `RawPtr` — and any inline
//! IR — is only legal in a source file containing a line that is exactly
//! `// unsafe`.

use std::ops::ControlFlow;

use indexmap::IndexMap;

use crate::compiling::driver::Source;
use crate::compiling::module::ModuleId;
use crate::hir::{self, HirFile};
use crate::name_resolution::symbol::Symbol;
use crate::node_id::NodeID;
use crate::flow::OwnershipError;
use crate::types::ty::Ty;

pub(crate) fn check(
    hir: &IndexMap<Source, HirFile>,
    module_id: ModuleId,
) -> Vec<(OwnershipError, NodeID)> {
    if module_id == ModuleId::Core {
        return vec![];
    }
    let mut errors = vec![];
    for (source, file) in hir {
        if source_allows_unsafe(source) {
            continue;
        }
        let mut visitor = RawPtrVisitor { errors: &mut errors };
        for root in &file.roots {
            use derive_visitor::Drive;
            root.drive(&mut visitor);
        }
    }
    errors
}

/// A source opts into raw pointers with a line that is exactly `// unsafe`.
fn source_allows_unsafe(source: &Source) -> bool {
    source
        .read()
        .map(|text| text.lines().any(|line| line.trim() == "// unsafe"))
        .unwrap_or(false)
}

#[derive(derive_visitor::Visitor)]
#[visitor(hir::Expr(enter))]
struct RawPtrVisitor<'a> {
    errors: &'a mut Vec<(OwnershipError, NodeID)>,
}

impl RawPtrVisitor<'_> {
    fn enter_expr(&mut self, expr: &hir::Expr) {
        if let hir::ExprKind::InlineIR(_) = &expr.kind {
            self.errors.push((
                OwnershipError::UnsafeRawPointerUsage {
                    ty: "inline IR".to_string(),
                },
                expr.id,
            ));
            return;
        }
        if mentions_raw_ptr(&expr.ty) {
            self.errors.push((
                OwnershipError::UnsafeRawPointerUsage {
                    ty: expr.ty.render_mono(),
                },
                expr.id,
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
