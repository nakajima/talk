use derive_visitor::{DriveMut, VisitorMut};

use crate::{
    ast::{AST, Parsed},
    id_generator::IDGenerator,
    node_id::{FileID, NodeID},
    node_kinds::{
        expr::{Expr, ExprKind},
        match_arm::MatchArm,
        pattern::{Pattern, PatternKind},
    },
    span::Span,
};

/// Desugars an `if` **expression** into a `match` on its boolean condition:
///
/// ```talk
/// if c { t } else { e }
/// ```
///
/// becomes
///
/// ```talk
/// match c {
///     true { t }
///     false { e }
/// }
/// ```
///
/// The two are typed identically: an expression-`if` already checks both
/// branches against the expected type, and a `true`/`false` pattern already
/// constrains the scrutinee to `Bool` — so this collapse is exact, and the
/// type checker, ownership, and lowering never need a separate `if`-expression
/// rule.
///
/// Statement-`if` is left alone: it infers its branches independently (they
/// need not unify) and drives divergence analysis, so it is not a `match` and
/// is lowered later, when statement control flow collapses.
///
/// Runs after `LowerOperators`, which emits `if` expressions for `&&`/`||`.
#[derive(Debug, VisitorMut)]
#[visitor(Expr(enter))]
pub struct LowerIfToMatch {
    node_ids: IDGenerator,
    file_id: FileID,
}

impl LowerIfToMatch {
    pub fn run(ast: &mut AST<Parsed>) {
        let node_ids = std::mem::take(&mut ast.node_ids);
        let mut instance = Self {
            node_ids,
            file_id: ast.file_id,
        };

        for root in ast.roots.iter_mut() {
            root.drive_mut(&mut instance);
        }

        _ = std::mem::replace(&mut ast.node_ids, instance.node_ids);
    }

    fn next_id(&mut self) -> NodeID {
        NodeID(self.file_id, self.node_ids.next_id())
    }

    fn arm(&mut self, pattern: PatternKind, body: crate::node_kinds::block::Block) -> MatchArm {
        MatchArm {
            id: self.next_id(),
            pattern: Pattern {
                id: self.next_id(),
                span: Span::SYNTHESIZED,
                kind: pattern,
            },
            body,
            span: Span::SYNTHESIZED,
        }
    }

    fn enter_expr(&mut self, expr: &mut Expr) {
        let ExprKind::If(condition, then_block, else_block) = expr.kind.clone() else {
            return;
        };

        let true_arm = self.arm(PatternKind::LiteralTrue, then_block);
        let false_arm = self.arm(PatternKind::LiteralFalse, else_block);

        expr.kind = ExprKind::Match(condition, vec![true_arm, false_arm]);
    }
}

