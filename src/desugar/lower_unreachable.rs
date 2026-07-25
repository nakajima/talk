use derive_visitor::{DriveMut, VisitorMut};

use crate::{
    ast::{AST, Parsed},
    id_generator::IDGenerator,
    label::Label,
    name::Name,
    node_id::{FileID, NodeID},
    node_kinds::{
        call_arg::{CallArg, CallArgOrigin},
        expr::{Expr, ExprKind},
    },
    span::Span,
};

/// Lowers the `unreachable` expression to the ordinary Core panic effect.
///
/// Keeping panic as an effect means inference, handlers, and the host fallback
/// all use the same routing mechanism as every other runtime effect.
#[derive(Debug, VisitorMut)]
#[visitor(Expr(enter))]
pub struct LowerUnreachable {
    file_id: FileID,
    node_ids: IDGenerator,
}

impl LowerUnreachable {
    pub fn run(ast: &mut AST<Parsed>) {
        let node_ids = std::mem::take(&mut ast.node_ids);
        let mut instance = Self {
            file_id: ast.file_id,
            node_ids,
        };

        for root in &mut ast.roots {
            root.drive_mut(&mut instance);
        }

        _ = std::mem::replace(&mut ast.node_ids, instance.node_ids);
    }

    fn next_id(&mut self) -> NodeID {
        NodeID(self.file_id, self.node_ids.next_id())
    }

    fn enter_expr(&mut self, expr: &mut Expr) {
        if !matches!(expr.kind, ExprKind::Unreachable) {
            return;
        }

        let message_id = self.next_id();
        let arg_id = self.next_id();
        let message = Expr {
            id: message_id,
            span: Span::SYNTHESIZED,
            kind: ExprKind::LiteralString("reached unreachable".into()),
        };
        expr.kind = ExprKind::CallEffect {
            effect_name: Name::Raw("panic".into()),
            effect_name_span: expr.span,
            type_args: Vec::new(),
            args: vec![CallArg {
                origin: CallArgOrigin::Synthesized,
                id: arg_id,
                label: Label::Positional(0),
                label_span: Span::SYNTHESIZED,
                value: message,
                span: expr.span,
                mode: None,
                mode_span: None,
            }],
        };
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        desugar::lower_unreachable::LowerUnreachable,
        node_kinds::{expr::ExprKind, stmt::StmtKind},
        parser_tests::tests::parse,
    };

    #[test]
    fn lowers_to_the_panic_effect() {
        let mut parsed = parse("unreachable");
        LowerUnreachable::run(&mut parsed);

        let StmtKind::Expr(expr) = &parsed.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        let ExprKind::CallEffect {
            effect_name, args, ..
        } = &expr.kind
        else {
            panic!("expected panic perform");
        };
        assert_eq!(effect_name.name_str(), "panic");
        assert!(matches!(
            args.as_slice(),
            [arg] if matches!(arg.value.kind, ExprKind::LiteralString(ref message) if message == "reached unreachable")
        ));
    }
}
