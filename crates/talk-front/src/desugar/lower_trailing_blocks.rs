use derive_visitor::{DriveMut, VisitorMut};

use crate::{
    ast::{AST, Parsed},
    id_generator::IDGenerator,
    label::Label,
    name::Name,
    node_id::{FileID, NodeID},
    node_kinds::{
        block::Block,
        call_arg::{CallArg, CallArgOrigin},
        expr::{Expr, ExprKind},
        func::{EffectSet, Func, FuncOrigin},
    },
    parsing::span::Span,
};

/// Lowers a call's trailing block to an ordinary anonymous-function
/// argument: `foo { x in body }` becomes `foo(func(x) { body })`. Effect
/// performs use the same syntax and lower to the same argument shape.
///
/// A trailing block is nothing but closure syntax, so it desugars to the one
/// closure form (`ExprKind::Func`) and every later phase — name resolution,
/// checking, assignment conversion, lowering — sees a single kind of
/// function value. The parser has already synthesized `$0..$n` parameters
/// onto the block, so its `args` transfer directly.
#[derive(Debug, VisitorMut)]
#[visitor(Expr(enter))]
pub struct LowerTrailingBlocks {
    file_id: FileID,
    node_ids: IDGenerator,
}

impl LowerTrailingBlocks {
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
        let (args, trailing_block) = match &mut expr.kind {
            ExprKind::Call {
                args,
                trailing_block,
                ..
            }
            | ExprKind::CallEffect {
                args,
                trailing_block,
                ..
            } => (args, trailing_block),
            _ => return,
        };
        let Some(mut block) = trailing_block.take() else {
            return;
        };
        let params = std::mem::take(&mut block.args);
        let span = block.span;
        let func = Func {
            id: self.next_id(),
            name: Name::Raw(format!("#fn_trailing_{}", block.id.1)),
            name_span: Span::SYNTHESIZED,
            origin: FuncOrigin::default(),
            effects: EffectSet::default(),
            generics: vec![],
            captures: vec![],
            where_clause: None,
            params,
            body: Block {
                id: block.id,
                args: vec![],
                body: block.body,
                span,
            },
            ret: None,
            attributes: vec![],
        };
        args.push(CallArg {
            id: self.next_id(),
            label: Label::Positional(args.len()),
            label_span: Span::SYNTHESIZED,
            // The label exception is keyed off this origin (ADR 0041).
            origin: CallArgOrigin::TrailingBlock,
            value: Expr {
                id: self.next_id(),
                span,
                kind: ExprKind::Func(func),
            },
            span,
            mode: None,
            mode_span: None,
        });
    }
}

