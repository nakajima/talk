use derive_visitor::{DriveMut, VisitorMut};

use crate::{
    ast::{AST, Parsed},
    id_generator::IDGenerator,
    label::Label,
    name::Name,
    node_id::{FileID, NodeID},
    node_kinds::{
        block::Block,
        call_arg::CallArg,
        expr::{Expr, ExprKind},
        func::{EffectSet, Func},
    },
    parsing::span::Span,
};

/// Lowers a call's trailing block to an ordinary anonymous-function
/// argument: `foo { x in body }` becomes `foo(func(x) { body })`.
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
        let ExprKind::Call {
            args,
            trailing_block,
            ..
        } = &mut expr.kind
        else {
            return;
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    #[test]
    fn trailing_blocks_become_anonymous_func_arguments() {
        let lexer = Lexer::new("foo(1) { x in x }\nbar { $0 }\nbaz {}\n");
        let parser = Parser::new("-", crate::node_id::FileID(0), lexer);
        let (mut ast, _) = parser.parse().expect("parse");
        LowerTrailingBlocks::run(&mut ast);

        let mut calls = 0;
        for root in &ast.roots {
            let crate::node::Node::Stmt(stmt) = root else {
                panic!("expected statements, got {root:?}");
            };
            let crate::node_kinds::stmt::StmtKind::Expr(expr) = &stmt.kind else {
                panic!("expected expression statements");
            };
            let ExprKind::Call {
                args,
                trailing_block,
                ..
            } = &expr.kind
            else {
                panic!("expected calls");
            };
            assert!(trailing_block.is_none(), "trailing block must desugar");
            let Some(CallArg {
                value:
                    Expr {
                        kind: ExprKind::Func(func),
                        ..
                    },
                ..
            }) = args.last()
            else {
                panic!("expected a trailing func argument");
            };
            calls += 1;
            match calls {
                // `{ x in x }` carries its named parameter.
                1 => assert_eq!(func.params[0].name.name_str(), "x"),
                // `{ $0 }` carries the parser-synthesized positional.
                2 => assert_eq!(func.params[0].name.name_str(), "$0"),
                // `{}` is a zero-parameter closure.
                _ => assert!(func.params.is_empty()),
            }
        }
        assert_eq!(calls, 3);
    }
}
