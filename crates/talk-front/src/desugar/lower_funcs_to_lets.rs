use crate::ast::Parsed;
use crate::id_generator::IDGenerator;
use crate::node_id::{FileID, NodeID};
use crate::node_kinds::pattern::{Pattern, PatternKind};
use crate::{ast::AST, node_kinds::decl::Decl};
use derive_visitor::DriveMut;
use derive_visitor::VisitorMut;

#[derive(VisitorMut)]
#[visitor(Decl(enter))]
pub struct LowerFuncsToLets {
    node_ids: IDGenerator,
    file_id: FileID,
}

impl LowerFuncsToLets {
    pub fn run(ast: &mut AST<Parsed>) {
        // Take the id generator
        let ids = std::mem::take(&mut ast.node_ids);
        let mut pass = LowerFuncsToLets {
            file_id: ast.file_id,
            node_ids: ids,
        };
        for root in ast.roots.iter_mut() {
            root.drive_mut(&mut pass);
        }

        // Give the id generator back
        _ = std::mem::replace(&mut ast.node_ids, pass.node_ids);
    }

    fn enter_decl(&mut self, decl: &mut Decl) {
        use crate::node_kinds::{
            decl::DeclKind,
            expr::{Expr, ExprKind},
        };

        if let DeclKind::Let {
            lhs:
                Pattern {
                    kind: PatternKind::Bind(name),
                    ..
                },
            rhs:
                Some(Expr {
                    kind: ExprKind::Func(func),
                    ..
                }),
            ..
        } = &mut decl.kind
        {
            // If we get `let foo = func bar() {}`, just rename the func to foo
            // because who has time for this nonsense anyway.
            // TODO: Maybe handle this during name resolution instead?
            func.name = name.clone();
            return;
        }

        if let DeclKind::Func(func) = decl.kind.clone() {
            let name = func.name.clone();
            // Build an Expr::Func from the decl’s parts (reusing nodes and
            // keeping the named-callable origin — ADR 0041).
            let func_expr = Expr {
                id: NodeID(self.file_id, self.node_ids.next_id()),
                span: decl.span,
                kind: ExprKind::Func(func),
            };

            // Replace decl with: let <name> = <func_expr>;
            decl.kind = DeclKind::Let {
                lhs: crate::node_kinds::pattern::Pattern {
                    id: NodeID(self.file_id, self.node_ids.next_id()),
                    span: decl.span,
                    kind: crate::node_kinds::pattern::PatternKind::Bind(name.clone()),
                },
                type_annotation: None,
                rhs: Some(func_expr),
            };
        }
    }
}

