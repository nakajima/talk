use crate::{
    node_kinds::inline_ir_instruction::TypedInlineIRInstruction,
    types::{
        ty::Ty,
        type_error::TypeError,
        typed_ast::{
            TypedAST, TypedBlock, TypedExpr, TypedExprKind, TypedFunc, TypedMatchArm,
            TypedRecordField, TypedStmt, TypedStmtKind,
        },
        types::Types,
    },
};

pub struct SpecializationPass<'a> {
    ast: &'a mut TypedAST<Ty>,
    types: &'a Types,
}

impl<'a> SpecializationPass<'a> {
    pub fn new(ast: &'a mut TypedAST<Ty>, types: &'a Types) -> Self {
        Self { ast, types }
    }

    pub fn drive(&mut self) -> Result<(), TypeError> {
        let stmts = std::mem::take(&mut self.ast.stmts);
        let mut specialized_stmts = vec![];
        for stmt in stmts {
            specialized_stmts.push(self.visit_stmt(stmt)?);
        }
        _ = std::mem::replace(&mut self.ast.stmts, specialized_stmts);

        Ok(())
    }

    fn visit_stmt(&mut self, mut stmt: TypedStmt<Ty>) -> Result<TypedStmt<Ty>, TypeError> {
        stmt.kind = match stmt.kind {
            TypedStmtKind::Expr(expr) => TypedStmtKind::Expr(self.visit_expr(expr)?),
            TypedStmtKind::Assignment(lhs, rhs) => {
                TypedStmtKind::Assignment(self.visit_expr(lhs)?, self.visit_expr(rhs)?)
            }
            TypedStmtKind::Return(expr) => {
                TypedStmtKind::Return(expr.map(|e| self.visit_expr(e)).transpose()?)
            }
            TypedStmtKind::Continue(expr) => {
                TypedStmtKind::Continue(expr.map(|e| self.visit_expr(e)).transpose()?)
            }
            TypedStmtKind::Loop(cond, body) => {
                TypedStmtKind::Loop(self.visit_expr(cond)?, self.visit_block(body)?)
            }
            TypedStmtKind::Handler { effect, func } => TypedStmtKind::Handler {
                effect,
                func: self.visit_func(func)?,
            },
            TypedStmtKind::Break => TypedStmtKind::Break,
        };

        Ok(stmt)
    }

    fn visit_expr(&mut self, mut expr: TypedExpr<Ty>) -> Result<TypedExpr<Ty>, TypeError> {
        expr.kind = match expr.kind {
            TypedExprKind::InlineIR(box instr) => {
                TypedExprKind::InlineIR(self.visit_inline_ir(instr)?.into())
            }
            TypedExprKind::LiteralArray(items) => TypedExprKind::LiteralArray(
                items
                    .into_iter()
                    .map(|i| self.visit_expr(i))
                    .try_collect()?,
            ),
            TypedExprKind::Tuple(items) => TypedExprKind::Tuple(
                items
                    .into_iter()
                    .map(|i| self.visit_expr(i))
                    .try_collect()?,
            ),
            TypedExprKind::Block(block) => TypedExprKind::Block(self.visit_block(block)?),
            TypedExprKind::CallEffect { effect, args } => TypedExprKind::CallEffect {
                effect,
                args: args.into_iter().map(|i| self.visit_expr(i)).try_collect()?,
            },
            TypedExprKind::Call { .. } => return self.visit_call(expr),
            TypedExprKind::Member {
                box receiver,
                label,
            } => TypedExprKind::Member {
                receiver: self.visit_expr(receiver)?.into(),
                label,
            },
            TypedExprKind::ProtocolMember {
                box receiver,
                label,
                witness,
            } => TypedExprKind::ProtocolMember {
                receiver: self.visit_expr(receiver)?.into(),
                label,
                witness,
            },
            TypedExprKind::Func(func) => TypedExprKind::Func(self.visit_func(func)?),
            TypedExprKind::If(box cond, conseq, alt) => TypedExprKind::If(
                self.visit_expr(cond)?.into(),
                self.visit_block(conseq)?,
                self.visit_block(alt)?,
            ),
            TypedExprKind::Match(box scrutinee, arms) => TypedExprKind::Match(
                self.visit_expr(scrutinee)?.into(),
                arms.into_iter()
                    .map(|a| self.visit_match_arm(a))
                    .try_collect()?,
            ),
            TypedExprKind::RecordLiteral { fields } => {
                let mut new_fields: Vec<_> = Default::default();
                for field in fields {
                    new_fields.push(TypedRecordField {
                        name: field.name,
                        value: self.visit_expr(field.value)?,
                    });
                }
                TypedExprKind::RecordLiteral { fields: new_fields }
            }
            kind => kind,
        };

        Ok(expr)
    }

    fn visit_call(&mut self, mut expr: TypedExpr<Ty>) -> Result<TypedExpr<Ty>, TypeError> {
        let TypedExprKind::Call {
            box callee,
            type_args,
            args,
            resolved,
        } = expr.kind
        else {
            unreachable!()
        };

        expr.kind = TypedExprKind::Call {
            callee: self.visit_expr(callee)?.into(),
            type_args,
            args: args.into_iter().map(|i| self.visit_expr(i)).try_collect()?,
            resolved,
        };
        Ok(expr)
    }

    fn visit_block(&mut self, block: TypedBlock<Ty>) -> Result<TypedBlock<Ty>, TypeError> {
        Ok(block)
    }

    fn visit_func(&mut self, func: TypedFunc<Ty>) -> Result<TypedFunc<Ty>, TypeError> {
        Ok(func)
    }

    fn visit_match_arm(
        &mut self,
        match_arm: TypedMatchArm<Ty>,
    ) -> Result<TypedMatchArm<Ty>, TypeError> {
        Ok(match_arm)
    }

    fn visit_inline_ir(
        &mut self,
        instr: TypedInlineIRInstruction<Ty>,
    ) -> Result<TypedInlineIRInstruction<Ty>, TypeError> {
        Ok(instr)
    }
}

#[cfg(test)]
pub mod tests {
    use crate::{
        name_resolution::symbol::{Symbol, SynthesizedId},
        node_id::NodeID,
        types::{
            row::Row,
            ty::Ty,
            typed_ast::{TypedAST, TypedExpr, TypedExprKind, TypedStmtKind},
            types_tests::tests::typecheck,
        },
    };

    fn specialize(code: &'static str) -> TypedAST<Ty> {
        typecheck(code).0
    }

    #[test]
    fn specializes_generic_func_call() {
        let ast = specialize(
            "
      func id(x) { x }
      id(123)
      id(true)
      ",
        );

        assert_eq!(
            ast.stmts[0].kind,
            TypedStmtKind::Expr(TypedExpr {
                id: NodeID::ANY,
                ty: Ty::Int,
                kind: TypedExprKind::Call {
                    callee: TypedExpr {
                        id: NodeID::ANY,
                        ty: Ty::Func(Ty::Int.into(), Ty::Int.into(), Row::Param(1.into()).into()),
                        kind: TypedExprKind::Variable(Symbol::Synthesized(SynthesizedId::from(1)))
                    }
                    .into(),
                    type_args: vec![Ty::Int],
                    args: vec![TypedExpr {
                        id: NodeID::ANY,
                        ty: Ty::Int,
                        kind: TypedExprKind::LiteralInt("123".into())
                    }],
                    resolved: None,
                }
            })
        )
    }
}
