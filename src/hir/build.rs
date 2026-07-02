//! AST → HIR lowering (the HirLowerer). Consumes the name-resolved, type-checked
//! AST and produces the owned HIR: NodeID-preserving, and with each expression's
//! type baked onto its node (read once from the checker's tables). All real
//! desugaring already happened in `name_resolution/transforms/`, so the dropped
//! surface forms (`Unary`/`Binary`/`For`/`Incomplete`) must not appear — they
//! panic loudly if they somehow do.

use crate::hir;
use crate::node::Node;
use crate::node_kinds::{decl, expr, pattern, stmt};
use crate::parsing::ast::{AST, NameResolved};
use crate::types::TypeOutput;

/// Lower one name-resolved, type-checked source file to a `HirFile`.
pub fn build_file(ast: &AST<NameResolved>, types: &TypeOutput) -> hir::HirFile {
    HirLowerer { types }.file(ast)
}

struct HirLowerer<'a> {
    types: &'a TypeOutput,
}

impl HirLowerer<'_> {
    fn file(&self, ast: &AST<NameResolved>) -> hir::HirFile {
        hir::HirFile {
            file_id: ast.file_id,
            roots: self.roots(&ast.roots),
        }
    }

    fn roots(&self, roots: &[Node]) -> Vec<hir::Node> {
        roots.iter().map(|n| self.node(n)).collect()
    }

    fn node(&self, node: &Node) -> hir::Node {
        match node {
            Node::Decl(d) => hir::Node::Decl(self.decl(d)),
            Node::Stmt(s) => hir::Node::Stmt(self.stmt(s)),
            Node::Expr(e) => hir::Node::Expr(self.expr(e)),
            other => unreachable!("unexpected node in HIR lowering position: {other:?}"),
        }
    }

    // ----- Expressions -----------------------------------------------------

    fn expr(&self, e: &expr::Expr) -> hir::Expr {
        hir::Expr {
            id: e.id,
            kind: self.expr_kind(&e.kind),
            span: e.span,
            ownership: hir::ExprOwnership::default(),
            ty: {
                let Some(ty) = self.types.node_types.get(&e.id) else {
                    unreachable!("the type checker assigns every expression a type")
                };
                ty.clone()
            },
            member_resolution: self.types.member_resolutions.get(&e.id).cloned(),
            instantiation: self.types.instantiations.get(&e.id).cloned(),
            existential_pack: self.types.existential_packs.get(&e.id).cloned(),
        }
    }

    fn boxed(&self, e: &expr::Expr) -> Box<hir::Expr> {
        Box::new(self.expr(e))
    }

    fn expr_kind(&self, k: &expr::ExprKind) -> hir::ExprKind {
        match k {
            expr::ExprKind::InlineIR(ir) => hir::ExprKind::InlineIR(hir::InlineIRInstruction {
                id: ir.id,
                span: ir.span,
                binds: ir.binds.iter().map(|b| self.expr(b)).collect(),
                kind: ir.kind.clone(),
            }),
            expr::ExprKind::As(inner, ty) => hir::ExprKind::As(self.boxed(inner), ty.clone()),
            expr::ExprKind::CallEffect {
                effect_name,
                type_args,
                args,
                ..
            } => hir::ExprKind::CallEffect {
                effect_name: effect_name.clone(),
                type_args: type_args.clone(),
                args: args.iter().map(|a| self.call_arg(a)).collect(),
            },
            expr::ExprKind::LiteralArray(items) => {
                hir::ExprKind::LiteralArray(items.iter().map(|i| self.expr(i)).collect())
            }
            expr::ExprKind::LiteralInt(s) => hir::ExprKind::LiteralInt(s.clone()),
            expr::ExprKind::LiteralFloat(s) => hir::ExprKind::LiteralFloat(s.clone()),
            expr::ExprKind::LiteralTrue => hir::ExprKind::LiteralTrue,
            expr::ExprKind::LiteralFalse => hir::ExprKind::LiteralFalse,
            expr::ExprKind::LiteralString(s) => hir::ExprKind::LiteralString(s.clone()),
            expr::ExprKind::Tuple(items) => {
                hir::ExprKind::Tuple(items.iter().map(|i| self.expr(i)).collect())
            }
            expr::ExprKind::Block(block) => hir::ExprKind::Block(self.block(block)),
            expr::ExprKind::Call {
                callee,
                type_args,
                args,
                trailing_block,
            } => hir::ExprKind::Call {
                callee: self.boxed(callee),
                type_args: type_args.clone(),
                args: args.iter().map(|a| self.call_arg(a)).collect(),
                trailing_block: trailing_block.as_ref().map(|b| self.block(b)),
            },
            expr::ExprKind::Member(recv, label, _span) => {
                hir::ExprKind::Member(recv.as_ref().map(|r| self.boxed(r)), label.clone())
            }
            expr::ExprKind::Func(func) => hir::ExprKind::Func(self.func(func)),
            expr::ExprKind::Variable(name) => hir::ExprKind::Variable(name.clone()),
            expr::ExprKind::Constructor(name) => hir::ExprKind::Constructor(name.clone()),
            expr::ExprKind::If(cond, then, els) => {
                hir::ExprKind::If(self.boxed(cond), self.block(then), self.block(els))
            }
            expr::ExprKind::Match(scrut, arms) => hir::ExprKind::Match(
                self.boxed(scrut),
                arms.iter().map(|a| self.match_arm(a)).collect(),
            ),
            expr::ExprKind::RecordLiteral { fields, spread } => hir::ExprKind::RecordLiteral {
                fields: fields.iter().map(|f| self.record_field(f)).collect(),
                spread: spread.as_ref().map(|s| self.boxed(s)),
            },
            expr::ExprKind::RowVariable(name) => hir::ExprKind::RowVariable(name.clone()),
            expr::ExprKind::Unary(..) | expr::ExprKind::Binary(..) => {
                unreachable!("Unary/Binary should be desugared by LowerOperators before HIR")
            }
            expr::ExprKind::Incomplete(_) => {
                unreachable!("Incomplete expressions cannot be lowered to HIR")
            }
        }
    }

    fn call_arg(&self, a: &crate::node_kinds::call_arg::CallArg) -> hir::CallArg {
        hir::CallArg {
            id: a.id,
            label: a.label.clone(),
            value: self.expr(&a.value),
        }
    }

    fn record_field(&self, f: &crate::node_kinds::record_field::RecordField) -> hir::RecordField {
        hir::RecordField {
            id: f.id,
            label: f.label.clone(),
            value: self.expr(&f.value),
        }
    }

    fn match_arm(&self, arm: &crate::node_kinds::match_arm::MatchArm) -> hir::MatchArm {
        hir::MatchArm {
            id: arm.id,
            pattern: self.pattern(&arm.pattern),
            body: self.block(&arm.body),
        }
    }

    // ----- Patterns --------------------------------------------------------

    fn pattern(&self, p: &pattern::Pattern) -> hir::Pattern {
        hir::Pattern {
            id: p.id,
            kind: self.pattern_kind(&p.kind),
            span: p.span,
        }
    }

    fn pattern_kind(&self, k: &pattern::PatternKind) -> hir::PatternKind {
        match k {
            pattern::PatternKind::LiteralInt(s) => hir::PatternKind::LiteralInt(s.clone()),
            pattern::PatternKind::LiteralFloat(s) => hir::PatternKind::LiteralFloat(s.clone()),
            pattern::PatternKind::LiteralTrue => hir::PatternKind::LiteralTrue,
            pattern::PatternKind::LiteralFalse => hir::PatternKind::LiteralFalse,
            pattern::PatternKind::Bind(name) => hir::PatternKind::Bind(name.clone()),
            pattern::PatternKind::Tuple(ps) => {
                hir::PatternKind::Tuple(ps.iter().map(|p| self.pattern(p)).collect())
            }
            pattern::PatternKind::Or(ps) => {
                hir::PatternKind::Or(ps.iter().map(|p| self.pattern(p)).collect())
            }
            pattern::PatternKind::Wildcard => hir::PatternKind::Wildcard,
            pattern::PatternKind::Variant {
                enum_name,
                variant_name,
                fields,
                ..
            } => hir::PatternKind::Variant {
                enum_name: enum_name.clone(),
                variant_name: variant_name.clone(),
                fields: fields.iter().map(|p| self.pattern(p)).collect(),
            },
            pattern::PatternKind::Record { fields } => hir::PatternKind::Record {
                fields: fields
                    .iter()
                    .map(|f| self.record_field_pattern(f))
                    .collect(),
            },
            pattern::PatternKind::Struct {
                struct_name,
                fields,
                field_names,
                rest,
            } => hir::PatternKind::Struct {
                struct_name: struct_name.clone(),
                fields: fields
                    .iter()
                    .map(|n| match n {
                        Node::Pattern(p) => self.pattern(p),
                        other => unreachable!("struct pattern field is not a pattern: {other:?}"),
                    })
                    .collect(),
                field_names: field_names.clone(),
                rest: *rest,
            },
        }
    }

    fn record_field_pattern(&self, f: &pattern::RecordFieldPattern) -> hir::RecordFieldPattern {
        let kind = match &f.kind {
            pattern::RecordFieldPatternKind::Bind(name) => {
                hir::RecordFieldPatternKind::Bind(name.clone())
            }
            pattern::RecordFieldPatternKind::Equals { name, value, .. } => {
                hir::RecordFieldPatternKind::Equals {
                    name: name.clone(),
                    value: self.pattern(value),
                }
            }
            pattern::RecordFieldPatternKind::Rest => hir::RecordFieldPatternKind::Rest,
        };
        hir::RecordFieldPattern { id: f.id, kind }
    }

    // ----- Blocks and statements -------------------------------------------

    fn block(&self, b: &crate::node_kinds::block::Block) -> hir::Block {
        hir::Block {
            id: b.id,
            args: self.params(&b.args),
            body: self.roots(&b.body),
            span: b.span,
            drops: vec![],
        }
    }

    fn stmt(&self, s: &stmt::Stmt) -> hir::Stmt {
        hir::Stmt {
            id: s.id,
            kind: self.stmt_kind(&s.kind),
            span: s.span,
            drops: vec![],
        }
    }

    fn stmt_kind(&self, k: &stmt::StmtKind) -> hir::StmtKind {
        match k {
            stmt::StmtKind::Expr(e) => hir::StmtKind::Expr(self.expr(e)),
            stmt::StmtKind::If(cond, then, els) => hir::StmtKind::If(
                self.expr(cond),
                self.block(then),
                els.as_ref().map(|b| self.block(b)),
            ),
            stmt::StmtKind::Return(e) => hir::StmtKind::Return(e.as_ref().map(|e| self.expr(e))),
            stmt::StmtKind::Break => hir::StmtKind::Break,
            stmt::StmtKind::Assignment(lhs, rhs) => {
                hir::StmtKind::Assignment(self.boxed(lhs), self.boxed(rhs))
            }
            stmt::StmtKind::Loop(cond, body) => {
                hir::StmtKind::Loop(cond.as_ref().map(|e| self.expr(e)), self.block(body))
            }
            stmt::StmtKind::Continue(e) => {
                hir::StmtKind::Continue(e.as_ref().map(|e| self.expr(e)))
            }
            stmt::StmtKind::Handling {
                effect_name, body, ..
            } => hir::StmtKind::Handling {
                effect_name: effect_name.clone(),
                body: self.block(body),
            },
            stmt::StmtKind::For { .. } => {
                unreachable!("For should be desugared by LowerForLoops before HIR")
            }
        }
    }

    // ----- Functions and declarations --------------------------------------

    fn param(&self, p: &crate::node_kinds::parameter::Parameter) -> hir::Parameter {
        hir::Parameter {
            id: p.id,
            name: p.name.clone(),
            name_span: p.name_span,
            type_annotation: p.type_annotation.clone(),
            span: p.span,
            ty: self.types.node_types.get(&p.id).cloned(),
        }
    }

    fn params(&self, ps: &[crate::node_kinds::parameter::Parameter]) -> Vec<hir::Parameter> {
        ps.iter().map(|p| self.param(p)).collect()
    }

    fn func(&self, f: &crate::node_kinds::func::Func) -> hir::Func {
        hir::Func {
            id: f.id,
            name: f.name.clone(),
            effects: f.effects.clone(),
            generics: f.generics.clone(),
            captures: f.captures.clone(),
            where_clause: f.where_clause.clone(),
            params: self.params(&f.params),
            body: self.block(&f.body),
            ret: f.ret.clone(),
            attributes: f.attributes.clone(),
        }
    }

    fn body(&self, b: &crate::node_kinds::body::Body) -> hir::Body {
        hir::Body {
            id: b.id,
            decls: b.decls.iter().map(|d| self.decl(d)).collect(),
            span: b.span,
        }
    }

    fn decl(&self, d: &decl::Decl) -> hir::Decl {
        hir::Decl {
            id: d.id,
            kind: self.decl_kind(&d.kind),
            span: d.span,
            visibility: d.visibility,
        }
    }

    fn decl_kind(&self, k: &decl::DeclKind) -> hir::DeclKind {
        match k {
            decl::DeclKind::Import(import) => hir::DeclKind::Import(import.clone()),
            decl::DeclKind::Effect {
                name,
                generics,
                where_clause,
                params,
                ret,
                ..
            } => hir::DeclKind::Effect {
                name: name.clone(),
                generics: generics.clone(),
                where_clause: where_clause.clone(),
                params: self.params(params),
                ret: ret.clone(),
            },
            decl::DeclKind::Struct {
                name,
                generics,
                where_clause,
                body,
                ..
            } => hir::DeclKind::Struct {
                name: name.clone(),
                generics: generics.clone(),
                where_clause: where_clause.clone(),
                body: self.body(body),
            },
            decl::DeclKind::Let {
                lhs,
                type_annotation,
                rhs,
            } => hir::DeclKind::Let {
                lhs: self.pattern(lhs),
                type_annotation: type_annotation.clone(),
                rhs: rhs.as_ref().map(|e| self.expr(e)),
            },
            decl::DeclKind::Protocol {
                name,
                generics,
                where_clause,
                body,
                conformances,
                ..
            } => hir::DeclKind::Protocol {
                name: name.clone(),
                generics: generics.clone(),
                where_clause: where_clause.clone(),
                body: self.body(body),
                conformances: conformances.clone(),
            },
            decl::DeclKind::Init { name, params, body } => hir::DeclKind::Init {
                name: name.clone(),
                params: self.params(params),
                body: self.block(body),
            },
            decl::DeclKind::Property {
                name,
                is_static,
                type_annotation,
                default_value,
                ..
            } => hir::DeclKind::Property {
                name: name.clone(),
                is_static: *is_static,
                type_annotation: type_annotation.clone(),
                default_value: default_value.as_ref().map(|e| self.expr(e)),
            },
            decl::DeclKind::Method {
                func,
                is_static,
                receiver_mode,
            } => hir::DeclKind::Method {
                func: Box::new(self.func(func)),
                is_static: *is_static,
                receiver_mode: *receiver_mode,
            },
            decl::DeclKind::Associated {
                generic,
                where_clause,
            } => hir::DeclKind::Associated {
                generic: generic.clone(),
                where_clause: where_clause.clone(),
            },
            decl::DeclKind::Func(func) => hir::DeclKind::Func(self.func(func)),
            decl::DeclKind::Extend {
                name,
                conformances,
                generics,
                where_clause,
                body,
                ..
            } => hir::DeclKind::Extend {
                name: name.clone(),
                conformances: conformances.clone(),
                generics: generics.clone(),
                where_clause: where_clause.clone(),
                body: self.body(body),
            },
            decl::DeclKind::Enum {
                name,
                generics,
                where_clause,
                body,
                ..
            } => hir::DeclKind::Enum {
                name: name.clone(),
                generics: generics.clone(),
                where_clause: where_clause.clone(),
                body: self.body(body),
            },
            decl::DeclKind::EnumVariant {
                name,
                generics,
                payloads,
                result,
                ..
            } => hir::DeclKind::EnumVariant {
                name: name.clone(),
                generics: generics.clone(),
                payloads: payloads.clone(),
                result: result.clone(),
            },
            decl::DeclKind::FuncSignature(sig) => hir::DeclKind::FuncSignature(sig.clone()),
            decl::DeclKind::MethodRequirement {
                signature,
                receiver_mode,
            } => hir::DeclKind::MethodRequirement {
                signature: signature.clone(),
                receiver_mode: *receiver_mode,
            },
            decl::DeclKind::TypeAlias(name, _span, ty) => {
                hir::DeclKind::TypeAlias(name.clone(), ty.clone())
            }
        }
    }
}
