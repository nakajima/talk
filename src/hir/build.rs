//! AST → HIR lowering. Consumes the name-resolved surface AST and produces the
//! owned HIR, preserving every `NodeID`. All real desugaring already happened in
//! `name_resolution/transforms/`, so the dropped surface forms
//! (`Unary`/`Binary`/`For`/`Incomplete`) must not appear here — they panic loudly
//! if they somehow do.
//!
//! Stage 1: clone-based (the AST is not consumed yet). Stage 6 switches to moving.

use crate::hir;
use crate::node::Node;
use crate::node_kinds::{decl, expr, pattern, stmt};

pub fn lower_roots(roots: &[Node]) -> Vec<hir::Node> {
    roots.iter().map(lower_node).collect()
}

fn lower_node(node: &Node) -> hir::Node {
    match node {
        Node::Decl(decl) => hir::Node::Decl(lower_decl(decl)),
        Node::Stmt(stmt) => hir::Node::Stmt(lower_stmt(stmt)),
        Node::Expr(expr) => hir::Node::Expr(lower_expr(expr)),
        other => panic!("unexpected node in HIR lowering position: {other:?}"),
    }
}

// ----- Expressions ---------------------------------------------------------

fn lower_expr(e: &expr::Expr) -> hir::Expr {
    hir::Expr {
        id: e.id,
        kind: lower_expr_kind(&e.kind),
        span: e.span,
    }
}

fn boxed(e: &expr::Expr) -> Box<hir::Expr> {
    Box::new(lower_expr(e))
}

fn lower_expr_kind(k: &expr::ExprKind) -> hir::ExprKind {
    use expr::ExprKind as A;
    match k {
        A::InlineIR(ir) => hir::ExprKind::InlineIR(hir::InlineIRInstruction {
            id: ir.id,
            span: ir.span,
            binds: ir.binds.iter().map(lower_expr).collect(),
            kind: ir.kind.clone(),
        }),
        A::As(inner, ty) => hir::ExprKind::As(boxed(inner), ty.clone()),
        A::CallEffect {
            effect_name,
            type_args,
            args,
            ..
        } => hir::ExprKind::CallEffect {
            effect_name: effect_name.clone(),
            type_args: type_args.clone(),
            args: args.iter().map(lower_call_arg).collect(),
        },
        A::LiteralArray(items) => hir::ExprKind::LiteralArray(items.iter().map(lower_expr).collect()),
        A::LiteralInt(s) => hir::ExprKind::LiteralInt(s.clone()),
        A::LiteralFloat(s) => hir::ExprKind::LiteralFloat(s.clone()),
        A::LiteralTrue => hir::ExprKind::LiteralTrue,
        A::LiteralFalse => hir::ExprKind::LiteralFalse,
        A::LiteralString(s) => hir::ExprKind::LiteralString(s.clone()),
        A::Tuple(items) => hir::ExprKind::Tuple(items.iter().map(lower_expr).collect()),
        A::Block(block) => hir::ExprKind::Block(lower_block(block)),
        A::Call {
            callee,
            type_args,
            args,
            trailing_block,
        } => hir::ExprKind::Call {
            callee: boxed(callee),
            type_args: type_args.clone(),
            args: args.iter().map(lower_call_arg).collect(),
            trailing_block: trailing_block.as_ref().map(lower_block),
        },
        A::Member(recv, label, _span) => {
            hir::ExprKind::Member(recv.as_ref().map(|r| boxed(r)), label.clone())
        }
        A::Func(func) => hir::ExprKind::Func(lower_func(func)),
        A::Variable(name) => hir::ExprKind::Variable(name.clone()),
        A::Constructor(name) => hir::ExprKind::Constructor(name.clone()),
        A::If(cond, then, els) => {
            hir::ExprKind::If(boxed(cond), lower_block(then), lower_block(els))
        }
        A::Match(scrut, arms) => {
            hir::ExprKind::Match(boxed(scrut), arms.iter().map(lower_match_arm).collect())
        }
        A::RecordLiteral { fields, spread } => hir::ExprKind::RecordLiteral {
            fields: fields.iter().map(lower_record_field).collect(),
            spread: spread.as_ref().map(|s| boxed(s)),
        },
        A::RowVariable(name) => hir::ExprKind::RowVariable(name.clone()),
        A::Unary(..) | A::Binary(..) => {
            panic!("Unary/Binary should be desugared by LowerOperators before HIR")
        }
        A::Incomplete(_) => panic!("Incomplete expressions cannot be lowered to HIR"),
    }
}

fn lower_call_arg(a: &crate::node_kinds::call_arg::CallArg) -> hir::CallArg {
    hir::CallArg {
        id: a.id,
        label: a.label.clone(),
        value: lower_expr(&a.value),
    }
}

fn lower_record_field(f: &crate::node_kinds::record_field::RecordField) -> hir::RecordField {
    hir::RecordField {
        id: f.id,
        label: f.label.clone(),
        value: lower_expr(&f.value),
    }
}

fn lower_match_arm(arm: &crate::node_kinds::match_arm::MatchArm) -> hir::MatchArm {
    hir::MatchArm {
        id: arm.id,
        pattern: lower_pattern(&arm.pattern),
        body: lower_block(&arm.body),
    }
}

// ----- Patterns ------------------------------------------------------------

fn lower_pattern(p: &pattern::Pattern) -> hir::Pattern {
    hir::Pattern {
        id: p.id,
        kind: lower_pattern_kind(&p.kind),
        span: p.span,
    }
}

fn lower_pattern_kind(k: &pattern::PatternKind) -> hir::PatternKind {
    use pattern::PatternKind as A;
    match k {
        A::LiteralInt(s) => hir::PatternKind::LiteralInt(s.clone()),
        A::LiteralFloat(s) => hir::PatternKind::LiteralFloat(s.clone()),
        A::LiteralTrue => hir::PatternKind::LiteralTrue,
        A::LiteralFalse => hir::PatternKind::LiteralFalse,
        A::Bind(name) => hir::PatternKind::Bind(name.clone()),
        A::Tuple(ps) => hir::PatternKind::Tuple(ps.iter().map(lower_pattern).collect()),
        A::Or(ps) => hir::PatternKind::Or(ps.iter().map(lower_pattern).collect()),
        A::Wildcard => hir::PatternKind::Wildcard,
        A::Variant {
            enum_name,
            variant_name,
            fields,
            ..
        } => hir::PatternKind::Variant {
            enum_name: enum_name.clone(),
            variant_name: variant_name.clone(),
            fields: fields.iter().map(lower_pattern).collect(),
        },
        A::Record { fields } => hir::PatternKind::Record {
            fields: fields.iter().map(lower_record_field_pattern).collect(),
        },
        A::Struct {
            struct_name,
            fields,
            field_names,
            rest,
        } => hir::PatternKind::Struct {
            struct_name: struct_name.clone(),
            fields: fields
                .iter()
                .map(|n| match n {
                    Node::Pattern(p) => lower_pattern(p),
                    other => panic!("struct pattern field is not a pattern: {other:?}"),
                })
                .collect(),
            field_names: field_names.clone(),
            rest: *rest,
        },
    }
}

fn lower_record_field_pattern(
    f: &pattern::RecordFieldPattern,
) -> hir::RecordFieldPattern {
    use pattern::RecordFieldPatternKind as A;
    let kind = match &f.kind {
        A::Bind(name) => hir::RecordFieldPatternKind::Bind(name.clone()),
        A::Equals { name, value, .. } => hir::RecordFieldPatternKind::Equals {
            name: name.clone(),
            value: lower_pattern(value),
        },
        A::Rest => hir::RecordFieldPatternKind::Rest,
    };
    hir::RecordFieldPattern { id: f.id, kind }
}

// ----- Blocks and statements ----------------------------------------------

fn lower_block(b: &crate::node_kinds::block::Block) -> hir::Block {
    hir::Block {
        id: b.id,
        args: b.args.clone(),
        body: lower_roots(&b.body),
        span: b.span,
    }
}

fn lower_stmt(s: &stmt::Stmt) -> hir::Stmt {
    hir::Stmt {
        id: s.id,
        kind: lower_stmt_kind(&s.kind),
        span: s.span,
    }
}

fn lower_stmt_kind(k: &stmt::StmtKind) -> hir::StmtKind {
    use stmt::StmtKind as A;
    match k {
        A::Expr(e) => hir::StmtKind::Expr(lower_expr(e)),
        A::If(cond, then, els) => hir::StmtKind::If(
            lower_expr(cond),
            lower_block(then),
            els.as_ref().map(lower_block),
        ),
        A::Return(e) => hir::StmtKind::Return(e.as_ref().map(lower_expr)),
        A::Break => hir::StmtKind::Break,
        A::Assignment(lhs, rhs) => hir::StmtKind::Assignment(boxed(lhs), boxed(rhs)),
        A::Loop(cond, body) => {
            hir::StmtKind::Loop(cond.as_ref().map(lower_expr), lower_block(body))
        }
        A::Continue(e) => hir::StmtKind::Continue(e.as_ref().map(lower_expr)),
        A::Handling {
            effect_name, body, ..
        } => hir::StmtKind::Handling {
            effect_name: effect_name.clone(),
            body: lower_block(body),
        },
        A::For { .. } => panic!("For should be desugared by LowerForLoops before HIR"),
    }
}

// ----- Functions and declarations -----------------------------------------

fn lower_func(f: &crate::node_kinds::func::Func) -> hir::Func {
    hir::Func {
        id: f.id,
        name: f.name.clone(),
        effects: f.effects.clone(),
        generics: f.generics.clone(),
        captures: f.captures.clone(),
        where_clause: f.where_clause.clone(),
        params: f.params.clone(),
        body: lower_block(&f.body),
        ret: f.ret.clone(),
        attributes: f.attributes.clone(),
    }
}

fn lower_body(b: &crate::node_kinds::body::Body) -> hir::Body {
    hir::Body {
        id: b.id,
        decls: b.decls.iter().map(lower_decl).collect(),
        span: b.span,
    }
}

fn lower_decl(d: &decl::Decl) -> hir::Decl {
    hir::Decl {
        id: d.id,
        kind: lower_decl_kind(&d.kind),
        span: d.span,
        visibility: d.visibility,
    }
}

fn lower_decl_kind(k: &decl::DeclKind) -> hir::DeclKind {
    use decl::DeclKind as A;
    match k {
        A::Import(import) => hir::DeclKind::Import(import.clone()),
        A::Effect {
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
            params: params.clone(),
            ret: ret.clone(),
        },
        A::Struct {
            name,
            generics,
            where_clause,
            body,
            ..
        } => hir::DeclKind::Struct {
            name: name.clone(),
            generics: generics.clone(),
            where_clause: where_clause.clone(),
            body: lower_body(body),
        },
        A::Let {
            lhs,
            type_annotation,
            rhs,
        } => hir::DeclKind::Let {
            lhs: lower_pattern(lhs),
            type_annotation: type_annotation.clone(),
            rhs: rhs.as_ref().map(lower_expr),
        },
        A::Protocol {
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
            body: lower_body(body),
            conformances: conformances.clone(),
        },
        A::Init { name, params, body } => hir::DeclKind::Init {
            name: name.clone(),
            params: params.clone(),
            body: lower_block(body),
        },
        A::Property {
            name,
            is_static,
            type_annotation,
            default_value,
            ..
        } => hir::DeclKind::Property {
            name: name.clone(),
            is_static: *is_static,
            type_annotation: type_annotation.clone(),
            default_value: default_value.as_ref().map(lower_expr),
        },
        A::Method {
            func,
            is_static,
            receiver_mode,
        } => hir::DeclKind::Method {
            func: Box::new(lower_func(func)),
            is_static: *is_static,
            receiver_mode: *receiver_mode,
        },
        A::Associated {
            generic,
            where_clause,
        } => hir::DeclKind::Associated {
            generic: generic.clone(),
            where_clause: where_clause.clone(),
        },
        A::Func(func) => hir::DeclKind::Func(lower_func(func)),
        A::Extend {
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
            body: lower_body(body),
        },
        A::Enum {
            name,
            generics,
            where_clause,
            body,
            ..
        } => hir::DeclKind::Enum {
            name: name.clone(),
            generics: generics.clone(),
            where_clause: where_clause.clone(),
            body: lower_body(body),
        },
        A::EnumVariant {
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
        A::FuncSignature(sig) => hir::DeclKind::FuncSignature(sig.clone()),
        A::MethodRequirement {
            signature,
            receiver_mode,
        } => hir::DeclKind::MethodRequirement {
            signature: signature.clone(),
            receiver_mode: *receiver_mode,
        },
        A::TypeAlias(name, _span, ty) => hir::DeclKind::TypeAlias(name.clone(), ty.clone()),
    }
}
