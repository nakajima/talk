//! AST FoldMut trait for in-place mutations
//!
//! This module provides a FoldMut trait that allows traversal and mutation
//! of AST nodes in-place using mutable references.
//!
//! Key features:
//! - Enter/exit hooks for all node types with mutable access
//! - Specific handlers for each Decl variant with mutable access
//! - Specific handlers for each Expr variant with mutable access
//! - Pre-order and post-order traversal support with mutations

use tracing::instrument;

use crate::node::Node;
use crate::node_kinds::{
    attribute::Attribute,
    block::Block,
    call_arg::CallArg,
    decl::{Decl, DeclKind},
    expr::{Expr, ExprKind},
    generic_decl::GenericDecl,
    incomplete_expr::IncompleteExpr,
    match_arm::MatchArm,
    parameter::Parameter,
    pattern::{Pattern, PatternKind},
    record_field::RecordField,
    stmt::{Stmt, StmtKind},
    type_annotation::{TypeAnnotation, TypeAnnotationKind},
};

pub trait FoldMut: Sized {
    // Visit methods - these orchestrate the traversal
    #[instrument(skip(self))]
    fn fold_node_mut(&mut self, node: &mut Node) {
        self.enter_node_mut(node);
        walk_node_mut(self, node);
        self.exit_node_mut(node);
    }

    #[instrument(skip(self))]
    fn fold_attribute_mut(&mut self, attr: &mut Attribute) {
        self.enter_attribute_mut(attr);
        // Attribute has no child nodes to walk
        self.exit_attribute_mut(attr);
    }

    #[instrument(skip(self))]
    fn fold_decl_mut(&mut self, decl: &mut Decl) {
        self.enter_decl_mut(decl);
        walk_decl_mut(self, decl);
        self.exit_decl_mut(decl);
    }

    #[instrument(skip(self))]
    fn fold_generic_decl_mut(&mut self, generic: &mut GenericDecl) {
        self.enter_generic_decl_mut(generic);
        walk_generic_decl_mut(self, generic);
        self.exit_generic_decl_mut(generic);
    }

    #[instrument(skip(self))]
    fn fold_parameter_mut(&mut self, param: &mut Parameter) {
        self.enter_parameter_mut(param);
        walk_parameter_mut(self, param);
        self.exit_parameter_mut(param);
    }

    #[instrument(skip(self))]
    fn fold_stmt_mut(&mut self, stmt: &mut Stmt) {
        self.enter_stmt_mut(stmt);
        walk_stmt_mut(self, stmt);
        self.exit_stmt_mut(stmt);
    }

    #[instrument(skip(self))]
    fn fold_expr_mut(&mut self, expr: &mut Expr) {
        self.enter_expr_mut(expr);
        walk_expr_mut(self, expr);
        self.exit_expr_mut(expr);
    }

    #[instrument(skip(self))]
    fn fold_pattern_mut(&mut self, pattern: &mut Pattern) {
        self.enter_pattern_mut(pattern);
        walk_pattern_mut(self, pattern);
        self.exit_pattern_mut(pattern);
    }

    #[instrument(skip(self))]
    fn fold_match_arm_mut(&mut self, arm: &mut MatchArm) {
        self.enter_match_arm_mut(arm);
        walk_match_arm_mut(self, arm);
        self.exit_match_arm_mut(arm);
    }

    #[instrument(skip(self))]
    fn fold_block_mut(&mut self, block: &mut Block) {
        self.enter_block_mut(block);
        walk_block_mut(self, block);
        self.exit_block_mut(block);
    }

    #[instrument(skip(self))]
    fn fold_type_annotation_mut(&mut self, ty: &mut TypeAnnotation) {
        self.enter_type_annotation_mut(ty);
        walk_type_annotation_mut(self, ty);
        self.exit_type_annotation_mut(ty);
    }

    #[instrument(skip(self))]
    fn fold_record_field_mut(&mut self, field: &mut RecordField) {
        self.enter_record_field_mut(field);
        walk_record_field_mut(self, field);
        self.exit_record_field_mut(field);
    }

    #[instrument(skip(self))]
    fn fold_incomplete_expr_mut(&mut self, expr: &mut IncompleteExpr) {
        self.enter_incomplete_expr_mut(expr);
        walk_incomplete_expr_mut(self, expr);
        self.exit_incomplete_expr_mut(expr);
    }

    #[instrument(skip(self))]
    fn fold_call_arg_mut(&mut self, arg: &mut CallArg) {
        self.enter_call_arg_mut(arg);
        walk_call_arg_mut(self, arg);
        self.exit_call_arg_mut(arg);
    }

    // Enter methods - called before visiting children
    #[instrument(skip(self))]
    fn enter_node_mut(&mut self, _node: &mut Node) {}
    #[instrument(skip(self))]
    fn enter_attribute_mut(&mut self, _attr: &mut Attribute) {}
    #[instrument(skip(self))]
    fn enter_decl_mut(&mut self, _decl: &mut Decl) {}
    #[instrument(skip(self))]
    fn enter_generic_decl_mut(&mut self, _generic: &mut GenericDecl) {}
    #[instrument(skip(self))]
    fn enter_parameter_mut(&mut self, _param: &mut Parameter) {}
    #[instrument(skip(self))]
    fn enter_stmt_mut(&mut self, _stmt: &mut Stmt) {}
    #[instrument(skip(self))]
    fn enter_expr_mut(&mut self, _expr: &mut Expr) {}
    #[instrument(skip(self))]
    fn enter_pattern_mut(&mut self, _pattern: &mut Pattern) {}
    #[instrument(skip(self))]
    fn enter_match_arm_mut(&mut self, _arm: &mut MatchArm) {}
    #[instrument(skip(self))]
    fn enter_block_mut(&mut self, _block: &mut Block) {}
    #[instrument(skip(self))]
    fn enter_type_annotation_mut(&mut self, _ty: &mut TypeAnnotation) {}
    #[instrument(skip(self))]
    fn enter_record_field_mut(&mut self, _field: &mut RecordField) {}
    #[instrument(skip(self))]
    fn enter_incomplete_expr_mut(&mut self, _expr: &mut IncompleteExpr) {}
    #[instrument(skip(self))]
    fn enter_call_arg_mut(&mut self, _arg: &mut CallArg) {}

    // Enter methods for specific Decl variants
    #[instrument(skip(self))]
    fn enter_decl_import_mut(&mut self, _s: &mut String) {}
    #[instrument(skip(self))]
    fn enter_decl_struct_mut(&mut self, _decl: &mut Decl) {}
    #[instrument(skip(self))]
    fn enter_decl_let_mut(&mut self, _decl: &mut Decl) {}
    #[instrument(skip(self))]
    fn enter_decl_protocol_mut(&mut self, _decl: &mut Decl) {}
    #[instrument(skip(self))]
    fn enter_decl_init_mut(&mut self, _decl: &mut Decl) {}
    #[instrument(skip(self))]
    fn enter_decl_property_mut(&mut self, _decl: &mut Decl) {}
    #[instrument(skip(self))]
    fn enter_decl_method_mut(&mut self, _decl: &mut Decl) {}
    #[instrument(skip(self))]
    fn enter_decl_func_mut(&mut self, _decl: &mut Decl) {}
    #[instrument(skip(self))]
    fn enter_decl_extend_mut(&mut self, _decl: &mut Decl) {}
    #[instrument(skip(self))]
    fn enter_decl_enum_mut(&mut self, _decl: &mut Decl) {}
    #[instrument(skip(self))]
    fn enter_decl_enum_variant_mut(&mut self, _decl: &mut Decl) {}
    #[instrument(skip(self))]
    fn enter_decl_func_signature_mut(&mut self, _decl: &mut Decl) {}

    // Enter methods for specific Expr variants
    fn enter_expr_incomplete_mut(&mut self, _expr: &mut Expr) {}
    fn enter_expr_literal_array_mut(&mut self, _expr: &mut Expr) {}
    fn enter_expr_literal_int_mut(&mut self, _expr: &mut Expr) {}
    fn enter_expr_literal_float_mut(&mut self, _expr: &mut Expr) {}
    fn enter_expr_literal_true_mut(&mut self, _expr: &mut Expr) {}
    fn enter_expr_literal_false_mut(&mut self, _expr: &mut Expr) {}
    fn enter_expr_literal_string_mut(&mut self, _expr: &mut Expr) {}
    fn enter_expr_unary_mut(&mut self, _expr: &mut Expr) {}
    fn enter_expr_binary_mut(&mut self, _expr: &mut Expr) {}
    fn enter_expr_tuple_mut(&mut self, _expr: &mut Expr) {}
    fn enter_expr_block_mut(&mut self, _expr: &mut Expr) {}
    fn enter_expr_call_mut(&mut self, _expr: &mut Expr) {}
    fn enter_expr_member_mut(&mut self, _expr: &mut Expr) {}
    fn enter_expr_func_mut(&mut self, _expr: &mut Expr) {}
    fn enter_expr_variable_mut(&mut self, _expr: &mut Expr) {}
    fn enter_expr_if_mut(&mut self, _expr: &mut Expr) {}
    fn enter_expr_match_mut(&mut self, _expr: &mut Expr) {}
    fn enter_expr_pattern_variant_mut(&mut self, _expr: &mut Expr) {}
    fn enter_expr_record_literal_mut(&mut self, _expr: &mut Expr) {}
    fn enter_expr_row_variable_mut(&mut self, _expr: &mut Expr) {}
    fn enter_expr_spread_mut(&mut self, _expr: &mut Expr) {}

    // Exit methods - called after visiting children
    fn exit_node_mut(&mut self, _node: &mut Node) {}
    fn exit_attribute_mut(&mut self, _attr: &mut Attribute) {}
    fn exit_decl_mut(&mut self, _decl: &mut Decl) {}
    fn exit_generic_decl_mut(&mut self, _generic: &mut GenericDecl) {}
    fn exit_parameter_mut(&mut self, _param: &mut Parameter) {}
    fn exit_stmt_mut(&mut self, _stmt: &mut Stmt) {}
    fn exit_expr_mut(&mut self, _expr: &mut Expr) {}
    fn exit_pattern_mut(&mut self, _pattern: &mut Pattern) {}
    fn exit_match_arm_mut(&mut self, _arm: &mut MatchArm) {}
    fn exit_block_mut(&mut self, _block: &mut Block) {}
    fn exit_type_annotation_mut(&mut self, _ty: &mut TypeAnnotation) {}
    fn exit_record_field_mut(&mut self, _field: &mut RecordField) {}
    fn exit_incomplete_expr_mut(&mut self, _expr: &mut IncompleteExpr) {}
    fn exit_call_arg_mut(&mut self, _arg: &mut CallArg) {}

    // Exit methods for specific Decl variants
    fn exit_decl_import_mut(&mut self, _s: &mut String) {}
    fn exit_decl_struct_mut(&mut self, _decl: &mut Decl) {}
    fn exit_decl_let_mut(&mut self, _decl: &mut Decl) {}
    fn exit_decl_protocol_mut(&mut self, _decl: &mut Decl) {}
    fn exit_decl_init_mut(&mut self, _decl: &mut Decl) {}
    fn exit_decl_property_mut(&mut self, _decl: &mut Decl) {}
    fn exit_decl_method_mut(&mut self, _decl: &mut Decl) {}
    fn exit_decl_func_mut(&mut self, _decl: &mut Decl) {}
    fn exit_decl_extend_mut(&mut self, _decl: &mut Decl) {}
    fn exit_decl_enum_mut(&mut self, _decl: &mut Decl) {}
    fn exit_decl_enum_variant_mut(&mut self, _decl: &mut Decl) {}
    fn exit_decl_func_signature_mut(&mut self, _decl: &mut Decl) {}

    // Exit methods for specific Expr variants
    fn exit_expr_incomplete_mut(&mut self, _expr: &mut Expr) {}
    fn exit_expr_literal_array_mut(&mut self, _expr: &mut Expr) {}
    fn exit_expr_literal_int_mut(&mut self, _expr: &mut Expr) {}
    fn exit_expr_literal_float_mut(&mut self, _expr: &mut Expr) {}
    fn exit_expr_literal_true_mut(&mut self, _expr: &mut Expr) {}
    fn exit_expr_literal_false_mut(&mut self, _expr: &mut Expr) {}
    fn exit_expr_literal_string_mut(&mut self, _expr: &mut Expr) {}
    fn exit_expr_unary_mut(&mut self, _expr: &mut Expr) {}
    fn exit_expr_binary_mut(&mut self, _expr: &mut Expr) {}
    fn exit_expr_tuple_mut(&mut self, _expr: &mut Expr) {}
    fn exit_expr_block_mut(&mut self, _expr: &mut Expr) {}
    fn exit_expr_call_mut(&mut self, _expr: &mut Expr) {}
    fn exit_expr_member_mut(&mut self, _expr: &mut Expr) {}
    fn exit_expr_func_mut(&mut self, _expr: &mut Expr) {}
    fn exit_expr_variable_mut(&mut self, _expr: &mut Expr) {}
    fn exit_expr_if_mut(&mut self, _expr: &mut Expr) {}
    fn exit_expr_match_mut(&mut self, _expr: &mut Expr) {}
    fn exit_expr_pattern_variant_mut(&mut self, _expr: &mut Expr) {}
    fn exit_expr_record_literal_mut(&mut self, _expr: &mut Expr) {}
    fn exit_expr_row_variable_mut(&mut self, _expr: &mut Expr) {}
    fn exit_expr_spread_mut(&mut self, _expr: &mut Expr) {}
}

// Walk functions that traverse the AST
pub fn walk_node_mut<F: FoldMut>(fold: &mut F, node: &mut Node) {
    match node {
        Node::Attribute(attr) => fold.fold_attribute_mut(attr),
        Node::Decl(decl) => fold.fold_decl_mut(decl),
        Node::GenericDecl(generic) => fold.fold_generic_decl_mut(generic),
        Node::Parameter(param) => fold.fold_parameter_mut(param),
        Node::Stmt(stmt) => fold.fold_stmt_mut(stmt),
        Node::Expr(expr) => fold.fold_expr_mut(expr),
        Node::Pattern(pattern) => fold.fold_pattern_mut(pattern),
        Node::MatchArm(arm) => fold.fold_match_arm_mut(arm),
        Node::Block(block) => fold.fold_block_mut(block),
        Node::TypeAnnotation(ty) => fold.fold_type_annotation_mut(ty),
        Node::RecordField(field) => fold.fold_record_field_mut(field),
        Node::IncompleteExpr(expr) => fold.fold_incomplete_expr_mut(expr),
        Node::CallArg(arg) => fold.fold_call_arg_mut(arg),
    }
}

pub fn walk_decl_mut<F: FoldMut>(fold: &mut F, decl: &mut Decl) {
    // Call specific enter method based on variant
    match &mut decl.kind {
        DeclKind::Import(s) => fold.enter_decl_import_mut(s),
        _ => {
            // For all other variants, pass the whole decl
            match &decl.kind {
                DeclKind::Struct { .. } => fold.enter_decl_struct_mut(decl),
                DeclKind::Let { .. } => fold.enter_decl_let_mut(decl),
                DeclKind::Protocol { .. } => fold.enter_decl_protocol_mut(decl),
                DeclKind::Init { .. } => fold.enter_decl_init_mut(decl),
                DeclKind::Property { .. } => fold.enter_decl_property_mut(decl),
                DeclKind::Method { .. } => fold.enter_decl_method_mut(decl),
                DeclKind::Func { .. } => fold.enter_decl_func_mut(decl),
                DeclKind::Extend { .. } => fold.enter_decl_extend_mut(decl),
                DeclKind::Enum { .. } => fold.enter_decl_enum_mut(decl),
                DeclKind::EnumVariant(..) => fold.enter_decl_enum_variant_mut(decl),
                DeclKind::FuncSignature { .. } => fold.enter_decl_func_signature_mut(decl),
                _ => {}
            }
        }
    }

    // Walk children
    match &mut decl.kind {
        DeclKind::Import(_) => {}
        DeclKind::Struct {
            generics,
            conformances,
            body,
            ..
        } => {
            for g in generics {
                fold.fold_generic_decl_mut(g);
            }
            for c in conformances {
                fold.fold_type_annotation_mut(c);
            }
            fold.fold_block_mut(body);
        }
        DeclKind::Let {
            lhs,
            type_annotation,
            value,
        } => {
            fold.fold_pattern_mut(lhs);
            if let Some(t) = type_annotation {
                fold.fold_type_annotation_mut(t);
            }
            if let Some(v) = value {
                fold.fold_expr_mut(v);
            }
        }
        DeclKind::Protocol {
            generics,
            body,
            conformances,
            ..
        } => {
            for g in generics {
                fold.fold_generic_decl_mut(g);
            }
            fold.fold_block_mut(body);
            for c in conformances {
                fold.fold_type_annotation_mut(c);
            }
        }
        DeclKind::Init { params, body } => {
            for p in params {
                fold.fold_parameter_mut(p);
            }
            fold.fold_block_mut(body);
        }
        DeclKind::Property {
            type_annotation,
            default_value,
            ..
        } => {
            if let Some(t) = type_annotation {
                fold.fold_type_annotation_mut(t);
            }
            if let Some(d) = default_value {
                fold.fold_expr_mut(d);
            }
        }
        DeclKind::Method { func, .. } => {
            fold.fold_decl_mut(func);
        }
        DeclKind::Func {
            generics,
            params,
            body,
            ret,
            attributes,
            ..
        } => {
            for g in generics {
                fold.fold_generic_decl_mut(g);
            }
            for p in params {
                fold.fold_parameter_mut(p);
            }
            fold.fold_block_mut(body);
            if let Some(r) = ret {
                fold.fold_type_annotation_mut(r);
            }
            for a in attributes {
                fold.fold_attribute_mut(a);
            }
        }
        DeclKind::Extend {
            conformances,
            generics,
            body,
            ..
        } => {
            for c in conformances {
                fold.fold_type_annotation_mut(c);
            }
            for g in generics {
                fold.fold_generic_decl_mut(g);
            }
            fold.fold_block_mut(body);
        }
        DeclKind::Enum {
            conformances,
            generics,
            body,
            ..
        } => {
            for c in conformances {
                fold.fold_type_annotation_mut(c);
            }
            for g in generics {
                fold.fold_generic_decl_mut(g);
            }
            fold.fold_block_mut(body);
        }
        DeclKind::EnumVariant(_, fields) => {
            for f in fields {
                fold.fold_type_annotation_mut(f);
            }
        }
        DeclKind::FuncSignature {
            params,
            generics,
            ret,
            ..
        } => {
            for p in params {
                fold.fold_parameter_mut(p);
            }
            for g in generics {
                fold.fold_generic_decl_mut(g);
            }
            fold.fold_type_annotation_mut(ret);
        }
    }

    // Call specific exit method based on variant
    match &mut decl.kind {
        DeclKind::Import(s) => fold.exit_decl_import_mut(s),
        _ => match &decl.kind {
            DeclKind::Struct { .. } => fold.exit_decl_struct_mut(decl),
            DeclKind::Let { .. } => fold.exit_decl_let_mut(decl),
            DeclKind::Protocol { .. } => fold.exit_decl_protocol_mut(decl),
            DeclKind::Init { .. } => fold.exit_decl_init_mut(decl),
            DeclKind::Property { .. } => fold.exit_decl_property_mut(decl),
            DeclKind::Method { .. } => fold.exit_decl_method_mut(decl),
            DeclKind::Func { .. } => fold.exit_decl_func_mut(decl),
            DeclKind::Extend { .. } => fold.exit_decl_extend_mut(decl),
            DeclKind::Enum { .. } => fold.exit_decl_enum_mut(decl),
            DeclKind::EnumVariant(..) => fold.exit_decl_enum_variant_mut(decl),
            DeclKind::FuncSignature { .. } => fold.exit_decl_func_signature_mut(decl),
            _ => {}
        },
    }
}

pub fn walk_generic_decl_mut<F: FoldMut>(fold: &mut F, generic: &mut GenericDecl) {
    for g in &mut generic.generics {
        fold.fold_generic_decl_mut(g);
    }
    for c in &mut generic.conformances {
        fold.fold_generic_decl_mut(c);
    }
}

pub fn walk_parameter_mut<F: FoldMut>(fold: &mut F, param: &mut Parameter) {
    if let Some(t) = &mut param.type_annotation {
        fold.fold_type_annotation_mut(t);
    }
}

pub fn walk_stmt_mut<F: FoldMut>(fold: &mut F, stmt: &mut Stmt) {
    match &mut stmt.kind {
        StmtKind::Expr(expr) => fold.fold_expr_mut(expr),
        StmtKind::If(cond, body) => {
            fold.fold_expr_mut(cond);
            fold.fold_block_mut(body);
        }
        StmtKind::Return(expr) => {
            if let Some(e) = expr {
                fold.fold_expr_mut(e);
            }
        }
        StmtKind::Break => {}
        StmtKind::Assignment(lhs, rhs) => {
            fold.fold_expr_mut(lhs);
            fold.fold_expr_mut(rhs);
        }
        StmtKind::LetAssignment(lhs, rhs) => {
            fold.fold_pattern_mut(lhs);
            fold.fold_expr_mut(rhs);
        }
        StmtKind::Loop(cond, body) => {
            if let Some(c) = cond {
                fold.fold_expr_mut(c);
            }
            fold.fold_block_mut(body);
        }
    }
}

pub fn walk_expr_mut<F: FoldMut>(fold: &mut F, expr: &mut Expr) {
    // Call specific enter method based on variant
    match &expr.kind {
        ExprKind::Incomplete(_) => fold.enter_expr_incomplete_mut(expr),
        ExprKind::LiteralArray(_) => fold.enter_expr_literal_array_mut(expr),
        ExprKind::LiteralInt(_) => fold.enter_expr_literal_int_mut(expr),
        ExprKind::LiteralFloat(_) => fold.enter_expr_literal_float_mut(expr),
        ExprKind::LiteralTrue => fold.enter_expr_literal_true_mut(expr),
        ExprKind::LiteralFalse => fold.enter_expr_literal_false_mut(expr),
        ExprKind::LiteralString(_) => fold.enter_expr_literal_string_mut(expr),
        ExprKind::Unary(_, _) => fold.enter_expr_unary_mut(expr),
        ExprKind::Binary(_, _, _) => fold.enter_expr_binary_mut(expr),
        ExprKind::Tuple(_) => fold.enter_expr_tuple_mut(expr),
        ExprKind::Block(_) => fold.enter_expr_block_mut(expr),
        ExprKind::Call { .. } => fold.enter_expr_call_mut(expr),
        ExprKind::Member(_, _) => fold.enter_expr_member_mut(expr),
        ExprKind::Func { .. } => fold.enter_expr_func_mut(expr),
        ExprKind::Variable(_) => fold.enter_expr_variable_mut(expr),
        ExprKind::If(_, _, _) => fold.enter_expr_if_mut(expr),
        ExprKind::Match(_, _) => fold.enter_expr_match_mut(expr),
        ExprKind::PatternVariant(_, _, _) => fold.enter_expr_pattern_variant_mut(expr),
        ExprKind::RecordLiteral(_) => fold.enter_expr_record_literal_mut(expr),
        ExprKind::RowVariable(_) => fold.enter_expr_row_variable_mut(expr),
        ExprKind::Spread(_) => fold.enter_expr_spread_mut(expr),
    }

    // Walk children
    match &mut expr.kind {
        ExprKind::Incomplete(inc) => fold.fold_incomplete_expr_mut(inc),
        ExprKind::LiteralArray(exprs) => {
            for e in exprs {
                fold.fold_expr_mut(e);
            }
        }
        ExprKind::LiteralInt(_)
        | ExprKind::LiteralFloat(_)
        | ExprKind::LiteralString(_)
        | ExprKind::LiteralTrue
        | ExprKind::LiteralFalse => {}
        ExprKind::Unary(_, expr) => fold.fold_expr_mut(expr),
        ExprKind::Binary(lhs, _, rhs) => {
            fold.fold_expr_mut(lhs);
            fold.fold_expr_mut(rhs);
        }
        ExprKind::Tuple(exprs) => {
            for e in exprs {
                fold.fold_expr_mut(e);
            }
        }
        ExprKind::Block(block) => fold.fold_block_mut(block),
        ExprKind::Call {
            callee,
            type_args,
            args,
        } => {
            fold.fold_expr_mut(callee);
            for t in type_args {
                fold.fold_type_annotation_mut(t);
            }
            for a in args {
                fold.fold_call_arg_mut(a);
            }
        }
        ExprKind::Member(expr, _) => {
            if let Some(e) = expr {
                fold.fold_expr_mut(e);
            }
        }
        ExprKind::Func {
            generics,
            params,
            body,
            ret,
            attributes,
        } => {
            for g in generics {
                fold.fold_generic_decl_mut(g);
            }
            for p in params {
                fold.fold_parameter_mut(p);
            }
            fold.fold_block_mut(body);
            if let Some(r) = ret {
                fold.fold_type_annotation_mut(r);
            }
            for a in attributes {
                fold.fold_attribute_mut(a);
            }
        }
        ExprKind::Variable(_) | ExprKind::RowVariable(_) => {}
        ExprKind::If(cond, then_block, else_block) => {
            fold.fold_expr_mut(cond);
            fold.fold_block_mut(then_block);
            fold.fold_block_mut(else_block);
        }
        ExprKind::Match(scrutinee, arms) => {
            fold.fold_expr_mut(scrutinee);
            for a in arms {
                fold.fold_match_arm_mut(a);
            }
        }
        ExprKind::PatternVariant(_, _, patterns) => {
            for p in patterns {
                fold.fold_pattern_mut(p);
            }
        }
        ExprKind::RecordLiteral(fields) => {
            for f in fields {
                fold.fold_record_field_mut(f);
            }
        }
        ExprKind::Spread(node) => fold.fold_node_mut(node),
    }

    // Call specific exit method based on variant
    match &expr.kind {
        ExprKind::Incomplete(_) => fold.exit_expr_incomplete_mut(expr),
        ExprKind::LiteralArray(_) => fold.exit_expr_literal_array_mut(expr),
        ExprKind::LiteralInt(_) => fold.exit_expr_literal_int_mut(expr),
        ExprKind::LiteralFloat(_) => fold.exit_expr_literal_float_mut(expr),
        ExprKind::LiteralTrue => fold.exit_expr_literal_true_mut(expr),
        ExprKind::LiteralFalse => fold.exit_expr_literal_false_mut(expr),
        ExprKind::LiteralString(_) => fold.exit_expr_literal_string_mut(expr),
        ExprKind::Unary(_, _) => fold.exit_expr_unary_mut(expr),
        ExprKind::Binary(_, _, _) => fold.exit_expr_binary_mut(expr),
        ExprKind::Tuple(_) => fold.exit_expr_tuple_mut(expr),
        ExprKind::Block(_) => fold.exit_expr_block_mut(expr),
        ExprKind::Call { .. } => fold.exit_expr_call_mut(expr),
        ExprKind::Member(_, _) => fold.exit_expr_member_mut(expr),
        ExprKind::Func { .. } => fold.exit_expr_func_mut(expr),
        ExprKind::Variable(_) => fold.exit_expr_variable_mut(expr),
        ExprKind::If(_, _, _) => fold.exit_expr_if_mut(expr),
        ExprKind::Match(_, _) => fold.exit_expr_match_mut(expr),
        ExprKind::PatternVariant(_, _, _) => fold.exit_expr_pattern_variant_mut(expr),
        ExprKind::RecordLiteral(_) => fold.exit_expr_record_literal_mut(expr),
        ExprKind::RowVariable(_) => fold.exit_expr_row_variable_mut(expr),
        ExprKind::Spread(_) => fold.exit_expr_spread_mut(expr),
    }
}

pub fn walk_pattern_mut<F: FoldMut>(fold: &mut F, pattern: &mut Pattern) {
    match &mut pattern.kind {
        PatternKind::LiteralInt(_)
        | PatternKind::LiteralFloat(_)
        | PatternKind::LiteralTrue
        | PatternKind::LiteralFalse
        | PatternKind::Bind(_)
        | PatternKind::Wildcard => {}
        PatternKind::Variant { fields, .. } => {
            for f in fields {
                fold.fold_pattern_mut(f);
            }
        }
        PatternKind::Struct { fields, .. } => {
            for f in fields {
                fold.fold_node_mut(f);
            }
        }
    }
}

pub fn walk_match_arm_mut<F: FoldMut>(fold: &mut F, arm: &mut MatchArm) {
    fold.fold_pattern_mut(&mut arm.pattern);
    fold.fold_block_mut(&mut arm.body);
}

pub fn walk_block_mut<F: FoldMut>(fold: &mut F, block: &mut Block) {
    for n in &mut block.body {
        fold.fold_node_mut(n);
    }
}

pub fn walk_type_annotation_mut<F: FoldMut>(fold: &mut F, ty: &mut TypeAnnotation) {
    match &mut ty.kind {
        TypeAnnotationKind::Func { params, returns } => {
            for p in params {
                fold.fold_type_annotation_mut(p);
            }
            fold.fold_type_annotation_mut(returns);
        }
        TypeAnnotationKind::Nominal { generics, .. } => {
            for g in generics {
                fold.fold_type_annotation_mut(g);
            }
        }
        TypeAnnotationKind::Tuple(types) => {
            for t in types {
                fold.fold_type_annotation_mut(t);
            }
        }
    }
}

pub fn walk_record_field_mut<F: FoldMut>(fold: &mut F, field: &mut RecordField) {
    fold.fold_expr_mut(&mut field.value);
}

pub fn walk_incomplete_expr_mut<F: FoldMut>(fold: &mut F, expr: &mut IncompleteExpr) {
    match expr {
        IncompleteExpr::Member(expr) => {
            if let Some(e) = expr {
                fold.fold_expr_mut(e);
            }
        }
        IncompleteExpr::Func {
            params,
            generics,
            ret,
            body,
            ..
        } => {
            if let Some(ps) = params {
                for p in ps {
                    fold.fold_node_mut(p);
                }
            }
            if let Some(gs) = generics {
                for g in gs {
                    fold.fold_node_mut(g);
                }
            }
            if let Some(r) = ret {
                fold.fold_node_mut(r);
            }
            if let Some(b) = body {
                fold.fold_node_mut(b);
            }
        }
    }
}

pub fn walk_call_arg_mut<F: FoldMut>(fold: &mut F, arg: &mut CallArg) {
    fold.fold_expr_mut(&mut arg.value);
}
