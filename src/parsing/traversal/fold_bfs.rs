//! Breadth-first fold trait for AST traversal
//!
//! This module provides a BfsFold trait that traverses the AST in breadth-first
//! order, visiting all nodes at the current level before descending to children.

use std::collections::VecDeque;

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

/// A trait for breadth-first traversal of AST nodes
pub trait BfsFold: Sized {
    // Level processing hooks - called before/after processing each level
    fn begin_level(&mut self, _depth: usize) {}
    fn end_level(&mut self, _depth: usize) {}

    // Enter hooks - called when first encountering each node at current level
    fn enter_node(&mut self, _node: &Node, _depth: usize) {}
    fn enter_attribute(&mut self, _attr: &Attribute, _depth: usize) {}
    fn enter_decl(&mut self, _decl: &Decl, _depth: usize) {}
    fn enter_generic_decl(&mut self, _generic: &GenericDecl, _depth: usize) {}
    fn enter_parameter(&mut self, _param: &Parameter, _depth: usize) {}
    fn enter_stmt(&mut self, _stmt: &Stmt, _depth: usize) {}
    fn enter_expr(&mut self, _expr: &Expr, _depth: usize) {}
    fn enter_pattern(&mut self, _pattern: &Pattern, _depth: usize) {}
    fn enter_match_arm(&mut self, _arm: &MatchArm, _depth: usize) {}
    fn enter_block(&mut self, _block: &Block, _depth: usize) {}
    fn enter_type_annotation(&mut self, _ty: &TypeAnnotation, _depth: usize) {}
    fn enter_record_field(&mut self, _field: &RecordField, _depth: usize) {}
    fn enter_incomplete_expr(&mut self, _expr: &IncompleteExpr, _depth: usize) {}
    fn enter_call_arg(&mut self, _arg: &CallArg, _depth: usize) {}

    // Enter hooks for specific Decl variants
    fn enter_decl_import(&mut self, _s: &str, _depth: usize) {}
    fn enter_decl_struct(
        &mut self,
        _name: &crate::name::Name,
        _generics: &[GenericDecl],
        _conformances: &[TypeAnnotation],
        _body: &Block,
        _depth: usize,
    ) {
    }
    fn enter_decl_let(
        &mut self,
        _lhs: &Pattern,
        _type_annotation: &Option<TypeAnnotation>,
        _value: &Option<Expr>,
        _depth: usize,
    ) {
    }
    fn enter_decl_protocol(
        &mut self,
        _name: &crate::name::Name,
        _generics: &[GenericDecl],
        _body: &Block,
        _conformances: &[TypeAnnotation],
        _depth: usize,
    ) {
    }
    fn enter_decl_init(&mut self, _params: &[Parameter], _body: &Block, _depth: usize) {}
    fn enter_decl_property(
        &mut self,
        _name: &crate::name::Name,
        _is_static: bool,
        _type_annotation: &Option<TypeAnnotation>,
        _default_value: &Option<Expr>,
        _depth: usize,
    ) {
    }
    fn enter_decl_method(&mut self, _func: &Decl, _is_static: bool, _depth: usize) {}
    #[allow(clippy::too_many_arguments)]
    fn enter_decl_func(
        &mut self,
        _name: &crate::name::Name,
        _generics: &[GenericDecl],
        _params: &[Parameter],
        _body: &Block,
        _ret: &Option<TypeAnnotation>,
        _attributes: &[Attribute],
        _depth: usize,
    ) {
    }
    fn enter_decl_extend(
        &mut self,
        _name: &crate::name::Name,
        _conformances: &[TypeAnnotation],
        _generics: &[GenericDecl],
        _body: &Block,
        _depth: usize,
    ) {
    }
    fn enter_decl_enum(
        &mut self,
        _name: &crate::name::Name,
        _conformances: &[TypeAnnotation],
        _generics: &[GenericDecl],
        _body: &Block,
        _depth: usize,
    ) {
    }
    fn enter_decl_enum_variant(
        &mut self,
        _name: &crate::name::Name,
        _fields: &[TypeAnnotation],
        _depth: usize,
    ) {
    }
    fn enter_decl_func_signature(
        &mut self,
        _name: &crate::name::Name,
        _params: &[Parameter],
        _generics: &[GenericDecl],
        _ret: &TypeAnnotation,
        _depth: usize,
    ) {
    }

    // Enter hooks for specific Expr variants
    fn enter_expr_incomplete(&mut self, _expr: &Expr, _depth: usize) {}
    fn enter_expr_literal_array(&mut self, _expr: &Expr, _depth: usize) {}
    fn enter_expr_literal_int(&mut self, _expr: &Expr, _depth: usize) {}
    fn enter_expr_literal_float(&mut self, _expr: &Expr, _depth: usize) {}
    fn enter_expr_literal_true(&mut self, _expr: &Expr, _depth: usize) {}
    fn enter_expr_literal_false(&mut self, _expr: &Expr, _depth: usize) {}
    fn enter_expr_literal_string(&mut self, _expr: &Expr, _depth: usize) {}
    fn enter_expr_unary(&mut self, _expr: &Expr, _depth: usize) {}
    fn enter_expr_binary(&mut self, _expr: &Expr, _depth: usize) {}
    fn enter_expr_tuple(&mut self, _expr: &Expr, _depth: usize) {}
    fn enter_expr_block(&mut self, _expr: &Expr, _depth: usize) {}
    fn enter_expr_call(&mut self, _expr: &Expr, _depth: usize) {}
    fn enter_expr_member(&mut self, _expr: &Expr, _depth: usize) {}
    fn enter_expr_func(&mut self, _expr: &Expr, _depth: usize) {}
    fn enter_expr_variable(&mut self, _expr: &Expr, _depth: usize) {}
    fn enter_expr_if(&mut self, _expr: &Expr, _depth: usize) {}
    fn enter_expr_match(&mut self, _expr: &Expr, _depth: usize) {}
    fn enter_expr_pattern_variant(&mut self, _expr: &Expr, _depth: usize) {}
    fn enter_expr_record_literal(&mut self, _expr: &Expr, _depth: usize) {}
    fn enter_expr_row_variable(&mut self, _expr: &Expr, _depth: usize) {}
    fn enter_expr_spread(&mut self, _expr: &Expr, _depth: usize) {}

    // Exit hooks - called after all nodes at current level are processed (before moving to next level)
    fn exit_node(&mut self, _node: &Node, _depth: usize) {}
    fn exit_attribute(&mut self, _attr: &Attribute, _depth: usize) {}
    fn exit_decl(&mut self, _decl: &Decl, _depth: usize) {}
    fn exit_generic_decl(&mut self, _generic: &GenericDecl, _depth: usize) {}
    fn exit_parameter(&mut self, _param: &Parameter, _depth: usize) {}
    fn exit_stmt(&mut self, _stmt: &Stmt, _depth: usize) {}
    fn exit_expr(&mut self, _expr: &Expr, _depth: usize) {}
    fn exit_pattern(&mut self, _pattern: &Pattern, _depth: usize) {}
    fn exit_match_arm(&mut self, _arm: &MatchArm, _depth: usize) {}
    fn exit_block(&mut self, _block: &Block, _depth: usize) {}
    fn exit_type_annotation(&mut self, _ty: &TypeAnnotation, _depth: usize) {}
    fn exit_record_field(&mut self, _field: &RecordField, _depth: usize) {}
    fn exit_incomplete_expr(&mut self, _expr: &IncompleteExpr, _depth: usize) {}
    fn exit_call_arg(&mut self, _arg: &CallArg, _depth: usize) {}

    // Exit hooks for specific Decl variants
    fn exit_decl_import(&mut self, _s: &str, _depth: usize) {}
    fn exit_decl_struct(
        &mut self,
        _name: &crate::name::Name,
        _generics: &[GenericDecl],
        _conformances: &[TypeAnnotation],
        _body: &Block,
        _depth: usize,
    ) {
    }
    fn exit_decl_let(
        &mut self,
        _lhs: &Pattern,
        _type_annotation: &Option<TypeAnnotation>,
        _value: &Option<Expr>,
        _depth: usize,
    ) {
    }
    fn exit_decl_protocol(
        &mut self,
        _name: &crate::name::Name,
        _generics: &[GenericDecl],
        _body: &Block,
        _conformances: &[TypeAnnotation],
        _depth: usize,
    ) {
    }
    fn exit_decl_init(&mut self, _params: &[Parameter], _body: &Block, _depth: usize) {}
    fn exit_decl_property(
        &mut self,
        _name: &crate::name::Name,
        _is_static: bool,
        _type_annotation: &Option<TypeAnnotation>,
        _default_value: &Option<Expr>,
        _depth: usize,
    ) {
    }
    fn exit_decl_method(&mut self, _func: &Decl, _is_static: bool, _depth: usize) {}
    #[allow(clippy::too_many_arguments)]
    fn exit_decl_func(
        &mut self,
        _name: &crate::name::Name,
        _generics: &[GenericDecl],
        _params: &[Parameter],
        _body: &Block,
        _ret: &Option<TypeAnnotation>,
        _attributes: &[Attribute],
        _depth: usize,
    ) {
    }
    fn exit_decl_extend(
        &mut self,
        _name: &crate::name::Name,
        _conformances: &[TypeAnnotation],
        _generics: &[GenericDecl],
        _body: &Block,
        _depth: usize,
    ) {
    }
    fn exit_decl_enum(
        &mut self,
        _name: &crate::name::Name,
        _conformances: &[TypeAnnotation],
        _generics: &[GenericDecl],
        _body: &Block,
        _depth: usize,
    ) {
    }
    fn exit_decl_enum_variant(
        &mut self,
        _name: &crate::name::Name,
        _fields: &[TypeAnnotation],
        _depth: usize,
    ) {
    }
    fn exit_decl_func_signature(
        &mut self,
        _name: &crate::name::Name,
        _params: &[Parameter],
        _generics: &[GenericDecl],
        _ret: &TypeAnnotation,
        _depth: usize,
    ) {
    }

    // Exit hooks for specific Expr variants
    fn exit_expr_incomplete(&mut self, _expr: &Expr, _depth: usize) {}
    fn exit_expr_literal_array(&mut self, _expr: &Expr, _depth: usize) {}
    fn exit_expr_literal_int(&mut self, _expr: &Expr, _depth: usize) {}
    fn exit_expr_literal_float(&mut self, _expr: &Expr, _depth: usize) {}
    fn exit_expr_literal_true(&mut self, _expr: &Expr, _depth: usize) {}
    fn exit_expr_literal_false(&mut self, _expr: &Expr, _depth: usize) {}
    fn exit_expr_literal_string(&mut self, _expr: &Expr, _depth: usize) {}
    fn exit_expr_unary(&mut self, _expr: &Expr, _depth: usize) {}
    fn exit_expr_binary(&mut self, _expr: &Expr, _depth: usize) {}
    fn exit_expr_tuple(&mut self, _expr: &Expr, _depth: usize) {}
    fn exit_expr_block(&mut self, _expr: &Expr, _depth: usize) {}
    fn exit_expr_call(&mut self, _expr: &Expr, _depth: usize) {}
    fn exit_expr_member(&mut self, _expr: &Expr, _depth: usize) {}
    fn exit_expr_func(&mut self, _expr: &Expr, _depth: usize) {}
    fn exit_expr_variable(&mut self, _expr: &Expr, _depth: usize) {}
    fn exit_expr_if(&mut self, _expr: &Expr, _depth: usize) {}
    fn exit_expr_match(&mut self, _expr: &Expr, _depth: usize) {}
    fn exit_expr_pattern_variant(&mut self, _expr: &Expr, _depth: usize) {}
    fn exit_expr_record_literal(&mut self, _expr: &Expr, _depth: usize) {}
    fn exit_expr_row_variable(&mut self, _expr: &Expr, _depth: usize) {}
    fn exit_expr_spread(&mut self, _expr: &Expr, _depth: usize) {}

    // Main traversal method
    fn traverse(&mut self, root: Node) -> Node {
        self.traverse_bfs(root)
    }

    // Breadth-first traversal implementation
    fn traverse_bfs(&mut self, root: Node) -> Node {
        // Define a queue item type that can hold any AST node type
        bfs_traverse_impl(self, root.clone())
    }
}

#[derive(Clone)]
enum QueueItem {
    Node(Node),
    Attribute(Attribute),
    Decl(Decl),
    GenericDecl(GenericDecl),
    Parameter(Parameter),
    Stmt(Stmt),
    Expr(Expr),
    Pattern(Pattern),
    MatchArm(MatchArm),
    Block(Block),
    TypeAnnotation(TypeAnnotation),
    RecordField(RecordField),
    IncompleteExpr(IncompleteExpr),
    CallArg(CallArg),
}

// Implementation function that performs the actual BFS traversal
fn bfs_traverse_impl<F: BfsFold>(fold: &mut F, root: Node) -> Node {
    let mut current_level = VecDeque::new();
    let mut next_level = VecDeque::new();
    let mut exit_items = Vec::new(); // Store items for exit processing
    let mut depth = 0;

    // Start with the root node
    current_level.push_back(QueueItem::Node(root.clone()));

    while !current_level.is_empty() {
        fold.begin_level(depth);
        exit_items.clear();

        // Process all nodes at the current level - enter phase and collect children
        while let Some(item) = current_level.pop_front() {
            // Call enter hooks and collect for exit
            process_enter(&item, fold, depth);
            exit_items.push(item.clone());

            // Collect children for next level
            match &item {
                QueueItem::Node(n) => collect_node_children(n, &mut next_level),
                QueueItem::Attribute(_) => {} // No children
                QueueItem::Decl(d) => collect_decl_children(d, &mut next_level),
                QueueItem::GenericDecl(g) => collect_generic_decl_children(g, &mut next_level),
                QueueItem::Parameter(p) => collect_parameter_children(p, &mut next_level),
                QueueItem::Stmt(s) => collect_stmt_children(s, &mut next_level),
                QueueItem::Expr(e) => collect_expr_children(e, &mut next_level),
                QueueItem::Pattern(p) => collect_pattern_children(p, &mut next_level),
                QueueItem::MatchArm(m) => collect_match_arm_children(m, &mut next_level),
                QueueItem::Block(b) => collect_block_children(b, &mut next_level),
                QueueItem::TypeAnnotation(t) => {
                    collect_type_annotation_children(t, &mut next_level)
                }
                QueueItem::RecordField(r) => collect_record_field_children(r, &mut next_level),
                QueueItem::IncompleteExpr(i) => {
                    collect_incomplete_expr_children(i, &mut next_level)
                }
                QueueItem::CallArg(c) => collect_call_arg_children(c, &mut next_level),
            }
        }

        // Process exit hooks for all items at this level
        for item in &exit_items {
            process_exit(item, fold, depth);
        }

        fold.end_level(depth);

        // Move to the next level
        std::mem::swap(&mut current_level, &mut next_level);
        depth += 1;
    }

    // Return the original root (BFS doesn't transform)
    root
}

// Process enter hooks for an item
fn process_enter<F: BfsFold>(item: &QueueItem, fold: &mut F, depth: usize) {
    match item {
        QueueItem::Node(n) => {
            fold.enter_node(n, depth);
        }
        QueueItem::Attribute(a) => {
            fold.enter_attribute(a, depth);
        }
        QueueItem::Decl(d) => {
            fold.enter_decl(d, depth);
            // Call specific decl enter hooks
            match &d.kind {
                DeclKind::Import(s) => fold.enter_decl_import(s, depth),
                DeclKind::Struct {
                    name,
                    generics,
                    conformances,
                    body,
                } => fold.enter_decl_struct(name, generics, conformances, body, depth),
                DeclKind::Let {
                    lhs,
                    type_annotation,
                    value,
                } => fold.enter_decl_let(lhs, type_annotation, value, depth),
                DeclKind::Protocol {
                    name,
                    generics,
                    body,
                    conformances,
                } => fold.enter_decl_protocol(name, generics, body, conformances, depth),
                DeclKind::Init { params, body } => fold.enter_decl_init(params, body, depth),
                DeclKind::Property {
                    name,
                    is_static,
                    type_annotation,
                    default_value,
                } => fold.enter_decl_property(
                    name,
                    *is_static,
                    type_annotation,
                    default_value,
                    depth,
                ),
                DeclKind::Method { func, is_static } => {
                    fold.enter_decl_method(func, *is_static, depth)
                }
                DeclKind::Func {
                    name,
                    generics,
                    params,
                    body,
                    ret,
                    attributes,
                } => fold.enter_decl_func(name, generics, params, body, ret, attributes, depth),
                DeclKind::Extend {
                    name,
                    conformances,
                    generics,
                    body,
                } => fold.enter_decl_extend(name, conformances, generics, body, depth),
                DeclKind::Enum {
                    name,
                    conformances,
                    generics,
                    body,
                } => fold.enter_decl_enum(name, conformances, generics, body, depth),
                DeclKind::EnumVariant(name, fields) => {
                    fold.enter_decl_enum_variant(name, fields, depth)
                }
                DeclKind::FuncSignature {
                    name,
                    params,
                    generics,
                    ret,
                } => fold.enter_decl_func_signature(name, params, generics, ret, depth),
            }
        }
        QueueItem::GenericDecl(g) => {
            fold.enter_generic_decl(g, depth);
        }
        QueueItem::Parameter(p) => {
            fold.enter_parameter(p, depth);
        }
        QueueItem::Stmt(s) => {
            fold.enter_stmt(s, depth);
        }
        QueueItem::Expr(e) => {
            fold.enter_expr(e, depth);
            // Call specific expr enter hooks
            match &e.kind {
                ExprKind::Incomplete(_) => fold.enter_expr_incomplete(e, depth),
                ExprKind::LiteralArray(_) => fold.enter_expr_literal_array(e, depth),
                ExprKind::LiteralInt(_) => fold.enter_expr_literal_int(e, depth),
                ExprKind::LiteralFloat(_) => fold.enter_expr_literal_float(e, depth),
                ExprKind::LiteralTrue => fold.enter_expr_literal_true(e, depth),
                ExprKind::LiteralFalse => fold.enter_expr_literal_false(e, depth),
                ExprKind::LiteralString(_) => fold.enter_expr_literal_string(e, depth),
                ExprKind::Unary(_, _) => fold.enter_expr_unary(e, depth),
                ExprKind::Binary(_, _, _) => fold.enter_expr_binary(e, depth),
                ExprKind::Tuple(_) => fold.enter_expr_tuple(e, depth),
                ExprKind::Block(_) => fold.enter_expr_block(e, depth),
                ExprKind::Call { .. } => fold.enter_expr_call(e, depth),
                ExprKind::Member(_, _) => fold.enter_expr_member(e, depth),
                ExprKind::Func { .. } => fold.enter_expr_func(e, depth),
                ExprKind::Variable(_) => fold.enter_expr_variable(e, depth),
                ExprKind::If(_, _, _) => fold.enter_expr_if(e, depth),
                ExprKind::Match(_, _) => fold.enter_expr_match(e, depth),
                ExprKind::PatternVariant(_, _, _) => fold.enter_expr_pattern_variant(e, depth),
                ExprKind::RecordLiteral(_) => fold.enter_expr_record_literal(e, depth),
                ExprKind::RowVariable(_) => fold.enter_expr_row_variable(e, depth),
                ExprKind::Spread(_) => fold.enter_expr_spread(e, depth),
            }
        }
        QueueItem::Pattern(p) => {
            fold.enter_pattern(p, depth);
        }
        QueueItem::MatchArm(m) => {
            fold.enter_match_arm(m, depth);
        }
        QueueItem::Block(b) => {
            fold.enter_block(b, depth);
        }
        QueueItem::TypeAnnotation(t) => {
            fold.enter_type_annotation(t, depth);
        }
        QueueItem::RecordField(r) => {
            fold.enter_record_field(r, depth);
        }
        QueueItem::IncompleteExpr(i) => {
            fold.enter_incomplete_expr(i, depth);
        }
        QueueItem::CallArg(c) => {
            fold.enter_call_arg(c, depth);
        }
    }
}

// Process exit hooks for an item
fn process_exit<F: BfsFold>(item: &QueueItem, fold: &mut F, depth: usize) {
    match item {
        QueueItem::Node(n) => {
            fold.exit_node(n, depth);
        }
        QueueItem::Attribute(a) => {
            fold.exit_attribute(a, depth);
        }
        QueueItem::Decl(d) => {
            // Call specific decl exit hooks
            match &d.kind {
                DeclKind::Import(s) => fold.exit_decl_import(s, depth),
                DeclKind::Struct {
                    name,
                    generics,
                    conformances,
                    body,
                } => fold.exit_decl_struct(name, generics, conformances, body, depth),
                DeclKind::Let {
                    lhs,
                    type_annotation,
                    value,
                } => fold.exit_decl_let(lhs, type_annotation, value, depth),
                DeclKind::Protocol {
                    name,
                    generics,
                    body,
                    conformances,
                } => fold.exit_decl_protocol(name, generics, body, conformances, depth),
                DeclKind::Init { params, body } => fold.exit_decl_init(params, body, depth),
                DeclKind::Property {
                    name,
                    is_static,
                    type_annotation,
                    default_value,
                } => {
                    fold.exit_decl_property(name, *is_static, type_annotation, default_value, depth)
                }
                DeclKind::Method { func, is_static } => {
                    fold.exit_decl_method(func, *is_static, depth)
                }
                DeclKind::Func {
                    name,
                    generics,
                    params,
                    body,
                    ret,
                    attributes,
                } => fold.exit_decl_func(name, generics, params, body, ret, attributes, depth),
                DeclKind::Extend {
                    name,
                    conformances,
                    generics,
                    body,
                } => fold.exit_decl_extend(name, conformances, generics, body, depth),
                DeclKind::Enum {
                    name,
                    conformances,
                    generics,
                    body,
                } => fold.exit_decl_enum(name, conformances, generics, body, depth),
                DeclKind::EnumVariant(name, fields) => {
                    fold.exit_decl_enum_variant(name, fields, depth)
                }
                DeclKind::FuncSignature {
                    name,
                    params,
                    generics,
                    ret,
                } => fold.exit_decl_func_signature(name, params, generics, ret, depth),
            }
            fold.exit_decl(d, depth);
        }
        QueueItem::GenericDecl(g) => {
            fold.exit_generic_decl(g, depth);
        }
        QueueItem::Parameter(p) => {
            fold.exit_parameter(p, depth);
        }
        QueueItem::Stmt(s) => {
            fold.exit_stmt(s, depth);
        }
        QueueItem::Expr(e) => {
            // Call specific expr exit hooks
            match &e.kind {
                ExprKind::Incomplete(_) => fold.exit_expr_incomplete(e, depth),
                ExprKind::LiteralArray(_) => fold.exit_expr_literal_array(e, depth),
                ExprKind::LiteralInt(_) => fold.exit_expr_literal_int(e, depth),
                ExprKind::LiteralFloat(_) => fold.exit_expr_literal_float(e, depth),
                ExprKind::LiteralTrue => fold.exit_expr_literal_true(e, depth),
                ExprKind::LiteralFalse => fold.exit_expr_literal_false(e, depth),
                ExprKind::LiteralString(_) => fold.exit_expr_literal_string(e, depth),
                ExprKind::Unary(_, _) => fold.exit_expr_unary(e, depth),
                ExprKind::Binary(_, _, _) => fold.exit_expr_binary(e, depth),
                ExprKind::Tuple(_) => fold.exit_expr_tuple(e, depth),
                ExprKind::Block(_) => fold.exit_expr_block(e, depth),
                ExprKind::Call { .. } => fold.exit_expr_call(e, depth),
                ExprKind::Member(_, _) => fold.exit_expr_member(e, depth),
                ExprKind::Func { .. } => fold.exit_expr_func(e, depth),
                ExprKind::Variable(_) => fold.exit_expr_variable(e, depth),
                ExprKind::If(_, _, _) => fold.exit_expr_if(e, depth),
                ExprKind::Match(_, _) => fold.exit_expr_match(e, depth),
                ExprKind::PatternVariant(_, _, _) => fold.exit_expr_pattern_variant(e, depth),
                ExprKind::RecordLiteral(_) => fold.exit_expr_record_literal(e, depth),
                ExprKind::RowVariable(_) => fold.exit_expr_row_variable(e, depth),
                ExprKind::Spread(_) => fold.exit_expr_spread(e, depth),
            }
            fold.exit_expr(e, depth);
        }
        QueueItem::Pattern(p) => {
            fold.exit_pattern(p, depth);
        }
        QueueItem::MatchArm(m) => {
            fold.exit_match_arm(m, depth);
        }
        QueueItem::Block(b) => {
            fold.exit_block(b, depth);
        }
        QueueItem::TypeAnnotation(t) => {
            fold.exit_type_annotation(t, depth);
        }
        QueueItem::RecordField(r) => {
            fold.exit_record_field(r, depth);
        }
        QueueItem::IncompleteExpr(i) => {
            fold.exit_incomplete_expr(i, depth);
        }
        QueueItem::CallArg(c) => {
            fold.exit_call_arg(c, depth);
        }
    }
}

// Helper functions to collect children for each node type
fn collect_node_children(node: &Node, queue: &mut VecDeque<QueueItem>) {
    match node {
        Node::Attribute(attr) => queue.push_back(QueueItem::Attribute(attr.clone())),
        Node::Decl(decl) => queue.push_back(QueueItem::Decl(decl.clone())),
        Node::GenericDecl(generic) => queue.push_back(QueueItem::GenericDecl(generic.clone())),
        Node::Parameter(param) => queue.push_back(QueueItem::Parameter(param.clone())),
        Node::Stmt(stmt) => queue.push_back(QueueItem::Stmt(stmt.clone())),
        Node::Expr(expr) => queue.push_back(QueueItem::Expr(expr.clone())),
        Node::Pattern(pattern) => queue.push_back(QueueItem::Pattern(pattern.clone())),
        Node::MatchArm(arm) => queue.push_back(QueueItem::MatchArm(arm.clone())),
        Node::Block(block) => queue.push_back(QueueItem::Block(block.clone())),
        Node::TypeAnnotation(ty) => queue.push_back(QueueItem::TypeAnnotation(ty.clone())),
        Node::RecordField(field) => queue.push_back(QueueItem::RecordField(field.clone())),
        Node::IncompleteExpr(expr) => queue.push_back(QueueItem::IncompleteExpr(expr.clone())),
        Node::CallArg(arg) => queue.push_back(QueueItem::CallArg(arg.clone())),
    }
}

fn collect_decl_children(decl: &Decl, queue: &mut VecDeque<QueueItem>) {
    match &decl.kind {
        DeclKind::Import(_) => {}
        DeclKind::Struct {
            generics,
            conformances,
            body,
            ..
        } => {
            for g in generics {
                queue.push_back(QueueItem::GenericDecl(g.clone()));
            }
            for c in conformances {
                queue.push_back(QueueItem::TypeAnnotation(c.clone()));
            }
            queue.push_back(QueueItem::Block(body.clone()));
        }
        DeclKind::Let {
            lhs,
            type_annotation,
            value,
        } => {
            queue.push_back(QueueItem::Pattern(lhs.clone()));
            if let Some(t) = type_annotation {
                queue.push_back(QueueItem::TypeAnnotation(t.clone()));
            }
            if let Some(v) = value {
                queue.push_back(QueueItem::Expr(v.clone()));
            }
        }
        DeclKind::Protocol {
            generics,
            body,
            conformances,
            ..
        } => {
            for g in generics {
                queue.push_back(QueueItem::GenericDecl(g.clone()));
            }
            queue.push_back(QueueItem::Block(body.clone()));
            for c in conformances {
                queue.push_back(QueueItem::TypeAnnotation(c.clone()));
            }
        }
        DeclKind::Init { params, body } => {
            for p in params {
                queue.push_back(QueueItem::Parameter(p.clone()));
            }
            queue.push_back(QueueItem::Block(body.clone()));
        }
        DeclKind::Property {
            type_annotation,
            default_value,
            ..
        } => {
            if let Some(t) = type_annotation {
                queue.push_back(QueueItem::TypeAnnotation(t.clone()));
            }
            if let Some(d) = default_value {
                queue.push_back(QueueItem::Expr(d.clone()));
            }
        }
        DeclKind::Method { func, .. } => {
            queue.push_back(QueueItem::Decl(func.as_ref().clone()));
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
                queue.push_back(QueueItem::GenericDecl(g.clone()));
            }
            for p in params {
                queue.push_back(QueueItem::Parameter(p.clone()));
            }
            queue.push_back(QueueItem::Block(body.clone()));
            if let Some(r) = ret {
                queue.push_back(QueueItem::TypeAnnotation(r.clone()));
            }
            for a in attributes {
                queue.push_back(QueueItem::Attribute(a.clone()));
            }
        }
        DeclKind::Extend {
            conformances,
            generics,
            body,
            ..
        } => {
            for c in conformances {
                queue.push_back(QueueItem::TypeAnnotation(c.clone()));
            }
            for g in generics {
                queue.push_back(QueueItem::GenericDecl(g.clone()));
            }
            queue.push_back(QueueItem::Block(body.clone()));
        }
        DeclKind::Enum {
            conformances,
            generics,
            body,
            ..
        } => {
            for c in conformances {
                queue.push_back(QueueItem::TypeAnnotation(c.clone()));
            }
            for g in generics {
                queue.push_back(QueueItem::GenericDecl(g.clone()));
            }
            queue.push_back(QueueItem::Block(body.clone()));
        }
        DeclKind::EnumVariant(_, fields) => {
            for f in fields {
                queue.push_back(QueueItem::TypeAnnotation(f.clone()));
            }
        }
        DeclKind::FuncSignature {
            params,
            generics,
            ret,
            ..
        } => {
            for p in params {
                queue.push_back(QueueItem::Parameter(p.clone()));
            }
            for g in generics {
                queue.push_back(QueueItem::GenericDecl(g.clone()));
            }
            queue.push_back(QueueItem::TypeAnnotation(ret.as_ref().clone()));
        }
    }
}

fn collect_generic_decl_children(generic: &GenericDecl, queue: &mut VecDeque<QueueItem>) {
    for g in &generic.generics {
        queue.push_back(QueueItem::GenericDecl(g.clone()));
    }
    for c in &generic.conformances {
        queue.push_back(QueueItem::GenericDecl(c.clone()));
    }
}

fn collect_parameter_children(param: &Parameter, queue: &mut VecDeque<QueueItem>) {
    if let Some(t) = &param.type_annotation {
        queue.push_back(QueueItem::TypeAnnotation(t.clone()));
    }
}

fn collect_stmt_children(stmt: &Stmt, queue: &mut VecDeque<QueueItem>) {
    match &stmt.kind {
        StmtKind::Expr(expr) => queue.push_back(QueueItem::Expr(expr.clone())),
        StmtKind::If(cond, body) => {
            queue.push_back(QueueItem::Expr(cond.clone()));
            queue.push_back(QueueItem::Block(body.clone()));
        }
        StmtKind::Return(expr) => {
            if let Some(e) = expr {
                queue.push_back(QueueItem::Expr(e.clone()));
            }
        }
        StmtKind::Break => {}
        StmtKind::Assignment(lhs, rhs) => {
            queue.push_back(QueueItem::Expr(lhs.clone()));
            queue.push_back(QueueItem::Expr(rhs.clone()));
        }
        StmtKind::LetAssignment(lhs, rhs) => {
            queue.push_back(QueueItem::Pattern(lhs.clone()));
            queue.push_back(QueueItem::Expr(rhs.clone()));
        }
        StmtKind::Loop(cond, body) => {
            if let Some(c) = cond {
                queue.push_back(QueueItem::Expr(c.clone()));
            }
            queue.push_back(QueueItem::Block(body.clone()));
        }
    }
}

fn collect_expr_children(expr: &Expr, queue: &mut VecDeque<QueueItem>) {
    match &expr.kind {
        ExprKind::Incomplete(inc) => queue.push_back(QueueItem::IncompleteExpr(inc.clone())),
        ExprKind::LiteralArray(exprs) => {
            for e in exprs {
                queue.push_back(QueueItem::Expr(e.clone()));
            }
        }
        ExprKind::LiteralInt(_)
        | ExprKind::LiteralFloat(_)
        | ExprKind::LiteralString(_)
        | ExprKind::LiteralTrue
        | ExprKind::LiteralFalse => {}
        ExprKind::Unary(_, expr) => queue.push_back(QueueItem::Expr(expr.as_ref().clone())),
        ExprKind::Binary(lhs, _, rhs) => {
            queue.push_back(QueueItem::Expr(lhs.as_ref().clone()));
            queue.push_back(QueueItem::Expr(rhs.as_ref().clone()));
        }
        ExprKind::Tuple(exprs) => {
            for e in exprs {
                queue.push_back(QueueItem::Expr(e.clone()));
            }
        }
        ExprKind::Block(block) => queue.push_back(QueueItem::Block(block.clone())),
        ExprKind::Call {
            callee,
            type_args,
            args,
        } => {
            queue.push_back(QueueItem::Expr(callee.as_ref().clone()));
            for t in type_args {
                queue.push_back(QueueItem::TypeAnnotation(t.clone()));
            }
            for a in args {
                queue.push_back(QueueItem::CallArg(a.clone()));
            }
        }
        ExprKind::Member(expr, _) => {
            if let Some(e) = expr {
                queue.push_back(QueueItem::Expr(e.as_ref().clone()));
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
                queue.push_back(QueueItem::GenericDecl(g.clone()));
            }
            for p in params {
                queue.push_back(QueueItem::Parameter(p.clone()));
            }
            queue.push_back(QueueItem::Block(body.clone()));
            if let Some(r) = ret {
                queue.push_back(QueueItem::TypeAnnotation(r.clone()));
            }
            for a in attributes {
                queue.push_back(QueueItem::Attribute(a.clone()));
            }
        }
        ExprKind::Variable(_) | ExprKind::RowVariable(_) => {}
        ExprKind::If(cond, then_block, else_block) => {
            queue.push_back(QueueItem::Expr(cond.as_ref().clone()));
            queue.push_back(QueueItem::Block(then_block.clone()));
            queue.push_back(QueueItem::Block(else_block.clone()));
        }
        ExprKind::Match(scrutinee, arms) => {
            queue.push_back(QueueItem::Expr(scrutinee.as_ref().clone()));
            for a in arms {
                queue.push_back(QueueItem::MatchArm(a.clone()));
            }
        }
        ExprKind::PatternVariant(_, _, patterns) => {
            for p in patterns {
                queue.push_back(QueueItem::Pattern(p.clone()));
            }
        }
        ExprKind::RecordLiteral(fields) => {
            for f in fields {
                queue.push_back(QueueItem::RecordField(f.clone()));
            }
        }
        ExprKind::Spread(node) => queue.push_back(QueueItem::Node(node.as_ref().clone())),
    }
}

fn collect_pattern_children(pattern: &Pattern, queue: &mut VecDeque<QueueItem>) {
    match &pattern.kind {
        PatternKind::LiteralInt(_)
        | PatternKind::LiteralFloat(_)
        | PatternKind::LiteralTrue
        | PatternKind::LiteralFalse
        | PatternKind::Bind(_)
        | PatternKind::Wildcard => {}
        PatternKind::Variant { fields, .. } => {
            for f in fields {
                queue.push_back(QueueItem::Pattern(f.clone()));
            }
        }
        PatternKind::Struct { fields, .. } => {
            for f in fields {
                queue.push_back(QueueItem::Node(f.clone()));
            }
        }
    }
}

fn collect_match_arm_children(arm: &MatchArm, queue: &mut VecDeque<QueueItem>) {
    queue.push_back(QueueItem::Pattern(arm.pattern.clone()));
    queue.push_back(QueueItem::Block(arm.body.clone()));
}

fn collect_block_children(block: &Block, queue: &mut VecDeque<QueueItem>) {
    for n in &block.body {
        queue.push_back(QueueItem::Node(n.clone()));
    }
}

fn collect_type_annotation_children(ty: &TypeAnnotation, queue: &mut VecDeque<QueueItem>) {
    match &ty.kind {
        TypeAnnotationKind::Func { params, returns } => {
            for p in params {
                queue.push_back(QueueItem::TypeAnnotation(p.clone()));
            }
            queue.push_back(QueueItem::TypeAnnotation(returns.as_ref().clone()));
        }
        TypeAnnotationKind::Nominal { generics, .. } => {
            for g in generics {
                queue.push_back(QueueItem::TypeAnnotation(g.clone()));
            }
        }
        TypeAnnotationKind::Tuple(types) => {
            for t in types {
                queue.push_back(QueueItem::TypeAnnotation(t.clone()));
            }
        }
    }
}

fn collect_record_field_children(field: &RecordField, queue: &mut VecDeque<QueueItem>) {
    queue.push_back(QueueItem::Expr(field.value.clone()));
}

fn collect_incomplete_expr_children(expr: &IncompleteExpr, queue: &mut VecDeque<QueueItem>) {
    match expr {
        IncompleteExpr::Member(expr) => {
            if let Some(e) = expr {
                queue.push_back(QueueItem::Expr(e.as_ref().clone()));
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
                    queue.push_back(QueueItem::Node(p.clone()));
                }
            }
            if let Some(gs) = generics {
                for g in gs {
                    queue.push_back(QueueItem::Node(g.clone()));
                }
            }
            if let Some(r) = ret {
                queue.push_back(QueueItem::Node(r.as_ref().clone()));
            }
            if let Some(b) = body {
                queue.push_back(QueueItem::Node(b.as_ref().clone()));
            }
        }
    }
}

fn collect_call_arg_children(arg: &CallArg, queue: &mut VecDeque<QueueItem>) {
    queue.push_back(QueueItem::Expr(arg.value.clone()));
}
