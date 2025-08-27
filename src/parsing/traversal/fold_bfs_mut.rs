//! Mutable breadth-first fold trait for AST traversal
//!
//! This module provides a BfsFoldMut trait that traverses the AST in breadth-first
//! order with mutable access, visiting all nodes at the current level before descending to children.

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
    pattern::Pattern,
    record_field::RecordField,
    stmt::{Stmt, StmtKind},
    type_annotation::TypeAnnotation,
};

/// A trait for mutable breadth-first traversal of AST nodes
pub trait BfsFoldMut: Sized {
    // Level processing hooks - called before/after processing each level
    fn begin_level_mut(&mut self, _depth: usize) {}
    fn end_level_mut(&mut self, _depth: usize) {}

    // Enter hooks - called when first encountering each node at current level
    fn enter_node_mut(&mut self, _node: &mut Node, _depth: usize) {}
    fn enter_attribute_mut(&mut self, _attr: &mut Attribute, _depth: usize) {}
    fn enter_decl_mut(&mut self, _decl: &mut Decl, _depth: usize) {}
    fn enter_generic_decl_mut(&mut self, _generic: &mut GenericDecl, _depth: usize) {}
    fn enter_parameter_mut(&mut self, _param: &mut Parameter, _depth: usize) {}
    fn enter_stmt_mut(&mut self, _stmt: &mut Stmt, _depth: usize) {}
    fn enter_expr_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn enter_pattern_mut(&mut self, _pattern: &mut Pattern, _depth: usize) {}
    fn enter_match_arm_mut(&mut self, _arm: &mut MatchArm, _depth: usize) {}
    fn enter_block_mut(&mut self, _block: &mut Block, _depth: usize) {}
    fn enter_type_annotation_mut(&mut self, _ty: &mut TypeAnnotation, _depth: usize) {}
    fn enter_record_field_mut(&mut self, _field: &mut RecordField, _depth: usize) {}
    fn enter_incomplete_expr_mut(&mut self, _expr: &mut IncompleteExpr, _depth: usize) {}
    fn enter_call_arg_mut(&mut self, _arg: &mut CallArg, _depth: usize) {}

    // Enter hooks for specific Decl variants
    fn enter_decl_import_mut(&mut self, _s: &mut str, _depth: usize) {}
    fn enter_decl_struct_mut(
        &mut self,
        _name: &mut crate::name::Name,
        _generics: &mut [GenericDecl],
        _conformances: &mut [TypeAnnotation],
        _body: &mut Block,
        _depth: usize,
    ) {
    }
    fn enter_decl_let_mut(
        &mut self,
        _lhs: &mut Pattern,
        _type_annotation: &mut Option<TypeAnnotation>,
        _value: &mut Option<Expr>,
        _depth: usize,
    ) {
    }
    fn enter_decl_protocol_mut(
        &mut self,
        _name: &mut crate::name::Name,
        _generics: &mut [GenericDecl],
        _body: &mut Block,
        _conformances: &mut [TypeAnnotation],
        _depth: usize,
    ) {
    }
    fn enter_decl_init_mut(&mut self, _params: &mut [Parameter], _body: &mut Block, _depth: usize) {
    }
    fn enter_decl_property_mut(
        &mut self,
        _name: &mut crate::name::Name,
        _is_static: bool,
        _type_annotation: &mut Option<TypeAnnotation>,
        _default_value: &mut Option<Expr>,
        _depth: usize,
    ) {
    }
    fn enter_decl_method_mut(&mut self, _func: &mut Decl, _is_static: bool, _depth: usize) {}
    #[allow(clippy::too_many_arguments)]
    fn enter_decl_func_mut(
        &mut self,
        _name: &mut crate::name::Name,
        _generics: &mut [GenericDecl],
        _params: &mut [Parameter],
        _body: &mut Block,
        _ret: &mut Option<TypeAnnotation>,
        _attributes: &mut [Attribute],
        _depth: usize,
    ) {
    }
    fn enter_decl_extend_mut(
        &mut self,
        _name: &mut crate::name::Name,
        _conformances: &mut [TypeAnnotation],
        _generics: &mut [GenericDecl],
        _body: &mut Block,
        _depth: usize,
    ) {
    }
    fn enter_decl_enum_mut(
        &mut self,
        _name: &mut crate::name::Name,
        _conformances: &mut [TypeAnnotation],
        _generics: &mut [GenericDecl],
        _body: &mut Block,
        _depth: usize,
    ) {
    }
    fn enter_decl_enum_variant_mut(
        &mut self,
        _name: &mut crate::name::Name,
        _fields: &mut [TypeAnnotation],
        _depth: usize,
    ) {
    }
    fn enter_decl_func_signature_mut(
        &mut self,
        _name: &mut crate::name::Name,
        _params: &mut [Parameter],
        _generics: &mut [GenericDecl],
        _ret: &mut TypeAnnotation,
        _depth: usize,
    ) {
    }

    // Enter hooks for specific Expr variants
    fn enter_expr_incomplete_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn enter_expr_literal_array_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn enter_expr_literal_int_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn enter_expr_literal_float_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn enter_expr_literal_true_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn enter_expr_literal_false_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn enter_expr_literal_string_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn enter_expr_unary_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn enter_expr_binary_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn enter_expr_tuple_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn enter_expr_block_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn enter_expr_call_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn enter_expr_member_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn enter_expr_func_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn enter_expr_variable_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn enter_expr_if_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn enter_expr_match_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn enter_expr_pattern_variant_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn enter_expr_record_literal_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn enter_expr_row_variable_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn enter_expr_spread_mut(&mut self, _expr: &mut Expr, _depth: usize) {}

    // Exit hooks - called after all nodes at current level are processed
    fn exit_node_mut(&mut self, _node: &mut Node, _depth: usize) {}
    fn exit_attribute_mut(&mut self, _attr: &mut Attribute, _depth: usize) {}
    fn exit_decl_mut(&mut self, _decl: &mut Decl, _depth: usize) {}
    fn exit_generic_decl_mut(&mut self, _generic: &mut GenericDecl, _depth: usize) {}
    fn exit_parameter_mut(&mut self, _param: &mut Parameter, _depth: usize) {}
    fn exit_stmt_mut(&mut self, _stmt: &mut Stmt, _depth: usize) {}
    fn exit_expr_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn exit_pattern_mut(&mut self, _pattern: &mut Pattern, _depth: usize) {}
    fn exit_match_arm_mut(&mut self, _arm: &mut MatchArm, _depth: usize) {}
    fn exit_block_mut(&mut self, _block: &mut Block, _depth: usize) {}
    fn exit_type_annotation_mut(&mut self, _ty: &mut TypeAnnotation, _depth: usize) {}
    fn exit_record_field_mut(&mut self, _field: &mut RecordField, _depth: usize) {}
    fn exit_incomplete_expr_mut(&mut self, _expr: &mut IncompleteExpr, _depth: usize) {}
    fn exit_call_arg_mut(&mut self, _arg: &mut CallArg, _depth: usize) {}

    // Exit hooks for specific Decl variants
    fn exit_decl_import_mut(&mut self, _s: &mut str, _depth: usize) {}
    fn exit_decl_struct_mut(
        &mut self,
        _name: &mut crate::name::Name,
        _generics: &mut [GenericDecl],
        _conformances: &mut [TypeAnnotation],
        _body: &mut Block,
        _depth: usize,
    ) {
    }
    fn exit_decl_let_mut(
        &mut self,
        _lhs: &mut Pattern,
        _type_annotation: &mut Option<TypeAnnotation>,
        _value: &mut Option<Expr>,
        _depth: usize,
    ) {
    }
    fn exit_decl_protocol_mut(
        &mut self,
        _name: &mut crate::name::Name,
        _generics: &mut [GenericDecl],
        _body: &mut Block,
        _conformances: &mut [TypeAnnotation],
        _depth: usize,
    ) {
    }
    fn exit_decl_init_mut(&mut self, _params: &mut [Parameter], _body: &mut Block, _depth: usize) {}
    fn exit_decl_property_mut(
        &mut self,
        _name: &mut crate::name::Name,
        _is_static: bool,
        _type_annotation: &mut Option<TypeAnnotation>,
        _default_value: &mut Option<Expr>,
        _depth: usize,
    ) {
    }
    fn exit_decl_method_mut(&mut self, _func: &mut Decl, _is_static: bool, _depth: usize) {}
    #[allow(clippy::too_many_arguments)]
    fn exit_decl_func_mut(
        &mut self,
        _name: &mut crate::name::Name,
        _generics: &mut [GenericDecl],
        _params: &mut [Parameter],
        _body: &mut Block,
        _ret: &mut Option<TypeAnnotation>,
        _attributes: &mut [Attribute],
        _depth: usize,
    ) {
    }
    fn exit_decl_extend_mut(
        &mut self,
        _name: &mut crate::name::Name,
        _conformances: &mut [TypeAnnotation],
        _generics: &mut [GenericDecl],
        _body: &mut Block,
        _depth: usize,
    ) {
    }
    fn exit_decl_enum_mut(
        &mut self,
        _name: &mut crate::name::Name,
        _conformances: &mut [TypeAnnotation],
        _generics: &mut [GenericDecl],
        _body: &mut Block,
        _depth: usize,
    ) {
    }
    fn exit_decl_enum_variant_mut(
        &mut self,
        _name: &mut crate::name::Name,
        _fields: &mut [TypeAnnotation],
        _depth: usize,
    ) {
    }
    fn exit_decl_func_signature_mut(
        &mut self,
        _name: &mut crate::name::Name,
        _params: &mut [Parameter],
        _generics: &mut [GenericDecl],
        _ret: &mut TypeAnnotation,
        _depth: usize,
    ) {
    }

    // Exit hooks for specific Expr variants
    fn exit_expr_incomplete_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn exit_expr_literal_array_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn exit_expr_literal_int_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn exit_expr_literal_float_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn exit_expr_literal_true_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn exit_expr_literal_false_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn exit_expr_literal_string_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn exit_expr_unary_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn exit_expr_binary_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn exit_expr_tuple_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn exit_expr_block_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn exit_expr_call_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn exit_expr_member_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn exit_expr_func_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn exit_expr_variable_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn exit_expr_if_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn exit_expr_match_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn exit_expr_pattern_variant_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn exit_expr_record_literal_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn exit_expr_row_variable_mut(&mut self, _expr: &mut Expr, _depth: usize) {}
    fn exit_expr_spread_mut(&mut self, _expr: &mut Expr, _depth: usize) {}

    // Main traversal method
    fn traverse_mut(&mut self, root: &mut Node) {
        bfs_traverse_mut_impl(self, root);
    }
}

enum NodeRefMut<'a> {
    Node(&'a mut Node),
    Attribute(&'a mut Attribute),
    Decl(&'a mut Decl),
    GenericDecl(&'a mut GenericDecl),
    Parameter(&'a mut Parameter),
    Stmt(&'a mut Stmt),
    Expr(&'a mut Expr),
    Pattern(&'a mut Pattern),
    MatchArm(&'a mut MatchArm),
    Block(&'a mut Block),
    TypeAnnotation(&'a mut TypeAnnotation),
    RecordField(&'a mut RecordField),
    IncompleteExpr(&'a mut IncompleteExpr),
    CallArg(&'a mut CallArg),
}

// Implementation function that performs the actual mutable BFS traversal
fn bfs_traverse_mut_impl<F: BfsFoldMut>(fold: &mut F, root: &mut Node) {
    // We need to process the tree level by level
    // Since we can't hold multiple mutable references at once, we need to:
    // 1. Collect indices/paths to all nodes at current level
    // 2. Process them one by one
    // 3. Collect children for next level

    let mut current_level_paths: Vec<Vec<usize>> = vec![vec![]]; // Start with root path
    let mut depth = 0;

    while !current_level_paths.is_empty() {
        fold.begin_level_mut(depth);

        let mut next_level_paths = Vec::new();

        // Process each node at current level - enter phase
        let mut exit_paths = Vec::new();
        for path in current_level_paths {
            // Navigate to the node and process it with enter hooks
            let node_ref = navigate_to_node_mut(root, &path);
            process_node_mut_enter(fold, node_ref, depth, &mut next_level_paths, &path);
            exit_paths.push(path);
        }

        // Process exit hooks for all items at this level
        for path in exit_paths {
            let node_ref = navigate_to_node_mut(root, &path);
            process_node_mut_exit(fold, node_ref, depth);
        }

        fold.end_level_mut(depth);

        current_level_paths = next_level_paths;
        depth += 1;
    }
}

// Navigate to a specific node in the tree using a path
fn navigate_to_node_mut<'a>(root: &'a mut Node, path: &[usize]) -> NodeRefMut<'a> {
    if path.is_empty() {
        return NodeRefMut::Node(root);
    }

    let mut current = NodeRefMut::Node(root);

    for &index in path {
        current = get_child_at_index_mut(current, index);
    }

    current
}

// Process a node with enter hooks and collect paths to its children
fn process_node_mut_enter<F: BfsFoldMut>(
    fold: &mut F,
    node_ref: NodeRefMut,
    depth: usize,
    next_level_paths: &mut Vec<Vec<usize>>,
    current_path: &[usize],
) {
    // Call enter hooks
    match node_ref {
        NodeRefMut::Node(n) => {
            fold.enter_node_mut(n, depth);
            collect_node_child_paths(n, next_level_paths, current_path);
        }
        NodeRefMut::Attribute(a) => {
            fold.enter_attribute_mut(a, depth);
            // Attributes have no children
        }
        NodeRefMut::Decl(d) => {
            fold.enter_decl_mut(d, depth);
            // Call specific decl enter hooks
            match &mut d.kind {
                DeclKind::Import(s) => fold.enter_decl_import_mut(s, depth),
                DeclKind::Struct {
                    name,
                    generics,
                    conformances,
                    body,
                } => fold.enter_decl_struct_mut(name, generics, conformances, body, depth),
                DeclKind::Let {
                    lhs,
                    type_annotation,
                    value,
                } => fold.enter_decl_let_mut(lhs, type_annotation, value, depth),
                DeclKind::Protocol {
                    name,
                    generics,
                    body,
                    conformances,
                } => fold.enter_decl_protocol_mut(name, generics, body, conformances, depth),
                DeclKind::Init { params, body } => fold.enter_decl_init_mut(params, body, depth),
                DeclKind::Property {
                    name,
                    is_static,
                    type_annotation,
                    default_value,
                } => fold.enter_decl_property_mut(
                    name,
                    *is_static,
                    type_annotation,
                    default_value,
                    depth,
                ),
                DeclKind::Method { func, is_static } => {
                    fold.enter_decl_method_mut(func, *is_static, depth)
                }
                DeclKind::Func {
                    name,
                    generics,
                    params,
                    body,
                    ret,
                    attributes,
                } => fold.enter_decl_func_mut(name, generics, params, body, ret, attributes, depth),
                DeclKind::Extend {
                    name,
                    conformances,
                    generics,
                    body,
                } => fold.enter_decl_extend_mut(name, conformances, generics, body, depth),
                DeclKind::Enum {
                    name,
                    conformances,
                    generics,
                    body,
                } => fold.enter_decl_enum_mut(name, conformances, generics, body, depth),
                DeclKind::EnumVariant(name, fields) => {
                    fold.enter_decl_enum_variant_mut(name, fields, depth)
                }
                DeclKind::FuncSignature {
                    name,
                    params,
                    generics,
                    ret,
                } => fold.enter_decl_func_signature_mut(name, params, generics, ret, depth),
            }
            collect_decl_child_paths(d, next_level_paths, current_path);
        }
        NodeRefMut::GenericDecl(g) => {
            fold.enter_generic_decl_mut(g, depth);
            collect_generic_decl_child_paths(g, next_level_paths, current_path);
        }
        NodeRefMut::Parameter(p) => {
            fold.enter_parameter_mut(p, depth);
            collect_parameter_child_paths(p, next_level_paths, current_path);
        }
        NodeRefMut::Stmt(s) => {
            fold.enter_stmt_mut(s, depth);
            collect_stmt_child_paths(s, next_level_paths, current_path);
        }
        NodeRefMut::Expr(e) => {
            fold.enter_expr_mut(e, depth);
            // Call specific expr enter hooks
            match &mut e.kind {
                ExprKind::Incomplete(_) => fold.enter_expr_incomplete_mut(e, depth),
                ExprKind::LiteralArray(_) => fold.enter_expr_literal_array_mut(e, depth),
                ExprKind::LiteralInt(_) => fold.enter_expr_literal_int_mut(e, depth),
                ExprKind::LiteralFloat(_) => fold.enter_expr_literal_float_mut(e, depth),
                ExprKind::LiteralTrue => fold.enter_expr_literal_true_mut(e, depth),
                ExprKind::LiteralFalse => fold.enter_expr_literal_false_mut(e, depth),
                ExprKind::LiteralString(_) => fold.enter_expr_literal_string_mut(e, depth),
                ExprKind::Unary(_, _) => fold.enter_expr_unary_mut(e, depth),
                ExprKind::Binary(_, _, _) => fold.enter_expr_binary_mut(e, depth),
                ExprKind::Tuple(_) => fold.enter_expr_tuple_mut(e, depth),
                ExprKind::Block(_) => fold.enter_expr_block_mut(e, depth),
                ExprKind::Call { .. } => fold.enter_expr_call_mut(e, depth),
                ExprKind::Member(_, _) => fold.enter_expr_member_mut(e, depth),
                ExprKind::Func { .. } => fold.enter_expr_func_mut(e, depth),
                ExprKind::Variable(_) => fold.enter_expr_variable_mut(e, depth),
                ExprKind::If(_, _, _) => fold.enter_expr_if_mut(e, depth),
                ExprKind::Match(_, _) => fold.enter_expr_match_mut(e, depth),
                ExprKind::PatternVariant(_, _, _) => fold.enter_expr_pattern_variant_mut(e, depth),
                ExprKind::RecordLiteral(_) => fold.enter_expr_record_literal_mut(e, depth),
                ExprKind::RowVariable(_) => fold.enter_expr_row_variable_mut(e, depth),
                ExprKind::Spread(_) => fold.enter_expr_spread_mut(e, depth),
            }
            collect_expr_child_paths(e, next_level_paths, current_path);
        }
        NodeRefMut::Pattern(p) => {
            fold.enter_pattern_mut(p, depth);
            collect_pattern_child_paths(p, next_level_paths, current_path);
        }
        NodeRefMut::MatchArm(m) => {
            fold.enter_match_arm_mut(m, depth);
            collect_match_arm_child_paths(m, next_level_paths, current_path);
        }
        NodeRefMut::Block(b) => {
            fold.enter_block_mut(b, depth);
            collect_block_child_paths(b, next_level_paths, current_path);
        }
        NodeRefMut::TypeAnnotation(t) => {
            fold.enter_type_annotation_mut(t, depth);
            collect_type_annotation_child_paths(t, next_level_paths, current_path);
        }
        NodeRefMut::RecordField(r) => {
            fold.enter_record_field_mut(r, depth);
            collect_record_field_child_paths(r, next_level_paths, current_path);
        }
        NodeRefMut::IncompleteExpr(i) => {
            fold.enter_incomplete_expr_mut(i, depth);
            collect_incomplete_expr_child_paths(i, next_level_paths, current_path);
        }
        NodeRefMut::CallArg(c) => {
            fold.enter_call_arg_mut(c, depth);
            collect_call_arg_child_paths(c, next_level_paths, current_path);
        }
    }
}

// Process a node with exit hooks
fn process_node_mut_exit<F: BfsFoldMut>(fold: &mut F, node_ref: NodeRefMut, depth: usize) {
    // Call exit hooks
    match node_ref {
        NodeRefMut::Node(n) => {
            fold.exit_node_mut(n, depth);
        }
        NodeRefMut::Attribute(a) => {
            fold.exit_attribute_mut(a, depth);
        }
        NodeRefMut::Decl(d) => {
            // Call specific decl exit hooks
            match &mut d.kind {
                DeclKind::Import(s) => fold.exit_decl_import_mut(s, depth),
                DeclKind::Struct {
                    name,
                    generics,
                    conformances,
                    body,
                } => fold.exit_decl_struct_mut(name, generics, conformances, body, depth),
                DeclKind::Let {
                    lhs,
                    type_annotation,
                    value,
                } => fold.exit_decl_let_mut(lhs, type_annotation, value, depth),
                DeclKind::Protocol {
                    name,
                    generics,
                    body,
                    conformances,
                } => fold.exit_decl_protocol_mut(name, generics, body, conformances, depth),
                DeclKind::Init { params, body } => fold.exit_decl_init_mut(params, body, depth),
                DeclKind::Property {
                    name,
                    is_static,
                    type_annotation,
                    default_value,
                } => fold.exit_decl_property_mut(
                    name,
                    *is_static,
                    type_annotation,
                    default_value,
                    depth,
                ),
                DeclKind::Method { func, is_static } => {
                    fold.exit_decl_method_mut(func, *is_static, depth)
                }
                DeclKind::Func {
                    name,
                    generics,
                    params,
                    body,
                    ret,
                    attributes,
                } => fold.exit_decl_func_mut(name, generics, params, body, ret, attributes, depth),
                DeclKind::Extend {
                    name,
                    conformances,
                    generics,
                    body,
                } => fold.exit_decl_extend_mut(name, conformances, generics, body, depth),
                DeclKind::Enum {
                    name,
                    conformances,
                    generics,
                    body,
                } => fold.exit_decl_enum_mut(name, conformances, generics, body, depth),
                DeclKind::EnumVariant(name, fields) => {
                    fold.exit_decl_enum_variant_mut(name, fields, depth)
                }
                DeclKind::FuncSignature {
                    name,
                    params,
                    generics,
                    ret,
                } => fold.exit_decl_func_signature_mut(name, params, generics, ret, depth),
            }
            fold.exit_decl_mut(d, depth);
        }
        NodeRefMut::GenericDecl(g) => {
            fold.exit_generic_decl_mut(g, depth);
        }
        NodeRefMut::Parameter(p) => {
            fold.exit_parameter_mut(p, depth);
        }
        NodeRefMut::Stmt(s) => {
            fold.exit_stmt_mut(s, depth);
        }
        NodeRefMut::Expr(e) => {
            // Call specific expr exit hooks
            match &mut e.kind {
                ExprKind::Incomplete(_) => fold.exit_expr_incomplete_mut(e, depth),
                ExprKind::LiteralArray(_) => fold.exit_expr_literal_array_mut(e, depth),
                ExprKind::LiteralInt(_) => fold.exit_expr_literal_int_mut(e, depth),
                ExprKind::LiteralFloat(_) => fold.exit_expr_literal_float_mut(e, depth),
                ExprKind::LiteralTrue => fold.exit_expr_literal_true_mut(e, depth),
                ExprKind::LiteralFalse => fold.exit_expr_literal_false_mut(e, depth),
                ExprKind::LiteralString(_) => fold.exit_expr_literal_string_mut(e, depth),
                ExprKind::Unary(_, _) => fold.exit_expr_unary_mut(e, depth),
                ExprKind::Binary(_, _, _) => fold.exit_expr_binary_mut(e, depth),
                ExprKind::Tuple(_) => fold.exit_expr_tuple_mut(e, depth),
                ExprKind::Block(_) => fold.exit_expr_block_mut(e, depth),
                ExprKind::Call { .. } => fold.exit_expr_call_mut(e, depth),
                ExprKind::Member(_, _) => fold.exit_expr_member_mut(e, depth),
                ExprKind::Func { .. } => fold.exit_expr_func_mut(e, depth),
                ExprKind::Variable(_) => fold.exit_expr_variable_mut(e, depth),
                ExprKind::If(_, _, _) => fold.exit_expr_if_mut(e, depth),
                ExprKind::Match(_, _) => fold.exit_expr_match_mut(e, depth),
                ExprKind::PatternVariant(_, _, _) => fold.exit_expr_pattern_variant_mut(e, depth),
                ExprKind::RecordLiteral(_) => fold.exit_expr_record_literal_mut(e, depth),
                ExprKind::RowVariable(_) => fold.exit_expr_row_variable_mut(e, depth),
                ExprKind::Spread(_) => fold.exit_expr_spread_mut(e, depth),
            }
            fold.exit_expr_mut(e, depth);
        }
        NodeRefMut::Pattern(p) => {
            fold.exit_pattern_mut(p, depth);
        }
        NodeRefMut::MatchArm(m) => {
            fold.exit_match_arm_mut(m, depth);
        }
        NodeRefMut::Block(b) => {
            fold.exit_block_mut(b, depth);
        }
        NodeRefMut::TypeAnnotation(t) => {
            fold.exit_type_annotation_mut(t, depth);
        }
        NodeRefMut::RecordField(r) => {
            fold.exit_record_field_mut(r, depth);
        }
        NodeRefMut::IncompleteExpr(i) => {
            fold.exit_incomplete_expr_mut(i, depth);
        }
        NodeRefMut::CallArg(c) => {
            fold.exit_call_arg_mut(c, depth);
        }
    }
}

// Helper to get a child at a specific index
fn get_child_at_index_mut(parent: NodeRefMut, index: usize) -> NodeRefMut {
    match parent {
        NodeRefMut::Node(n) => match n {
            Node::Attribute(attr) => NodeRefMut::Attribute(attr),
            Node::Decl(decl) => NodeRefMut::Decl(decl),
            Node::GenericDecl(generic) => NodeRefMut::GenericDecl(generic),
            Node::Parameter(param) => NodeRefMut::Parameter(param),
            Node::Stmt(stmt) => NodeRefMut::Stmt(stmt),
            Node::Expr(expr) => NodeRefMut::Expr(expr),
            Node::Pattern(pattern) => NodeRefMut::Pattern(pattern),
            Node::MatchArm(arm) => NodeRefMut::MatchArm(arm),
            Node::Block(block) => NodeRefMut::Block(block),
            Node::TypeAnnotation(ty) => NodeRefMut::TypeAnnotation(ty),
            Node::RecordField(field) => NodeRefMut::RecordField(field),
            Node::IncompleteExpr(expr) => NodeRefMut::IncompleteExpr(expr),
            Node::CallArg(arg) => NodeRefMut::CallArg(arg),
        },
        NodeRefMut::Block(b) => {
            if index < b.body.len() {
                match &mut b.body[index] {
                    Node::Attribute(attr) => NodeRefMut::Attribute(attr),
                    Node::Decl(decl) => NodeRefMut::Decl(decl),
                    Node::GenericDecl(generic) => NodeRefMut::GenericDecl(generic),
                    Node::Parameter(param) => NodeRefMut::Parameter(param),
                    Node::Stmt(stmt) => NodeRefMut::Stmt(stmt),
                    Node::Expr(expr) => NodeRefMut::Expr(expr),
                    Node::Pattern(pattern) => NodeRefMut::Pattern(pattern),
                    Node::MatchArm(arm) => NodeRefMut::MatchArm(arm),
                    Node::Block(block) => NodeRefMut::Block(block),
                    Node::TypeAnnotation(ty) => NodeRefMut::TypeAnnotation(ty),
                    Node::RecordField(field) => NodeRefMut::RecordField(field),
                    Node::IncompleteExpr(expr) => NodeRefMut::IncompleteExpr(expr),
                    Node::CallArg(arg) => NodeRefMut::CallArg(arg),
                }
            } else {
                panic!("Index out of bounds for block body");
            }
        }
        NodeRefMut::Decl(d) => match &mut d.kind {
            DeclKind::Func { body, .. } | DeclKind::Init { body, .. } => {
                if index == 0 {
                    NodeRefMut::Block(body)
                } else {
                    panic!("Index out of bounds for decl");
                }
            }
            DeclKind::Struct { body, .. }
            | DeclKind::Protocol { body, .. }
            | DeclKind::Extend { body, .. }
            | DeclKind::Enum { body, .. } => {
                if index == 0 {
                    NodeRefMut::Block(body)
                } else {
                    panic!("Index out of bounds for decl");
                }
            }
            DeclKind::Method { func, .. } => {
                if index == 0 {
                    NodeRefMut::Decl(func.as_mut())
                } else {
                    panic!("Index out of bounds for method");
                }
            }
            _ => panic!("Cannot get child at index for this decl kind"),
        },
        NodeRefMut::Expr(e) => match &mut e.kind {
            ExprKind::Block(block) => {
                if index == 0 {
                    NodeRefMut::Block(block)
                } else {
                    panic!("Index out of bounds for expr block");
                }
            }
            ExprKind::Binary(lhs, _, rhs) => match index {
                0 => NodeRefMut::Expr(lhs.as_mut()),
                1 => NodeRefMut::Expr(rhs.as_mut()),
                _ => panic!("Index out of bounds for binary expr"),
            },
            ExprKind::Unary(_, expr) => {
                if index == 0 {
                    NodeRefMut::Expr(expr.as_mut())
                } else {
                    panic!("Index out of bounds for unary expr");
                }
            }
            ExprKind::If(cond, then_block, else_block) => match index {
                0 => NodeRefMut::Expr(cond.as_mut()),
                1 => NodeRefMut::Block(then_block),
                2 => NodeRefMut::Block(else_block),
                _ => panic!("Index out of bounds for if expr"),
            },
            ExprKind::Call { callee, args, .. } => {
                if index == 0 {
                    NodeRefMut::Expr(callee.as_mut())
                } else if index > 0 && index <= args.len() {
                    NodeRefMut::CallArg(&mut args[index - 1])
                } else {
                    panic!("Index out of bounds for call expr");
                }
            }
            ExprKind::Func { body, .. } => {
                if index == 0 {
                    NodeRefMut::Block(body)
                } else {
                    panic!("Index out of bounds for func expr");
                }
            }
            ExprKind::LiteralArray(exprs) => {
                if index < exprs.len() {
                    NodeRefMut::Expr(&mut exprs[index])
                } else {
                    panic!("Index out of bounds for array literal");
                }
            }
            ExprKind::Tuple(exprs) => {
                if index < exprs.len() {
                    NodeRefMut::Expr(&mut exprs[index])
                } else {
                    panic!("Index out of bounds for tuple");
                }
            }
            ExprKind::Member(expr, _) => {
                if let Some(e) = expr {
                    if index == 0 {
                        NodeRefMut::Expr(e.as_mut())
                    } else {
                        panic!("Index out of bounds for member expr");
                    }
                } else {
                    panic!("No expression in member expr");
                }
            }
            ExprKind::Match(scrutinee, arms) => {
                if index == 0 {
                    NodeRefMut::Expr(scrutinee.as_mut())
                } else if index > 0 && index <= arms.len() {
                    NodeRefMut::MatchArm(&mut arms[index - 1])
                } else {
                    panic!("Index out of bounds for match expr");
                }
            }
            ExprKind::RecordLiteral(fields) => {
                if index < fields.len() {
                    NodeRefMut::RecordField(&mut fields[index])
                } else {
                    panic!("Index out of bounds for record literal");
                }
            }
            _ => panic!("Cannot get child at index for this expr kind"),
        },
        NodeRefMut::Stmt(s) => match &mut s.kind {
            StmtKind::Expr(expr) => {
                if index == 0 {
                    NodeRefMut::Expr(expr)
                } else {
                    panic!("Index out of bounds for stmt expr");
                }
            }
            StmtKind::If(cond, body) => match index {
                0 => NodeRefMut::Expr(cond),
                1 => NodeRefMut::Block(body),
                _ => panic!("Index out of bounds for if stmt"),
            },
            StmtKind::Assignment(lhs, rhs) => match index {
                0 => NodeRefMut::Expr(lhs),
                1 => NodeRefMut::Expr(rhs),
                _ => panic!("Index out of bounds for assignment stmt"),
            },
            StmtKind::Loop(cond, body) => {
                if let Some(c) = cond {
                    match index {
                        0 => NodeRefMut::Expr(c),
                        1 => NodeRefMut::Block(body),
                        _ => panic!("Index out of bounds for loop stmt"),
                    }
                } else if index == 0 {
                    NodeRefMut::Block(body)
                } else {
                    panic!("Index out of bounds for loop stmt");
                }
            }
            StmtKind::LetAssignment(pattern, expr) => match index {
                0 => NodeRefMut::Pattern(pattern),
                1 => NodeRefMut::Expr(expr),
                _ => panic!("Index out of bounds for let assignment stmt"),
            },
            StmtKind::Return(expr) => {
                if let Some(e) = expr {
                    if index == 0 {
                        NodeRefMut::Expr(e)
                    } else {
                        panic!("Index out of bounds for return stmt");
                    }
                } else {
                    panic!("No expression in return stmt");
                }
            }
            StmtKind::Break => panic!("Cannot get child at index for break stmt"),
        },
        NodeRefMut::MatchArm(arm) => match index {
            0 => NodeRefMut::Pattern(&mut arm.pattern),
            1 => NodeRefMut::Block(&mut arm.body),
            _ => panic!("Index out of bounds for match arm"),
        },
        NodeRefMut::CallArg(arg) => {
            if index == 0 {
                NodeRefMut::Expr(&mut arg.value)
            } else {
                panic!("Index out of bounds for call arg");
            }
        }
        NodeRefMut::RecordField(field) => {
            if index == 0 {
                NodeRefMut::Expr(&mut field.value)
            } else {
                panic!("Index out of bounds for record field");
            }
        }
        _ => panic!("Cannot get child at index for this node type"),
    }
}

// Helper functions to collect child paths for each node type
fn collect_node_child_paths(_node: &Node, paths: &mut Vec<Vec<usize>>, current_path: &[usize]) {
    // Node itself is already at depth, its content is the child
    let mut child_path = current_path.to_vec();
    child_path.push(0); // Single child index
    paths.push(child_path);
}

fn collect_decl_child_paths(decl: &Decl, paths: &mut Vec<Vec<usize>>, current_path: &[usize]) {
    match &decl.kind {
        DeclKind::Import(_) => {}
        DeclKind::Struct { .. } => {
            let mut child_path = current_path.to_vec();
            child_path.push(0); // Index for body
            paths.push(child_path);
        }
        DeclKind::Let { .. } => {
            // Don't traverse into expressions for now
        }
        DeclKind::Protocol { .. } => {
            let mut child_path = current_path.to_vec();
            child_path.push(0);
            paths.push(child_path);
        }
        DeclKind::Init { .. } => {
            let mut child_path = current_path.to_vec();
            child_path.push(0);
            paths.push(child_path);
        }
        DeclKind::Property { .. } => {}
        DeclKind::Method { .. } => {
            let mut child_path = current_path.to_vec();
            child_path.push(0);
            paths.push(child_path);
        }
        DeclKind::Func { .. } => {
            let mut child_path = current_path.to_vec();
            child_path.push(0);
            paths.push(child_path);
        }
        DeclKind::Extend { .. } => {
            let mut child_path = current_path.to_vec();
            child_path.push(0);
            paths.push(child_path);
        }
        DeclKind::Enum { .. } => {
            let mut child_path = current_path.to_vec();
            child_path.push(0);
            paths.push(child_path);
        }
        DeclKind::EnumVariant(..) => {}
        DeclKind::FuncSignature { .. } => {}
    }
}

#[allow(clippy::ptr_arg)]
fn collect_generic_decl_child_paths(
    _generic: &GenericDecl,
    _paths: &mut Vec<Vec<usize>>,
    _current_path: &[usize],
) {
    // Simplified for now
}

#[allow(clippy::ptr_arg)]
fn collect_parameter_child_paths(
    _param: &Parameter,
    _paths: &mut Vec<Vec<usize>>,
    _current_path: &[usize],
) {
    // Simplified for now
}

fn collect_stmt_child_paths(stmt: &Stmt, paths: &mut Vec<Vec<usize>>, current_path: &[usize]) {
    match &stmt.kind {
        StmtKind::Expr(_) => {
            let mut child_path = current_path.to_vec();
            child_path.push(0);
            paths.push(child_path);
        }
        StmtKind::If(_, _) => {
            // Condition at index 0
            let mut cond_path = current_path.to_vec();
            cond_path.push(0);
            paths.push(cond_path);

            // Body at index 1
            let mut body_path = current_path.to_vec();
            body_path.push(1);
            paths.push(body_path);
        }
        StmtKind::Assignment(_, _) => {
            // LHS at index 0
            let mut lhs_path = current_path.to_vec();
            lhs_path.push(0);
            paths.push(lhs_path);

            // RHS at index 1
            let mut rhs_path = current_path.to_vec();
            rhs_path.push(1);
            paths.push(rhs_path);
        }
        StmtKind::LetAssignment(_, _) => {
            // Pattern at index 0
            let mut lhs_path = current_path.to_vec();
            lhs_path.push(0);
            paths.push(lhs_path);

            // Value at index 1
            let mut rhs_path = current_path.to_vec();
            rhs_path.push(1);
            paths.push(rhs_path);
        }
        StmtKind::Loop(cond, _) => {
            if cond.is_some() {
                // Condition at index 0
                let mut cond_path = current_path.to_vec();
                cond_path.push(0);
                paths.push(cond_path);

                // Body at index 1
                let mut body_path = current_path.to_vec();
                body_path.push(1);
                paths.push(body_path);
            } else {
                // Body at index 0 (no condition)
                let mut body_path = current_path.to_vec();
                body_path.push(0);
                paths.push(body_path);
            }
        }
        StmtKind::Return(expr) => {
            if expr.is_some() {
                let mut child_path = current_path.to_vec();
                child_path.push(0);
                paths.push(child_path);
            }
        }
        StmtKind::Break => {}
    }
}

fn collect_expr_child_paths(expr: &Expr, paths: &mut Vec<Vec<usize>>, current_path: &[usize]) {
    match &expr.kind {
        ExprKind::Binary(_, _, _) => {
            // Left operand at index 0
            let mut left_path = current_path.to_vec();
            left_path.push(0);
            paths.push(left_path);

            // Right operand at index 1
            let mut right_path = current_path.to_vec();
            right_path.push(1);
            paths.push(right_path);
        }
        ExprKind::Unary(_, _) => {
            let mut child_path = current_path.to_vec();
            child_path.push(0);
            paths.push(child_path);
        }
        ExprKind::Block(_) => {
            let mut child_path = current_path.to_vec();
            child_path.push(0);
            paths.push(child_path);
        }
        ExprKind::If(_, _, _) => {
            // Condition at index 0
            let mut cond_path = current_path.to_vec();
            cond_path.push(0);
            paths.push(cond_path);

            // Then block at index 1
            let mut then_path = current_path.to_vec();
            then_path.push(1);
            paths.push(then_path);

            // Else block at index 2
            let mut else_path = current_path.to_vec();
            else_path.push(2);
            paths.push(else_path);
        }
        ExprKind::Call { args, .. } => {
            // Callee at index 0
            let mut callee_path = current_path.to_vec();
            callee_path.push(0);
            paths.push(callee_path);

            // Arguments at indices 1..
            for i in 0..args.len() {
                let mut arg_path = current_path.to_vec();
                arg_path.push(i + 1);
                paths.push(arg_path);
            }
        }
        ExprKind::Func { .. } => {
            // Body block at index 0
            let mut body_path = current_path.to_vec();
            body_path.push(0);
            paths.push(body_path);
        }
        ExprKind::LiteralArray(exprs) => {
            for i in 0..exprs.len() {
                let mut elem_path = current_path.to_vec();
                elem_path.push(i);
                paths.push(elem_path);
            }
        }
        ExprKind::Tuple(exprs) => {
            for i in 0..exprs.len() {
                let mut elem_path = current_path.to_vec();
                elem_path.push(i);
                paths.push(elem_path);
            }
        }
        ExprKind::Member(expr, _) => {
            if expr.is_some() {
                let mut child_path = current_path.to_vec();
                child_path.push(0);
                paths.push(child_path);
            }
        }
        ExprKind::Match(_, arms) => {
            // Scrutinee at index 0
            let mut scrut_path = current_path.to_vec();
            scrut_path.push(0);
            paths.push(scrut_path);

            // Arms at indices 1..
            for i in 0..arms.len() {
                let mut arm_path = current_path.to_vec();
                arm_path.push(i + 1);
                paths.push(arm_path);
            }
        }
        ExprKind::RecordLiteral(fields) => {
            for i in 0..fields.len() {
                let mut field_path = current_path.to_vec();
                field_path.push(i);
                paths.push(field_path);
            }
        }
        _ => {} // Other expression kinds have no children to traverse
    }
}

#[allow(clippy::ptr_arg)]
fn collect_pattern_child_paths(
    _pattern: &Pattern,
    _paths: &mut Vec<Vec<usize>>,
    _current_path: &[usize],
) {
    // Simplified for now
}

fn collect_match_arm_child_paths(
    _arm: &MatchArm,
    paths: &mut Vec<Vec<usize>>,
    current_path: &[usize],
) {
    // Pattern at index 0
    let mut pattern_path = current_path.to_vec();
    pattern_path.push(0);
    paths.push(pattern_path);

    // Body at index 1
    let mut body_path = current_path.to_vec();
    body_path.push(1);
    paths.push(body_path);
}

fn collect_block_child_paths(block: &Block, paths: &mut Vec<Vec<usize>>, current_path: &[usize]) {
    for i in 0..block.body.len() {
        let mut child_path = current_path.to_vec();
        child_path.push(i);
        paths.push(child_path);
    }
}

#[allow(clippy::ptr_arg)]
fn collect_type_annotation_child_paths(
    _ty: &TypeAnnotation,
    _paths: &mut Vec<Vec<usize>>,
    _current_path: &[usize],
) {
    // Simplified for now
}

fn collect_record_field_child_paths(
    _field: &RecordField,
    paths: &mut Vec<Vec<usize>>,
    current_path: &[usize],
) {
    // Value at index 0
    let mut value_path = current_path.to_vec();
    value_path.push(0);
    paths.push(value_path);
}

#[allow(clippy::ptr_arg)]
fn collect_incomplete_expr_child_paths(
    _expr: &IncompleteExpr,
    _paths: &mut Vec<Vec<usize>>,
    _current_path: &[usize],
) {
    // Incomplete expressions can have complex variations, simplified for now
}

fn collect_call_arg_child_paths(
    _arg: &CallArg,
    paths: &mut Vec<Vec<usize>>,
    current_path: &[usize],
) {
    // Value at index 0
    let mut value_path = current_path.to_vec();
    value_path.push(0);
    paths.push(value_path);
}
