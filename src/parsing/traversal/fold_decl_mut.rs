//! Specialized fold trait for mutable declaration-only traversal
//!
//! This module provides a DeclFoldMut trait that focuses exclusively on
//! traversing and mutating declaration nodes in-place, ignoring expressions
//! and other non-declaration parts of the AST.

use crate::node_kinds::{
    block::Block,
    decl::{Decl, DeclKind},
};

/// A trait for folding only declaration nodes with mutable access
pub trait DeclFoldMut: Sized {
    // Main fold method for declarations
    fn fold_decl_mut(&mut self, decl: &mut Decl) {
        self.enter_decl_mut(decl);
        walk_decl_mut(self, decl);
        self.exit_decl_mut(decl);
    }

    // Enter/exit hooks for declarations
    fn enter_decl_mut(&mut self, _decl: &mut Decl) {}
    fn exit_decl_mut(&mut self, _decl: &mut Decl) {}

    // Helper method to traverse only declarations in a block
    fn fold_decl_block_mut(&mut self, block: &mut Block) {
        use crate::node::Node;

        // Only process declaration nodes in the block body
        for node in &mut block.body {
            if let Node::Decl(decl) = node {
                self.fold_decl_mut(decl);
            }
            // Non-declarations are left unchanged
        }
    }

    // Enter methods for specific declaration variants
    fn enter_decl_import_mut(&mut self, _s: &mut String) {}
    fn enter_decl_struct_mut(&mut self, _decl: &mut Decl) {}
    fn enter_decl_let_mut(&mut self, _decl: &mut Decl) {}
    fn enter_decl_protocol_mut(&mut self, _decl: &mut Decl) {}
    fn enter_decl_init_mut(&mut self, _decl: &mut Decl) {}
    fn enter_decl_property_mut(&mut self, _decl: &mut Decl) {}
    fn enter_decl_method_mut(&mut self, _decl: &mut Decl) {}
    fn enter_decl_func_mut(&mut self, _decl: &mut Decl) {}
    fn enter_decl_extend_mut(&mut self, _decl: &mut Decl) {}
    fn enter_decl_enum_mut(&mut self, _decl: &mut Decl) {}
    fn enter_decl_enum_variant_mut(&mut self, _decl: &mut Decl) {}
    fn enter_decl_func_signature_mut(&mut self, _decl: &mut Decl) {}

    // Exit methods for specific declaration variants
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
}

// Walk function for mutable declarations
pub fn walk_decl_mut<F: DeclFoldMut>(fold: &mut F, decl: &mut Decl) {
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

    // Walk children (only other declarations in blocks)
    match &mut decl.kind {
        DeclKind::Import(_) => {}
        DeclKind::Struct { body, .. } => {
            fold.fold_decl_block_mut(body);
        }
        DeclKind::Let { .. } => {
            // Don't traverse expressions
        }
        DeclKind::Protocol { body, .. } => {
            fold.fold_decl_block_mut(body);
        }
        DeclKind::Init { body, .. } => {
            fold.fold_decl_block_mut(body);
        }
        DeclKind::Property { .. } => {
            // Don't traverse expressions
        }
        DeclKind::Method { func, .. } => {
            fold.fold_decl_mut(func);
        }
        DeclKind::Func { body, .. } => {
            fold.fold_decl_block_mut(body);
        }
        DeclKind::Extend { body, .. } => {
            fold.fold_decl_block_mut(body);
        }
        DeclKind::Enum { body, .. } => {
            fold.fold_decl_block_mut(body);
        }
        DeclKind::EnumVariant(..) => {}
        DeclKind::FuncSignature { .. } => {}
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
