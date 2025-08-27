//! Specialized fold trait for declaration-only traversal
//!
//! This module provides a DeclFold trait that focuses exclusively on
//! traversing and transforming declaration nodes, ignoring expressions
//! and other non-declaration parts of the AST.

use crate::name::Name;
use crate::node_kinds::{
    attribute::Attribute,
    block::Block,
    decl::{Decl, DeclKind},
    generic_decl::GenericDecl,
    parameter::Parameter,
    pattern::Pattern,
    type_annotation::TypeAnnotation,
};

/// A trait for folding only declaration nodes
pub trait DeclFold: Sized {
    // Main fold method for declarations
    fn fold_decl(&mut self, decl: Decl) -> Decl {
        self.enter_decl(&decl);
        let result = walk_decl(self, decl);
        self.exit_decl(&result);
        result
    }

    // Enter/exit hooks for declarations
    fn enter_decl(&mut self, _decl: &Decl) {}
    fn exit_decl(&mut self, _decl: &Decl) {}

    // Specific handlers for each declaration variant
    fn fold_decl_import(&mut self, s: String) -> DeclKind {
        self.enter_decl_import(&s);
        let result = DeclKind::Import(s.clone());
        self.exit_decl_import(&s);
        result
    }

    fn fold_decl_struct(
        &mut self,
        name: Name,
        generics: Vec<GenericDecl>,
        conformances: Vec<TypeAnnotation>,
        body: Block,
    ) -> DeclKind {
        self.enter_decl_struct(&name, &generics, &conformances, &body);

        // Only traverse nested declarations in the body
        let new_body = self.fold_decl_block(body);

        let result = DeclKind::Struct {
            name,
            generics,
            conformances,
            body: new_body,
        };

        if let DeclKind::Struct {
            name: ref n,
            generics: ref g,
            conformances: ref c,
            body: ref b,
        } = result
        {
            self.exit_decl_struct(n, g, c, b);
        }
        result
    }

    fn fold_decl_let(
        &mut self,
        lhs: Pattern,
        type_annotation: Option<TypeAnnotation>,
        value: Option<crate::node_kinds::expr::Expr>,
    ) -> DeclKind {
        self.enter_decl_let(&lhs, &type_annotation, &value);
        let result = DeclKind::Let {
            lhs,
            type_annotation,
            value, // Don't traverse expressions
        };
        if let DeclKind::Let {
            lhs: ref l,
            type_annotation: ref t,
            value: ref v,
        } = result
        {
            self.exit_decl_let(l, t, v);
        }
        result
    }

    fn fold_decl_protocol(
        &mut self,
        name: Name,
        generics: Vec<GenericDecl>,
        body: Block,
        conformances: Vec<TypeAnnotation>,
    ) -> DeclKind {
        self.enter_decl_protocol(&name, &generics, &body, &conformances);

        // Only traverse nested declarations in the body
        let new_body = self.fold_decl_block(body);

        let result = DeclKind::Protocol {
            name,
            generics,
            body: new_body,
            conformances,
        };

        if let DeclKind::Protocol {
            name: ref n,
            generics: ref g,
            body: ref b,
            conformances: ref c,
        } = result
        {
            self.exit_decl_protocol(n, g, b, c);
        }
        result
    }

    fn fold_decl_init(&mut self, params: Vec<Parameter>, body: Block) -> DeclKind {
        self.enter_decl_init(&params, &body);

        // Only traverse nested declarations in the body
        let new_body = self.fold_decl_block(body);

        let result = DeclKind::Init {
            params,
            body: new_body,
        };

        if let DeclKind::Init {
            params: ref p,
            body: ref b,
        } = result
        {
            self.exit_decl_init(p, b);
        }
        result
    }

    fn fold_decl_property(
        &mut self,
        name: Name,
        is_static: bool,
        type_annotation: Option<TypeAnnotation>,
        default_value: Option<crate::node_kinds::expr::Expr>,
    ) -> DeclKind {
        self.enter_decl_property(&name, is_static, &type_annotation, &default_value);
        let result = DeclKind::Property {
            name,
            is_static,
            type_annotation,
            default_value, // Don't traverse expressions
        };
        if let DeclKind::Property {
            name: ref n,
            is_static: s,
            type_annotation: ref t,
            default_value: ref d,
        } = result
        {
            self.exit_decl_property(n, s, t, d);
        }
        result
    }

    fn fold_decl_method(&mut self, func: Box<Decl>, is_static: bool) -> DeclKind {
        self.enter_decl_method(&func, is_static);
        let result = DeclKind::Method {
            func: Box::new(self.fold_decl(*func)),
            is_static,
        };
        if let DeclKind::Method {
            func: ref f,
            is_static: s,
        } = result
        {
            self.exit_decl_method(f, s);
        }
        result
    }

    fn fold_decl_func(
        &mut self,
        name: Name,
        generics: Vec<GenericDecl>,
        params: Vec<Parameter>,
        body: Block,
        ret: Option<TypeAnnotation>,
        attributes: Vec<Attribute>,
    ) -> DeclKind {
        self.enter_decl_func(&name, &generics, &params, &body, &ret, &attributes);

        // Only traverse nested declarations in the body
        let new_body = self.fold_decl_block(body);

        let result = DeclKind::Func {
            name,
            generics,
            params,
            body: new_body,
            ret,
            attributes,
        };

        if let DeclKind::Func {
            name: ref n,
            generics: ref g,
            params: ref p,
            body: ref b,
            ret: ref r,
            attributes: ref a,
        } = result
        {
            self.exit_decl_func(n, g, p, b, r, a);
        }
        result
    }

    fn fold_decl_extend(
        &mut self,
        name: Name,
        conformances: Vec<TypeAnnotation>,
        generics: Vec<GenericDecl>,
        body: Block,
    ) -> DeclKind {
        self.enter_decl_extend(&name, &conformances, &generics, &body);

        // Only traverse nested declarations in the body
        let new_body = self.fold_decl_block(body);

        let result = DeclKind::Extend {
            name,
            conformances,
            generics,
            body: new_body,
        };

        if let DeclKind::Extend {
            name: ref n,
            conformances: ref c,
            generics: ref g,
            body: ref b,
        } = result
        {
            self.exit_decl_extend(n, c, g, b);
        }
        result
    }

    fn fold_decl_enum(
        &mut self,
        name: Name,
        conformances: Vec<TypeAnnotation>,
        generics: Vec<GenericDecl>,
        body: Block,
    ) -> DeclKind {
        self.enter_decl_enum(&name, &conformances, &generics, &body);

        // Only traverse nested declarations in the body
        let new_body = self.fold_decl_block(body);

        let result = DeclKind::Enum {
            name,
            conformances,
            generics,
            body: new_body,
        };

        if let DeclKind::Enum {
            name: ref n,
            conformances: ref c,
            generics: ref g,
            body: ref b,
        } = result
        {
            self.exit_decl_enum(n, c, g, b);
        }
        result
    }

    fn fold_decl_enum_variant(&mut self, name: Name, fields: Vec<TypeAnnotation>) -> DeclKind {
        self.enter_decl_enum_variant(&name, &fields);
        let result = DeclKind::EnumVariant(name.clone(), fields.clone());
        self.exit_decl_enum_variant(&name, &fields);
        result
    }

    fn fold_decl_func_signature(
        &mut self,
        name: Name,
        params: Vec<Parameter>,
        generics: Vec<GenericDecl>,
        ret: TypeAnnotation,
    ) -> DeclKind {
        self.enter_decl_func_signature(&name, &params, &generics, &ret);
        let result = DeclKind::FuncSignature {
            name: name.clone(),
            params: params.clone(),
            generics: generics.clone(),
            ret: Box::new(ret.clone()),
        };
        self.exit_decl_func_signature(&name, &params, &generics, &ret);
        result
    }

    // Helper method to traverse only declarations in a block
    fn fold_decl_block(&mut self, mut block: Block) -> Block {
        use crate::node::Node;

        // Only process declaration nodes in the block body
        block.body = block
            .body
            .into_iter()
            .map(|node| match node {
                Node::Decl(decl) => Node::Decl(self.fold_decl(decl)),
                other => other, // Pass through non-declarations unchanged
            })
            .collect();

        block
    }

    // Enter methods for specific declaration variants
    fn enter_decl_import(&mut self, _s: &str) {}
    fn enter_decl_struct(
        &mut self,
        _name: &Name,
        _generics: &[GenericDecl],
        _conformances: &[TypeAnnotation],
        _body: &Block,
    ) {
    }
    fn enter_decl_let(
        &mut self,
        _lhs: &Pattern,
        _type_annotation: &Option<TypeAnnotation>,
        _value: &Option<crate::node_kinds::expr::Expr>,
    ) {
    }
    fn enter_decl_protocol(
        &mut self,
        _name: &Name,
        _generics: &[GenericDecl],
        _body: &Block,
        _conformances: &[TypeAnnotation],
    ) {
    }
    fn enter_decl_init(&mut self, _params: &[Parameter], _body: &Block) {}
    fn enter_decl_property(
        &mut self,
        _name: &Name,
        _is_static: bool,
        _type_annotation: &Option<TypeAnnotation>,
        _default_value: &Option<crate::node_kinds::expr::Expr>,
    ) {
    }
    fn enter_decl_method(&mut self, _func: &Decl, _is_static: bool) {}
    fn enter_decl_func(
        &mut self,
        _name: &Name,
        _generics: &[GenericDecl],
        _params: &[Parameter],
        _body: &Block,
        _ret: &Option<TypeAnnotation>,
        _attributes: &[Attribute],
    ) {
    }
    fn enter_decl_extend(
        &mut self,
        _name: &Name,
        _conformances: &[TypeAnnotation],
        _generics: &[GenericDecl],
        _body: &Block,
    ) {
    }
    fn enter_decl_enum(
        &mut self,
        _name: &Name,
        _conformances: &[TypeAnnotation],
        _generics: &[GenericDecl],
        _body: &Block,
    ) {
    }
    fn enter_decl_enum_variant(&mut self, _name: &Name, _fields: &[TypeAnnotation]) {}
    fn enter_decl_func_signature(
        &mut self,
        _name: &Name,
        _params: &[Parameter],
        _generics: &[GenericDecl],
        _ret: &TypeAnnotation,
    ) {
    }

    // Exit methods for specific declaration variants
    fn exit_decl_import(&mut self, _s: &str) {}
    fn exit_decl_struct(
        &mut self,
        _name: &Name,
        _generics: &[GenericDecl],
        _conformances: &[TypeAnnotation],
        _body: &Block,
    ) {
    }
    fn exit_decl_let(
        &mut self,
        _lhs: &Pattern,
        _type_annotation: &Option<TypeAnnotation>,
        _value: &Option<crate::node_kinds::expr::Expr>,
    ) {
    }
    fn exit_decl_protocol(
        &mut self,
        _name: &Name,
        _generics: &[GenericDecl],
        _body: &Block,
        _conformances: &[TypeAnnotation],
    ) {
    }
    fn exit_decl_init(&mut self, _params: &[Parameter], _body: &Block) {}
    fn exit_decl_property(
        &mut self,
        _name: &Name,
        _is_static: bool,
        _type_annotation: &Option<TypeAnnotation>,
        _default_value: &Option<crate::node_kinds::expr::Expr>,
    ) {
    }
    fn exit_decl_method(&mut self, _func: &Decl, _is_static: bool) {}
    fn exit_decl_func(
        &mut self,
        _name: &Name,
        _generics: &[GenericDecl],
        _params: &[Parameter],
        _body: &Block,
        _ret: &Option<TypeAnnotation>,
        _attributes: &[Attribute],
    ) {
    }
    fn exit_decl_extend(
        &mut self,
        _name: &Name,
        _conformances: &[TypeAnnotation],
        _generics: &[GenericDecl],
        _body: &Block,
    ) {
    }
    fn exit_decl_enum(
        &mut self,
        _name: &Name,
        _conformances: &[TypeAnnotation],
        _generics: &[GenericDecl],
        _body: &Block,
    ) {
    }
    fn exit_decl_enum_variant(&mut self, _name: &Name, _fields: &[TypeAnnotation]) {}
    fn exit_decl_func_signature(
        &mut self,
        _name: &Name,
        _params: &[Parameter],
        _generics: &[GenericDecl],
        _ret: &TypeAnnotation,
    ) {
    }
}

// Walk function for declarations
pub fn walk_decl<F: DeclFold>(fold: &mut F, mut decl: Decl) -> Decl {
    // Keep the node ID unchanged
    // decl.id is already set from the input

    decl.kind = match decl.kind {
        DeclKind::Import(s) => fold.fold_decl_import(s),
        DeclKind::Struct {
            name,
            generics,
            conformances,
            body,
        } => fold.fold_decl_struct(name, generics, conformances, body),
        DeclKind::Let {
            lhs,
            type_annotation,
            value,
        } => fold.fold_decl_let(lhs, type_annotation, value),
        DeclKind::Protocol {
            name,
            generics,
            body,
            conformances,
        } => fold.fold_decl_protocol(name, generics, body, conformances),
        DeclKind::Init { params, body } => fold.fold_decl_init(params, body),
        DeclKind::Property {
            name,
            is_static,
            type_annotation,
            default_value,
        } => fold.fold_decl_property(name, is_static, type_annotation, default_value),
        DeclKind::Method { func, is_static } => fold.fold_decl_method(func, is_static),
        DeclKind::Func {
            name,
            generics,
            params,
            body,
            ret,
            attributes,
        } => fold.fold_decl_func(name, generics, params, body, ret, attributes),
        DeclKind::Extend {
            name,
            conformances,
            generics,
            body,
        } => fold.fold_decl_extend(name, conformances, generics, body),
        DeclKind::Enum {
            name,
            conformances,
            generics,
            body,
        } => fold.fold_decl_enum(name, conformances, generics, body),
        DeclKind::EnumVariant(name, fields) => fold.fold_decl_enum_variant(name, fields),
        DeclKind::FuncSignature {
            name,
            params,
            generics,
            ret,
        } => fold.fold_decl_func_signature(name, params, generics, *ret),
    };

    decl
}
