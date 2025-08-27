//! AST Fold trait for functional transformations
//!
//! This module provides a Fold trait that allows traversal and transformation
//! of AST nodes in a functional style (consume and produce new nodes).
//!
//! Key features:
//! - Enter/exit hooks for all node types
//! - Specific handlers for each Decl variant  
//! - Specific handlers for each Expr variant
//! - Pre-order and post-order traversal support

use tracing::instrument;

use crate::label::Label;
use crate::lexing::token_kind::TokenKind;
use crate::name::Name;
use crate::node::Node;
use crate::node_id::NodeID;
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

pub trait Fold: Sized + std::fmt::Debug {
    // Enter methods - called before visiting children
    fn enter_node(&mut self, _node: &Node) {}
    fn enter_attribute(&mut self, _attr: &Attribute) {}
    fn enter_decl(&mut self, _decl: &Decl) {}
    fn enter_generic_decl(&mut self, _generic: &GenericDecl) {}
    fn enter_parameter(&mut self, _param: &Parameter) {}
    fn enter_stmt(&mut self, _stmt: &Stmt) {}
    fn enter_expr(&mut self, _expr: &Expr) {}
    fn enter_pattern(&mut self, _pattern: &Pattern) {}
    fn enter_match_arm(&mut self, _arm: &MatchArm) {}
    fn enter_block(&mut self, _block: &Block) {}
    fn enter_type_annotation(&mut self, _ty: &TypeAnnotation) {}
    fn enter_record_field(&mut self, _field: &RecordField) {}
    fn enter_incomplete_expr(&mut self, _expr: &IncompleteExpr) {}
    fn enter_call_arg(&mut self, _arg: &CallArg) {}

    // Enter methods for specific Decl variants
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
        _value: &Option<Expr>,
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
        _default_value: &Option<Expr>,
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

    // Enter methods for specific Expr variants
    fn enter_expr_incomplete(&mut self, _expr: &Expr) {}
    fn enter_expr_literal_array(&mut self, _expr: &Expr) {}
    fn enter_expr_literal_int(&mut self, _expr: &Expr) {}
    fn enter_expr_literal_float(&mut self, _expr: &Expr) {}
    fn enter_expr_literal_true(&mut self, _expr: &Expr) {}
    fn enter_expr_literal_false(&mut self, _expr: &Expr) {}
    fn enter_expr_literal_string(&mut self, _expr: &Expr) {}
    fn enter_expr_unary(&mut self, _expr: &Expr) {}
    fn enter_expr_binary(&mut self, _expr: &Expr) {}
    fn enter_expr_tuple(&mut self, _expr: &Expr) {}
    fn enter_expr_block(&mut self, _expr: &Expr) {}
    fn enter_expr_call(&mut self, _expr: &Expr) {}
    fn enter_expr_member(&mut self, _expr: &Expr) {}
    fn enter_expr_func(&mut self, _expr: &Expr) {}
    fn enter_expr_variable(&mut self, _expr: &Expr) {}
    fn enter_expr_if(&mut self, _expr: &Expr) {}
    fn enter_expr_match(&mut self, _expr: &Expr) {}
    fn enter_expr_pattern_variant(&mut self, _expr: &Expr) {}
    fn enter_expr_record_literal(&mut self, _expr: &Expr) {}
    fn enter_expr_row_variable(&mut self, _expr: &Expr) {}
    fn enter_expr_spread(&mut self, _expr: &Expr) {}

    #[instrument] // Fold methods - called to transform nodes (with default implementations that walk children)
    fn fold_node(&mut self, node: Node) -> Node {
        println!("fold_node: {node:?}");
        self.enter_node(&node);
        let result = walk_node(self, node);
        self.exit_node(&result);
        result
    }
    #[instrument]
    fn fold_attribute(&mut self, attr: Attribute) -> Attribute {
        self.enter_attribute(&attr);
        let result = attr;
        self.exit_attribute(&result);
        result
    }
    #[instrument]
    fn fold_decl(&mut self, decl: Decl) -> Decl {
        self.enter_decl(&decl);
        let result = walk_decl(self, decl);
        self.exit_decl(&result);
        result
    }

    #[instrument] // Decl variant handlers - override these to customize handling of specific declaration types
    fn fold_decl_import(&mut self, s: String) -> DeclKind {
        self.enter_decl_import(&s);
        let result = DeclKind::Import(s.clone());
        self.exit_decl_import(&s);
        result
    }
    #[instrument]
    fn fold_decl_struct(
        &mut self,
        name: Name,
        generics: Vec<GenericDecl>,
        conformances: Vec<TypeAnnotation>,
        body: Block,
    ) -> DeclKind {
        self.enter_decl_struct(&name, &generics, &conformances, &body);
        let result = DeclKind::Struct {
            name: self.fold_name(name.clone()),
            generics: generics
                .into_iter()
                .map(|g| self.fold_generic_decl(g))
                .collect(),
            conformances: conformances
                .into_iter()
                .map(|c| self.fold_type_annotation(c))
                .collect(),
            body: self.fold_block(body.clone()),
        };
        // Need to get references for the exit call
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
    #[instrument]
    fn fold_decl_let(
        &mut self,
        lhs: Pattern,
        type_annotation: Option<TypeAnnotation>,
        value: Option<Expr>,
    ) -> DeclKind {
        self.enter_decl_let(&lhs, &type_annotation, &value);
        let result = DeclKind::Let {
            lhs: self.fold_pattern(lhs.clone()),
            type_annotation: type_annotation.map(|t| self.fold_type_annotation(t)),
            value: value.map(|v| self.fold_expr(v)),
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
    #[instrument]
    fn fold_decl_protocol(
        &mut self,
        name: Name,
        generics: Vec<GenericDecl>,
        body: Block,
        conformances: Vec<TypeAnnotation>,
    ) -> DeclKind {
        self.enter_decl_protocol(&name, &generics, &body, &conformances);
        let result = DeclKind::Protocol {
            name: self.fold_name(name.clone()),
            generics: generics
                .into_iter()
                .map(|g| self.fold_generic_decl(g))
                .collect(),
            body: self.fold_block(body.clone()),
            conformances: conformances
                .into_iter()
                .map(|c| self.fold_type_annotation(c))
                .collect(),
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
    #[instrument]
    fn fold_decl_init(&mut self, params: Vec<Parameter>, body: Block) -> DeclKind {
        self.enter_decl_init(&params, &body);
        let result = DeclKind::Init {
            params: params.into_iter().map(|p| self.fold_parameter(p)).collect(),
            body: self.fold_block(body.clone()),
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
    #[instrument]
    fn fold_decl_property(
        &mut self,
        name: Name,
        is_static: bool,
        type_annotation: Option<TypeAnnotation>,
        default_value: Option<Expr>,
    ) -> DeclKind {
        self.enter_decl_property(&name, is_static, &type_annotation, &default_value);
        let result = DeclKind::Property {
            name: self.fold_name(name.clone()),
            is_static,
            type_annotation: type_annotation.map(|t| self.fold_type_annotation(t)),
            default_value: default_value.map(|e| self.fold_expr(e)),
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
    #[instrument]
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
    #[instrument]
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
        let result = DeclKind::Func {
            name: self.fold_name(name.clone()),
            generics: generics
                .into_iter()
                .map(|g| self.fold_generic_decl(g))
                .collect(),
            params: params.into_iter().map(|p| self.fold_parameter(p)).collect(),
            body: self.fold_block(body.clone()),
            ret: ret.map(|r| self.fold_type_annotation(r)),
            attributes: attributes
                .into_iter()
                .map(|a| self.fold_attribute(a))
                .collect(),
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
    #[instrument]
    fn fold_decl_extend(
        &mut self,
        name: Name,
        conformances: Vec<TypeAnnotation>,
        generics: Vec<GenericDecl>,
        body: Block,
    ) -> DeclKind {
        self.enter_decl_extend(&name, &conformances, &generics, &body);
        let result = DeclKind::Extend {
            name: self.fold_name(name.clone()),
            conformances: conformances
                .into_iter()
                .map(|c| self.fold_type_annotation(c))
                .collect(),
            generics: generics
                .into_iter()
                .map(|g| self.fold_generic_decl(g))
                .collect(),
            body: self.fold_block(body.clone()),
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
    #[instrument]
    fn fold_decl_enum(
        &mut self,
        name: Name,
        conformances: Vec<TypeAnnotation>,
        generics: Vec<GenericDecl>,
        body: Block,
    ) -> DeclKind {
        self.enter_decl_enum(&name, &conformances, &generics, &body);
        let result = DeclKind::Enum {
            name: self.fold_name(name.clone()),
            conformances: conformances
                .into_iter()
                .map(|c| self.fold_type_annotation(c))
                .collect(),
            generics: generics
                .into_iter()
                .map(|g| self.fold_generic_decl(g))
                .collect(),
            body: self.fold_block(body.clone()),
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
    #[instrument]
    fn fold_decl_enum_variant(&mut self, name: Name, fields: Vec<TypeAnnotation>) -> DeclKind {
        self.enter_decl_enum_variant(&name, &fields);
        let result = DeclKind::EnumVariant(
            self.fold_name(name.clone()),
            fields
                .into_iter()
                .map(|f| self.fold_type_annotation(f))
                .collect(),
        );
        if let DeclKind::EnumVariant(ref n, ref f) = result {
            self.exit_decl_enum_variant(n, f);
        }
        result
    }
    #[instrument]
    fn fold_decl_func_signature(
        &mut self,
        name: Name,
        params: Vec<Parameter>,
        generics: Vec<GenericDecl>,
        ret: Box<TypeAnnotation>,
    ) -> DeclKind {
        self.enter_decl_func_signature(&name, &params, &generics, &ret);
        let result = DeclKind::FuncSignature {
            name: self.fold_name(name.clone()),
            params: params.into_iter().map(|p| self.fold_parameter(p)).collect(),
            generics: generics
                .into_iter()
                .map(|g| self.fold_generic_decl(g))
                .collect(),
            ret: Box::new(self.fold_type_annotation(*ret)),
        };
        if let DeclKind::FuncSignature {
            name: ref n,
            params: ref p,
            generics: ref g,
            ret: ref r,
        } = result
        {
            self.exit_decl_func_signature(n, p, g, r);
        }
        result
    }
    #[instrument]
    fn fold_generic_decl(&mut self, generic: GenericDecl) -> GenericDecl {
        self.enter_generic_decl(&generic);
        let result = walk_generic_decl(self, generic);
        self.exit_generic_decl(&result);
        result
    }
    #[instrument]
    fn fold_parameter(&mut self, param: Parameter) -> Parameter {
        self.enter_parameter(&param);
        let result = walk_parameter(self, param);
        self.exit_parameter(&result);
        result
    }
    #[instrument]
    fn fold_stmt(&mut self, stmt: Stmt) -> Stmt {
        self.enter_stmt(&stmt);
        let result = walk_stmt(self, stmt);
        self.exit_stmt(&result);
        result
    }
    #[instrument]
    fn fold_expr(&mut self, expr: Expr) -> Expr {
        self.enter_expr(&expr);
        let result = walk_expr(self, expr);
        self.exit_expr(&result);
        result
    }
    #[instrument]
    fn fold_pattern(&mut self, pattern: Pattern) -> Pattern {
        self.enter_pattern(&pattern);
        let result = walk_pattern(self, pattern);
        self.exit_pattern(&result);
        result
    }
    #[instrument]
    fn fold_match_arm(&mut self, arm: MatchArm) -> MatchArm {
        self.enter_match_arm(&arm);
        let result = walk_match_arm(self, arm);
        self.exit_match_arm(&result);
        result
    }
    #[instrument]
    fn fold_block(&mut self, block: Block) -> Block {
        self.enter_block(&block);
        let result = walk_block(self, block);
        self.exit_block(&result);
        result
    }
    #[instrument]
    fn fold_type_annotation(&mut self, ty: TypeAnnotation) -> TypeAnnotation {
        self.enter_type_annotation(&ty);
        let result = walk_type_annotation(self, ty);
        self.exit_type_annotation(&result);
        result
    }
    #[instrument]
    fn fold_record_field(&mut self, field: RecordField) -> RecordField {
        self.enter_record_field(&field);
        let result = walk_record_field(self, field);
        self.exit_record_field(&result);
        result
    }
    #[instrument]
    fn fold_incomplete_expr(&mut self, expr: IncompleteExpr) -> IncompleteExpr {
        self.enter_incomplete_expr(&expr);
        let result = walk_incomplete_expr(self, expr);
        self.exit_incomplete_expr(&result);
        result
    }
    #[instrument]
    fn fold_call_arg(&mut self, arg: CallArg) -> CallArg {
        self.enter_call_arg(&arg);
        let result = walk_call_arg(self, arg);
        self.exit_call_arg(&result);
        result
    }

    // Exit methods - called after visiting children
    fn exit_node(&mut self, _node: &Node) {}
    fn exit_attribute(&mut self, _attr: &Attribute) {}
    fn exit_decl(&mut self, _decl: &Decl) {}
    fn exit_generic_decl(&mut self, _generic: &GenericDecl) {}
    fn exit_parameter(&mut self, _param: &Parameter) {}
    fn exit_stmt(&mut self, _stmt: &Stmt) {}
    fn exit_expr(&mut self, _expr: &Expr) {}
    fn exit_pattern(&mut self, _pattern: &Pattern) {}
    fn exit_match_arm(&mut self, _arm: &MatchArm) {}
    fn exit_block(&mut self, _block: &Block) {}
    fn exit_type_annotation(&mut self, _ty: &TypeAnnotation) {}
    fn exit_record_field(&mut self, _field: &RecordField) {}
    fn exit_incomplete_expr(&mut self, _expr: &IncompleteExpr) {}
    fn exit_call_arg(&mut self, _arg: &CallArg) {}

    // Exit methods for specific Decl variants
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
        _value: &Option<Expr>,
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
        _default_value: &Option<Expr>,
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

    // Exit methods for specific Expr variants
    fn exit_expr_incomplete(&mut self, _expr: &Expr) {}
    fn exit_expr_literal_array(&mut self, _expr: &Expr) {}
    fn exit_expr_literal_int(&mut self, _expr: &Expr) {}
    fn exit_expr_literal_float(&mut self, _expr: &Expr) {}
    fn exit_expr_literal_true(&mut self, _expr: &Expr) {}
    fn exit_expr_literal_false(&mut self, _expr: &Expr) {}
    fn exit_expr_literal_string(&mut self, _expr: &Expr) {}
    fn exit_expr_unary(&mut self, _expr: &Expr) {}
    fn exit_expr_binary(&mut self, _expr: &Expr) {}
    fn exit_expr_tuple(&mut self, _expr: &Expr) {}
    fn exit_expr_block(&mut self, _expr: &Expr) {}
    fn exit_expr_call(&mut self, _expr: &Expr) {}
    fn exit_expr_member(&mut self, _expr: &Expr) {}
    fn exit_expr_func(&mut self, _expr: &Expr) {}
    fn exit_expr_variable(&mut self, _expr: &Expr) {}
    fn exit_expr_if(&mut self, _expr: &Expr) {}
    fn exit_expr_match(&mut self, _expr: &Expr) {}
    fn exit_expr_pattern_variant(&mut self, _expr: &Expr) {}
    fn exit_expr_record_literal(&mut self, _expr: &Expr) {}
    fn exit_expr_row_variable(&mut self, _expr: &Expr) {}
    fn exit_expr_spread(&mut self, _expr: &Expr) {}

    #[instrument]
    fn fold_node_id(&mut self, id: NodeID) -> NodeID {
        id
    }
    #[instrument]
    fn fold_name(&mut self, name: Name) -> Name {
        name
    }
    #[instrument]
    fn fold_label(&mut self, label: Label) -> Label {
        label
    }
    #[instrument]
    fn fold_token_kind(&mut self, token: TokenKind) -> TokenKind {
        token
    }
}

pub fn walk_node<F: Fold>(fold: &mut F, node: Node) -> Node {
    match node {
        Node::Attribute(attr) => Node::Attribute(fold.fold_attribute(attr)),
        Node::Decl(decl) => Node::Decl(fold.fold_decl(decl)),
        Node::GenericDecl(generic) => Node::GenericDecl(fold.fold_generic_decl(generic)),
        Node::Parameter(param) => Node::Parameter(fold.fold_parameter(param)),
        Node::Stmt(stmt) => Node::Stmt(fold.fold_stmt(stmt)),
        Node::Expr(expr) => Node::Expr(fold.fold_expr(expr)),
        Node::Pattern(pattern) => Node::Pattern(fold.fold_pattern(pattern)),
        Node::MatchArm(arm) => Node::MatchArm(fold.fold_match_arm(arm)),
        Node::Block(block) => Node::Block(fold.fold_block(block)),
        Node::TypeAnnotation(ty) => Node::TypeAnnotation(fold.fold_type_annotation(ty)),
        Node::RecordField(field) => Node::RecordField(fold.fold_record_field(field)),
        Node::IncompleteExpr(expr) => Node::IncompleteExpr(fold.fold_incomplete_expr(expr)),
        Node::CallArg(arg) => Node::CallArg(fold.fold_call_arg(arg)),
    }
}

pub fn walk_decl<F: Fold>(fold: &mut F, mut decl: Decl) -> Decl {
    decl.id = fold.fold_node_id(decl.id);
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
        } => fold.fold_decl_func_signature(name, params, generics, ret),
    };
    decl
}

pub fn walk_generic_decl<F: Fold>(fold: &mut F, mut generic: GenericDecl) -> GenericDecl {
    generic.id = fold.fold_node_id(generic.id);
    generic.name = fold.fold_name(generic.name);
    generic.generics = generic
        .generics
        .into_iter()
        .map(|g| fold.fold_generic_decl(g))
        .collect();
    generic.conformances = generic
        .conformances
        .into_iter()
        .map(|c| fold.fold_generic_decl(c))
        .collect();
    generic
}

pub fn walk_parameter<F: Fold>(fold: &mut F, mut param: Parameter) -> Parameter {
    param.id = fold.fold_node_id(param.id);
    param.name = fold.fold_name(param.name);
    param.type_annotation = param.type_annotation.map(|t| fold.fold_type_annotation(t));
    param
}

pub fn walk_stmt<F: Fold>(fold: &mut F, mut stmt: Stmt) -> Stmt {
    stmt.id = fold.fold_node_id(stmt.id);
    stmt.kind = match stmt.kind {
        StmtKind::Expr(expr) => StmtKind::Expr(fold.fold_expr(expr)),
        StmtKind::If(cond, body) => StmtKind::If(fold.fold_expr(cond), fold.fold_block(body)),
        StmtKind::Return(expr) => StmtKind::Return(expr.map(|e| fold.fold_expr(e))),
        StmtKind::Break => StmtKind::Break,
        StmtKind::Assignment(lhs, rhs) => {
            StmtKind::Assignment(fold.fold_expr(lhs), fold.fold_expr(rhs))
        }
        StmtKind::LetAssignment(lhs, rhs) => {
            StmtKind::LetAssignment(fold.fold_pattern(lhs), fold.fold_expr(rhs))
        }
        StmtKind::Loop(cond, body) => {
            StmtKind::Loop(cond.map(|c| fold.fold_expr(c)), fold.fold_block(body))
        }
    };
    stmt
}

pub fn walk_expr<F: Fold>(fold: &mut F, mut expr: Expr) -> Expr {
    // Call specific enter method based on variant
    match &expr.kind {
        ExprKind::Incomplete(_) => fold.enter_expr_incomplete(&expr),
        ExprKind::LiteralArray(_) => fold.enter_expr_literal_array(&expr),
        ExprKind::LiteralInt(_) => fold.enter_expr_literal_int(&expr),
        ExprKind::LiteralFloat(_) => fold.enter_expr_literal_float(&expr),
        ExprKind::LiteralTrue => fold.enter_expr_literal_true(&expr),
        ExprKind::LiteralFalse => fold.enter_expr_literal_false(&expr),
        ExprKind::LiteralString(_) => fold.enter_expr_literal_string(&expr),
        ExprKind::Unary(_, _) => fold.enter_expr_unary(&expr),
        ExprKind::Binary(_, _, _) => fold.enter_expr_binary(&expr),
        ExprKind::Tuple(_) => fold.enter_expr_tuple(&expr),
        ExprKind::Block(_) => fold.enter_expr_block(&expr),
        ExprKind::Call { .. } => fold.enter_expr_call(&expr),
        ExprKind::Member(_, _) => fold.enter_expr_member(&expr),
        ExprKind::Func { .. } => fold.enter_expr_func(&expr),
        ExprKind::Variable(_) => fold.enter_expr_variable(&expr),
        ExprKind::If(_, _, _) => fold.enter_expr_if(&expr),
        ExprKind::Match(_, _) => fold.enter_expr_match(&expr),
        ExprKind::PatternVariant(_, _, _) => fold.enter_expr_pattern_variant(&expr),
        ExprKind::RecordLiteral(_) => fold.enter_expr_record_literal(&expr),
        ExprKind::RowVariable(_) => fold.enter_expr_row_variable(&expr),
        ExprKind::Spread(_) => fold.enter_expr_spread(&expr),
    }

    // Walk and transform children
    expr.id = fold.fold_node_id(expr.id);
    expr.kind = match expr.kind {
        ExprKind::Incomplete(inc) => ExprKind::Incomplete(fold.fold_incomplete_expr(inc)),
        ExprKind::LiteralArray(exprs) => {
            ExprKind::LiteralArray(exprs.into_iter().map(|e| fold.fold_expr(e)).collect())
        }
        ExprKind::LiteralInt(s) => ExprKind::LiteralInt(s),
        ExprKind::LiteralFloat(s) => ExprKind::LiteralFloat(s),
        ExprKind::LiteralString(s) => ExprKind::LiteralString(s),
        ExprKind::LiteralTrue => ExprKind::LiteralTrue,
        ExprKind::LiteralFalse => ExprKind::LiteralFalse,
        ExprKind::Unary(op, expr) => {
            ExprKind::Unary(fold.fold_token_kind(op), Box::new(fold.fold_expr(*expr)))
        }
        ExprKind::Binary(lhs, op, rhs) => ExprKind::Binary(
            Box::new(fold.fold_expr(*lhs)),
            fold.fold_token_kind(op),
            Box::new(fold.fold_expr(*rhs)),
        ),
        ExprKind::Tuple(exprs) => {
            ExprKind::Tuple(exprs.into_iter().map(|e| fold.fold_expr(e)).collect())
        }
        ExprKind::Block(block) => ExprKind::Block(fold.fold_block(block)),
        ExprKind::Call {
            callee,
            type_args,
            args,
        } => ExprKind::Call {
            callee: Box::new(fold.fold_expr(*callee)),
            type_args: type_args
                .into_iter()
                .map(|t| fold.fold_type_annotation(t))
                .collect(),
            args: args.into_iter().map(|a| fold.fold_call_arg(a)).collect(),
        },
        ExprKind::Member(expr, label) => ExprKind::Member(
            expr.map(|e| Box::new(fold.fold_expr(*e))),
            fold.fold_label(label),
        ),
        ExprKind::Func {
            generics,
            params,
            body,
            ret,
            attributes,
        } => ExprKind::Func {
            generics: generics
                .into_iter()
                .map(|g| fold.fold_generic_decl(g))
                .collect(),
            params: params.into_iter().map(|p| fold.fold_parameter(p)).collect(),
            body: fold.fold_block(body),
            ret: ret.map(|r| fold.fold_type_annotation(r)),
            attributes: attributes
                .into_iter()
                .map(|a| fold.fold_attribute(a))
                .collect(),
        },
        ExprKind::Variable(name) => ExprKind::Variable(fold.fold_name(name)),
        ExprKind::If(cond, then_block, else_block) => ExprKind::If(
            Box::new(fold.fold_expr(*cond)),
            fold.fold_block(then_block),
            fold.fold_block(else_block),
        ),
        ExprKind::Match(scrutinee, arms) => ExprKind::Match(
            Box::new(fold.fold_expr(*scrutinee)),
            arms.into_iter().map(|a| fold.fold_match_arm(a)).collect(),
        ),
        ExprKind::PatternVariant(enum_name, variant_name, patterns) => ExprKind::PatternVariant(
            enum_name.map(|n| fold.fold_name(n)),
            fold.fold_name(variant_name),
            patterns.into_iter().map(|p| fold.fold_pattern(p)).collect(),
        ),
        ExprKind::RecordLiteral(fields) => ExprKind::RecordLiteral(
            fields
                .into_iter()
                .map(|f| fold.fold_record_field(f))
                .collect(),
        ),
        ExprKind::RowVariable(name) => ExprKind::RowVariable(fold.fold_name(name)),
        ExprKind::Spread(node) => ExprKind::Spread(Box::new(fold.fold_node(*node))),
    };

    // Call specific exit method based on variant
    match &expr.kind {
        ExprKind::Incomplete(_) => fold.exit_expr_incomplete(&expr),
        ExprKind::LiteralArray(_) => fold.exit_expr_literal_array(&expr),
        ExprKind::LiteralInt(_) => fold.exit_expr_literal_int(&expr),
        ExprKind::LiteralFloat(_) => fold.exit_expr_literal_float(&expr),
        ExprKind::LiteralTrue => fold.exit_expr_literal_true(&expr),
        ExprKind::LiteralFalse => fold.exit_expr_literal_false(&expr),
        ExprKind::LiteralString(_) => fold.exit_expr_literal_string(&expr),
        ExprKind::Unary(_, _) => fold.exit_expr_unary(&expr),
        ExprKind::Binary(_, _, _) => fold.exit_expr_binary(&expr),
        ExprKind::Tuple(_) => fold.exit_expr_tuple(&expr),
        ExprKind::Block(_) => fold.exit_expr_block(&expr),
        ExprKind::Call { .. } => fold.exit_expr_call(&expr),
        ExprKind::Member(_, _) => fold.exit_expr_member(&expr),
        ExprKind::Func { .. } => fold.exit_expr_func(&expr),
        ExprKind::Variable(_) => fold.exit_expr_variable(&expr),
        ExprKind::If(_, _, _) => fold.exit_expr_if(&expr),
        ExprKind::Match(_, _) => fold.exit_expr_match(&expr),
        ExprKind::PatternVariant(_, _, _) => fold.exit_expr_pattern_variant(&expr),
        ExprKind::RecordLiteral(_) => fold.exit_expr_record_literal(&expr),
        ExprKind::RowVariable(_) => fold.exit_expr_row_variable(&expr),
        ExprKind::Spread(_) => fold.exit_expr_spread(&expr),
    }

    expr
}

pub fn walk_pattern<F: Fold>(fold: &mut F, mut pattern: Pattern) -> Pattern {
    pattern.id = fold.fold_node_id(pattern.id);
    pattern.kind = match pattern.kind {
        PatternKind::LiteralInt(s) => PatternKind::LiteralInt(s),
        PatternKind::LiteralFloat(s) => PatternKind::LiteralFloat(s),
        PatternKind::LiteralTrue => PatternKind::LiteralTrue,
        PatternKind::LiteralFalse => PatternKind::LiteralFalse,
        PatternKind::Bind(name) => PatternKind::Bind(fold.fold_name(name)),
        PatternKind::Wildcard => PatternKind::Wildcard,
        PatternKind::Variant {
            enum_name,
            variant_name,
            fields,
        } => PatternKind::Variant {
            enum_name: enum_name.map(|n| fold.fold_name(n)),
            variant_name,
            fields: fields.into_iter().map(|f| fold.fold_pattern(f)).collect(),
        },
        PatternKind::Struct {
            struct_name,
            fields,
            field_names,
            rest,
        } => PatternKind::Struct {
            struct_name: struct_name.map(|n| fold.fold_name(n)),
            fields: fields.into_iter().map(|f| fold.fold_node(f)).collect(),
            field_names: field_names.into_iter().map(|n| fold.fold_name(n)).collect(),
            rest,
        },
    };
    pattern
}

pub fn walk_match_arm<F: Fold>(fold: &mut F, mut arm: MatchArm) -> MatchArm {
    arm.id = fold.fold_node_id(arm.id);
    arm.pattern = fold.fold_pattern(arm.pattern);
    arm.body = fold.fold_block(arm.body);
    arm
}

pub fn walk_block<F: Fold>(fold: &mut F, mut block: Block) -> Block {
    block.id = fold.fold_node_id(block.id);
    block.args = block.args.into_iter().map(|a| fold.fold_name(a)).collect();
    block.body = block.body.into_iter().map(|n| fold.fold_node(n)).collect();
    block
}

pub fn walk_type_annotation<F: Fold>(fold: &mut F, mut ty: TypeAnnotation) -> TypeAnnotation {
    ty.id = fold.fold_node_id(ty.id);
    ty.kind = match ty.kind {
        TypeAnnotationKind::Func { params, returns } => TypeAnnotationKind::Func {
            params: params
                .into_iter()
                .map(|p| fold.fold_type_annotation(p))
                .collect(),
            returns: Box::new(fold.fold_type_annotation(*returns)),
        },
        TypeAnnotationKind::Nominal { name, generics } => TypeAnnotationKind::Nominal {
            name: fold.fold_name(name),
            generics: generics
                .into_iter()
                .map(|g| fold.fold_type_annotation(g))
                .collect(),
        },
        TypeAnnotationKind::Tuple(types) => TypeAnnotationKind::Tuple(
            types
                .into_iter()
                .map(|t| fold.fold_type_annotation(t))
                .collect(),
        ),
    };
    ty
}

pub fn walk_record_field<F: Fold>(fold: &mut F, mut field: RecordField) -> RecordField {
    field.id = fold.fold_node_id(field.id);
    field.label = fold.fold_name(field.label);
    field.value = fold.fold_expr(field.value);
    field
}

pub fn walk_incomplete_expr<F: Fold>(fold: &mut F, expr: IncompleteExpr) -> IncompleteExpr {
    match expr {
        IncompleteExpr::Member(expr) => {
            IncompleteExpr::Member(expr.map(|e| Box::new(fold.fold_expr(*e))))
        }
        IncompleteExpr::Func {
            name,
            params,
            generics,
            ret,
            body,
        } => IncompleteExpr::Func {
            name: name.map(|n| fold.fold_name(n)),
            params: params.map(|ps| ps.into_iter().map(|p| fold.fold_node(p)).collect()),
            generics: generics.map(|gs| gs.into_iter().map(|g| fold.fold_node(g)).collect()),
            ret: ret.map(|r| Box::new(fold.fold_node(*r))),
            body: body.map(|b| Box::new(fold.fold_node(*b))),
        },
    }
}

pub fn walk_call_arg<F: Fold>(fold: &mut F, mut arg: CallArg) -> CallArg {
    arg.id = fold.fold_node_id(arg.id);
    arg.label = fold.fold_label(arg.label);
    arg.value = fold.fold_expr(arg.value);
    arg
}
