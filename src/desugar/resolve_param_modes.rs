//! Resolve unadorned parameter modes (ADR 0018): parameters are
//! borrow-by-default. Every parameter leaves this pass with an explicit
//! mode, so no later stage special-cases `init`:
//!
//! - ordinary parameters (funcs, methods, requirement signatures, closure
//!   and trailing-block binders) default to `Borrow`;
//! - `init` parameters default to `Consume` (storing arguments is an
//!   initializer's whole job);
//! - effect operation parameters default to `Consume` (a performed payload
//!   moves into its continuation).
//!
//! Runs before `PrependSelfToMethods`: the receiver's ownership is spelled
//! in the synthesized `self` annotation itself, so `self` params keep
//! `mode: None` (lowered as written).

use derive_visitor::{DriveMut, VisitorMut};

use crate::{
    ast::{AST, Parsed},
    node_kinds::{
        block::Block,
        decl::{Decl, DeclKind},
        func::Func,
        func_signature::FuncSignature,
        parameter::{ParamMode, Parameter},
    },
};

#[derive(VisitorMut)]
#[visitor(Decl(enter), Func(enter), FuncSignature(enter), Block(enter))]
pub struct ResolveParamModes;

impl ResolveParamModes {
    pub fn run(ast: &mut AST<Parsed>) {
        for root in &mut ast.roots {
            root.drive_mut(&mut ResolveParamModes);
        }
    }

    fn stamp(params: &mut [Parameter], default: ParamMode) {
        for param in params {
            if param.mode.is_none() {
                param.mode = Some(default);
            }
        }
    }

    fn enter_decl(&mut self, decl: &mut Decl) {
        match &mut decl.kind {
            DeclKind::Init { params, .. } | DeclKind::Effect { params, .. } => {
                Self::stamp(params, ParamMode::Consume);
            }
            // Stamped here, before the visitor reaches the signature and
            // applies the ordinary `Borrow` default.
            DeclKind::InitRequirement { signature } => {
                Self::stamp(&mut signature.params, ParamMode::Consume);
            }
            _ => {}
        }
    }

    fn enter_func(&mut self, func: &mut Func) {
        Self::stamp(&mut func.params, ParamMode::Borrow);
    }

    fn enter_func_signature(&mut self, signature: &mut FuncSignature) {
        Self::stamp(&mut signature.params, ParamMode::Borrow);
    }

    fn enter_block(&mut self, block: &mut Block) {
        Self::stamp(&mut block.args, ParamMode::Borrow);
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        node::Node,
        node_kinds::{
            decl::{Decl, DeclKind},
            parameter::ParamMode,
        },
    };

    #[test]
    fn stamps_extension_method_params() {
        let mut ast = crate::parser_tests::tests::parse(
            "struct Wrap {}\nextend Wrap {\n\tfunc poke(t: Token) -> Int { 0 }\n}",
        );
        crate::desugar::desugar(std::slice::from_mut(&mut ast));
        let Node::Decl(Decl {
            kind: DeclKind::Extend { body, .. },
            ..
        }) = &ast.roots[1]
        else {
            panic!("expected extend, got {:?}", ast.roots[1]);
        };
        let Decl {
            kind: DeclKind::Method { func, .. },
            ..
        } = &body.decls[0]
        else {
            panic!("expected method, got {:?}", body.decls[0]);
        };
        // params[0] is the prepended self; the user param follows.
        assert_eq!(func.params[1].mode, Some(ParamMode::Borrow));
    }

    #[test]
    fn stamps_init_requirement_params_consume() {
        let mut ast = crate::parser_tests::tests::parse(
            "protocol FromPair {\n\tinit(lower: Int, upper: Int)\n}",
        );
        crate::desugar::desugar(std::slice::from_mut(&mut ast));
        let Node::Decl(Decl {
            kind: DeclKind::Protocol { body, .. },
            ..
        }) = &ast.roots[0]
        else {
            panic!("expected protocol, got {:?}", ast.roots[0]);
        };
        let Decl {
            kind: DeclKind::InitRequirement { signature },
            ..
        } = &body.decls[0]
        else {
            panic!("expected init requirement, got {:?}", body.decls[0]);
        };
        assert_eq!(signature.params[0].mode, Some(ParamMode::Consume));
        assert_eq!(signature.params[1].mode, Some(ParamMode::Consume));
    }
}
