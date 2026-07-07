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
