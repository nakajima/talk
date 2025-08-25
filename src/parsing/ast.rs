use derive_visitor::{Drive, DriveMut};

use crate::{
    diagnostic::Diagnostic,
    node_kinds::{decl::Decl, stmt::Stmt},
    node_meta_storage::NodeMetaStorage,
    parser_error::ParserError,
};

#[derive(Clone, Debug, PartialEq, Eq, DriveMut, Drive)]
pub enum Root {
    Decl(Decl),
    Stmt(Stmt),
}

impl Root {
    pub fn as_decl(&self) -> &Decl {
        let Self::Decl(decl) = self else {
            panic!("Cannot get decl from {self:?}");
        };

        decl
    }

    pub fn as_stmt(&self) -> &Stmt {
        let Self::Stmt(stmt) = self else {
            panic!("Cannot get stmt from {self:?}");
        };

        stmt
    }
}

#[derive(Clone, Debug, PartialEq, Eq, DriveMut, Drive)]
pub struct AST {
    #[drive(skip)]
    pub path: String,
    pub roots: Vec<Root>,
    #[drive(skip)]
    pub diagnostics: Vec<Diagnostic<ParserError>>,
    #[drive(skip)]
    pub meta: NodeMetaStorage,
}
