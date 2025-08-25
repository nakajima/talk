use derive_visitor::{Drive, DriveMut};

use crate::{name::Name, node::Node, node_kinds::expr::Expr};

#[derive(Clone, Debug, PartialEq, Eq, DriveMut, Drive)]
pub enum IncompleteExpr {
    Member(Option<Box<Expr>>), // Receiver
    Func {
        #[drive(skip)]
        name: Option<Name>,
        params: Option<Vec<Node>>,
        generics: Option<Vec<Node>>,
        ret: Option<Box<Node>>,
        body: Option<Box<Node>>,
    },
}
