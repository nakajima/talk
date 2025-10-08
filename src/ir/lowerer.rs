use crate::{ast::AST, name_resolution::name_resolver::NameResolved, types::type_session::Types};

pub struct Lowerer<'a> {
    ast: &'a AST<NameResolved>,
    types: &'a Types,
}

impl<'a> Lowerer<'a> {
    pub fn new(ast: &'a AST<NameResolved>, types: &'a Types) -> Self {
        Self { ast, types }
    }
}
