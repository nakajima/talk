use crate::{ast::AST, name_resolution::name_resolver::NameResolved, types::type_session::Types};

pub struct Lowerer<'a> {
    _ast: &'a AST<NameResolved>,
    _types: &'a Types,
}

impl<'a> Lowerer<'a> {
    pub fn new(ast: &'a AST<NameResolved>, types: &'a Types) -> Self {
        Self {
            _ast: ast,
            _types: types,
        }
    }
}
