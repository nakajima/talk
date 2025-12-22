use crate::types::{ty::Ty, typed_ast::TypedAST};

pub struct PatternPass<'a> {
    ast: &'a TypedAST<Ty>,
}

impl<'a> PatternPass<'a> {
    pub fn drive(ast: &TypedAST<Ty>) {
        let pass = PatternPass { ast };
    }
}
