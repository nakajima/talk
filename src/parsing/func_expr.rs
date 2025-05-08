use crate::token::Token;

#[derive(Clone, Debug, PartialEq)]
pub struct FuncExpr {
    name: Option<Token>,
    parameters: usize,
    body: usize,
}

impl FuncExpr {
    pub fn new(name: Option<Token>, parameters: usize, body: usize) -> Self {
        Self {
            name,
            parameters,
            body,
        }
    }
}
