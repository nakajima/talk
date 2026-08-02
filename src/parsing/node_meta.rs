use crate::token::Token;

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct NodeMeta {
    pub start: Token,
    pub end: Token,
    pub identifiers: Vec<Token>,
}
