use crate::token_kind::TokenKind;

pub(super) fn handle(string: String) -> TokenKind {
    use TokenKind::*;
    match string.as_str() {
        "as" => As,
        "func" => Func,
        "let" => Let,
        "if" => If,
        "else" => Else,
        "true" => True,
        "false" => False,
        "loop" => Loop,
        "enum" => Enum,
        "case" => Case,
        "match" => Match,
        "return" => Return,
        "struct" => Struct,
        "extend" => Extend,
        "break" => Break,
        "init" => Init,
        "protocol" => Protocol,
        "import" => Import,
        "public" => Public,
        "static" => Static,
        "associated" => Associated,
        "typealias" => Typealias,
        "effect" => Effect,
        "handling" => Handling,
        "in" => In,
        "continue" => Continue,
        _ => Identifier(string),
    }
}
