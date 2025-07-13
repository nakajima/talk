use crate::{
    SourceFile,
    lexer::Lexer,
    parsed_expr::{Expr, IncompleteExpr, ParsedExpr, Pattern},
    parser::parse,
    token::Token,
    token_kind::TokenKind,
};

#[derive(Debug, Copy, Clone)]
#[allow(non_camel_case_types)]
pub enum Kind {
    NAMESPACE,
    TYPE,
    CLASS,
    ENUM,
    INTERFACE,
    STRUCT,
    TYPE_PARAMETER,
    PARAMETER,
    VARIABLE,
    PROPERTY,
    ENUM_MEMBER,
    EVENT,
    FUNCTION,
    METHOD,
    MACRO,
    KEYWORD,
    MODIFIER,
    COMMENT,
    STRING,
    NUMBER,
    REGEXP,
    OPERATOR,
}

impl std::fmt::Display for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", format!("{self:?}").to_lowercase())
    }
}

#[derive(Debug, Copy, Clone)]
pub struct HighlightToken {
    pub kind: Kind,
    pub start: u32,
    pub end: u32,
}

impl HighlightToken {
    pub fn new(kind: Kind, start: u32, end: u32) -> Self {
        Self { kind, start, end }
    }
}

#[derive(Debug, Clone)]
pub struct Higlighter<'a> {
    source: &'a str,
    source_file: SourceFile,
}

impl<'a> Higlighter<'a> {
    pub fn new(source: &'a str) -> Self {
        let source_file = parse(source, "-".into());

        Self {
            source,
            source_file,
        }
    }

    pub fn highlight(&mut self) -> Vec<HighlightToken> {
        let mut result = vec![];
        result.extend(self.collect_lexed_tokens());

        for root in self.source_file.roots() {
            result.extend(self.tokens_from_expr(&root));
        }

        result
    }

    fn collect_lexed_tokens(&mut self) -> Vec<HighlightToken> {
        let mut lexer = Lexer::preserving_comments(self.source);
        let mut tokens: Vec<HighlightToken> = vec![];

        while let Ok(tok) = &lexer.next() {
            match tok.kind {
                TokenKind::LineComment(_) => self.make(tok, Kind::COMMENT, &mut tokens),
                TokenKind::Extend => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::If => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::Else => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::Loop => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::Return => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::True => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::False => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::Enum => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::Case => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::Match => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::StringLiteral(_) => self.make_string(tok, Kind::STRING, &mut tokens),
                TokenKind::Underscore => (),
                TokenKind::QuestionMark => (),
                TokenKind::Semicolon => (),
                TokenKind::Arrow => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::Colon => (),
                TokenKind::Newline => (),
                TokenKind::Dot => (),
                TokenKind::Plus => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::Minus => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::Slash => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::Star => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::Equals => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::Bang => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::Less => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::LessEquals => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::Greater => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::GreaterEquals => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::Tilde => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::PlusEquals => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::MinusEquals => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::StarEquals => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::SlashEquals => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::EqualsEquals => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::BangEquals => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::TildeEquals => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::Caret => (),
                TokenKind::CaretEquals => (),
                TokenKind::Pipe => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::PipePipe => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::Amp => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::AmpEquals => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::LeftBrace => (),
                TokenKind::RightBrace => (),
                TokenKind::LeftParen => (),
                TokenKind::RightParen => (),
                TokenKind::LeftBracket => (),
                TokenKind::RightBracket => (),
                TokenKind::Comma => (),
                TokenKind::Struct => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::Break => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::Int(_) => self.make(tok, Kind::NUMBER, &mut tokens),
                TokenKind::Float(_) => self.make(tok, Kind::NUMBER, &mut tokens),
                TokenKind::Identifier(_) => (),
                TokenKind::Func => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::Let => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::EOF => break,
                TokenKind::Generated => (),
                TokenKind::Init => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::Mut => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::Protocol => self.make(tok, Kind::KEYWORD, &mut tokens),
            }
        }

        for tok in lexer.comments.iter() {
            tracing::info!("Got a comment token: {tok:?}");
            self.make(tok, Kind::COMMENT, &mut tokens)
        }

        tokens
    }

    fn tokens_from_expr(&self, expr: &ParsedExpr) -> Vec<HighlightToken> {
        let mut result = vec![];

        let Some(meta) = self.source_file.meta.get(&expr.id) else {
            return vec![];
        };

        let start = meta.start.start;
        let end = meta.end.end;

        match &expr.expr {
            Expr::Incomplete(e) => match e {
                IncompleteExpr::Member(rec) => {
                    if let Some(receiver) = rec {
                        result.extend(self.tokens_from_expr(&receiver))
                    }
                }
                IncompleteExpr::Func { .. } => (),
            },
            Expr::LiteralString(_) => (), // already handled by lexed
            Expr::LiteralArray(items) => result.extend(self.tokens_from_exprs(&items)),
            Expr::LiteralInt(_) | Expr::LiteralFloat(_) => {
                result.push(HighlightToken::new(Kind::NUMBER, start, end));
            }
            Expr::LiteralTrue | Expr::LiteralFalse => {
                result.push(HighlightToken::new(Kind::KEYWORD, start, end))
            }
            Expr::Unary(_token_kind, rhs) => result.extend(self.tokens_from_expr(&rhs)),
            Expr::Binary(box lhs, _token_kind, box rhs) => {
                result.extend(self.tokens_from_expr_refs(&[lhs, rhs]))
            }
            Expr::Tuple(items) => {
                result.push(HighlightToken::new(Kind::KEYWORD, start, end));
                result.extend(self.tokens_from_exprs(&items));
            }
            Expr::Break => result.push(HighlightToken::new(Kind::KEYWORD, start, end)),
            Expr::Block(items) => result.extend(self.tokens_from_exprs(&items)),
            Expr::Call {
                callee,
                type_args,
                args,
            } => {
                result.extend(self.tokens_from_expr(&callee));
                result.extend(self.tokens_from_exprs(&type_args));
                result.extend(self.tokens_from_exprs(&args));
            }
            Expr::ParsedPattern(pattern) => match pattern {
                Pattern::LiteralInt(_) => {
                    result.push(HighlightToken::new(Kind::NUMBER, start, end))
                }
                Pattern::LiteralFloat(_) => {
                    result.push(HighlightToken::new(Kind::NUMBER, start, end))
                }
                Pattern::LiteralTrue => result.push(HighlightToken::new(Kind::KEYWORD, start, end)),
                Pattern::LiteralFalse => {
                    result.push(HighlightToken::new(Kind::KEYWORD, start, end))
                }
                Pattern::Bind(_name) => {}
                Pattern::Wildcard => {}
                Pattern::Variant { fields, .. } => result.extend(self.tokens_from_exprs(&fields)),
            },
            Expr::Return(rhs) => {
                if let Some(rhs) = rhs {
                    result.extend(self.tokens_from_expr(&rhs))
                }
            }
            Expr::Struct {
                generics,
                conformances,
                body,
                ..
            } => {
                result.extend(self.tokens_from_exprs(&generics));
                result.extend(self.tokens_from_exprs(&conformances));
                result.extend(self.tokens_from_expr(&body));
            }
            Expr::Extend {
                generics,
                conformances,
                body,
                ..
            } => {
                result.extend(self.tokens_from_exprs(&generics));
                result.extend(self.tokens_from_exprs(&conformances));
                result.extend(self.tokens_from_expr(&body));
            }
            Expr::Property {
                name: _name,
                type_repr,
                default_value,
            } => {
                if let Some(type_repr) = type_repr {
                    result.extend(self.tokens_from_expr(&type_repr));
                }
                if let Some(default_value) = default_value {
                    result.extend(self.tokens_from_expr(&default_value));
                }
            }
            Expr::TypeRepr {
                generics,
                conformances,
                ..
            } => {
                if let Some(meta) = self.source_file.meta.get(&expr.id) {
                    result.extend(
                        meta.identifiers
                            .iter()
                            .map(|i| HighlightToken::new(Kind::TYPE_PARAMETER, i.start, i.end)),
                    )
                }
                result.extend(self.tokens_from_exprs(&generics));
                result.extend(self.tokens_from_exprs(&conformances));
            }
            Expr::FuncTypeRepr(items, ret, _) => {
                result.extend(self.tokens_from_exprs(&items));
                result.extend(self.tokens_from_expr(&ret));
            }
            Expr::TupleTypeRepr(items, _) => {
                result.extend(self.tokens_from_exprs(&items));
            }
            Expr::Member(receiver, _) => {
                if let Some(receiver) = receiver {
                    result.extend(self.tokens_from_expr(&receiver));
                }
            }
            Expr::Func {
                generics,
                params,
                body,
                ret,
                ..
            } => {
                result.extend(self.tokens_from_exprs(&generics));
                result.extend(self.tokens_from_exprs(&params));
                result.extend(self.tokens_from_expr(&body));
                if let Some(ret) = ret {
                    result.extend(self.tokens_from_expr(&ret));
                }
            }
            Expr::Init(_, func_id) => result.extend(self.tokens_from_expr(&func_id)),
            Expr::Parameter(_name, ty) => {
                if let Some(ty) = ty {
                    result.extend(self.tokens_from_expr(&ty));
                }
            }
            Expr::Let(_name, rhs) => {
                if let Some(rhs) = rhs {
                    result.extend(self.tokens_from_expr(&rhs));
                }
            }
            Expr::Assignment(box lhs, box rhs) => {
                result.extend(self.tokens_from_expr_refs(&[lhs, rhs]))
            }
            Expr::Variable(_name) => {}
            Expr::If(cond, then, alt) => {
                result.extend(self.tokens_from_expr(&cond));
                result.extend(self.tokens_from_expr(&then));
                if let Some(alt) = alt {
                    result.extend(self.tokens_from_expr(&alt));
                }
            }
            Expr::Loop(cond, body) => {
                if let Some(cond) = cond {
                    result.extend(self.tokens_from_expr(&cond));
                }
                result.extend(self.tokens_from_expr(&body));
            }
            Expr::EnumDecl { generics, body, .. } => {
                result.extend(self.tokens_from_exprs(generics));
                result.extend(self.tokens_from_expr(&body));
            }
            Expr::EnumVariant(_name, items) => result.extend(self.tokens_from_exprs(&items)),
            Expr::Match(_, items) => result.extend(self.tokens_from_exprs(&items)),
            Expr::MatchArm(box pattern, box body) => {
                result.extend(self.tokens_from_expr_refs(&[pattern, body]))
            }
            Expr::PatternVariant(_name, _name1, items) => {
                result.extend(self.tokens_from_exprs(&items))
            }
            Expr::CallArg { value, .. } => {
                if let Some(meta) = self.source_file.meta.get(&expr.id) {
                    result.extend(
                        meta.identifiers
                            .iter()
                            .map(|i| HighlightToken::new(Kind::PROPERTY, i.start, i.end)),
                    )
                }

                result.extend(self.tokens_from_expr(&value));
            }
            Expr::ProtocolDecl {
                associated_types,
                body,
                conformances,
                ..
            } => {
                result.extend(self.tokens_from_exprs(&associated_types));
                result.extend(self.tokens_from_expr(&body));
                result.extend(self.tokens_from_exprs(&conformances));
            }
            Expr::FuncSignature {
                params,
                generics,
                ret,
                ..
            } => {
                result.extend(self.tokens_from_exprs(&params));
                result.extend(self.tokens_from_exprs(&generics));
                result.extend(self.tokens_from_expr(&ret));
            }
        };

        result
    }

    fn tokens_from_expr_refs(&self, exprs: &[&ParsedExpr]) -> Vec<HighlightToken> {
        exprs
            .iter()
            .flat_map(|e| self.tokens_from_expr(e))
            .collect()
    }

    fn tokens_from_exprs(&self, exprs: &[ParsedExpr]) -> Vec<HighlightToken> {
        exprs
            .iter()
            .flat_map(|e| self.tokens_from_expr(e))
            .collect()
    }

    fn make(&self, token: &Token, token_type: Kind, tokens: &mut Vec<HighlightToken>) {
        tokens.push(HighlightToken::new(token_type, token.start, token.end));
    }

    fn make_string(&self, token: &Token, token_type: Kind, tokens: &mut Vec<HighlightToken>) {
        tokens.push(HighlightToken::new(
            token_type,
            token.start.saturating_sub(1),
            token.end.saturating_add(1),
        ));
    }
}
