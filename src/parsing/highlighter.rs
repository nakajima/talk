use crate::{
    ast::{AST, Parsed},
    label::Label,
    lexer::Lexer,
    node::Node,
    node_id::FileID,
    node_kinds::{
        decl::DeclKind,
        expr::ExprKind,
        pattern::{PatternKind, RecordFieldPatternKind},
        record_field::RecordFieldTypeAnnotation,
        stmt::StmtKind,
        type_annotation::TypeAnnotationKind,
    },
    parser::Parser,
    span::Span,
    token::Token,
    token_kind::TokenKind,
};

#[derive(Debug, Copy, Clone)]
#[allow(non_camel_case_types)]
pub enum Kind {
    DECORATOR,
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
    EFFECT,
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
}

impl<'a> Higlighter<'a> {
    pub fn new(source: &'a str) -> Self {
        Self { source }
    }

    pub fn highlight(&mut self) -> Vec<HighlightToken> {
        let mut result = vec![];

        let lexer = Lexer::preserving_comments(self.source);

        result.extend(self.collect_lexed_tokens(lexer.clone()));

        let parser = Parser::new("-", FileID(0), lexer);
        let Ok(ast) = parser.parse() else {
            return result;
        };

        for root in ast.0.roots.iter() {
            result.extend(self.tokens_from_expr(&root, &ast.0));
        }

        result
    }

    fn collect_lexed_tokens(&mut self, mut lexer: Lexer) -> Vec<HighlightToken> {
        let mut tokens: Vec<HighlightToken> = vec![];

        while let Ok(tok) = &lexer.next() {
            match tok.kind {
                TokenKind::Continue => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::SingleQuote => (),
                TokenKind::In => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::EffectName(..) => {
                    let mut tok = tok.clone();
                    tok.start = tok.start.saturating_sub(1);
                    self.make(&tok, Kind::EFFECT, &mut tokens)
                }
                TokenKind::Handling => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::Effect => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::Dollar => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::BoundVar(..) => self.make(tok, Kind::VARIABLE, &mut tokens),
                TokenKind::Percent => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::IRRegister(..) => self.make(tok, Kind::PARAMETER, &mut tokens),
                TokenKind::Attribute(..) => self.make(tok, Kind::DECORATOR, &mut tokens),
                TokenKind::As => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::At => self.make(tok, Kind::DECORATOR, &mut tokens),
                TokenKind::LineComment(_) => self.make(tok, Kind::COMMENT, &mut tokens),
                TokenKind::Extend => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::If => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::Else => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::Loop => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::Return => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::True => self.make(tok, Kind::NUMBER, &mut tokens),
                TokenKind::False => self.make(tok, Kind::NUMBER, &mut tokens),
                TokenKind::Enum => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::Case => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::Match => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::Import => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::StringLiteral(_) => self.make_string(tok, Kind::STRING, &mut tokens),
                TokenKind::Underscore => (),
                TokenKind::QuestionMark => self.make(tok, Kind::OPERATOR, &mut tokens),
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
                TokenKind::AmpAmp => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::Caret => self.make(tok, Kind::OPERATOR, &mut tokens),
                TokenKind::CaretEquals => self.make(tok, Kind::OPERATOR, &mut tokens),
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
                TokenKind::DotDot | TokenKind::DotDotDot => {
                    self.make(tok, Kind::OPERATOR, &mut tokens)
                }
                TokenKind::Associated => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::Typealias => self.make(tok, Kind::KEYWORD, &mut tokens),
                TokenKind::Static => self.make(tok, Kind::KEYWORD, &mut tokens),
            }
        }

        for tok in lexer.comments.iter() {
            tracing::info!("Got a comment token: {tok:?}");
            self.make(tok, Kind::COMMENT, &mut tokens)
        }

        tokens
    }

    fn tokens_from_expr<T: Into<Node> + Clone>(
        &self,
        node: &T,
        ast: &AST<Parsed>,
    ) -> Vec<HighlightToken> {
        let mut result = vec![];
        let node: Node = node.clone().into();

        let Some(meta) = ast.meta.get(&node.node_id()) else {
            return vec![];
        };

        let start = meta.start.start;
        let end = meta.end.end;

        match &node {
            Node::InlineIRInstruction(_ir) => {}
            Node::Attribute(..) => {
                result.push(HighlightToken {
                    kind: Kind::DECORATOR,
                    start,
                    end,
                });
            }
            Node::Decl(decl) => match &decl.kind {
                DeclKind::Effect {
                    name_span,
                    params,
                    ret,
                    ..
                } => {
                    result.push(self.make_span(Kind::EFFECT, *name_span));
                    result.extend(self.tokens_from_exprs(params, ast));
                    result.extend(self.tokens_from_expr(ret, ast));
                }
                DeclKind::Import(_) => (),
                DeclKind::Struct {
                    generics,
                    body,
                    name_span,
                    ..
                } => {
                    result.push(self.make_span(Kind::TYPE, *name_span));
                    result.extend(self.tokens_from_exprs(generics, ast));
                    result.extend(self.tokens_from_expr(body, ast));
                }
                DeclKind::Let {
                    lhs,
                    type_annotation,
                    rhs: value,
                } => {
                    result.extend(self.tokens_from_expr(lhs, ast));

                    if let Some(node) = type_annotation {
                        result.extend(self.tokens_from_expr(node, ast));
                    }

                    if let Some(node) = value {
                        result.extend(self.tokens_from_expr(node, ast));
                    }
                }
                DeclKind::Protocol {
                    generics,
                    body,
                    conformances,
                    name_span,
                    ..
                } => {
                    result.push(self.make_span(Kind::INTERFACE, *name_span));
                    result.extend(self.tokens_from_exprs(generics, ast));
                    result.extend(self.tokens_from_exprs(conformances, ast));
                    result.extend(self.tokens_from_expr(body, ast));
                }
                DeclKind::Init { params, body, .. } => {
                    result.extend(self.tokens_from_exprs(params, ast));
                    result.extend(self.tokens_from_expr(body, ast));
                }
                DeclKind::Property {
                    type_annotation,
                    default_value,
                    ..
                } => {
                    if let Some(node) = type_annotation {
                        result.extend(self.tokens_from_expr(node, ast));
                    }

                    if let Some(node) = default_value {
                        result.extend(self.tokens_from_expr(node, ast));
                    }
                }
                DeclKind::Method { box func, .. } => {
                    result.extend(self.tokens_from_expr(func, ast));
                }
                DeclKind::Associated { generic } => {
                    result.extend(self.tokens_from_expr(generic, ast));
                }
                DeclKind::Func(func) => {
                    result.extend(self.tokens_from_expr(func, ast));
                }
                DeclKind::Extend {
                    conformances,
                    generics,
                    body,
                    name_span,
                    ..
                } => {
                    result.push(self.make_span(Kind::TYPE, *name_span));
                    result.extend(self.tokens_from_exprs(generics, ast));
                    result.extend(self.tokens_from_exprs(conformances, ast));
                    result.extend(self.tokens_from_expr(body, ast));
                }
                DeclKind::Enum {
                    generics,
                    body,
                    name_span,
                    ..
                } => {
                    result.push(self.make_span(Kind::TYPE, *name_span));
                    result.extend(self.tokens_from_exprs(generics, ast));
                    result.extend(self.tokens_from_expr(body, ast));
                }
                DeclKind::EnumVariant(.., name_span, type_annotations) => {
                    result.push(self.make_span(Kind::ENUM_MEMBER, *name_span));
                    result.extend(self.tokens_from_exprs(type_annotations, ast));
                }
                DeclKind::FuncSignature(func_signature) => {
                    result.extend(self.tokens_from_expr(func_signature, ast));
                }
                DeclKind::MethodRequirement(func_signature) => {
                    result.extend(self.tokens_from_expr(func_signature, ast));
                }
                DeclKind::TypeAlias(.., lhs_span, rhs) => {
                    result.push(self.make_span(Kind::TYPE, *lhs_span));
                    result.extend(self.tokens_from_expr(rhs, ast));
                }
            },
            Node::Func(func) => {
                result.push(self.make_span(Kind::FUNCTION, func.name_span));
                result.extend(self.tokens_from_exprs(&func.params, ast));
                result.extend(self.tokens_from_expr(&func.body, ast));
                result.extend(self.tokens_from_exprs(&func.attributes, ast));
                if let Some(ret) = &func.ret {
                    result.extend(self.tokens_from_expr(ret, ast));
                }
            }
            Node::GenericDecl(generic_decl) => {
                result.push(self.make_span(Kind::TYPE_PARAMETER, generic_decl.name_span));
                result.extend(self.tokens_from_exprs(&generic_decl.conformances, ast));
                result.extend(self.tokens_from_exprs(&generic_decl.generics, ast));
            }
            Node::Parameter(parameter) => {
                result.push(self.make_span(Kind::PARAMETER, parameter.name_span));
                if let Some(ty) = &parameter.type_annotation {
                    result.extend(self.tokens_from_expr(&ty, ast));
                }
            }
            Node::TypeAnnotation(type_annotation) => match &type_annotation.kind {
                TypeAnnotationKind::Nominal {
                    name_span,
                    generics,
                    ..
                } => {
                    result.push(self.make_span(Kind::TYPE, *name_span));
                    result.extend(self.tokens_from_exprs(generics, ast));
                }
                TypeAnnotationKind::SelfType(..) => {
                    result.push(self.make_span(Kind::TYPE, node.span()));
                }
                TypeAnnotationKind::Func {
                    params,
                    box returns,
                } => {
                    result.extend(self.tokens_from_exprs(params, ast));
                    result.extend(self.tokens_from_expr(&returns, ast));
                }
                TypeAnnotationKind::NominalPath {
                    box base,
                    member: _,
                    member_span,
                    member_generics,
                } => {
                    result.extend(self.tokens_from_expr(base, ast));
                    result.push(self.make_span(Kind::TYPE, *member_span));
                    result.extend(self.tokens_from_exprs(member_generics, ast));
                }
                TypeAnnotationKind::Tuple(type_annotations) => {
                    result.extend(self.tokens_from_exprs(type_annotations, ast));
                }
                TypeAnnotationKind::Record { fields } => {
                    for RecordFieldTypeAnnotation {
                        label_span, value, ..
                    } in fields
                    {
                        result.push(self.make_span(Kind::PARAMETER, *label_span));
                        result.extend(self.tokens_from_expr(value, ast));
                    }
                }
            },
            Node::Stmt(stmt) => match &stmt.kind {
                StmtKind::Expr(expr) => {
                    result.extend(self.tokens_from_expr(expr, ast));
                }
                StmtKind::Continue(expr) => {
                    if let Some(expr) = expr {
                        result.extend(self.tokens_from_expr(expr, ast))
                    }
                }
                StmtKind::If(cond, conseq, alt) => {
                    result.extend(self.tokens_from_expr(cond, ast));
                    result.extend(self.tokens_from_expr(conseq, ast));
                    if let Some(alt) = alt {
                        result.extend(self.tokens_from_expr(alt, ast));
                    }
                }
                StmtKind::Return(expr) => {
                    if let Some(expr) = expr {
                        result.extend(self.tokens_from_expr(expr, ast));
                    }
                }
                StmtKind::Break => {
                    result.push(self.make_span(Kind::KEYWORD, stmt.span));
                }
                StmtKind::Assignment(lhs, rhs) => {
                    result.extend(self.tokens_from_expr(lhs, ast));
                    result.extend(self.tokens_from_expr(rhs, ast));
                }
                StmtKind::Loop(cond, block) => {
                    if let Some(cond) = cond {
                        result.extend(self.tokens_from_expr(cond, ast));
                    }

                    result.extend(self.tokens_from_expr(block, ast));
                }
            },
            Node::Expr(expr) => match &expr.kind {
                ExprKind::Incomplete(..) => (),
                ExprKind::Handling {
                    effect_name_span,
                    body,
                    ..
                } => {
                    result.push(self.make_span(Kind::EFFECT, *effect_name_span));
                    result.extend(self.tokens_from_expr(body, ast));
                }
                ExprKind::CallEffect {
                    effect_name_span,
                    args,
                    ..
                } => {
                    result.push(self.make_span(Kind::EFFECT, *effect_name_span));
                    result.extend(self.tokens_from_exprs(args, ast));
                }
                ExprKind::LiteralArray(exprs) => {
                    result.extend(self.tokens_from_exprs(exprs, ast));
                }
                ExprKind::As(box lhs, rhs) => {
                    result.extend(self.tokens_from_expr(lhs, ast));
                    result.extend(self.tokens_from_expr(rhs, ast));
                }
                // Literals are handled by tokens pass
                ExprKind::LiteralInt(_) => (),
                ExprKind::LiteralFloat(_) => (),
                ExprKind::LiteralTrue => (),
                ExprKind::LiteralFalse => (),
                ExprKind::LiteralString(_) => (),
                ExprKind::Unary(.., box expr) => result.extend(self.tokens_from_expr(expr, ast)),
                ExprKind::Binary(box lhs, _, box rhs) => {
                    result.extend(self.tokens_from_expr(lhs, ast));
                    result.extend(self.tokens_from_expr(rhs, ast));
                }
                ExprKind::Tuple(items) => {
                    result.extend(self.tokens_from_exprs(items, ast));
                }
                ExprKind::Block(block) => {
                    result.extend(self.tokens_from_exprs(&block.body, ast));
                }
                ExprKind::Call {
                    box callee,
                    type_args,
                    args,
                } => {
                    result.extend(self.tokens_from_expr(callee, ast));
                    result.extend(self.tokens_from_exprs(type_args, ast));
                    result.extend(self.tokens_from_exprs(args, ast));
                }
                ExprKind::Member(receiver, ..) => {
                    if let Some(box receiver) = receiver {
                        result.extend(self.tokens_from_expr(receiver, ast));
                    }
                }
                ExprKind::Func(func) => {
                    result.extend(self.tokens_from_expr(&func.body, ast));
                    result.extend(self.tokens_from_exprs(&func.params, ast));
                }
                ExprKind::Variable(name) => {
                    if name.name_str() == "self"
                        || name.name_str().chars().next().map(|c| c.is_uppercase()) == Some(true)
                    {
                        result.push(self.make_span(Kind::TYPE, expr.span));
                    } else {
                        result.push(self.make_span(Kind::VARIABLE, expr.span));
                    }
                }
                ExprKind::Constructor(..) => {
                    result.push(self.make_span(Kind::TYPE, expr.span));
                }
                ExprKind::If(box cond, conseq, alt) => {
                    result.extend(self.tokens_from_expr(cond, ast));
                    result.extend(self.tokens_from_expr(conseq, ast));
                    result.extend(self.tokens_from_expr(alt, ast));
                }
                ExprKind::Match(box scrutinee, arms) => {
                    result.extend(self.tokens_from_expr(scrutinee, ast));
                    result.extend(self.tokens_from_exprs(arms, ast));
                }
                ExprKind::RecordLiteral { fields, .. } => {
                    for field in fields {
                        result.push(self.make_span(Kind::PARAMETER, field.label_span));
                        result.extend(self.tokens_from_expr(&field.value, ast));
                    }
                }
                ExprKind::RowVariable(..) => (),
                ExprKind::InlineIR(instr) => {
                    result.push(self.make_span(Kind::KEYWORD, instr.instr_name_span))
                }
            },
            Node::Body(body) => {
                result.extend(self.tokens_from_exprs(&body.decls, ast));
            }
            Node::Pattern(pattern) => match &pattern.kind {
                PatternKind::Tuple(patterns) => {
                    result.extend(self.tokens_from_exprs(patterns, ast));
                }
                PatternKind::Or(patterns) => {
                    result.extend(self.tokens_from_exprs(patterns, ast));
                }
                PatternKind::Variant {
                    variant_name_span,
                    fields,
                    ..
                } => {
                    result.push(self.make_span(Kind::ENUM_MEMBER, *variant_name_span));
                    result.extend(self.tokens_from_exprs(fields, ast));
                }
                PatternKind::Record { fields } => {
                    for field in fields {
                        match &field.kind {
                            RecordFieldPatternKind::Bind(..) => {
                                result.push(self.make_span(Kind::PARAMETER, field.span));
                            }
                            RecordFieldPatternKind::Equals {
                                name_span, value, ..
                            } => {
                                result.push(self.make_span(Kind::PARAMETER, *name_span));
                                result.extend(self.tokens_from_expr(value, ast));
                            }
                            _ => (),
                        }
                    }
                }
                PatternKind::Struct { .. } => (),
                _ => (),
            },
            Node::MatchArm(arm) => {
                result.extend(self.tokens_from_expr(&arm.pattern, ast));
                result.extend(self.tokens_from_expr(&arm.body, ast));
            }
            Node::Block(block) => {
                result.extend(self.tokens_from_exprs(&block.body, ast));
            }
            Node::RecordField(field) => {
                result.push(self.make_span(Kind::PROPERTY, field.label_span));
                result.extend(self.tokens_from_expr(&field.value, ast));
            }
            Node::IncompleteExpr(..) => (),
            Node::CallArg(arg) => {
                if matches!(arg.label, Label::Named(..)) {
                    result.push(self.make_span(Kind::PARAMETER, arg.label_span));
                }
                result.extend(self.tokens_from_expr(&arg.value, ast));
            }
            Node::FuncSignature(signature) => {
                result.extend(self.tokens_from_exprs(&signature.params, ast));
                if let Some(box ret) = &signature.ret {
                    result.extend(self.tokens_from_expr(ret, ast));
                }
            }
        };

        result
    }

    fn tokens_from_exprs<T: Into<Node> + Clone>(
        &self,
        exprs: &[T],
        ast: &AST<Parsed>,
    ) -> Vec<HighlightToken> {
        exprs
            .iter()
            .flat_map(|e| self.tokens_from_expr(e, ast))
            .collect()
    }

    fn make_span(&self, kind: Kind, span: Span) -> HighlightToken {
        HighlightToken {
            kind,
            start: span.start,
            end: span.end,
        }
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

pub fn highlight_html(source: &str) -> String {
    let mut highlighter = Higlighter::new(source);
    let mut tokens = highlighter.highlight();
    tokens.sort_by(|a, b| a.start.cmp(&b.start).then_with(|| b.end.cmp(&a.end)));
    render_html_with_tokens(source, &tokens)
}

pub fn render_html_with_tokens(source: &str, tokens: &[HighlightToken]) -> String {
    let mut output = String::with_capacity(source.len() + tokens.len() * 32);
    let mut cursor = 0usize;

    for token in tokens {
        let start = token.start as usize;
        let end = token.end as usize;
        if start >= end || start < cursor || end > source.len() {
            continue;
        }

        if let Some(prefix) = source.get(cursor..start) {
            push_escaped(&mut output, prefix);
            cursor = start;
        } else {
            continue;
        }

        if let Some(slice) = source.get(start..end) {
            output.push_str("<span class=\"");
            output.push_str(&token.kind.to_string());
            output.push_str("\">");
            push_escaped(&mut output, slice);
            output.push_str("</span>");
            cursor = end;
        }
    }

    if let Some(tail) = source.get(cursor..) {
        push_escaped(&mut output, tail);
    }

    output
}

fn push_escaped(output: &mut String, text: &str) {
    for ch in text.chars() {
        match ch {
            '&' => output.push_str("&amp;"),
            '<' => output.push_str("&lt;"),
            '>' => output.push_str("&gt;"),
            _ => output.push(ch),
        }
    }
}
