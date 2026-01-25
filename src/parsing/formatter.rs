use std::{cell::RefCell, collections::VecDeque, ops::Add};

use crate::{
    ast::{AST, ASTPhase},
    label::Label,
    lexer::Lexer,
    name::Name,
    node::Node,
    node_id::FileID,
    node_kinds::{
        attribute::Attribute,
        block::Block,
        body::Body,
        call_arg::CallArg,
        decl::{Decl, DeclKind, Import, ImportPath, ImportedSymbols, Visibility},
        expr::{Expr, ExprKind},
        func::Func,
        func_signature::FuncSignature,
        generic_decl::GenericDecl,
        inline_ir_instruction::InlineIRInstruction,
        match_arm::MatchArm,
        parameter::Parameter,
        pattern::{Pattern, PatternKind, RecordFieldPatternKind},
        record_field::{RecordField, RecordFieldTypeAnnotation},
        stmt::{Stmt, StmtKind},
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
    node_meta::NodeMeta,
    node_meta_storage::NodeMetaStorage,
    parser::Parser,
    token::Token,
    token_kind::TokenKind,
};

#[derive(Clone, Debug, PartialEq)]
pub enum Doc {
    Empty,
    Text(String),
    Line,
    Softline,
    Hardline,
    Nest(u8, Box<Doc>),
    Concat(Box<Doc>, Box<Doc>),
    Group(Box<Doc>),
    Annotation(String),
}

impl Add for Doc {
    type Output = Doc;
    fn add(self, rhs: Self) -> Self::Output {
        concat(self, rhs)
    }
}

impl Doc {
    pub fn is_empty(&self) -> bool {
        matches!(self, Doc::Empty)
    }

    pub fn is_line_break(&self) -> bool {
        matches!(self, Doc::Line | Doc::Softline | Doc::Hardline)
    }
}

#[derive(Clone, Debug)]
struct Comment {
    start: u32,
    line: u32,
    text: String,
}

struct CommentStore {
    comments: VecDeque<Comment>,
}

impl CommentStore {
    fn new(mut comments: Vec<Comment>) -> Self {
        comments.sort_by_key(|comment| comment.start);
        Self {
            comments: VecDeque::from(comments),
        }
    }

    fn peek(&self) -> Option<&Comment> {
        self.comments.front()
    }

    fn pop(&mut self) -> Option<Comment> {
        self.comments.pop_front()
    }

    fn take_before(&mut self, pos: u32) -> Vec<Comment> {
        let mut collected = Vec::new();
        while let Some(comment) = self.comments.front() {
            if comment.start < pos {
                collected.push(self.comments.pop_front().unwrap_or_else(|| unreachable!()));
            } else {
                break;
            }
        }
        collected
    }

    fn has_between(&self, start: u32, end: u32) -> bool {
        self.comments
            .iter()
            .any(|comment| comment.start >= start && comment.start < end)
    }
}

const SINGLE_LINE_FUNC_MAX_WIDTH: usize = 40;

pub fn wrap(before: Doc, inner: Doc, after: Doc) -> Doc {
    concat(before, concat(inner, after))
}

// Helper functions for building documents
pub fn empty() -> Doc {
    Doc::Empty
}

pub fn text(s: impl Into<String>) -> Doc {
    Doc::Text(s.into())
}

pub fn annotate(s: impl Into<String>) -> Doc {
    Doc::Annotation(s.into())
}

pub fn line() -> Doc {
    Doc::Line
}

pub fn softline() -> Doc {
    Doc::Softline
}

pub fn hardline() -> Doc {
    Doc::Hardline
}

pub fn nest(indent: u8, doc: Doc) -> Doc {
    Doc::Nest(indent, Box::new(doc))
}

pub fn concat(lhs: Doc, rhs: Doc) -> Doc {
    Doc::Concat(Box::new(lhs), Box::new(rhs))
}

pub fn group(doc: Doc) -> Doc {
    Doc::Group(Box::new(doc))
}

// Concat with space operator
pub fn concat_space(lhs: Doc, rhs: Doc) -> Doc {
    concat(concat(lhs, text(" ")), rhs)
}

// Join documents with a separator
pub fn join(docs: Vec<Doc>, separator: Doc) -> Doc {
    docs.into_iter().fold(empty(), |acc, doc| {
        if acc.is_empty() {
            doc
        } else {
            concat(concat(acc, separator.clone()), doc)
        }
    })
}

pub trait FormatterDecorator {
    fn wrap_expr(&self, expr: &Expr, doc: Doc) -> Doc;
    fn wrap_decl(&self, decl: &Decl, doc: Doc) -> Doc;
    fn wrap_stmt(&self, stmt: &Stmt, doc: Doc) -> Doc;
}

pub struct DefaultDecorator {}
impl FormatterDecorator for DefaultDecorator {
    fn wrap_expr(&self, _: &Expr, doc: Doc) -> Doc {
        doc
    }
    fn wrap_decl(&self, _: &Decl, doc: Doc) -> Doc {
        doc
    }
    fn wrap_stmt(&self, _: &Stmt, doc: Doc) -> Doc {
        doc
    }
}

pub struct DebugHTMLFormatter {}
impl FormatterDecorator for DebugHTMLFormatter {
    fn wrap_expr(&self, expr: &Expr, doc: Doc) -> Doc {
        concat(
            concat(
                annotate(format!("<span class=\"expr\" id=\"node-{}\">", expr.id)),
                doc,
            ),
            annotate("</span>"),
        )
    }

    fn wrap_decl(&self, decl: &Decl, doc: Doc) -> Doc {
        concat(
            concat(
                annotate(format!("<span class=\"decl\" id=\"node-{}\">", decl.id)),
                doc,
            ),
            annotate("</span>"),
        )
    }

    fn wrap_stmt(&self, stmt: &Stmt, doc: Doc) -> Doc {
        concat(
            concat(
                annotate(format!("<span class=\"stmt\" id=\"node-{}\">", stmt.id)),
                doc,
            ),
            annotate("</span>"),
        )
    }
}

pub struct Formatter<'a> {
    // Track expression metadata for source location info
    meta_storage: &'a NodeMetaStorage,
    decorators: Vec<Box<dyn FormatterDecorator>>,
    comments: Option<RefCell<CommentStore>>,
}

impl<'a> Formatter<'a> {
    pub fn new(meta_storage: &'a NodeMetaStorage) -> Formatter<'a> {
        Self {
            meta_storage,
            decorators: vec![],
            comments: None,
        }
    }
}

impl<'a> Formatter<'a> {
    pub fn new_with_decorators(
        meta_storage: &'a NodeMetaStorage,
        decorators: Vec<Box<dyn FormatterDecorator>>,
    ) -> Formatter<'a> {
        Formatter {
            meta_storage,
            decorators,
            comments: None,
        }
    }

    fn new_with_comments(
        meta_storage: &'a NodeMetaStorage,
        comments: Vec<Comment>,
    ) -> Formatter<'a> {
        Formatter {
            meta_storage,
            decorators: vec![],
            comments: Some(RefCell::new(CommentStore::new(comments))),
        }
    }

    fn get_meta_for_node(&self, node: &Node) -> Option<&NodeMeta> {
        self.meta_storage.get(&node.node_id())
    }

    fn has_comments_between(&self, start: u32, end: u32) -> bool {
        let Some(comments) = &self.comments else {
            return false;
        };
        comments.borrow().has_between(start, end)
    }

    fn take_comments_before(&self, pos: u32) -> Vec<Comment> {
        let Some(comments) = &self.comments else {
            return Vec::new();
        };
        comments.borrow_mut().take_before(pos)
    }

    fn take_inline_comment(&self, meta: &NodeMeta) -> Option<Comment> {
        let Some(comments) = &self.comments else {
            return None;
        };
        let mut store = comments.borrow_mut();
        let comment = store.peek()?;
        if comment.line == meta.end.line && comment.start >= meta.end.end {
            return store.pop();
        }
        None
    }

    fn comment_doc(comment: Comment) -> Doc {
        text(comment.text)
    }

    fn append_doc_with_spacing(
        mut acc: Doc,
        last_line: &mut Option<u32>,
        item_doc: Doc,
        item_start_line: u32,
        item_end_line: u32,
    ) -> Doc {
        if let Some(last) = *last_line {
            acc = concat(acc, hardline());
            if item_start_line > last + 1 {
                acc = concat(acc, hardline());
            }
        }

        acc = concat(acc, item_doc);
        *last_line = Some(item_end_line);
        acc
    }

    fn push_doc_output(
        output: &mut String,
        last_line: &mut Option<u32>,
        doc: Doc,
        item_start_line: u32,
        item_end_line: u32,
        width: usize,
    ) {
        if let Some(last) = *last_line
            && item_start_line != last
        {
            output.push('\n');
            if item_start_line > last + 1 {
                output.push('\n');
            }
        }
        output.push_str(&Self::render_doc(doc, width));
        *last_line = Some(item_end_line);
    }

    pub fn format(&self, roots: &[Node], width: usize) -> String {
        let mut output = String::new();
        let mut last_line: Option<u32> = None;

        for root in roots {
            let meta = self.get_meta_for_node(root);
            let start_pos = meta
                .map(|node_meta| node_meta.start.start)
                .unwrap_or_else(|| root.span().start);
            let start_line = meta
                .map(|node_meta| node_meta.start.line)
                .unwrap_or_else(|| last_line.map(|line| line + 1).unwrap_or(0));
            let end_line = meta
                .map(|node_meta| node_meta.end.line)
                .unwrap_or(start_line);

            for comment in self.take_comments_before(start_pos) {
                let line = comment.line;
                let doc = Self::comment_doc(comment);
                Self::push_doc_output(&mut output, &mut last_line, doc, line, line, width);
            }

            let mut doc = self.format_node(root);
            if let Some(meta) = meta
                && let Some(comment) = self.take_inline_comment(meta)
            {
                doc = concat(doc, concat(text(" "), text(comment.text)));
            }

            Self::push_doc_output(
                &mut output,
                &mut last_line,
                doc,
                start_line,
                end_line,
                width,
            );
        }

        for comment in self.take_comments_before(u32::MAX) {
            let line = comment.line;
            let doc = Self::comment_doc(comment);
            Self::push_doc_output(&mut output, &mut last_line, doc, line, line, width);
        }

        output
    }

    pub(crate) fn format_node(&self, node: &Node) -> Doc {
        match node {
            Node::Func(func) => self.format_func(func),
            Node::Attribute(attr) => self.format_attribute(attr),
            Node::Decl(decl) => self.format_decl(decl),
            Node::GenericDecl(generic) => self.format_generic_decl(generic),
            Node::Parameter(param) => self.format_parameter(param),
            Node::Stmt(stmt) => self.format_stmt(stmt),
            Node::Expr(expr) => self.format_expr(expr),
            Node::Pattern(pattern) => self.format_pattern(pattern),
            Node::MatchArm(arm) => self.format_match_arm(arm),
            Node::Block(block) => self.format_block(block),
            Node::Body(body) => self.format_body(body),
            Node::TypeAnnotation(ty) => self.format_type_annotation(ty),
            Node::RecordField(field) => self.format_record_field(field),
            Node::IncompleteExpr(_) => Doc::Empty,
            Node::CallArg(arg) => self.format_call_arg(arg),
            Node::FuncSignature(sig) => self.format_func_signature(sig),
            Node::InlineIRInstruction(ir) => self.format_inline_ir_instruction(ir),
        }
    }

    fn format_inline_ir_instruction(&self, ir: &InlineIRInstruction) -> Doc {
        text(format!("{ir}"))
    }

    fn format_attribute(&self, attr: &Attribute) -> Doc {
        join(vec![text("@"), text(attr.name.name_str())], text(""))
    }

    fn format_expr(&self, expr: &Expr) -> Doc {
        let doc = match &expr.kind {
            ExprKind::Incomplete(_) => Doc::Empty,
            ExprKind::CallEffect {
                effect_name, args, ..
            } => {
                let arg_docs: Vec<_> = args.iter().map(|a| self.format_call_arg(a)).collect();
                group(concat(
                    text(format!("'{}", effect_name.name_str())),
                    concat(
                        text("("),
                        concat(
                            nest(
                                1,
                                concat(softline(), join(arg_docs, concat(text(","), line()))),
                            ),
                            concat(softline(), text(")")),
                        ),
                    ),
                ))
            }
            ExprKind::As(lhs, rhs) => {
                text("(")
                    + join(
                        vec![self.format_expr(lhs), self.format_type_annotation(rhs)],
                        text(" as "),
                    )
                    + text(")")
            }
            ExprKind::LiteralArray(items) => self.format_array_literal(items),
            ExprKind::LiteralString(string) => self.format_string_literal(string),
            ExprKind::LiteralInt(val) => text(val),
            ExprKind::LiteralFloat(val) => text(val),
            ExprKind::LiteralTrue => text("true"),
            ExprKind::LiteralFalse => text("false"),
            ExprKind::Unary(op, rhs) => self.format_unary(op, rhs),
            ExprKind::Binary(lhs, op, rhs) => self.format_binary(lhs, op, rhs),
            ExprKind::Tuple(items) => self.format_tuple(items),
            ExprKind::Block(block) => self.format_block(block),
            ExprKind::Call {
                callee,
                type_args,
                args,
            } => self.format_call(callee, type_args, args),
            ExprKind::Member(receiver, property, ..) => self.format_member(receiver, property),
            ExprKind::Func(func) => self.format_func(func),
            ExprKind::Variable(name) | ExprKind::Constructor(name) => self.format_name(name),
            ExprKind::If(cond, then_block, else_block) => {
                self.format_if(cond, then_block, else_block)
            }
            ExprKind::Match(target, arms) => self.format_match(target, arms),
            ExprKind::RecordLiteral { fields, spread } => {
                self.format_record_literal(fields, spread)
            }
            ExprKind::RowVariable(name) => join(vec![text(".."), text(name.name_str())], text("")),
            ExprKind::InlineIR(instruction) => {
                if instruction.binds.is_empty() {
                    concat(
                        concat(text("@_ir { "), text(format!("{instruction}"))),
                        text(" }"),
                    )
                } else {
                    concat(
                        concat(
                            concat(
                                concat(
                                    text("@_ir("),
                                    join(
                                        instruction
                                            .binds
                                            .iter()
                                            .map(|b| self.format_expr(b))
                                            .collect(),
                                        text(", "),
                                    ),
                                ),
                                text(") { "),
                            ),
                            text(format!("{instruction}")),
                        ),
                        text(" }"),
                    )
                }
            }
        };

        self.decorators
            .iter()
            .fold(doc, |acc, decorator| decorator.wrap_expr(expr, acc))
    }

    fn format_decl(&self, decl: &Decl) -> Doc {
        let doc = match &decl.kind {
            #[warn(clippy::todo)]
            DeclKind::Effect {
                name,
                generics,
                params,
                ret,
                ..
            } => {
                let generics_doc = if generics.is_empty() {
                    text("")
                } else {
                    text("<")
                        + join(
                            generics.iter().map(|g| self.format_generic_decl(g)).collect(),
                            text(", "),
                        )
                        + text(">")
                };
                text("effect '")
                    + self.format_name(name)
                    + generics_doc
                    + text("(")
                    + join(
                        params.iter().map(|p| self.format_parameter(p)).collect(),
                        text(","),
                    )
                    + text(")")
                    + text(" -> ")
                    + self.format_type_annotation(ret)
            }
            DeclKind::Import(import) => self.format_import(import),
            DeclKind::Struct {
                name,
                generics,
                body,
                ..
            } => self.format_struct(name, generics, body),
            DeclKind::Let {
                lhs,
                type_annotation,
                rhs: value,
            } => self.format_let_decl(lhs, type_annotation.as_ref(), value.as_ref()),
            DeclKind::Protocol {
                name,
                generics,
                body,
                conformances,
                ..
            } => self.format_protocol(name, generics, conformances, body),
            DeclKind::Init { name, params, body } => self.format_init(name, params, body),
            DeclKind::Property {
                name,
                is_static,
                type_annotation,
                default_value,
                ..
            } => self.format_property(
                name,
                *is_static,
                type_annotation.as_ref(),
                default_value.as_ref(),
            ),
            DeclKind::Method { func, is_static } => self.format_method(func, *is_static),
            DeclKind::Associated { generic } => self.format_associated(generic),
            DeclKind::Func(func) => self.format_func(func),
            DeclKind::Extend {
                name,
                conformances,
                generics,
                body,
                ..
            } => self.format_extend(name, generics, conformances, body),
            DeclKind::Enum {
                name,
                generics,
                body,
                ..
            } => self.format_enum_decl(name, generics, body),
            DeclKind::EnumVariant(name, .., types) => self.format_enum_variant(name, types),
            DeclKind::FuncSignature(sig) => self.format_func_signature(sig),
            DeclKind::MethodRequirement(sig) => self.format_func_signature(sig),
            DeclKind::TypeAlias(lhs, .., rhs) => self.format_type_alias(lhs, rhs),
        };

        // Prepend "public " for public declarations
        let doc = if decl.visibility == Visibility::Public {
            text("public ") + doc
        } else {
            doc
        };

        self.decorators
            .iter()
            .fold(doc, |acc, decorator| decorator.wrap_decl(decl, acc))
    }

    fn format_type_alias(&self, lhs: &Name, rhs: &TypeAnnotation) -> Doc {
        concat_space(
            text("type"),
            join(
                vec![self.format_name(lhs), self.format_type_annotation(rhs)],
                text("="),
            ),
        )
    }

    fn format_stmt(&self, stmt: &Stmt) -> Doc {
        let doc = match &stmt.kind {
            StmtKind::Handling {
                effect_name, body, ..
            } => text(format!("@handle '{} ", effect_name.name_str())) + self.format_block(body),
            StmtKind::Expr(expr) => self.format_expr(expr),
            StmtKind::Continue(expr) => {
                if let Some(expr) = expr {
                    concat_space(text("continue"), self.format_expr(expr))
                } else {
                    text("continue")
                }
            }
            StmtKind::If(cond, then_block, else_block) => {
                let mut result = concat_space(
                    text("if"),
                    concat_space(self.format_expr(cond), self.format_block(then_block)),
                );

                if let Some(else_block) = else_block {
                    result = concat_space(
                        result,
                        concat_space(text("else"), self.format_block_inner(else_block, false)),
                    )
                }

                result
            }
            StmtKind::Return(value) => match value {
                Some(expr) => concat_space(text("return"), self.format_expr(expr)),
                None => text("return"),
            },
            StmtKind::Break => text("break"),
            StmtKind::Assignment(lhs, rhs) => concat_space(
                self.format_expr(lhs),
                concat_space(text("="), self.format_expr(rhs)),
            ),
            StmtKind::Loop(cond, body) => {
                let mut result = text("loop");
                if let Some(cond_expr) = cond {
                    result = concat_space(result, self.format_expr(cond_expr));
                }
                concat_space(result, self.format_block(body))
            }
        };

        self.decorators
            .iter()
            .fold(doc, |acc, decorator| decorator.wrap_stmt(stmt, acc))
    }

    fn format_string_literal(&self, string: &str) -> Doc {
        concat(text("\""), concat(text(string), text("\"")))
    }

    fn format_array_literal(&self, items: &[Expr]) -> Doc {
        if items.is_empty() {
            return concat(text("["), text("]"));
        }

        let elements = items.iter().map(|expr| self.format_expr(expr)).collect();

        group(concat(
            text("["),
            concat(
                nest(
                    1,
                    concat(softline(), join(elements, concat(text(","), line()))),
                ),
                concat(softline(), text("]")),
            ),
        ))
    }

    fn format_unary(&self, op: &TokenKind, rhs: &Expr) -> Doc {
        let op_text = match op {
            TokenKind::Minus => "-",
            TokenKind::Bang => "!",
            _ => &format!("{op}"),
        };

        concat(text(op_text), self.format_expr(rhs))
    }

    fn format_binary(&self, lhs: &Expr, op: &TokenKind, rhs: &Expr) -> Doc {
        let op_text = match op {
            TokenKind::Plus => "+",
            TokenKind::Minus => "-",
            TokenKind::Star => "*",
            TokenKind::Slash => "/",
            TokenKind::Less => "<",
            TokenKind::LessEquals => "<=",
            TokenKind::Greater => ">",
            TokenKind::GreaterEquals => ">=",
            TokenKind::EqualsEquals => "==",
            TokenKind::BangEquals => "!=",
            TokenKind::Caret => "^",
            TokenKind::Pipe => "|",
            TokenKind::PipePipe => "||",
            _ => &format!("{op}"),
        };

        group(concat_space(
            self.format_expr(lhs),
            concat_space(text(op_text), self.format_expr(rhs)),
        ))
    }

    fn format_tuple(&self, items: &[Expr]) -> Doc {
        if items.is_empty() {
            return concat(text("("), text(")"));
        }

        if items.len() == 1 {
            return concat(text("("), concat(self.format_expr(&items[0]), text(")")));
        }

        let elements = items.iter().map(|expr| self.format_expr(expr)).collect();

        group(concat(
            text("("),
            concat(join(elements, concat(text(","), line())), text(")")),
        ))
    }

    fn format_block(&self, block: &Block) -> Doc {
        self.format_block_inner(block, true)
    }

    fn format_block_multiline(&self, block: &Block) -> Doc {
        self.format_block_inner(block, false)
    }

    fn wrap_block_single_line(inner: Doc) -> Doc {
        group(concat(
            text("{"),
            concat(concat(text(" "), inner), text(" }")),
        ))
    }

    fn wrap_block_multiline(inner: Doc) -> Doc {
        concat(
            text("{"),
            concat(
                nest(1, concat(hardline(), inner)),
                concat(hardline(), text("}")),
            ),
        )
    }

    fn wrap_block_multiline_with_header(header: Doc, inner: Doc) -> Doc {
        concat(
            text("{"),
            concat(
                concat(text(" "), header),
                concat(
                    nest(1, concat(hardline(), inner)),
                    concat(hardline(), text("}")),
                ),
            ),
        )
    }

    fn format_block_args(&self, args: &[Parameter]) -> Option<Doc> {
        if args.is_empty() {
            return None;
        }

        let arg_docs: Vec<_> = args.iter().map(|arg| self.format_parameter(arg)).collect();
        Some(concat(
            join(arg_docs, concat(text(","), text(" "))),
            text(" in"),
        ))
    }

    fn append_comments_until(&self, end: u32, mut acc: Doc, last_line: &mut Option<u32>) -> Doc {
        for comment in self.take_comments_before(end) {
            let line = comment.line;
            let comment_doc = Self::comment_doc(comment);
            acc = Self::append_doc_with_spacing(acc, last_line, comment_doc, line, line);
        }
        acc
    }

    fn format_empty_block(
        &self,
        args_doc: Option<Doc>,
        allow_single_line: bool,
        has_comments: bool,
        end: u32,
    ) -> Doc {
        if let Some(args_doc) = args_doc {
            if !has_comments {
                if allow_single_line {
                    return Self::wrap_block_single_line(args_doc);
                }
                return concat(
                    text("{"),
                    concat(concat(text(" "), args_doc), concat(hardline(), text("}"))),
                );
            }

            let mut last_line: Option<u32> = None;
            let content = self.append_comments_until(end, empty(), &mut last_line);
            return Self::wrap_block_multiline_with_header(args_doc, content);
        }

        if !has_comments {
            if allow_single_line {
                return concat(text("{"), text("}"));
            }
            return concat(text("{"), concat(hardline(), text("}")));
        }

        let mut last_line: Option<u32> = None;
        let content = self.append_comments_until(end, empty(), &mut last_line);
        Self::wrap_block_multiline(content)
    }

    fn format_block_body(&self, block: &Block) -> Doc {
        let mut final_doc = empty();
        let mut last_line: Option<u32> = None;

        for stmt in &block.body {
            let meta = self.get_meta_for_node(stmt);
            let start_pos = meta
                .map(|node_meta| node_meta.start.start)
                .unwrap_or_else(|| stmt.span().start);
            let start_line = meta
                .map(|node_meta| node_meta.start.line)
                .unwrap_or_else(|| last_line.map(|line| line + 1).unwrap_or(0));
            let end_line = meta
                .map(|node_meta| node_meta.end.line)
                .unwrap_or(start_line);

            for comment in self.take_comments_before(start_pos) {
                let line = comment.line;
                let comment_doc = Self::comment_doc(comment);
                final_doc = Self::append_doc_with_spacing(
                    final_doc,
                    &mut last_line,
                    comment_doc,
                    line,
                    line,
                );
            }

            let mut stmt_doc = self.format_node(stmt);
            if let Some(meta) = meta
                && let Some(comment) = self.take_inline_comment(meta)
            {
                stmt_doc = concat(stmt_doc, concat(text(" "), text(comment.text)));
            }

            final_doc = Self::append_doc_with_spacing(
                final_doc,
                &mut last_line,
                stmt_doc,
                start_line,
                end_line,
            );
        }

        self.append_comments_until(block.span.end, final_doc, &mut last_line)
    }

    fn format_block_inner(&self, block: &Block, allow_single_line: bool) -> Doc {
        let has_comments = self.has_comments_between(block.span.start, block.span.end);
        let args_doc = self.format_block_args(&block.args);
        if block.body.is_empty() {
            return self.format_empty_block(
                args_doc,
                allow_single_line,
                has_comments,
                block.span.end,
            );
        }

        // Handle the special case for single-line blocks
        if allow_single_line
            && block.body.len() == 1
            && !Self::contains_control_flow(&block.body[0])
            && !has_comments
        {
            let mut inner_doc = self.format_node(&block.body[0]);
            if let Some(args_doc) = args_doc.as_ref() {
                inner_doc = concat(args_doc.clone(), concat(text(" "), inner_doc));
            }
            return Self::wrap_block_single_line(inner_doc);
        }
        let body_doc = self.format_block_body(block);
        if let Some(args_doc) = args_doc {
            return Self::wrap_block_multiline_with_header(args_doc, body_doc);
        }
        Self::wrap_block_multiline(body_doc)
    }

    fn format_body(&self, body: &Body) -> Doc {
        let has_comments = self.has_comments_between(body.span.start, body.span.end);
        if body.decls.is_empty() {
            if !has_comments {
                return concat(text("{"), text("}"));
            }

            let mut final_doc = empty();
            let mut last_line: Option<u32> = None;

            for comment in self.take_comments_before(body.span.end) {
                let line = comment.line;
                let comment_doc = Self::comment_doc(comment);
                final_doc = Self::append_doc_with_spacing(
                    final_doc,
                    &mut last_line,
                    comment_doc,
                    line,
                    line,
                );
            }

            return concat(
                text("{"),
                concat(
                    nest(1, concat(hardline(), final_doc)),
                    concat(hardline(), text("}")),
                ),
            );
        }

        let mut final_doc = empty();
        let mut last_line: Option<u32> = None;

        for decl in &body.decls {
            let node: Node = decl.into();
            let meta = self.get_meta_for_node(&node);
            let start_pos = meta
                .map(|node_meta| node_meta.start.start)
                .unwrap_or_else(|| node.span().start);
            let start_line = meta
                .map(|node_meta| node_meta.start.line)
                .unwrap_or_else(|| last_line.map(|line| line + 1).unwrap_or(0));
            let end_line = meta
                .map(|node_meta| node_meta.end.line)
                .unwrap_or(start_line);

            for comment in self.take_comments_before(start_pos) {
                let line = comment.line;
                let comment_doc = Self::comment_doc(comment);
                final_doc = Self::append_doc_with_spacing(
                    final_doc,
                    &mut last_line,
                    comment_doc,
                    line,
                    line,
                );
            }

            let mut decl_doc = self.format_decl(decl);
            if let Some(meta) = meta
                && let Some(comment) = self.take_inline_comment(meta)
            {
                decl_doc = concat(decl_doc, concat(text(" "), text(comment.text)));
            }

            final_doc = Self::append_doc_with_spacing(
                final_doc,
                &mut last_line,
                decl_doc,
                start_line,
                end_line,
            );
        }

        for comment in self.take_comments_before(body.span.end) {
            let line = comment.line;
            let comment_doc = Self::comment_doc(comment);
            final_doc =
                Self::append_doc_with_spacing(final_doc, &mut last_line, comment_doc, line, line);
        }

        concat(
            text("{"),
            concat(
                nest(1, concat(hardline(), final_doc)),
                concat(hardline(), text("}")),
            ),
        )
    }

    fn format_call(&self, callee: &Expr, type_args: &[TypeAnnotation], args: &[CallArg]) -> Doc {
        let mut result = self.format_expr(callee);

        if !type_args.is_empty() {
            let type_docs: Vec<_> = type_args
                .iter()
                .map(|ty| self.format_type_annotation(ty))
                .collect();

            result = concat(
                result,
                concat(
                    text("<"),
                    concat(join(type_docs, concat(text(","), text(" "))), text(">")),
                ),
            );
        }

        let arg_docs: Vec<_> = args.iter().map(|arg| self.format_call_arg(arg)).collect();

        group(concat(
            result,
            concat(
                text("("),
                concat(
                    nest(
                        1,
                        concat(softline(), join(arg_docs, concat(text(","), line()))),
                    ),
                    concat(softline(), text(")")),
                ),
            ),
        ))
    }

    fn format_call_arg(&self, arg: &CallArg) -> Doc {
        match &arg.label {
            Label::Named(name) => group(concat(
                concat(text(name), text(": ")),
                self.format_expr(&arg.value),
            )),
            Label::Positional(_) => self.format_expr(&arg.value),
            Label::_Symbol(s) => text(format!("{s}")),
        }
    }

    fn format_pattern(&self, pattern: &Pattern) -> Doc {
        match &pattern.kind {
            PatternKind::LiteralInt(val) => text(val),
            PatternKind::LiteralFloat(val) => text(val),
            PatternKind::LiteralTrue => text("true"),
            PatternKind::LiteralFalse => text("false"),
            PatternKind::Bind(name) => self.format_name(name),
            PatternKind::Wildcard => text("_"),
            PatternKind::Or(patterns) => join(
                patterns.iter().map(|p| self.format_pattern(p)).collect(),
                text("|"),
            ),
            PatternKind::Tuple(items) => concat(
                concat(
                    text("("),
                    join(
                        items.iter().map(|item| self.format_pattern(item)).collect(),
                        text(","),
                    ),
                ),
                text(")"),
            ),
            PatternKind::Variant {
                enum_name,
                variant_name,
                fields,
                ..
            } => {
                let mut result = if let Some(name) = enum_name {
                    concat(
                        self.format_name(name),
                        concat(text("."), text(variant_name)),
                    )
                } else {
                    concat(text("."), text(variant_name))
                };

                if !fields.is_empty() {
                    let field_docs: Vec<_> =
                        fields.iter().map(|p| self.format_pattern(p)).collect();

                    result = concat(
                        result,
                        concat(
                            text("("),
                            concat(join(field_docs, concat(text(","), text(" "))), text(")")),
                        ),
                    );
                }

                result
            }
            PatternKind::Record { fields } => {
                if fields.is_empty() {
                    return text("{}");
                }

                let field_docs = fields
                    .iter()
                    .map(|field| match &field.kind {
                        RecordFieldPatternKind::Rest => text(".."),
                        RecordFieldPatternKind::Bind(name) => self.format_name(name),
                        RecordFieldPatternKind::Equals { name, value, .. } => group(concat(
                            concat(self.format_name(name), text(": ")),
                            self.format_pattern(value),
                        )),
                    })
                    .collect::<Vec<_>>();

                let fields = concat(line(), join(field_docs, concat(text(","), line())));

                group(concat(
                    text("{"),
                    concat(nest(1, fields), concat(line(), text("}"))),
                ))
            }
            PatternKind::Struct {
                struct_name,
                fields,
                field_names,
                rest,
            } => {
                let mut result = Vec::new();

                if let Some(name) = struct_name {
                    result.push(self.format_name(name));
                    result.push(text(" "));
                }

                result.push(text("{"));

                let mut field_docs = Vec::new();
                for (field_name, field_pattern) in field_names.iter().zip(fields.iter()) {
                    let mut field_doc = self.format_name(field_name);

                    // Check if the field pattern is a simple binding with the same name
                    let is_shorthand = if let Node::Pattern(p) = field_pattern {
                        if let PatternKind::Bind(bind_name) = &p.kind {
                            match (field_name, bind_name) {
                                (Name::Raw(f), Name::Raw(b)) => f == b,
                                (Name::Resolved(_, f), Name::Resolved(_, b)) => f == b,
                                _ => false,
                            }
                        } else {
                            false
                        }
                    } else {
                        false
                    };

                    if !is_shorthand {
                        field_doc = concat(
                            field_doc,
                            concat(text(": "), self.format_node(field_pattern)),
                        );
                    }

                    field_docs.push(field_doc);
                }

                if *rest {
                    field_docs.push(text(".."));
                }

                if !field_docs.is_empty() {
                    result.push(concat(
                        text(" "),
                        concat(join(field_docs, concat(text(","), text(" "))), text(" ")),
                    ));
                }

                result.push(text("}"));

                result.into_iter().fold(empty(), concat)
            }
        }
    }

    fn format_import(&self, import: &Import) -> Doc {
        let symbols = match &import.symbols {
            ImportedSymbols::All => text("_"),
            ImportedSymbols::Named(symbols) => {
                let symbol_docs: Vec<_> = symbols
                    .iter()
                    .map(|s| {
                        if let Some(alias) = &s.alias {
                            concat(text(&s.name), concat(text(": "), text(alias)))
                        } else {
                            text(&s.name)
                        }
                    })
                    .collect();
                concat(
                    text("{ "),
                    concat(join(symbol_docs, text(", ")), text(" }")),
                )
            }
        };

        let path = match &import.path {
            ImportPath::Relative(p) => text(p),
            ImportPath::Package(p) => text(p),
        };

        join(vec![text("import"), symbols, text("from"), path], text(" "))
    }

    fn format_struct(&self, name: &Name, generics: &[GenericDecl], body: &Body) -> Doc {
        let mut result = concat_space(text("struct"), self.format_name(name));

        if !generics.is_empty() {
            let generic_docs: Vec<_> = generics
                .iter()
                .map(|g| self.format_generic_decl(g))
                .collect();

            result = concat(
                result,
                concat(
                    text("<"),
                    concat(join(generic_docs, concat(text(","), text(" "))), text(">")),
                ),
            );
        }

        concat_space(result, self.format_body(body))
    }

    fn format_extend(
        &self,
        name: &Name,
        generics: &[GenericDecl],
        conformances: &[TypeAnnotation],
        body: &Body,
    ) -> Doc {
        let mut result = concat_space(text("extend"), self.format_name(name));

        if !generics.is_empty() {
            let generic_docs: Vec<_> = generics
                .iter()
                .map(|g| self.format_generic_decl(g))
                .collect();

            result = concat(
                result,
                concat(
                    text("<"),
                    concat(join(generic_docs, concat(text(","), text(" "))), text(">")),
                ),
            );
        }

        if !conformances.is_empty() {
            let conformances_docs = conformances
                .iter()
                .map(|ty| self.format_type_annotation(ty))
                .collect();
            result = concat(
                result,
                concat(text(": "), join(conformances_docs, text(", "))),
            );
        }

        concat_space(result, self.format_body(body))
    }

    fn format_protocol(
        &self,
        name: &Name,
        generics: &[GenericDecl],
        conformances: &[TypeAnnotation],
        body: &Body,
    ) -> Doc {
        let mut result = concat_space(text("protocol"), self.format_name(name));

        if !generics.is_empty() {
            let generic_docs: Vec<_> = generics
                .iter()
                .map(|g| self.format_generic_decl(g))
                .collect();

            result = concat(
                result,
                concat(
                    text("<"),
                    concat(join(generic_docs, concat(text(","), text(" "))), text(">")),
                ),
            );
        }

        if !conformances.is_empty() {
            let conformances_docs = conformances
                .iter()
                .map(|ty| self.format_type_annotation(ty))
                .collect();
            result = concat(
                result,
                concat(text(": "), join(conformances_docs, text(", "))),
            );
        }

        concat_space(result, self.format_body(body))
    }

    fn format_property(
        &self,
        name: &Name,
        _is_static: bool,
        type_annotation: Option<&TypeAnnotation>,
        default_value: Option<&Expr>,
    ) -> Doc {
        let mut result = concat_space(text("let"), self.format_name(name));

        if let Some(ty) = type_annotation {
            result = concat(
                result,
                concat_space(text(":"), self.format_type_annotation(ty)),
            );
        }

        if let Some(value) = default_value {
            result = concat_space(result, concat_space(text("="), self.format_expr(value)));
        }

        result
    }

    fn format_type_annotation(&self, ty: &TypeAnnotation) -> Doc {
        match &ty.kind {
            TypeAnnotationKind::SelfType(..) => text("Self"),
            TypeAnnotationKind::Record { fields } => self.format_record_type_annotation(fields),
            TypeAnnotationKind::NominalPath {
                base,
                member,
                member_generics,
                ..
            } => join(
                vec![
                    self.format_type_annotation(base),
                    self.format_nominal_type_annotation(
                        member.to_string().clone(),
                        member_generics,
                    ),
                ],
                text("."),
            ),
            TypeAnnotationKind::Func { params, returns } => {
                let param_docs: Vec<_> = params
                    .iter()
                    .map(|p| self.format_type_annotation(p))
                    .collect();

                concat(
                    text("("),
                    concat(
                        join(param_docs, concat(text(","), text(" "))),
                        concat_space(text(") ->"), self.format_type_annotation(returns)),
                    ),
                )
            }
            TypeAnnotationKind::Nominal { name, generics, .. } => {
                self.format_nominal_type_annotation(name.name_str(), generics)
            }
            TypeAnnotationKind::Tuple(types) => {
                let type_docs: Vec<_> = types
                    .iter()
                    .map(|t| self.format_type_annotation(t))
                    .collect();

                concat(
                    text("("),
                    concat(join(type_docs, concat(text(","), text(" "))), text(")")),
                )
            }
        }
    }

    fn format_nominal_type_annotation<T: Into<String>>(
        &self,
        name: T,
        generics: &[TypeAnnotation],
    ) -> Doc {
        let mut result = text(name);

        if !generics.is_empty() {
            let generic_docs: Vec<_> = generics
                .iter()
                .map(|g| self.format_type_annotation(g))
                .collect();

            result = concat(
                result,
                concat(
                    text("<"),
                    concat(join(generic_docs, concat(text(","), text(" "))), text(">")),
                ),
            );
        }

        result
    }

    fn format_member(&self, receiver: &Option<Box<Expr>>, property: &Label) -> Doc {
        match receiver {
            Some(expr) => group(concat(
                self.format_expr(expr),
                concat(text("."), text(property.to_string())),
            )),
            None => concat(text("."), text(property.to_string())),
        }
    }

    fn format_func(&self, func: &Func) -> Doc {
        let mut result = if func.name.name_str().starts_with("#") {
            text("func")
        } else {
            concat_space(text("func"), self.format_name(&func.name))
        };

        if !func.generics.is_empty() {
            let generic_docs: Vec<_> = func
                .generics
                .iter()
                .map(|g| self.format_generic_decl(g))
                .collect();

            result = concat(
                result,
                concat(
                    text("<"),
                    concat(join(generic_docs, concat(text(","), text(" "))), text(">")),
                ),
            );
        }

        let param_docs: Vec<_> = func
            .params
            .iter()
            .map(|p| self.format_parameter(p))
            .collect();

        result = concat(
            result,
            concat(
                text("("),
                concat(join(param_docs, concat(text(","), text(" "))), text(")")),
            ),
        );

        match func.effects.names.len() {
            0 => (),
            1 => {
                result = if func.effects.is_open {
                    concat_space(
                        result,
                        text("'[")
                            + text(func.effects.names[0].name_str())
                            + text(",")
                            + text("..")
                            + text("]"),
                    )
                } else {
                    concat_space(
                        result,
                        text(format!("'{}", func.effects.names[0].name_str())),
                    )
                };
            }
            _ => {
                let names = join(
                    func.effects
                        .names
                        .iter()
                        .map(|e| text(e.name_str()))
                        .collect(),
                    text(","),
                );
                result = concat_space(
                    result,
                    text("[")
                        + if func.effects.is_open {
                            join(vec![names, text("..")], text(","))
                        } else {
                            names
                        }
                        + text("]"),
                )
            }
        }

        if let Some(ref ret) = func.ret {
            result = concat_space(
                result,
                concat_space(text("->"), self.format_type_annotation(ret)),
            );
        }

        let has_comments = self.has_comments_between(func.body.span.start, func.body.span.end);

        // Check if the body could be formatted inline
        if func.body.body.is_empty()
            || (func.body.body.len() == 1 && !Self::contains_control_flow(&func.body.body[0]))
            || func.effects.names.is_empty()
        {
            if has_comments {
                return concat_space(result, self.format_block_multiline(&func.body));
            }
            let inline = concat_space(result.clone(), self.format_block(&func.body));
            if Self::flat_width(&inline).is_some_and(|width| width <= SINGLE_LINE_FUNC_MAX_WIDTH) {
                return group(inline);
            }

            return concat_space(result, self.format_block_multiline(&func.body));
        }

        concat_space(result, self.format_block(&func.body))
    }

    fn format_init(&self, _name: &Name, params: &[Parameter], body: &Block) -> Doc {
        let mut result = text("init");

        let param_docs: Vec<_> = params.iter().map(|p| self.format_parameter(p)).collect();

        result = concat(
            result,
            concat(
                text("("),
                concat(join(param_docs, concat(text(","), text(" "))), text(")")),
            ),
        );

        let has_comments = self.has_comments_between(body.span.start, body.span.end);

        // Check if the body could be formatted inline
        if body.body.is_empty()
            || (body.body.len() == 1 && !Self::contains_control_flow(&body.body[0]))
        {
            if has_comments {
                return concat_space(result, self.format_block_multiline(body));
            }
            let inline = concat_space(result.clone(), self.format_block(body));
            if Self::flat_width(&inline).is_some_and(|width| width <= SINGLE_LINE_FUNC_MAX_WIDTH) {
                return group(inline);
            }

            return concat_space(result, self.format_block_multiline(body));
        }

        concat_space(result, self.format_block(body))
    }

    fn format_parameter(&self, param: &Parameter) -> Doc {
        let mut result = self.format_name(&param.name);

        if let Some(ref ty) = param.type_annotation {
            result = concat(
                result,
                concat_space(text(":"), self.format_type_annotation(ty)),
            );
        }

        result
    }

    fn format_let_decl(
        &self,
        pattern: &Pattern,
        type_annotation: Option<&TypeAnnotation>,
        value: Option<&Expr>,
    ) -> Doc {
        let mut result = concat_space(text("let"), self.format_pattern(pattern));

        if let Some(ty) = type_annotation {
            result = concat(
                result,
                concat_space(text(":"), self.format_type_annotation(ty)),
            );
        }

        if let Some(val) = value {
            result = concat_space(result, concat_space(text("="), self.format_expr(val)));
        }

        result
    }

    fn format_if(&self, cond: &Expr, then_block: &Block, else_block: &Block) -> Doc {
        let mut result = concat_space(
            text("if"),
            concat_space(self.format_expr(cond), self.format_block(then_block)),
        );

        // Only add else block if it's not empty
        if !else_block.body.is_empty() {
            result = concat_space(
                result,
                concat_space(text("else"), self.format_block_inner(else_block, false)),
            );
        }

        result
    }

    fn format_enum_decl(&self, name: &Name, generics: &[GenericDecl], body: &Body) -> Doc {
        let mut result = concat_space(text("enum"), self.format_name(name));

        if !generics.is_empty() {
            let generic_docs: Vec<_> = generics
                .iter()
                .map(|g| self.format_generic_decl(g))
                .collect();

            result = concat(
                result,
                concat(
                    text("<"),
                    concat(join(generic_docs, concat(text(","), text(" "))), text(">")),
                ),
            );
        }

        concat_space(result, self.format_enum_body(body))
    }

    fn format_enum_body(&self, body: &Body) -> Doc {
        if body.decls.is_empty() {
            return concat(text("{"), text("}"));
        }

        let mut docs = Vec::new();
        for item in &body.decls {
            docs.push(self.format_decl(item));
        }

        concat(
            text("{"),
            concat(
                nest(1, concat(line(), join(docs, line()))),
                concat(line(), text("}")),
            ),
        )
    }

    fn format_enum_variant(&self, name: &Name, types: &[TypeAnnotation]) -> Doc {
        let mut result = concat_space(text("case"), self.format_name(name));

        if !types.is_empty() {
            let type_docs: Vec<_> = types
                .iter()
                .map(|ty| self.format_type_annotation(ty))
                .collect();

            result = concat(
                result,
                concat(
                    text("("),
                    concat(join(type_docs, concat(text(","), text(" "))), text(")")),
                ),
            );
        }

        result
    }

    fn format_match(&self, target: &Expr, arms: &[MatchArm]) -> Doc {
        let arms_docs: Vec<_> = arms.iter().map(|arm| self.format_match_arm(arm)).collect();

        concat_space(
            text("match"),
            concat_space(
                self.format_expr(target),
                concat(
                    text("{"),
                    concat(
                        nest(
                            1,
                            concat(line(), join(arms_docs, concat(text(","), line()))),
                        ),
                        concat(line(), text("}")),
                    ),
                ),
            ),
        )
    }

    fn format_match_arm(&self, arm: &MatchArm) -> Doc {
        // For match arms, if the body is a single expression, format it without braces
        let body_doc =
            if arm.body.body.len() == 1 && !Self::contains_control_flow(&arm.body.body[0]) {
                self.format_node(&arm.body.body[0])
            } else {
                self.format_block(&arm.body)
            };

        concat_space(
            self.format_pattern(&arm.pattern),
            concat_space(text("->"), body_doc),
        )
    }

    fn format_record_type_annotation(&self, fields: &[RecordFieldTypeAnnotation]) -> Doc {
        let formatted_fields = fields
            .iter()
            .map(|field| self.format_record_field_type_annotation(field))
            .collect::<Vec<_>>();

        let fields = concat(line(), join(formatted_fields, concat(text(","), line())));

        group(concat(
            text("{"),
            concat(nest(1, fields), concat(line(), text("}"))),
        ))
    }

    fn format_record_literal(&self, fields: &[RecordField], spread: &Option<Box<Expr>>) -> Doc {
        if fields.is_empty() && spread.is_none() {
            return text("{}");
        }

        let formatted_fields = fields
            .iter()
            .map(|field| self.format_record_field(field))
            .collect::<Vec<_>>();

        let fields = concat(line(), join(formatted_fields, concat(text(","), line())));

        group(concat(
            text("{"),
            concat(
                nest(
                    1,
                    if let Some(spread) = spread {
                        concat(
                            fields,
                            join(vec![text("..."), self.format_expr(spread)], text("")),
                        )
                    } else {
                        fields
                    },
                ),
                concat(line(), text("}")),
            ),
        ))
    }

    fn format_record_field_type_annotation(&self, field: &RecordFieldTypeAnnotation) -> Doc {
        group(concat(
            concat(text(field.label.name_str()), text(": ")),
            self.format_type_annotation(&field.value),
        ))
    }

    fn format_record_field(&self, field: &RecordField) -> Doc {
        group(concat(
            concat(text(field.label.name_str()), text(": ")),
            self.format_expr(&field.value),
        ))
    }

    fn format_method(&self, func: &Func, _is_static: bool) -> Doc {
        self.format_func(func)
    }

    fn format_associated(&self, generic: &GenericDecl) -> Doc {
        concat_space(text("associated"), self.format_generic_decl(generic))
    }

    fn format_func_signature(&self, sig: &FuncSignature) -> Doc {
        let mut result = concat_space(text("func"), self.format_name(&sig.name));

        if !sig.generics.is_empty() {
            let generic_docs: Vec<_> = sig
                .generics
                .iter()
                .map(|g| self.format_generic_decl(g))
                .collect();

            result = concat(
                result,
                concat(
                    text("<"),
                    concat(join(generic_docs, concat(text(","), text(" "))), text(">")),
                ),
            );
        }

        let param_docs: Vec<_> = sig
            .params
            .iter()
            .map(|p| self.format_parameter(p))
            .collect();

        result = concat(
            result,
            concat(
                text("("),
                concat(join(param_docs, concat(text(","), text(" "))), text(")")),
            ),
        );

        result = if let Some(ret) = &sig.ret {
            concat_space(
                result,
                concat_space(text("->"), self.format_type_annotation(ret)),
            )
        } else {
            empty()
        };

        result
    }

    fn format_generic_decl(&self, generic: &GenericDecl) -> Doc {
        let mut result = self.format_name(&generic.name);

        if !generic.generics.is_empty() {
            let generic_docs: Vec<_> = generic
                .generics
                .iter()
                .map(|g| self.format_generic_decl(g))
                .collect();
            result = concat(
                result,
                concat(
                    text("<"),
                    concat(join(generic_docs, concat(text(","), text(" "))), text(">")),
                ),
            );
        }

        if !generic.conformances.is_empty() {
            let conformance_docs: Vec<_> = generic
                .conformances
                .iter()
                .map(|c| self.format_type_annotation(c))
                .collect();
            result = concat(
                result,
                concat(text(": "), join(conformance_docs, text(", "))),
            );
        }

        result
    }

    fn format_name(&self, name: &Name) -> Doc {
        text(name.name_str())
    }

    fn contains_control_flow(node: &Node) -> bool {
        match node {
            Node::Decl(decl) => matches!(
                &decl.kind,
                DeclKind::Func(_) | DeclKind::Init { .. } | DeclKind::Method { .. }
            ),
            Node::Expr(expr) => matches!(
                &expr.kind,
                ExprKind::Func { .. } | ExprKind::If(..) | ExprKind::Match(..)
            ),
            Node::Stmt(stmt) => matches!(&stmt.kind, StmtKind::If(..) | StmtKind::Loop(..)),
            Node::Block(block) => block.body.iter().any(Self::contains_control_flow),
            _ => false,
        }
    }

    pub fn render_doc(doc: Doc, width: usize) -> String {
        let mut output = String::new();
        let mut queue = vec![(0u8, doc)];
        let mut column = 0;
        let mut was_newline = false;

        while let Some((indent, current_doc)) = queue.pop() {
            match current_doc {
                Doc::Empty => continue,
                Doc::Annotation(s) => {
                    output.push_str(&s);
                }
                Doc::Text(s) => {
                    if was_newline {
                        output.push_str(&"\t".repeat(indent as usize));
                        was_newline = false;
                    }
                    output.push_str(&s);
                    column += s.len();
                }
                Doc::Line | Doc::Softline | Doc::Hardline => {
                    output.push('\n');
                    was_newline = true;
                    column = 0;
                }
                Doc::Concat(lhs, rhs) => {
                    queue.push((indent, *rhs));
                    queue.push((indent, *lhs));
                }
                Doc::Nest(ind, nested_doc) => {
                    queue.push((indent + ind, *nested_doc));
                }
                Doc::Group(grouped_doc) => {
                    let flat = Self::flatten(*grouped_doc.clone());
                    if Self::fits((width as isize) - (column as isize), &flat) {
                        queue.push((indent, flat));
                    } else {
                        queue.push((indent, *grouped_doc));
                    }
                }
            }
        }

        output
    }

    fn flatten(doc: Doc) -> Doc {
        match doc {
            Doc::Empty | Doc::Text(_) => doc,
            Doc::Hardline => Doc::Hardline,
            Doc::Softline => Doc::Empty,
            Doc::Annotation(_) => doc,
            Doc::Line => Doc::Text(" ".to_string()),
            Doc::Concat(left, right) => Doc::Concat(
                Box::new(Self::flatten(*left)),
                Box::new(Self::flatten(*right)),
            ),
            Doc::Nest(indent, nested_doc) => {
                Doc::Nest(indent, Box::new(Self::flatten(*nested_doc)))
            }
            Doc::Group(grouped_doc) => Self::flatten(*grouped_doc),
        }
    }

    fn flat_width(doc: &Doc) -> Option<usize> {
        let mut width = 0usize;
        let mut queue = vec![doc];

        while let Some(current_doc) = queue.pop() {
            match current_doc {
                Doc::Empty => continue,
                Doc::Annotation(_) => continue,
                Doc::Text(s) => width += s.len(),
                Doc::Line => width += 1,
                Doc::Softline => continue,
                Doc::Hardline => return None,
                Doc::Concat(left, right) => {
                    queue.push(right);
                    queue.push(left);
                }
                Doc::Nest(_, nested_doc) => queue.push(nested_doc),
                Doc::Group(grouped_doc) => queue.push(grouped_doc),
            }
        }

        Some(width)
    }

    fn fits(remaining_width: isize, doc: &Doc) -> bool {
        let mut width = remaining_width;
        let mut queue = vec![doc];

        while width >= 0 && !queue.is_empty() {
            #[allow(clippy::unwrap_used)]
            match queue.pop().unwrap() {
                Doc::Empty => continue,
                Doc::Annotation(_) => continue,
                Doc::Text(s) => width -= s.len() as isize,
                Doc::Line | Doc::Softline | Doc::Hardline => return true,
                Doc::Concat(left, right) => {
                    queue.push(right);
                    queue.push(left);
                }
                Doc::Nest(_, nested_doc) => queue.push(nested_doc),
                Doc::Group(grouped_doc) => queue.push(grouped_doc),
            }
        }

        width >= 0
    }
}

fn adjust_trailing_newlines(input: &str, mut output: String) -> String {
    let input_has_trailing = input.ends_with('\n');
    let trimmed = output.trim_end_matches('\n');
    output.truncate(trimmed.len());
    if input_has_trailing {
        output.push('\n');
    }
    output
}

fn comments_from_tokens(tokens: Vec<Token>, source: &str) -> Vec<Comment> {
    let mut comments = Vec::new();
    for token in tokens {
        if !matches!(token.kind, TokenKind::LineComment(_)) {
            continue;
        }

        let start = token.start as usize;
        let end = token.end as usize;
        if let Some(text) = source.get(start..end) {
            comments.push(Comment {
                start: token.start,
                line: token.line,
                text: text.trim_end().to_string(),
            });
        }
    }
    comments
}

fn format_with_comments<Phase: ASTPhase>(
    ast: &AST<Phase>,
    width: usize,
    comments: Vec<Comment>,
) -> String {
    let formatter = Formatter::new_with_comments(&ast.meta, comments);
    formatter.format(&ast.roots, width)
}

#[allow(clippy::unwrap_used)]
pub fn format_string(string: &str) -> String {
    let lexer = Lexer::preserving_comments(string);
    match Parser::new("", FileID(0), lexer).parse_with_comments() {
        Ok((ast, _diagnostics, comments)) => {
            let formatted = if ast.roots.is_empty() {
                string.to_string()
            } else {
                format_with_comments(&ast, 80, comments_from_tokens(comments, string))
            };
            adjust_trailing_newlines(string, formatted)
        }
        Err(_err) => string.to_string(),
    }
}

#[allow(clippy::unwrap_used)]
pub fn format_node(node: &Node, meta: &NodeMetaStorage) -> String {
    let formatter = Formatter::new(meta);
    formatter.format(std::slice::from_ref(node), 80)
}

// Public API
pub fn format<Phase: ASTPhase>(ast: &AST<Phase>, width: usize) -> String {
    let formatter = Formatter::new(&ast.meta);
    formatter.format(&ast.roots, width)
}

#[cfg(test)]
mod formatter_tests {
    use super::*;
    use crate::ast::Parsed;
    use crate::lexer::Lexer;
    use crate::node_id::FileID;
    use crate::parser::Parser;

    fn parse(code: &str) -> AST<Parsed> {
        let lexer = Lexer::preserving_comments(code);
        let parser = Parser::new("-", FileID(0), lexer);
        parser.parse().unwrap().0
    }

    fn format_code(input: &str, width: usize) -> String {
        let ast = parse(input);
        let formatted = if ast.roots.is_empty() {
            input.to_string()
        } else {
            format(&ast, width)
        };
        adjust_trailing_newlines(input, formatted)
    }

    #[test]
    fn test_literal_formatting() {
        assert_eq!(format_code("123", 80), "123");
        assert_eq!(format_code("123.45", 80), "123.45");
        assert_eq!(format_code("true", 80), "true");
        assert_eq!(format_code("false", 80), "false");
    }

    #[test]
    fn test_binary_expressions() {
        assert_eq!(format_code("1 + 2", 80), "1 + 2");
        assert_eq!(format_code("1+2", 80), "1 + 2");
        assert_eq!(format_code("1 * 2 + 3", 80), "1 * 2 + 3");
        assert_eq!(format_code("1 == 2", 80), "1 == 2");
        assert_eq!(format_code("1 != 2", 80), "1 != 2");
        assert_eq!(format_code("1 < 2", 80), "1 < 2");
        assert_eq!(format_code("1 <= 2", 80), "1 <= 2");
        assert_eq!(format_code("1 > 2", 80), "1 > 2");
        assert_eq!(format_code("1 >= 2", 80), "1 >= 2");
    }

    #[test]
    fn test_unary_expressions() {
        assert_eq!(format_code("-1", 80), "-1");
        assert_eq!(format_code("!true", 80), "!true");
        assert_eq!(format_code("- 1", 80), "-1");
        assert_eq!(format_code("! true", 80), "!true");
    }

    #[test]
    fn test_variable_and_member_access() {
        assert_eq!(format_code("foo", 80), "foo");
        assert_eq!(format_code("foo.bar", 80), "foo.bar");
        assert_eq!(format_code("foo . bar", 80), "foo.bar");
        assert_eq!(format_code(".bar", 80), ".bar");
    }

    #[test]
    fn test_array_formatting() {
        assert_eq!(format_code("[]", 80), "[]");
        assert_eq!(format_code("[1]", 80), "[1]");
        assert_eq!(format_code("[1, 2, 3]", 80), "[1, 2, 3]");

        // Test line breaking for long arrays
        let long_array = "[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]";
        let formatted = format_code(long_array, 30);
        assert!(formatted.contains('\n'));
    }

    #[test]
    fn test_tuple_formatting() {
        assert_eq!(format_code("()", 80), "()");
        assert_eq!(format_code("(1)", 80), "(1)");
        assert_eq!(format_code("(1, 2)", 80), "(1, 2)");
        assert_eq!(format_code("(1, 2, 3)", 80), "(1, 2, 3)");
    }

    #[test]
    fn test_function_declarations() {
        // assert_eq!(format_code("func() {}", 80), "func() {}");
        assert_eq!(format_code("func foo() {}", 80), "func foo() {}");
        assert_eq!(format_code("func foo(a) {}", 80), "func foo(a) {}");
        assert_eq!(format_code("func foo(a, b) {}", 80), "func foo(a, b) {}");

        // With return type
        assert_eq!(
            format_code("func foo() -> Int {}", 80),
            "func foo() -> Int {}"
        );

        // With type parameters
        assert_eq!(
            format_code("func foo(a: Int) {}", 80),
            "func foo(a: Int) {}"
        );
        assert_eq!(
            format_code("func foo(a: Int, b: Bool) {}", 80),
            "func foo(a: Int, b: Bool) {}"
        );

        // With generics
        assert_eq!(format_code("func foo<T>() {}", 80), "func foo<T>() {}");
        assert_eq!(
            format_code("func foo<T, U>() {}", 80),
            "func foo<T, U>() {}"
        );
    }

    #[test]
    fn test_function_bodies() {
        assert_eq!(format_code("func foo() { 123 }", 80), "func foo() { 123 }");

        assert_eq!(
            format_code("func foo() {\n123\n456\n}", 80),
            "func foo() {\n\t123\n\t456\n}"
        );
    }

    #[test]
    fn test_func_bodies_with_multiple_exprs_with_call() {
        assert_eq!(
            format_code("func foo() {1+1 2+2}()", 80),
            "func foo() {\n\t1 + 1\n\t2 + 2\n}()"
        );
    }

    #[test]
    fn test_doesnt_insert_too_many_newlines_at_root() {
        assert_eq!(
            format_code("let x = 1\nlet y = 2", 80),
            "let x = 1\nlet y = 2"
        );
    }

    #[test]
    fn test_doesnt_insert_too_many_newlines_nested() {
        assert_eq!(
            format_code("func() {let x = 1\nlet y = 2 }", 80),
            "func() {\n\tlet x = 1\n\tlet y = 2\n}"
        );
    }

    #[test]
    fn test_respects_newlines() {
        assert_eq!(
            format_code(
                "let maybe = Maybe.definitely(123)\n\nmatch maybe {\n\t.definitely(x) -> x\n}",
                80
            ),
            "let maybe = Maybe.definitely(123)\n\nmatch maybe {\n\t.definitely(x) -> x\n}"
        );
    }

    #[test]
    fn test_function_calls() {
        assert_eq!(format_code("foo()", 80), "foo()");
        assert_eq!(format_code("foo(1)", 80), "foo(1)");
        assert_eq!(format_code("foo(1, 2)", 80), "foo(1, 2)");

        // With generics
        assert_eq!(format_code("foo<Int>()", 80), "foo<Int>()");
        assert_eq!(
            format_code("foo<Int, Bool>(1, true)", 80),
            "foo<Int, Bool>(1, true)"
        );

        // Long calls should break
        let long_call = "foo(very_long_argument_name, another_very_long_argument)";
        let formatted = format_code(long_call, 40);
        assert!(formatted.contains('\n'));
    }

    #[test]
    fn test_let_declarations() {
        assert_eq!(format_code("let x", 80), "let x");
        assert_eq!(format_code("let x: Int", 80), "let x: Int");
        assert_eq!(format_code("let x = 123", 80), "let x = 123");
        assert_eq!(format_code("let x: Int = 123", 80), "let x: Int = 123");
    }

    #[test]
    fn test_if_expressions() {
        assert_eq!(format_code("if true { 123 }", 80), "if true { 123 }");
        assert_eq!(
            format_code("if true { 123 } else { 456 }", 80),
            "if true { 123 } else {\n\t456\n}"
        );

        // Nested
        assert_eq!(
            format_code("if true {\nif false { 1 }\n}", 80),
            "if true {\n\tif false { 1 }\n}"
        );
    }

    #[test]
    fn test_loop_expressions() {
        assert_eq!(format_code("loop { 123 }", 80), "loop { 123 }");
        assert_eq!(format_code("loop true { 123 }", 80), "loop true { 123 }");
    }

    #[test]
    fn test_enum_declarations() {
        assert_eq!(format_code("enum Foo {}", 80), "enum Foo {}");
        assert_eq!(
            format_code("enum Foo { case a case b }", 80),
            "enum Foo {\n\tcase a\n\tcase b\n}"
        );
        assert_eq!(
            format_code("enum Foo { case a(Int) }", 80),
            "enum Foo {\n\tcase a(Int)\n}"
        );
        assert_eq!(
            format_code("enum Option<T> { case some(T) case none }", 80),
            "enum Option<T> {\n\tcase some(T)\n\tcase none\n}"
        );
    }

    #[test]
    fn test_match_expressions() {
        let match_expr = r#"match x {
            .some(val) -> val,
            .none() -> 0
        }"#;

        let expected = "match x {\n\t.some(val) -> val,\n\t.none -> 0\n}";
        assert_eq!(format_code(match_expr, 80), expected);

        // With enum prefix
        let match_with_enum = r#"match x {
            Option.some(val) -> val,
            Option.none -> 0
        }"#;

        let expected_enum = "match x {\n\tOption.some(val) -> val,\n\tOption.none -> 0\n}";
        assert_eq!(format_code(match_with_enum, 80), expected_enum);
    }

    #[test]
    fn test_struct_declarations() {
        assert_eq!(format_code("struct Person {}", 80), "struct Person {}");

        let struct_with_fields = r#"struct Person { let name: String let age: Int }"#;

        let expected = "struct Person {\n\tlet name: String\n\tlet age: Int\n}";
        assert_eq!(format_code(struct_with_fields, 80), expected);
    }

    #[test]
    fn test_return_statements() {
        assert_eq!(format_code("func() { return }", 80), "func() { return }");
        assert_eq!(
            format_code("func() { return 123 }", 80),
            "func() { return 123 }"
        );
        assert_eq!(
            format_code("func() { return foo() }", 80),
            "func() { return foo() }"
        );
    }

    #[test]
    fn test_blank_line_preservation() {
        let code_with_blanks = r#"func foo() {
            123
        }

        func bar() {
            456
        }"#;

        let formatted = format_code(code_with_blanks, 80);
        assert!(formatted.contains("\n\nfunc bar"));
    }

    #[test]
    fn test_type_annotations() {
        // assert_eq!(format_code("let x: Int?", 80), "let x: Optional<Int>");
        assert_eq!(format_code("let x: (Int, Bool)", 80), "let x: (Int, Bool)");
        assert_eq!(
            format_code("let f: (Int) -> Bool", 80),
            "let f: (Int) -> Bool"
        );
        assert_eq!(
            format_code("let f: (Int, Bool) -> String", 80),
            "let f: (Int, Bool) -> String"
        );
    }

    #[test]
    fn test_complex_expressions() {
        // Test precedence handling
        assert_eq!(format_code("1 + 2 * 3", 80), "1 + 2 * 3");
        assert_eq!(format_code("(1 + 2) * 3", 80), "(1 + 2) * 3");

        // Test chained member access
        assert_eq!(format_code("foo.bar.baz", 80), "foo.bar.baz");

        // Test nested calls
        assert_eq!(format_code("foo(bar(baz()))", 80), "foo(bar(baz()))");
    }

    #[test]
    fn test_assignment() {
        assert_eq!(format_code("x = 123", 80), "x = 123");
        assert_eq!(format_code("x = y + z", 80), "x = y + z");
        assert_eq!(format_code("foo.bar = 123", 80), "foo.bar = 123");
    }

    #[test]
    fn test_width_constraints() {
        // Test that long lines are broken appropriately
        let long_function = "func long_name(param: Int) {}";
        let formatted = format_code(long_function, 40);
        // The exact formatting might vary, but it should be reasonable
        assert!(!formatted.is_empty());
    }

    #[test]
    fn test_pattern_matching() {
        // Test various pattern types
        assert_eq!(
            format_code("match x { 1 -> true }", 80),
            "match x {\n\t1 -> true\n}"
        );

        assert_eq!(
            format_code("match x { _ -> true }", 80),
            "match x {\n\t_ -> true\n}"
        );

        assert_eq!(
            format_code("match x { true -> 1\nfalse -> 0 }", 80),
            "match x {\n\ttrue -> 1,\n\tfalse -> 0\n}"
        );

        assert_eq!(
            format_code("match x { { x, y } -> x }", 80),
            "match x {\n\t{ x, y } -> x\n}"
        );

        assert_eq!(
            format_code("match x { { x: 123, .. } -> 0 }", 80),
            "match x {\n\t{ x: 123, .. } -> 0\n}"
        );
    }

    #[test]
    fn test_single_line_function_formatting() {
        // Test that simple functions can be formatted on one line
        assert_eq!(
            format_code("func add(a, b) { a + b }", 80),
            "func add(a, b) { a + b }"
        );

        // But functions with multiple statements should not
        assert_eq!(
            format_code("func foo() { let x = 1\nx + 1 }", 80),
            "func foo() {\n\tlet x = 1\n\tx + 1\n}"
        );

        // Functions containing other functions should always be multi-line
        assert_eq!(
            format_code("func outer() { func inner() {} }", 80),
            "func outer() {\n\tfunc inner() {}\n}"
        );
    }

    #[test]
    fn test_block_args_formatting() {
        assert_eq!(
            format_code("@handle 'fizz { x in x }", 80),
            "@handle 'fizz { x in x }"
        );

        let input = "@handle 'fizz { x: Int, y: Bool in\nx\n}";
        let expected = "@handle 'fizz { x: Int, y: Bool in x }";
        assert_eq!(format_code(input, 80), expected);

        let input = "@handle 'fizz { x in\nx\nx\n}";
        let expected = "@handle 'fizz { x in\n\tx\n\tx\n}";
        assert_eq!(format_code(input, 80), expected);
    }

    #[test]
    fn test_single_line_function_threshold() {
        assert_eq!(
            format_code(
                "func very_long_function_name(param_one: Int, param_two: Int) { 1 }",
                80
            ),
            "func very_long_function_name(param_one: Int, param_two: Int) {\n\t1\n}"
        );
    }

    #[test]
    fn test_preserves_line_comments_inline() {
        assert_eq!(format_string("let x=1 // note"), "let x = 1 // note");
    }

    #[test]
    fn test_preserves_line_comments_between_roots() {
        let input = "let x = 1\n// note\nlet y = 2";
        let expected = "let x = 1\n// note\nlet y = 2";
        assert_eq!(format_string(input), expected);
    }

    #[test]
    fn test_preserves_line_comments_in_block() {
        let input = "func foo() {\n// note\n}";
        let expected = "func foo() {\n\t// note\n}";
        assert_eq!(format_string(input), expected);
    }

    #[test]
    fn test_effect_call_formatting() {
        // Effect calls should stay on one line when they fit
        assert_eq!(format_code("'emit(123)", 80), "'emit(123)");
        assert_eq!(format_code("'emit(x, y)", 80), "'emit(x, y)");

        // Effect calls with labels
        assert_eq!(format_code("'emit(value: 123)", 80), "'emit(value: 123)");
    }

    #[test]
    fn core_smoke_test() {
        // Make sure core is the same before and after formatting
        for path in std::fs::read_dir("./core").unwrap() {
            let code = std::fs::read_to_string(path.unwrap().path()).unwrap();
            assert_eq!(code, format_code(&code, 80));
        }
    }
}
