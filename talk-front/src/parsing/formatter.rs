use std::{cell::RefCell, collections::VecDeque, ops::Add};

use crate::{
    ast::{AST, ASTPhase},
    label::Label,
    name::Name,
    node::Node,
    node_kinds::{
        attribute::Attribute,
        block::Block,
        body::Body,
        call_arg::{ArgMode, CallArg},
        decl::{Decl, DeclKind, Import, ImportPath, ImportedSymbols, ReceiverMode, Visibility},
        expr::{Expr, ExprKind},
        func::{CaptureMode, CaptureSpec, EffectSet, Func},
        func_signature::FuncSignature,
        generic_decl::GenericDecl,
        inline_ir_instruction::InlineIRInstruction,
        match_arm::MatchArm,
        parameter::{ParamLabel, ParamMode, Parameter},
        pattern::{Pattern, PatternKind, RecordFieldPatternKind},
        record_field::{RecordField, RecordFieldTypeAnnotation},
        stmt::{Stmt, StmtKind},
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
        type_application::TypeApplication,
        where_clause::{WhereClause, WherePredicateKind},
    },
    node_meta::NodeMeta,
    node_meta_storage::NodeMetaStorage,
    token_kind::TokenKind,
};

/// A document tree that is laid out by [`Formatter::render_doc`].
///
/// [`group`] controls whether its line breaks use their flat or broken form:
///
/// | Break | Flat group | Broken group or outside a group |
/// | --- | --- | --- |
/// | [`line()`] | One space | Newline |
/// | [`softline()`] | Nothing | Newline |
/// | [`hardline()`] | Newline | Newline |
#[derive(Clone, Debug, PartialEq)]
pub enum Doc {
    /// Produces no output.
    Empty,
    /// Produces literal text and contributes its byte length to line fitting.
    Text(String),
    /// Produces a line comment, reflowing its words when it exceeds the width.
    Comment(String),
    /// A break that becomes one space when flattened.
    Line,
    /// A break that disappears when flattened.
    Softline,
    /// A break that remains a newline when flattened.
    Hardline,
    /// Increases indentation for lines broken within the nested document.
    Nest(u8, Box<Doc>),
    /// Places two documents next to each other without an implicit separator.
    Concat(Box<Doc>, Box<Doc>),
    /// Chooses between the flattened and broken forms of a document.
    Group(Box<Doc>),
}

impl Add for Doc {
    type Output = Doc;
    fn add(self, rhs: Self) -> Self::Output {
        concat(self, rhs)
    }
}

impl Doc {
    /// Returns whether this is exactly [`Doc::Empty`].
    ///
    /// This does not recursively inspect concatenations or groups.
    pub fn is_empty(&self) -> bool {
        matches!(self, Doc::Empty)
    }

    /// Returns whether this is directly one of the three line-break variants.
    ///
    /// This does not recursively inspect nested documents.
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

/// Places `inner` between `before` and `after` with no implicit separators.
pub fn wrap(before: Doc, inner: Doc, after: Doc) -> Doc {
    concat(before, concat(inner, after))
}

/// Creates a document that produces no output and occupies no width.
pub fn empty() -> Doc {
    Doc::Empty
}

/// Creates literal output text.
///
/// Its byte length contributes to the width used when deciding whether a
/// [`group`] fits on the current line.
pub fn text(s: impl Into<String>) -> Doc {
    Doc::Text(s.into())
}

/// Spells an identifier, restoring the `#"..."` quoting for names that can't
/// lex as a plain identifier (keywords or exotic characters). Compiler-minted
/// names keep their `$`/`#` sigils unquoted.
fn identifier_text(name: &str) -> String {
    let quoted = crate::keywords::is_keyword(name)
        || name.chars().next().is_some_and(char::is_numeric)
        || name
            .chars()
            .any(|c| !(c.is_alphanumeric() || matches!(c, '_' | '$' | '#')));

    if quoted {
        format!("#\"{name}\"")
    } else {
        name.to_string()
    }
}

/// Creates a break that is a space in a flat [`group`] and a newline otherwise.
pub fn line() -> Doc {
    Doc::Line
}

/// Creates a break that disappears in a flat [`group`] and is a newline otherwise.
///
/// This is useful just inside delimiters when the flat form should have no
/// whitespace, such as between `(` and its first item.
pub fn softline() -> Doc {
    Doc::Softline
}

/// Creates an unconditional newline, including inside a flat [`group`].
pub fn hardline() -> Doc {
    Doc::Hardline
}

/// Increases indentation by `indent` tabs after breaks within `doc`.
///
/// Nesting does not indent the first line or force a break by itself.
pub fn nest(indent: u8, doc: Doc) -> Doc {
    Doc::Nest(indent, Box::new(doc))
}

/// Places `rhs` immediately after `lhs` with no implicit separator.
pub fn concat(lhs: Doc, rhs: Doc) -> Doc {
    Doc::Concat(Box::new(lhs), Box::new(rhs))
}

/// Uses a document's flat form if it fits, and its broken form otherwise.
///
/// Flattening turns [`line()`] into a space, removes [`softline()`], and preserves
/// [`hardline()`]. The fit check starts at the renderer's current column.
pub fn group(doc: Doc) -> Doc {
    Doc::Group(Box::new(doc))
}

/// Places one literal space between `lhs` and `rhs`.
pub fn concat_space(lhs: Doc, rhs: Doc) -> Doc {
    concat(concat(lhs, text(" ")), rhs)
}

/// Concatenates `docs` with `separator` between adjacent documents.
///
/// No separator is added before the first or after the last document. An empty
/// input produces [`empty`].
pub fn join(docs: Vec<Doc>, separator: Doc) -> Doc {
    docs.into_iter().fold(empty(), |acc, doc| {
        if acc.is_empty() {
            doc
        } else {
            concat(concat(acc, separator.clone()), doc)
        }
    })
}

enum IfConditionRef<'a> {
    Boolean(&'a Expr),
    Let(&'a Pattern, &'a Expr),
}

pub struct Formatter<'a> {
    // Track expression metadata for source location info
    meta_storage: &'a NodeMetaStorage,
    comments: Option<RefCell<CommentStore>>,
    source: Option<&'a str>,
}

impl<'a> Formatter<'a> {
    pub fn new(meta_storage: &'a NodeMetaStorage) -> Formatter<'a> {
        Self {
            meta_storage,
            comments: None,
            source: None,
        }
    }
}

impl<'a> Formatter<'a> {
    fn new_with_comments(
        meta_storage: &'a NodeMetaStorage,
        comments: Vec<Comment>,
        source: Option<&'a str>,
    ) -> Formatter<'a> {
        Formatter {
            meta_storage,
            comments: Some(RefCell::new(CommentStore::new(comments))),
            source,
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

    fn import_for_root(root: &Node) -> Option<&Import> {
        let Node::Decl(Decl {
            kind: DeclKind::Import(import),
            ..
        }) = root
        else {
            return None;
        };
        Some(import)
    }

    fn collapse_import_run(&self, roots: &[Node]) -> Vec<Import> {
        let mut collapsed: Vec<Import> = Vec::new();

        for root in roots {
            let Some(import) = Self::import_for_root(root) else {
                continue;
            };
            let existing = collapsed.iter_mut().find(|candidate| {
                if candidate.path != import.path {
                    return false;
                }
                matches!(
                    (&candidate.symbols, &import.symbols),
                    (ImportedSymbols::Named(_), ImportedSymbols::Named(_))
                        | (ImportedSymbols::All, ImportedSymbols::All)
                        | (ImportedSymbols::Glob, ImportedSymbols::Glob)
                )
            });

            let Some(existing) = existing else {
                collapsed.push(import.clone());
                continue;
            };
            if let (ImportedSymbols::Named(existing), ImportedSymbols::Named(additional)) =
                (&mut existing.symbols, &import.symbols)
            {
                for symbol in additional {
                    if !existing.iter().any(|candidate| {
                        candidate.name == symbol.name && candidate.alias == symbol.alias
                    }) {
                        existing.push(symbol.clone());
                    }
                }
            }
        }

        collapsed
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
        Doc::Comment(comment.text)
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
        force_blank_line_before: bool,
        width: usize,
    ) {
        if let Some(last) = *last_line
            && item_start_line != last
        {
            output.push('\n');
            if force_blank_line_before || item_start_line > last + 1 {
                output.push('\n');
            }
        }
        output.push_str(&Self::render_doc(doc, width));
        *last_line = Some(item_end_line);
    }

    pub fn format(&self, roots: &[Node], width: usize) -> String {
        let mut output = String::new();
        let mut last_line: Option<u32> = None;
        let mut previous_root_was_import = false;
        let mut root_index = 0;

        while root_index < roots.len() {
            let root = &roots[root_index];
            let root_is_import = Self::import_for_root(root).is_some();
            let mut force_blank_line_before = previous_root_was_import && !root_is_import;
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
                Self::push_doc_output(
                    &mut output,
                    &mut last_line,
                    doc,
                    line,
                    line,
                    force_blank_line_before,
                    width,
                );
                force_blank_line_before = false;
            }

            if root_is_import {
                let mut run_end = root_index + 1;
                let mut run_end_line = end_line;
                while let Some(candidate) = roots.get(run_end) {
                    if Self::import_for_root(candidate).is_none() {
                        break;
                    }
                    let candidate_meta = self.get_meta_for_node(candidate);
                    let candidate_start_line = candidate_meta
                        .map(|node_meta| node_meta.start.line)
                        .unwrap_or(run_end_line + 1);
                    if candidate_start_line > run_end_line + 1 {
                        break;
                    }
                    run_end_line = candidate_meta
                        .map(|node_meta| node_meta.end.line)
                        .unwrap_or(candidate_start_line);
                    run_end += 1;
                }

                let boundary = roots
                    .get(run_end)
                    .and_then(|candidate| self.get_meta_for_node(candidate))
                    .map(|node_meta| node_meta.start.start)
                    .unwrap_or(u32::MAX);
                if run_end > root_index + 1 && !self.has_comments_between(start_pos, boundary) {
                    let collapsed = self.collapse_import_run(&roots[root_index..run_end]);
                    let mut output_line = start_line;
                    for import in collapsed {
                        Self::push_doc_output(
                            &mut output,
                            &mut last_line,
                            self.format_import(&import),
                            output_line,
                            output_line,
                            false,
                            width,
                        );
                        output_line += 1;
                    }
                    last_line = Some(run_end_line);
                    previous_root_was_import = true;
                    root_index = run_end;
                    continue;
                }
            }

            let mut doc = self.format_node(root);
            if let Some(meta) = meta
                && let Some(comment) = self.take_inline_comment(meta)
            {
                doc = concat(doc, concat(text(" "), Self::comment_doc(comment)));
            }

            Self::push_doc_output(
                &mut output,
                &mut last_line,
                doc,
                start_line,
                end_line,
                force_blank_line_before,
                width,
            );
            previous_root_was_import = root_is_import;
            root_index += 1;
        }

        for comment in self.take_comments_before(u32::MAX) {
            let line = comment.line;
            let doc = Self::comment_doc(comment);
            Self::push_doc_output(&mut output, &mut last_line, doc, line, line, false, width);
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
            ExprKind::SyntaxQuote { .. } => self
                .source
                .and_then(|source| source.get(expr.span.start as usize..expr.span.end as usize))
                .map(|source| text(source.to_string()))
                .unwrap_or_else(|| text("quote {}")),
            ExprKind::MacroCall {
                name,
                input_span,
                args,
                ..
            } => {
                if let Some(source) = self.source
                    && let Some(input) =
                        source.get(input_span.start as usize..input_span.end as usize)
                    && !input.starts_with('(')
                {
                    let separator = if input.starts_with('{') { " " } else { "" };
                    text(format!("@{name}{separator}{input}"))
                } else {
                    group(
                        text(format!("@{name}("))
                            + nest(
                                1,
                                softline()
                                    + join(
                                        args.iter().map(|arg| self.format_expr(arg)).collect(),
                                        text(",") + line(),
                                    ),
                            )
                            + softline()
                            + text(")"),
                    )
                }
            }
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
            ExprKind::LiteralCharacter(character) => self.format_character_literal(character),
            ExprKind::LiteralInt(val) => text(val),
            ExprKind::LiteralFloat(val) => text(val),
            ExprKind::LiteralTrue => text("true"),
            ExprKind::LiteralFalse => text("false"),
            ExprKind::Unreachable => text("unreachable"),
            ExprKind::Unary(op, rhs) => self.format_unary(op, rhs),
            ExprKind::Propagate(inner) => concat(self.format_expr(inner), text("?")),
            ExprKind::ForceUnwrap(inner, _) => concat(self.format_expr(inner), text("!")),
            ExprKind::Binary(lhs, op, rhs) => self.format_binary(lhs, op, rhs),
            ExprKind::Subscript(value, index) => concat(
                self.format_expr(value),
                concat(text("["), concat(self.format_expr(index), text("]"))),
            ),
            ExprKind::Tuple(items) => self.format_tuple(items),
            ExprKind::Block(block) => self.format_block(block),
            ExprKind::Unsafe(block) => text("#unsafe ") + self.format_block(block),
            ExprKind::Call {
                callee,
                type_args,
                args,
                trailing_block,
                ..
            } => self.format_call(expr, callee, type_args, args, trailing_block.as_ref()),
            ExprKind::Member(receiver, property, ..) => self.format_member(receiver, property),
            ExprKind::Func(func) => self.format_func(func),
            ExprKind::Variable(name) => self.format_name(name),
            ExprKind::Constructor(name, segments) => {
                self.format_dotted_head(&name.name_str(), segments)
            }
            ExprKind::If(cond, then_block, else_block) => self
                .format_compound_expr_if(expr)
                .unwrap_or_else(|| self.format_if(cond, then_block, else_block)),
            ExprKind::Match(target, arms) if Self::is_if_let_match(arms) => self
                .format_compound_expr_if(expr)
                .unwrap_or_else(|| self.format_if_let_match(target, arms)),
            ExprKind::Match(target, arms) => self.format_match(target, arms),
            ExprKind::RecordLiteral { fields, spread } => {
                self.format_record_literal(fields, spread)
            }
            ExprKind::InlineIR(instruction) => {
                if instruction.binds.is_empty() {
                    concat(
                        concat(text("#_ir { "), text(format!("{instruction}"))),
                        text(" }"),
                    )
                } else {
                    concat(
                        concat(
                            concat(
                                concat(
                                    text("#_ir("),
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

        doc
    }

    fn format_decl(&self, decl: &Decl) -> Doc {
        let doc = match &decl.kind {
            #[warn(clippy::todo)]
            DeclKind::Effect {
                name,
                generics,
                where_clause,
                params,
                ret,
                ..
            } => {
                let generics_doc = if generics.is_empty() {
                    text("")
                } else {
                    text("<")
                        + join(
                            generics
                                .iter()
                                .map(|g| self.format_generic_decl(g))
                                .collect(),
                            text(", "),
                        )
                        + text(">")
                };
                let result = text("effect '")
                    + self.format_name(name)
                    + generics_doc
                    + text("(")
                    + join(
                        params.iter().map(|p| self.format_parameter(p)).collect(),
                        text(","),
                    )
                    + text(")")
                    + text(" -> ")
                    + self.format_type_annotation(ret);
                if let Some(where_clause) = where_clause {
                    concat_space(result, self.format_where_clause(where_clause))
                } else {
                    result
                }
            }
            DeclKind::Import(import) => self.format_import(import),
            DeclKind::MacroCall {
                name,
                input_span,
                args,
                ..
            } => {
                let input = self.source.and_then(|source| {
                    source.get(input_span.start as usize..input_span.end as usize)
                });
                match input {
                    // Brace and bracket inputs, and parenthesized inputs
                    // without parsed arguments, keep their source form.
                    Some(input) if !input.starts_with('(') || args.is_empty() => {
                        let separator = if input.starts_with('{') { " " } else { "" };
                        text(format!("@{name}{separator}{input}"))
                    }
                    _ => group(
                        text(format!("@{name}("))
                            + nest(
                                1,
                                softline()
                                    + join(
                                        args.iter().map(|arg| self.format_expr(arg)).collect(),
                                        text(",") + line(),
                                    ),
                            )
                            + softline()
                            + text(")"),
                    ),
                }
            }
            DeclKind::Macro {
                name,
                params,
                body_span,
                ..
            } => {
                let body = self
                    .source
                    .and_then(|source| source.get(body_span.start as usize..body_span.end as usize))
                    .map(str::trim)
                    .unwrap_or_default();
                text("macro ")
                    + text(name)
                    + text("(")
                    + join(
                        params
                            .iter()
                            .map(|param| text(format!("${}", param.name)))
                            .collect(),
                        text(", "),
                    )
                    + text(") { ")
                    + text(body)
                    + text(" }")
            }
            DeclKind::Struct {
                name,
                generics,
                where_clause,
                body,
                linear,
                heap,
                ..
            } => {
                let attribute = if *linear {
                    Some("'linear")
                } else if *heap {
                    Some("'heap")
                } else {
                    None
                };
                self.format_struct(name, generics, attribute, where_clause.as_ref(), body)
            }
            DeclKind::Let {
                lhs,
                type_annotation,
                rhs: value,
            } => self.format_let_decl(lhs, type_annotation.as_ref(), value.as_ref()),
            DeclKind::Protocol {
                name,
                generics,
                where_clause,
                body,
                conformances,
                ..
            } => self.format_protocol(name, generics, conformances, where_clause.as_ref(), body),
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
            DeclKind::Method {
                func,
                is_static,
                receiver_mode,
            } => self.format_method(func, *is_static, *receiver_mode),
            DeclKind::Associated {
                generic,
                where_clause,
            } => self.format_associated(generic, where_clause.as_ref()),
            DeclKind::Func(func) => self.format_func(func),
            DeclKind::Extend {
                binders,
                head,
                conformances,
                where_clause,
                body,
            } => self.format_extend(binders, head, conformances, where_clause.as_ref(), body),
            DeclKind::Enum {
                name,
                generics,
                where_clause,
                body,
                linear,
                heap,
                ..
            } => {
                let attribute = if *linear {
                    Some("'linear")
                } else if *heap {
                    Some("'heap")
                } else {
                    None
                };
                self.format_enum_decl(name, generics, attribute, where_clause.as_ref(), body)
            }
            DeclKind::EnumVariant {
                name,
                generics,
                payloads,
                payload_labels,
                result,
                ..
            } => {
                self.format_enum_variant(name, generics, payloads, payload_labels, result.as_ref())
            }
            DeclKind::FuncSignature(sig) => self.format_func_signature(sig),
            DeclKind::MethodRequirement {
                signature,
                receiver_mode,
            } => self.format_method_signature(signature, *receiver_mode),
            DeclKind::InitRequirement { signature } => self.format_init_requirement(signature),
            DeclKind::TypeAlias(lhs, .., rhs) => self.format_type_alias(lhs, rhs),
        };

        // Prepend "pub " for public declarations
        let doc = if decl.visibility == Visibility::Public {
            text("pub ") + doc
        } else {
            doc
        };

        doc
    }

    fn format_type_alias(&self, lhs: &Name, rhs: &TypeAnnotation) -> Doc {
        concat_space(
            text("typealias"),
            join(
                vec![self.format_name(lhs), self.format_type_annotation(rhs)],
                text(" = "),
            ),
        )
    }

    fn format_stmt(&self, stmt: &Stmt) -> Doc {
        let doc = match &stmt.kind {
            StmtKind::Handling {
                effect_name, body, ..
            } => text(format!("#handle '{} ", effect_name.name_str())) + self.format_block(body),
            StmtKind::Expr(expr) => self.format_expr(expr),
            StmtKind::Continue => text("continue"),
            StmtKind::Resume(expr) => {
                if let Some(expr) = expr {
                    concat_space(text("'continue"), self.format_expr(expr))
                } else {
                    text("'continue")
                }
            }
            StmtKind::If(cond, then_block, else_block) => {
                self.format_compound_stmt_if(stmt).unwrap_or_else(|| {
                    let has_else = else_block.is_some();
                    let then_doc = if has_else {
                        self.format_block_multiline(then_block)
                    } else {
                        self.format_block(then_block)
                    };
                    let mut result =
                        concat_space(text("if"), concat_space(self.format_expr(cond), then_doc));

                    if let Some(else_block) = else_block {
                        result = concat_space(
                            result,
                            concat_space(text("else"), self.format_block_inner(else_block, false)),
                        )
                    }

                    result
                })
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
            StmtKind::For {
                pattern,
                iterable,
                source_mode,
                body,
                ..
            } => {
                let iterable = match source_mode {
                    Some(ArgMode::Borrow) => {
                        concat_space(text("borrow"), self.format_expr(iterable))
                    }
                    Some(ArgMode::Mut) => concat_space(text("mut"), self.format_expr(iterable)),
                    Some(ArgMode::Consume) => {
                        concat_space(text("consume"), self.format_expr(iterable))
                    }
                    Some(ArgMode::Copy) => concat_space(text("copy"), self.format_expr(iterable)),
                    None => self.format_expr(iterable),
                };
                concat_space(
                    text("for"),
                    concat_space(
                        self.format_pattern(pattern),
                        concat_space(
                            text("in"),
                            // A `for` body always formats multi-line; collapsing it to
                            // `for x in xs { ... }` hurts readability of the loop.
                            concat_space(iterable, self.format_block_multiline(body)),
                        ),
                    ),
                )
            }
        };

        doc
    }

    fn format_string_literal(&self, string: &str) -> Doc {
        concat(text("\""), concat(text(string), text("\"")))
    }

    fn format_character_literal(&self, character: &str) -> Doc {
        concat(text("'"), concat(text(character), text("'")))
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
            TokenKind::Tilde => "~",
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
            TokenKind::Amp => "&",
            TokenKind::LessLess => "<<",
            TokenKind::GreaterGreater => ">>",
            TokenKind::PipePipe => "||",
            TokenKind::AmpAmp => "&&",
            // Range operators bind their bounds tightly: `1..5`, `1..<5`.
            TokenKind::DotDot => {
                return group(concat(
                    self.format_expr(lhs),
                    concat(text(".."), self.format_expr(rhs)),
                ));
            }
            TokenKind::DotDotLess => {
                return group(concat(
                    self.format_expr(lhs),
                    concat(text("..<"), self.format_expr(rhs)),
                ));
            }
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

    fn format_func_block(&self, func: &Func, allow_single_line: bool) -> Doc {
        let capture_docs = func
            .captures
            .iter()
            .map(|capture| self.format_capture_spec(capture))
            .collect();
        let capture_header = (!func.captures.is_empty()).then(|| {
            concat(
                text("["),
                concat(
                    join(capture_docs, concat(text(","), text(" "))),
                    text("] in"),
                ),
            )
        });
        self.format_block_inner_with_header(&func.body, allow_single_line, capture_header)
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
        if args.is_empty() || Self::is_synthesized_positional_block_args(args) {
            return None;
        }

        let arg_docs: Vec<_> = args.iter().map(|arg| self.format_parameter(arg)).collect();
        Some(concat(
            join(arg_docs, concat(text(","), text(" "))),
            text(" in"),
        ))
    }

    fn is_synthesized_positional_block_args(args: &[Parameter]) -> bool {
        !args.is_empty()
            && args.iter().enumerate().all(|(index, arg)| {
                arg.span == crate::span::Span::SYNTHESIZED
                    && arg.name.name_str() == format!("${index}")
                    && arg.type_annotation.is_none()
                    && arg.mode.is_none()
            })
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
                stmt_doc = concat(stmt_doc, concat(text(" "), Self::comment_doc(comment)));
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
        self.format_block_inner_with_header(block, allow_single_line, None)
    }

    fn format_block_inner_with_header(
        &self,
        block: &Block,
        allow_single_line: bool,
        leading_header: Option<Doc>,
    ) -> Doc {
        let has_comments = self.has_comments_between(block.span.start, block.span.end);
        let args_doc = match (leading_header, self.format_block_args(&block.args)) {
            (Some(leading), Some(args)) => Some(concat(leading, concat(text(" "), args))),
            (Some(leading), None) => Some(leading),
            (None, args) => args,
        };
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
                decl_doc = concat(decl_doc, concat(text(" "), Self::comment_doc(comment)));
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

    fn format_call(
        &self,
        call: &Expr,
        callee: &Expr,
        type_args: &[crate::node_kinds::generic_arg::GenericArg],
        args: &[CallArg],
        trailing_block: Option<&Block>,
    ) -> Doc {
        let mut result = self.format_expr(callee);

        if !type_args.is_empty() {
            let type_docs: Vec<_> = type_args
                .iter()
                .map(|ty| self.format_generic_arg(ty))
                .collect();

            result = concat(
                result,
                concat(
                    text("<"),
                    concat(join(type_docs, concat(text(","), text(" "))), text(">")),
                ),
            );
        }

        let force_trailing_block_multiline = trailing_block.is_some() && Self::is_test_call(callee);

        let arg_docs: Vec<_> = args.iter().map(|arg| self.format_call_arg(arg)).collect();

        if type_args.is_empty() && self.can_omit_call_parens(call, callee, args) {
            let call_doc = group(concat(
                result,
                nest(
                    1,
                    concat(text(" "), join(arg_docs, concat(text(","), line()))),
                ),
            ));
            return if let Some(block) = trailing_block {
                let block_doc = self.format_block_inner(block, !force_trailing_block_multiline);
                group(concat(call_doc, concat(text(" "), block_doc)))
            } else {
                call_doc
            };
        }

        // If we have a trailing block and no args, omit parens
        if let Some(trailing_block) = trailing_block
            && args.is_empty()
        {
            let block_doc =
                self.format_block_inner(trailing_block, !force_trailing_block_multiline);
            return group(concat(result, concat(text(" "), block_doc)));
        }

        // Empty call parentheses are indivisible. In a long member chain,
        // inheriting the general argument-list softlines would split `()`.
        if args.is_empty() {
            return concat(result, text("()"));
        }

        let call_doc = group(concat(
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
        ));

        // Add trailing block after parens if present
        if let Some(block) = trailing_block {
            let block_doc = self.format_block_inner(block, !force_trailing_block_multiline);
            group(concat(call_doc, concat(text(" "), block_doc)))
        } else {
            call_doc
        }
    }

    fn can_omit_call_parens(&self, _call: &Expr, callee: &Expr, args: &[CallArg]) -> bool {
        let Some(CallArg {
            label: Label::Positional(_),
            mode: None,
            value:
                Expr {
                    kind: ExprKind::LiteralString(_),
                    span,
                    ..
                },
            ..
        }) = args.first()
        else {
            return false;
        };
        let Some(source) = self.source else {
            return false;
        };
        let Some(between) = source.get(callee.span.end as usize..span.start as usize) else {
            return false;
        };
        !between.contains('(')
    }

    fn is_test_call(callee: &Expr) -> bool {
        matches!(&callee.kind, ExprKind::Variable(name) if name.name_str() == "test")
    }

    fn format_call_arg(&self, arg: &CallArg) -> Doc {
        let value = match arg.mode {
            None => self.format_expr(&arg.value),
            Some(ArgMode::Borrow) => concat_space(text("borrow"), self.format_expr(&arg.value)),
            Some(ArgMode::Mut) => concat_space(text("mut"), self.format_expr(&arg.value)),
            Some(ArgMode::Consume) => concat_space(text("consume"), self.format_expr(&arg.value)),
            Some(ArgMode::Copy) => concat_space(text("copy"), self.format_expr(&arg.value)),
        };
        match &arg.label {
            Label::Named(name) => group(concat(concat(text(name), text(": ")), value)),
            Label::Positional(_) => value,
            Label::_Symbol(s) => text(format!("{s}")),
        }
    }

    fn format_macro_invocation(&self, name: &str, input_span: crate::parsing::span::Span) -> Doc {
        if let Some(source) = self.source
            && let Some(input) = source.get(input_span.start as usize..input_span.end as usize)
        {
            let separator = if input.starts_with('{') { " " } else { "" };
            return text(format!("@{name}{separator}{input}"));
        }
        text(format!("@{name}(...)"))
    }

    fn format_pattern(&self, pattern: &Pattern) -> Doc {
        match &pattern.kind {
            PatternKind::MacroCall {
                name, input_span, ..
            } => self.format_macro_invocation(name, *input_span),
            PatternKind::LiteralInt(val) => text(val),
            PatternKind::LiteralFloat(val) => text(val),
            PatternKind::LiteralCharacter(val) => self.format_character_literal(val),
            PatternKind::LiteralString(val) => self.format_string_literal(val),
            PatternKind::LiteralTrue => text("true"),
            PatternKind::LiteralFalse => text("false"),
            PatternKind::Bind(name) => self.format_name(name),
            PatternKind::Wildcard => text("_"),
            PatternKind::Or(patterns) => join(
                patterns.iter().map(|p| self.format_pattern(p)).collect(),
                text("|"),
            ),
            PatternKind::Tuple(items) => group(concat(
                text("("),
                concat(
                    join(
                        items.iter().map(|item| self.format_pattern(item)).collect(),
                        concat(text(","), line()),
                    ),
                    text(")"),
                ),
            )),
            PatternKind::Variant {
                enum_name,
                enum_generics,
                variant_name,
                fields,
                field_labels,
                ..
            } => {
                let mut result = if let Some(name) = enum_name {
                    concat(
                        self.format_dotted_head(&name.name_str(), enum_generics),
                        concat(text("."), text(identifier_text(variant_name))),
                    )
                } else {
                    concat(text("."), text(identifier_text(variant_name)))
                };

                if !fields.is_empty() {
                    let field_docs: Vec<_> = fields
                        .iter()
                        .enumerate()
                        .map(|(index, pattern)| {
                            match field_labels.get(index).and_then(Option::as_ref) {
                                Some(label) => concat(
                                    concat(self.format_name(label), text(": ")),
                                    self.format_pattern(pattern),
                                ),
                                None => self.format_pattern(pattern),
                            }
                        })
                        .collect();

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
                struct_generics,
                fields,
                field_names,
                rest,
            } => {
                let mut result = Vec::new();

                if let Some(name) = struct_name {
                    result.push(self.format_dotted_head(&name.name_str(), struct_generics));
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
        let path = match &import.path {
            ImportPath::Local(p) | ImportPath::Package(p) => text(p),
        };

        match &import.symbols {
            ImportedSymbols::All => join(vec![text("use"), path], text(" ")),
            ImportedSymbols::Glob => concat(concat(text("use "), path), text("::*")),
            ImportedSymbols::Named(symbols) => {
                let symbol_docs: Vec<_> = symbols
                    .iter()
                    .map(|s| {
                        if let Some(alias) = &s.alias {
                            concat(text(&s.name), concat(text(" as "), text(alias)))
                        } else {
                            text(&s.name)
                        }
                    })
                    .collect();
                let symbols = concat(
                    text("{ "),
                    concat(join(symbol_docs, text(", ")), text(" }")),
                );
                concat(concat(text("use "), path), concat(text("::"), symbols))
            }
        }
    }

    fn format_struct(
        &self,
        name: &Name,
        generics: &[GenericDecl],
        attribute: Option<&'static str>,
        where_clause: Option<&WhereClause>,
        body: &Body,
    ) -> Doc {
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

        if let Some(attribute) = attribute {
            result = concat_space(result, text(attribute));
        }

        if let Some(where_clause) = where_clause {
            result = concat_space(result, self.format_where_clause(where_clause));
        }

        concat_space(result, self.format_body(body))
    }

    fn format_generic_decl_list(&self, generics: &[GenericDecl]) -> Doc {
        let generic_docs: Vec<_> = generics
            .iter()
            .map(|generic| self.format_generic_decl(generic))
            .collect();
        concat(
            text("<"),
            concat(join(generic_docs, concat(text(","), text(" "))), text(">")),
        )
    }

    fn format_extend(
        &self,
        binders: &[GenericDecl],
        head: &TypeApplication,
        conformances: &[TypeAnnotation],
        where_clause: Option<&WhereClause>,
        body: &Body,
    ) -> Doc {
        let mut result = text("extend");

        if !binders.is_empty() {
            result = concat(result, self.format_generic_decl_list(binders));
        }

        // The head prints from its name and args directly: annotation sugar
        // normalization (`Array<T>` as `[T]`) can never apply to a head.
        result = concat_space(
            result,
            self.format_nominal_type_annotation(identifier_text(&head.name.name_str()), &head.args),
        );

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

        if let Some(where_clause) = where_clause {
            result = concat_space(result, self.format_where_clause(where_clause));
        }

        concat_space(result, self.format_body(body))
    }

    fn format_protocol(
        &self,
        name: &Name,
        generics: &[GenericDecl],
        conformances: &[TypeAnnotation],
        where_clause: Option<&WhereClause>,
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

        if let Some(where_clause) = where_clause {
            result = concat_space(result, self.format_where_clause(where_clause));
        }

        concat_space(result, self.format_body(body))
    }

    fn format_property(
        &self,
        name: &Name,
        is_static: bool,
        type_annotation: Option<&TypeAnnotation>,
        default_value: Option<&Expr>,
    ) -> Doc {
        let mut result = if is_static {
            concat_space(
                text("static"),
                concat_space(text("let"), self.format_name(name)),
            )
        } else {
            concat_space(text("let"), self.format_name(name))
        };

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

    fn format_effect_set(&self, effects: &EffectSet) -> Option<Doc> {
        match effects.names.len() {
            0 if effects.is_open => None,
            0 => Some(text("'[]")),
            1 if !effects.is_open => Some(text(format!("'{}", effects.names[0].name_str()))),
            _ => {
                let mut parts: Vec<_> = effects
                    .names
                    .iter()
                    .map(|effect| text(effect.name_str()))
                    .collect();
                if effects.is_open {
                    parts.push(text(".."));
                }
                Some(text("'[") + join(parts, concat(text(","), text(" "))) + text("]"))
            }
        }
    }

    fn format_type_annotation(&self, ty: &TypeAnnotation) -> Doc {
        match &ty.kind {
            TypeAnnotationKind::MacroCall {
                name, input_span, ..
            } => self.format_macro_invocation(name, *input_span),
            TypeAnnotationKind::SelfType(..) => text("Self"),
            TypeAnnotationKind::Borrow { mutable, inner } => {
                if *mutable {
                    concat(text("&mut "), self.format_type_annotation(inner))
                } else {
                    concat(text("&"), self.format_type_annotation(inner))
                }
            }
            TypeAnnotationKind::Unique { inner } => {
                concat(text("*"), self.format_type_annotation(inner))
            }
            TypeAnnotationKind::Record { fields } => self.format_record_type_annotation(fields),
            TypeAnnotationKind::Any {
                protocol,
                assoc_bindings,
            } => {
                let mut result = concat_space(text("any"), self.format_type_annotation(protocol));
                if !assoc_bindings.is_empty() {
                    let bindings: Vec<_> = assoc_bindings
                        .iter()
                        .map(|binding| {
                            self.format_name(&binding.name)
                                + text(" = ")
                                + self.format_type_annotation(&binding.value)
                        })
                        .collect();
                    result = concat(
                        result,
                        concat(
                            text("<"),
                            concat(join(bindings, concat(text(","), text(" "))), text(">")),
                        ),
                    );
                }
                result
            }
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
            TypeAnnotationKind::Quantified {
                generics,
                where_clause,
                inner,
            } => {
                let mut result = self.format_generic_decl_list(generics);
                if let Some(where_clause) = where_clause {
                    result = concat_space(result, self.format_where_clause(where_clause));
                }
                concat_space(result, self.format_type_annotation(inner))
            }
            TypeAnnotationKind::Func {
                params,
                effects,
                returns,
            } => {
                let param_docs: Vec<_> = params
                    .iter()
                    .map(|p| self.format_func_type_param(p))
                    .collect();

                let mut result = concat(
                    text("("),
                    concat(join(param_docs, concat(text(","), text(" "))), text(")")),
                );
                if let Some(effects) = self.format_effect_set(effects) {
                    result = concat_space(result, effects);
                }
                concat_space(
                    concat_space(result, text("->")),
                    self.format_type_annotation(returns),
                )
            }
            TypeAnnotationKind::Nominal { name, generics, .. }
                if name.name_str() == "Optional"
                    && generics.len() == 1
                    && generics[0].as_type().is_some() =>
            {
                let inner = generics[0].as_type().expect("guarded above");
                if matches!(inner.kind, TypeAnnotationKind::Borrow { .. }) {
                    self.format_nominal_type_annotation(identifier_text(&name.name_str()), generics)
                } else {
                    concat(self.format_type_annotation(inner), text("?"))
                }
            }
            TypeAnnotationKind::Nominal { name, generics, .. }
                if name.name_str() == "Array"
                    && generics.len() == 1
                    && generics[0].as_type().is_some() =>
            {
                wrap(
                    text("["),
                    self.format_type_annotation(generics[0].as_type().expect("guarded above")),
                    text("]"),
                )
            }
            TypeAnnotationKind::Nominal { name, generics, .. }
                if name.name_str() == "InlineArray"
                    && generics.len() == 2
                    && generics[0].as_type().is_some() =>
            {
                let element =
                    self.format_type_annotation(generics[0].as_type().expect("guarded above"));
                wrap(
                    text("["),
                    element + text("; ") + self.format_generic_arg(&generics[1]),
                    text("]"),
                )
            }
            TypeAnnotationKind::Nominal { name, generics, .. } => {
                self.format_nominal_type_annotation(identifier_text(&name.name_str()), generics)
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

    fn format_generic_arg(&self, arg: &crate::node_kinds::generic_arg::GenericArg) -> Doc {
        use crate::node_kinds::generic_arg::GenericArg;
        match arg {
            GenericArg::Type(annotation) => self.format_type_annotation(annotation),
            GenericArg::Static(expr) => self.format_static_expr(expr),
        }
    }

    fn format_static_expr(&self, expr: &crate::node_kinds::generic_arg::StaticExpr) -> Doc {
        use crate::node_kinds::generic_arg::StaticExprKind;
        match &expr.kind {
            StaticExprKind::Int(literal) => text(literal.clone()),
            StaticExprKind::Bool(value) => text(if *value { "true" } else { "false" }),
            StaticExprKind::UnqualifiedCase { name, .. } => text(format!(".{name}")),
            StaticExprKind::Path(annotation) => self.format_type_annotation(annotation),
            StaticExprKind::Group(inner) => {
                concat(text("("), concat(self.format_static_expr(inner), text(")")))
            }
            StaticExprKind::Op { op, lhs, rhs } => {
                self.format_static_expr(lhs)
                    + text(format!(" {} ", op.as_str()))
                    + self.format_static_expr(rhs)
            }
        }
    }

    fn format_nominal_type_annotation<T: Into<String>>(
        &self,
        name: T,
        generics: &[crate::node_kinds::generic_arg::GenericArg],
    ) -> Doc {
        let mut result = text(name);

        if !generics.is_empty() {
            let generic_docs: Vec<_> = generics
                .iter()
                .map(|g| self.format_generic_arg(g))
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
        let property = match property {
            Label::Named(name) => identifier_text(name),
            other => other.to_string(),
        };

        match receiver {
            Some(expr) => group(concat(
                self.format_expr(expr),
                concat(text("."), text(property)),
            )),
            None => concat(text("."), text(property)),
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

        if let Some(effects) = self.format_effect_set(&func.effects) {
            result = concat_space(result, effects);
        }

        if let Some(ref ret) = func.ret {
            result = concat_space(
                result,
                concat_space(text("->"), self.format_type_annotation(ret)),
            );
        }

        if let Some(where_clause) = &func.where_clause {
            result = concat_space(result, self.format_where_clause(where_clause));
        }

        let has_comments = self.has_comments_between(func.body.span.start, func.body.span.end);

        // Check if the body could be formatted inline
        if func.body.body.is_empty()
            || (func.body.body.len() == 1 && !Self::contains_control_flow(&func.body.body[0]))
            || func.effects.names.is_empty()
        {
            if has_comments {
                return concat_space(result, self.format_func_block(func, false));
            }
            let inline = concat_space(result.clone(), self.format_func_block(func, true));
            if Self::flat_width(&inline).is_some_and(|width| width <= SINGLE_LINE_FUNC_MAX_WIDTH) {
                return group(inline);
            }

            return concat_space(result, self.format_func_block(func, false));
        }

        concat_space(result, self.format_func_block(func, true))
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

    /// A function-type parameter in the borrow-by-default spelling
    /// (ADR 0018): a shared borrow is the quiet default, an exclusive
    /// borrow is `mut T`, and a bare owned type is `consume T`.
    fn format_func_type_param(&self, annotation: &TypeAnnotation) -> Doc {
        match &annotation.kind {
            TypeAnnotationKind::Borrow {
                mutable: false,
                inner,
            } => self.format_type_annotation(inner),
            TypeAnnotationKind::Borrow {
                mutable: true,
                inner,
            } => concat_space(text("mut"), self.format_type_annotation(inner)),
            _ => concat_space(text("consume"), self.format_type_annotation(annotation)),
        }
    }

    fn format_parameter(&self, param: &Parameter) -> Doc {
        let same_name_label = param.uses_same_name_label_syntax();
        let mut result = self.format_name(&param.name);

        // ADR 0041: a same-name label shares the binder token (`x:`);
        // distinct labels and explicit omission precede the local binder.
        match &param.label {
            None => {}
            Some(ParamLabel::Named(label)) if !same_name_label => {
                result = concat_space(text(label.clone()), result);
            }
            Some(ParamLabel::Named(_)) => {}
            Some(ParamLabel::Omitted) => {
                result = concat_space(text("_"), result);
            }
        }

        if same_name_label || param.type_annotation.is_some() {
            result = concat(result, text(":"));
        }
        if let Some(ref ty) = param.type_annotation {
            result = concat_space(result, self.format_type_annotation(ty));
        }

        // Only print a mode the source spelled (mode_span is the keyword's
        // span). Desugar-stamped defaults print as the quiet unadorned form.
        if param.mode_span.is_none() {
            return result;
        }
        let keyword = match param.mode {
            None => return result,
            Some(ParamMode::Borrow) => "borrow",
            Some(ParamMode::Mut) => "mut",
            Some(ParamMode::Consume) => "consume",
            Some(ParamMode::ConsumeMut) => "consume mut",
        };
        concat_space(text(keyword), result)
    }

    fn format_capture_spec(&self, capture: &CaptureSpec) -> Doc {
        match capture.mode {
            CaptureMode::Copy => self.format_name(&capture.name),
            CaptureMode::Move => concat_space(text("consuming"), self.format_name(&capture.name)),
            CaptureMode::BorrowShared => concat(text("&"), self.format_name(&capture.name)),
            CaptureMode::BorrowMut => concat_space(text("&mut"), self.format_name(&capture.name)),
        }
    }

    fn format_let_decl(
        &self,
        pattern: &Pattern,
        type_annotation: Option<&TypeAnnotation>,
        value: Option<&Expr>,
    ) -> Doc {
        if let Some((source_pattern, source_type, target, else_block)) =
            Self::let_else_parts(pattern, type_annotation, value)
        {
            let mut result = concat_space(text("let"), self.format_pattern(source_pattern));
            if let Some(ty) = source_type {
                result = concat(
                    result,
                    concat_space(text(":"), self.format_type_annotation(ty)),
                );
            }
            result = concat_space(result, concat_space(text("="), self.format_expr(target)));
            return concat_space(
                result,
                concat_space(text("else"), self.format_block(else_block)),
            );
        }

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

    fn let_else_parts<'b>(
        outer_pattern: &'b Pattern,
        outer_type: Option<&'b TypeAnnotation>,
        value: Option<&'b Expr>,
    ) -> Option<(&'b Pattern, Option<&'b TypeAnnotation>, &'b Expr, &'b Block)> {
        if outer_pattern.span != crate::span::Span::SYNTHESIZED || outer_type.is_some() {
            return None;
        }
        let value = value?;
        if value.span != crate::span::Span::SYNTHESIZED {
            return None;
        }
        let ExprKind::Match(target, arms) = &value.kind else {
            return None;
        };
        if !Self::is_if_let_match(arms) || arms[1].body.span == crate::span::Span::SYNTHESIZED {
            return None;
        }

        let (target, source_type) = match &target.kind {
            ExprKind::As(inner, ty) if target.span == crate::span::Span::SYNTHESIZED => {
                (inner.as_ref(), Some(ty))
            }
            _ => (target.as_ref(), None),
        };
        Some((&arms[0].pattern, source_type, target, &arms[1].body))
    }

    fn synthesized_expr_continuation(block: &Block) -> Option<&Expr> {
        if block.span != crate::span::Span::SYNTHESIZED || block.body.len() != 1 {
            return None;
        }
        let Node::Expr(expr) = &block.body[0] else {
            return None;
        };
        (expr.span == crate::span::Span::SYNTHESIZED).then_some(expr)
    }

    fn compound_expr_if_parts<'b>(
        expr: &'b Expr,
    ) -> Option<(Vec<IfConditionRef<'b>>, &'b Block, &'b Block)> {
        let mut conditions = vec![];
        let mut current = expr;
        let mut outer_alt = None;

        loop {
            let (condition, success, failure) = match &current.kind {
                ExprKind::If(condition, success, failure) => {
                    (IfConditionRef::Boolean(condition), success, failure)
                }
                ExprKind::Match(target, arms) if Self::is_if_let_match(arms) => (
                    IfConditionRef::Let(&arms[0].pattern, target),
                    &arms[0].body,
                    &arms[1].body,
                ),
                _ => return None,
            };
            conditions.push(condition);
            outer_alt.get_or_insert(failure);

            if let Some(next) = Self::synthesized_expr_continuation(success) {
                current = next;
                continue;
            }

            return (conditions.len() > 1).then(|| {
                (
                    conditions,
                    success,
                    outer_alt.unwrap_or_else(|| unreachable!("compound if alternative")),
                )
            });
        }
    }

    fn format_if_conditions(
        &self,
        conditions: Vec<IfConditionRef<'_>>,
        then_block: &Block,
        else_block: Option<&Block>,
    ) -> Doc {
        let has_pattern = conditions
            .iter()
            .any(|condition| matches!(condition, IfConditionRef::Let(..)));
        let conditions = conditions
            .into_iter()
            .map(|condition| match condition {
                IfConditionRef::Boolean(expr) => self.format_expr(expr),
                IfConditionRef::Let(pattern, value) => concat_space(
                    concat_space(text("let"), self.format_pattern(pattern)),
                    concat_space(text("="), self.format_expr(value)),
                ),
            })
            .collect();
        let condition = join(conditions, text(", "));
        let has_else = else_block.is_some_and(|block| {
            !block.body.is_empty() || block.span != crate::span::Span::SYNTHESIZED
        });
        let then_doc = if has_else || has_pattern {
            self.format_block_multiline(then_block)
        } else {
            self.format_block(then_block)
        };
        let mut result = concat_space(text("if"), concat_space(condition, then_doc));

        if has_else {
            let else_block = else_block.unwrap_or_else(|| unreachable!("checked above"));
            result = concat_space(
                result,
                concat_space(text("else"), self.format_block_inner(else_block, false)),
            );
        }
        result
    }

    fn format_compound_expr_if(&self, expr: &Expr) -> Option<Doc> {
        let (conditions, success, failure) = Self::compound_expr_if_parts(expr)?;
        Some(self.format_if_conditions(conditions, success, Some(failure)))
    }

    fn synthesized_stmt_continuation(block: &Block) -> Option<&Stmt> {
        if block.span != crate::span::Span::SYNTHESIZED || block.body.len() != 1 {
            return None;
        }
        let Node::Stmt(stmt) = &block.body[0] else {
            return None;
        };
        (stmt.span == crate::span::Span::SYNTHESIZED).then_some(stmt)
    }

    fn format_compound_stmt_if(&self, stmt: &Stmt) -> Option<Doc> {
        let mut conditions = vec![];
        let mut current = stmt;
        let mut outer_alt = None;

        loop {
            let StmtKind::If(condition, success, failure) = &current.kind else {
                return None;
            };
            conditions.push(IfConditionRef::Boolean(condition));
            if outer_alt.is_none() {
                outer_alt = failure.as_ref();
            }

            if let Some(next) = Self::synthesized_stmt_continuation(success) {
                current = next;
                continue;
            }

            return (conditions.len() > 1)
                .then(|| self.format_if_conditions(conditions, success, outer_alt));
        }
    }

    fn format_if(&self, cond: &Expr, then_block: &Block, else_block: &Block) -> Doc {
        let has_else =
            !else_block.body.is_empty() || else_block.span != crate::span::Span::SYNTHESIZED;
        let then_doc = if has_else {
            self.format_block_multiline(then_block)
        } else {
            self.format_block(then_block)
        };
        let mut result = concat_space(text("if"), concat_space(self.format_expr(cond), then_doc));

        if has_else {
            result = concat_space(
                result,
                concat_space(text("else"), self.format_block_inner(else_block, false)),
            );
        }

        result
    }

    fn is_if_let_match(arms: &[MatchArm]) -> bool {
        arms.len() == 2
            && arms
                .iter()
                .all(|arm| arm.span == crate::span::Span::SYNTHESIZED)
            && matches!(arms[1].pattern.kind, PatternKind::Wildcard)
    }

    fn format_if_let_match(&self, target: &Expr, arms: &[MatchArm]) -> Doc {
        let condition = concat_space(
            concat_space(text("let"), self.format_pattern(&arms[0].pattern)),
            concat_space(text("="), self.format_expr(target)),
        );
        let mut result = concat_space(
            text("if"),
            concat_space(condition, self.format_block_multiline(&arms[0].body)),
        );

        if !arms[1].body.body.is_empty() || arms[1].body.span != crate::span::Span::SYNTHESIZED {
            result = concat_space(
                result,
                concat_space(text("else"), self.format_block_multiline(&arms[1].body)),
            );
        }

        result
    }

    fn format_enum_decl(
        &self,
        name: &Name,
        generics: &[GenericDecl],
        attribute: Option<&'static str>,
        where_clause: Option<&WhereClause>,
        body: &Body,
    ) -> Doc {
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

        if let Some(attribute) = attribute {
            result = concat_space(result, text(attribute));
        }

        if let Some(where_clause) = where_clause {
            result = concat_space(result, self.format_where_clause(where_clause));
        }

        concat_space(result, self.format_body(body))
    }

    fn format_enum_variant(
        &self,
        name: &Name,
        generics: &[GenericDecl],
        types: &[TypeAnnotation],
        payload_labels: &[Option<Name>],
        case_result: Option<&TypeAnnotation>,
    ) -> Doc {
        let mut result = concat_space(text("case"), self.format_name(name));

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

        if !types.is_empty() {
            let type_docs: Vec<_> = types
                .iter()
                .enumerate()
                .map(
                    |(index, ty)| match payload_labels.get(index).and_then(Option::as_ref) {
                        Some(label) => concat(
                            concat(self.format_name(label), text(": ")),
                            self.format_type_annotation(ty),
                        ),
                        None => self.format_type_annotation(ty),
                    },
                )
                .collect();

            result = concat(
                result,
                concat(
                    text("("),
                    concat(join(type_docs, concat(text(","), text(" "))), text(")")),
                ),
            );
        }

        if let Some(case_result) = case_result {
            result = concat_space(
                result,
                concat_space(text("->"), self.format_type_annotation(case_result)),
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
            concat(text(identifier_text(&field.label.name_str())), text(": ")),
            self.format_type_annotation(&field.value),
        ))
    }

    fn format_record_field(&self, field: &RecordField) -> Doc {
        group(concat(
            concat(text(identifier_text(&field.label.name_str())), text(": ")),
            self.format_expr(&field.value),
        ))
    }

    fn format_method(&self, func: &Func, is_static: bool, receiver_mode: ReceiverMode) -> Doc {
        if is_static {
            concat_space(text("static"), self.format_func(func))
        } else {
            self.receiver_mode_prefix(receiver_mode, self.format_func(func))
        }
    }

    fn receiver_mode_prefix(&self, receiver_mode: ReceiverMode, doc: Doc) -> Doc {
        match receiver_mode {
            ReceiverMode::None => doc,
            ReceiverMode::Ref => concat_space(text("mut"), doc),
            ReceiverMode::Consuming => concat_space(text("consuming"), doc),
        }
    }

    fn format_associated(&self, generic: &GenericDecl, where_clause: Option<&WhereClause>) -> Doc {
        let result = concat_space(text("associated"), self.format_generic_decl(generic));
        if let Some(where_clause) = where_clause {
            concat_space(result, self.format_where_clause(where_clause))
        } else {
            result
        }
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

        if let Some(effects) = self.format_effect_set(&sig.effects) {
            result = concat_space(result, effects);
        }

        if let Some(ret) = &sig.ret {
            result = concat_space(
                result,
                concat_space(text("->"), self.format_type_annotation(ret)),
            );
        }

        if let Some(where_clause) = &sig.where_clause {
            result = concat_space(result, self.format_where_clause(where_clause));
        }

        result
    }

    fn format_method_signature(&self, sig: &FuncSignature, receiver_mode: ReceiverMode) -> Doc {
        self.receiver_mode_prefix(receiver_mode, self.format_func_signature(sig))
    }

    /// `init(params)`: the implicit `-> Self` return never prints.
    fn format_init_requirement(&self, sig: &FuncSignature) -> Doc {
        let param_docs: Vec<_> = sig
            .params
            .iter()
            .map(|p| self.format_parameter(p))
            .collect();
        concat(
            text("init"),
            concat(
                text("("),
                concat(join(param_docs, concat(text(","), text(" "))), text(")")),
            ),
        )
    }

    fn format_where_clause(&self, where_clause: &WhereClause) -> Doc {
        text("where")
            + text(" ")
            + join(
                where_clause
                    .predicates
                    .iter()
                    .map(|predicate| match &predicate.kind {
                        WherePredicateKind::TypeEq { lhs, rhs } => {
                            self.format_generic_arg(lhs)
                                + text(" == ")
                                + self.format_generic_arg(rhs)
                        }
                        WherePredicateKind::Conforms { ty, protocols } => {
                            self.format_type_annotation(ty)
                                + text(": ")
                                + join(
                                    protocols
                                        .iter()
                                        .map(|p| self.format_type_annotation(p))
                                        .collect(),
                                    text(" & "),
                                )
                        }
                        WherePredicateKind::StaticCmp { strict, lhs, rhs } => {
                            self.format_generic_arg(lhs)
                                + text(if *strict { " < " } else { " <= " })
                                + self.format_generic_arg(rhs)
                        }
                    })
                    .collect(),
                text(" && "),
            )
    }

    fn format_generic_decl(&self, generic: &GenericDecl) -> Doc {
        if let Some(static_ty) = &generic.static_ty {
            let mut result = concat(
                text("static "),
                concat(
                    self.format_name(&generic.name),
                    concat(text(": "), self.format_type_annotation(static_ty)),
                ),
            );
            if let Some(default) = &generic.default {
                result = concat(
                    result,
                    concat(text(" = "), self.format_generic_arg(default)),
                );
            }
            return result;
        }

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

        if let Some(default) = &generic.default {
            result = concat(
                result,
                concat(text(" = "), self.format_generic_arg(default)),
            );
        }

        result
    }

    fn format_name(&self, name: &Name) -> Doc {
        text(identifier_text(&name.name_str()))
    }

    /// A possibly-dotted type head with per-segment generic args
    /// (`Res<Int>.A<Bool>`): each segment is its own identifier, escaped
    /// per segment, with its arg list attached where it was written.
    fn format_dotted_head(
        &self,
        path: &str,
        segments: &[Vec<crate::node_kinds::generic_arg::GenericArg>],
    ) -> Doc {
        let docs: Vec<Doc> = path
            .split('.')
            .enumerate()
            .map(|(index, segment)| {
                let mut doc = text(identifier_text(segment));
                if let Some(args) = segments.get(index)
                    && !args.is_empty()
                {
                    let arg_docs: Vec<_> = args
                        .iter()
                        .map(|arg| self.format_generic_arg(arg))
                        .collect();
                    doc = concat(
                        doc,
                        concat(
                            text("<"),
                            concat(join(arg_docs, concat(text(","), text(" "))), text(">")),
                        ),
                    );
                }
                doc
            })
            .collect();
        join(docs, text("."))
    }

    fn expr_contains_control_flow(expr: &Expr) -> bool {
        matches!(
            &expr.kind,
            ExprKind::Func { .. }
                | ExprKind::If(..)
                | ExprKind::Match(..)
                | ExprKind::MacroCall { .. }
        )
    }

    fn stmt_contains_control_flow(stmt: &Stmt) -> bool {
        match &stmt.kind {
            StmtKind::Expr(expr) => Self::expr_contains_control_flow(expr),
            StmtKind::If(..)
            | StmtKind::Loop(..)
            | StmtKind::Continue
            | StmtKind::Resume(..)
            | StmtKind::Break => true,
            _ => false,
        }
    }

    fn decl_contains_control_flow(decl: &Decl) -> bool {
        matches!(
            &decl.kind,
            DeclKind::Func(_)
                | DeclKind::Init { .. }
                | DeclKind::Method { .. }
                | DeclKind::MacroCall { .. }
        )
    }

    fn contains_control_flow(node: &Node) -> bool {
        match node {
            Node::Decl(decl) => Self::decl_contains_control_flow(decl),
            Node::Expr(expr) => Self::expr_contains_control_flow(expr),
            Node::Stmt(stmt) => Self::stmt_contains_control_flow(stmt),
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
                Doc::Text(s) => {
                    if was_newline {
                        output.push_str(&"\t".repeat(indent as usize));
                        was_newline = false;
                    }
                    output.push_str(&s);
                    column += s.len();
                }
                Doc::Comment(s) => {
                    if was_newline {
                        output.push_str(&"\t".repeat(indent as usize));
                        column += indent as usize;
                        was_newline = false;
                    }
                    Self::render_comment(&mut output, &s, width, indent as usize, &mut column);
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

    fn render_comment(
        output: &mut String,
        comment: &str,
        width: usize,
        indent: usize,
        column: &mut usize,
    ) {
        let (prefix, body) = Self::line_comment_parts(comment);
        if body.is_empty() {
            output.push_str(comment);
            *column += comment.len();
            return;
        }

        let words: Vec<&str> = body.split_whitespace().collect();
        if words.is_empty() {
            output.push_str(&prefix);
            *column += prefix.len();
            return;
        }

        let mut line_body = String::new();
        let mut current_column = *column;

        for word in words {
            let separator_width = usize::from(!line_body.is_empty());
            let projected_width =
                current_column + prefix.len() + line_body.len() + separator_width + word.len();
            if !line_body.is_empty() && projected_width > width {
                output.push_str(&prefix);
                output.push_str(&line_body);
                output.push('\n');
                output.push_str(&"\t".repeat(indent));
                current_column = indent;
                line_body.clear();
            }

            if !line_body.is_empty() {
                line_body.push(' ');
            }
            line_body.push_str(word);
        }

        output.push_str(&prefix);
        output.push_str(&line_body);
        *column = current_column + prefix.len() + line_body.len();
    }

    fn line_comment_parts(comment: &str) -> (String, &str) {
        let Some(after_slashes) = comment.strip_prefix("//") else {
            return (String::new(), comment);
        };

        let slash_count = 2 + after_slashes.chars().take_while(|ch| *ch == '/').count();
        let rest = &comment[slash_count..];
        let body = rest.trim_start();
        if body.is_empty() {
            (comment.to_string(), body)
        } else {
            let body_offset = comment.len() - body.len();
            (comment[..body_offset].to_string(), body)
        }
    }

    fn flatten(doc: Doc) -> Doc {
        match doc {
            Doc::Empty | Doc::Text(_) | Doc::Comment(_) => doc,
            Doc::Hardline => Doc::Hardline,
            Doc::Softline => Doc::Empty,
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
                Doc::Text(s) | Doc::Comment(s) => width += s.len(),
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

        while width >= 0 {
            let Some(doc) = queue.pop() else {
                break;
            };
            match doc {
                Doc::Empty => continue,
                Doc::Text(s) | Doc::Comment(s) => width -= s.len() as isize,
                Doc::Line | Doc::Softline => return true,
                // A hardline in the flattened doc means the group cannot
                // render flat; force it to break.
                Doc::Hardline => return false,
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

/// Comments from the frontend's byte ranges (ADR 0043: comments cross
/// the ABI as extents; the line is the newline count up to the end,
/// matching the reference token stamp).
fn comments_from_ranges(ranges: &[(u32, u32)], source: &str) -> Vec<Comment> {
    let mut comments = Vec::new();
    for (start, end) in ranges {
        if let Some(text) = source.get(*start as usize..*end as usize) {
            let line = source[..*end as usize]
                .bytes()
                .filter(|byte| *byte == b'\n')
                .count() as u32;
            comments.push(Comment {
                start: *start,
                line,
                text: text.trim_end().to_string(),
            });
        }
    }
    comments
}

fn format_with_comments<'a, Phase: ASTPhase>(
    ast: &'a AST<Phase>,
    width: usize,
    comments: Vec<Comment>,
    source: Option<&'a str>,
) -> String {
    let formatter = Formatter::new_with_comments(&ast.meta, comments, source);
    formatter.format(&ast.roots, width)
}

/// Format an already-parsed source with its lexed comment ranges: the
/// parse-free half of string formatting. The parsing halves
/// (`frontend::format_string`, `format_string_with_width`) live
/// root-side with the self-hosted frontend (ADR 0057 slice 3).
pub fn format_parsed<Phase: ASTPhase>(
    ast: &AST<Phase>,
    width: usize,
    comment_ranges: &[(u32, u32)],
    source: &str,
) -> String {
    let formatted = if ast.roots.is_empty() {
        source.to_string()
    } else {
        format_with_comments(
            ast,
            width,
            comments_from_ranges(comment_ranges, source),
            Some(source),
        )
    };
    adjust_trailing_newlines(source, formatted)
}

pub fn format_node(node: &Node, meta: &NodeMetaStorage) -> String {
    let formatter = Formatter::new(meta);
    formatter.format(std::slice::from_ref(node), 80)
}

// Public API
pub fn format<Phase: ASTPhase>(ast: &AST<Phase>, width: usize) -> String {
    let formatter = Formatter::new(&ast.meta);
    formatter.format(&ast.roots, width)
}

