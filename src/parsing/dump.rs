//! Normalized parse dumps (ADR 0043 stage 1). One deterministic text
//! rendering of everything the frontend contract promises downstream:
//! the token stream, the tree shape with byte spans, node-meta token
//! extents, comments, and diagnostics. The golden corpus under
//! `tests/parser/` pins this as the behavior a self-hosted frontend
//! must reproduce, so the format deliberately avoids anything tied to
//! this implementation: node identities appear only as structure (each
//! node's line nests under its parent), never as allocated numbers.

use std::fmt::Write as _;

use derive_visitor::{Drive, Visitor};

use crate::lexer::Lexer;
use crate::node_id::{FileID, NodeID};
use crate::node_kinds::{
    attribute::Attribute, block::Block, body::Body, call_arg::CallArg, decl::Decl, func::Func,
    func_signature::FuncSignature, generic_decl::GenericDecl, match_arm::MatchArm,
    parameter::Parameter, pattern::Pattern, record_field::RecordField,
    type_annotation::TypeAnnotation,
};
use crate::node_kinds::{expr::Expr, stmt::Stmt};
use crate::node_meta_storage::NodeMetaStorage;
use crate::parser::Parser;
use crate::parsing::span::Span;
use crate::token_kind::TokenKind;

/// Snippets longer than this stay out of the dump: the span already
/// identifies the text, and long repeats would bloat the goldens.
const SNIPPET_LIMIT: usize = 40;

/// Dump a strict whole-file parse of `source`.
pub fn dump(source: &str) -> String {
    dump_with(source, |parser| parser.parse_with_comments())
}

/// Dump a whole-input expression parse (ADR 0043 category entry).
pub fn dump_expr(source: &str) -> String {
    dump_with(source, |parser| parser.parse_expr())
}

/// Dump a whole-input pattern parse (ADR 0043 category entry).
pub fn dump_pattern(source: &str) -> String {
    dump_with(source, |parser| parser.parse_pattern())
}

/// Dump a whole-input type-annotation parse (ADR 0043 category entry).
pub fn dump_type(source: &str) -> String {
    dump_with(source, |parser| parser.parse_type())
}

/// Dump a whole-input block-items parse (ADR 0043 category entry).
pub fn dump_block_items(source: &str) -> String {
    dump_with(source, |parser| parser.parse_block_items())
}

/// Dump a lenient whole-file parse (ADR 0043): a hard failure
/// degrades to an empty tree plus the failure as a diagnostic.
pub fn dump_lenient(source: &str) -> String {
    dump_with(source, |parser| Ok(parser.parse_lenient()))
}

/// Dump the balanced token trees of `source` (ADR 0043
/// `capture_token_tree`): groups nest, every other token renders like
/// the flat token section.
pub fn dump_token_trees(source: &str) -> String {
    let mut out = String::from("trees:\n");
    match crate::parsing::token_tree::capture(source) {
        Ok(trees) => render_trees(source, &trees, 1, &mut out),
        Err(error) => {
            let _ = writeln!(out, "token tree error: {} {}", error.code(), error);
        }
    }
    out
}

fn render_trees(
    source: &str,
    trees: &[crate::parsing::token_tree::TokenTree],
    depth: usize,
    out: &mut String,
) {
    use crate::parsing::token_tree::TokenTree;
    let indent = "  ".repeat(depth);
    for tree in trees {
        match tree {
            TokenTree::Token(token) => {
                let _ = writeln!(
                    out,
                    "{indent}{:?} @{}..{}{}",
                    token.kind,
                    token.start,
                    token.end,
                    snippet(source, token.start, token.end)
                );
            }
            TokenTree::Group(group) => {
                let _ = writeln!(
                    out,
                    "{indent}Group {} open@{}..{} close@{}..{}",
                    group.delimiter.open_text(),
                    group.open.start,
                    group.open.end,
                    group.close.start,
                    group.close.end
                );
                render_trees(source, &group.children, depth + 1, out);
            }
        }
    }
}

type ParseResult = Result<
    (
        crate::ast::AST<crate::ast::Parsed>,
        Vec<crate::diagnostic::AnyDiagnostic>,
        Vec<crate::token::Token>,
    ),
    crate::parser_error::ParserError,
>;

/// The flat token section — the `lex` validation contract (ADR 0043):
/// what the self-hosted lexer must reproduce byte-for-byte.
pub fn dump_tokens(source: &str) -> String {
    let mut out = String::from("tokens:\n");
    let mut lexer = Lexer::new(source);
    loop {
        match lexer.next() {
            Ok(token) if token.kind == TokenKind::EOF => break,
            Ok(token) => {
                let _ = writeln!(
                    out,
                    "  {:?} @{}..{}{}",
                    token.kind,
                    token.start,
                    token.end,
                    snippet(source, token.start, token.end)
                );
            }
            Err(error) => {
                let _ = writeln!(out, "  lexer error: {}", error.message());
                break;
            }
        }
    }
    out
}

/// Render the post-token dump sections for an already-built AST — the
/// bridge's round-trip surface (ADR 0043 §5). Byte-identical to
/// `dump_with`'s rendering: tree, comments, and diagnostics (which the
/// bridge carries as code/message pairs; every parse diagnostic the
/// corpus produces is an error). A hard failure replaces everything
/// with the `parse error:` line, exactly like the parser's own path.
pub fn render_bridged(
    source: &str,
    roots: &[crate::node::Node],
    meta: &crate::node_meta_storage::NodeMetaStorage,
    comments: &[(u32, u32)],
    failure: Option<&crate::compiling::bridge::BridgedFail>,
    diags: &[crate::compiling::bridge::BridgedFail],
) -> String {
    use derive_visitor::Drive;
    let mut out = String::new();
    if let Some(crate::compiling::bridge::BridgedFail { code, message, .. }) = failure {
        let _ = writeln!(out, "parse error: {code} {message}");
        return out;
    }
    out.push_str("tree:\n");
    let mut visitor = DumpVisitor {
        source,
        meta,
        out: String::new(),
        depth: 1,
    };
    for root in roots {
        root.drive(&mut visitor);
    }
    out.push_str(&visitor.out);
    if !comments.is_empty() {
        out.push_str("comments:\n");
        for (start, end) in comments {
            let _ = writeln!(out, "  @{}..{}{}", start, end, snippet(source, *start, *end));
        }
    }
    if !diags.is_empty() {
        out.push_str("diagnostics:\n");
        for crate::compiling::bridge::BridgedFail { code, message, .. } in diags {
            let _ = writeln!(out, "  error {code} {message}");
        }
    }
    out
}

/// A reference dump with its token section stripped: what the bridged
/// rendering must reproduce (tokens are internal to the frontend and do
/// not cross the ABI).
pub fn dump_after_tokens(source: &str) -> String {
    let full = dump(source);
    if let Some(index) = full.find("\ntree:\n") {
        return full[index + 1..].to_string();
    }
    if let Some(index) = full.find("\nparse error:") {
        return full[index + 1..].to_string();
    }
    full
}

fn dump_with<'a>(source: &'a str, parse: impl FnOnce(Parser<'a>) -> ParseResult) -> String {
    let mut out = dump_tokens(source);

    let lexer = Lexer::preserving_comments(source);
    let parser = Parser::new(":dump:", FileID(0), lexer);
    match parse(parser) {
        Ok((ast, diagnostics, comments)) => {
            out.push_str("tree:\n");
            let mut visitor = DumpVisitor {
                source,
                meta: &ast.meta,
                out: String::new(),
                depth: 1,
            };
            for root in &ast.roots {
                root.drive(&mut visitor);
            }
            out.push_str(&visitor.out);

            if !comments.is_empty() {
                out.push_str("comments:\n");
                for comment in &comments {
                    let _ = writeln!(
                        out,
                        "  @{}..{}{}",
                        comment.start,
                        comment.end,
                        snippet(source, comment.start, comment.end)
                    );
                }
            }

            if !diagnostics.is_empty() {
                out.push_str("diagnostics:\n");
                for diagnostic in &diagnostics {
                    let crate::diagnostic::AnyDiagnostic::Parsing(diagnostic) = diagnostic else {
                        continue;
                    };
                    let severity = match diagnostic.severity {
                        crate::diagnostic::Severity::Warn => "warn",
                        crate::diagnostic::Severity::Error => "error",
                    };
                    let _ = writeln!(
                        out,
                        "  {severity} {} {}",
                        diagnostic.kind.code(),
                        diagnostic.kind
                    );
                }
            }
        }
        Err(error) => {
            let _ = writeln!(out, "parse error: {} {}", error.code(), error);
        }
    }

    out
}

/// The source text for short single-line spans, quoted and escaped.
fn snippet(source: &str, start: u32, end: u32) -> String {
    let (start, end) = (start as usize, end as usize);
    if end <= start || end > source.len() || end - start > SNIPPET_LIMIT {
        return String::new();
    }
    let Some(text) = source.get(start..end) else {
        return String::new();
    };
    if text.contains('\n') {
        return String::new();
    }
    let mut quoted = String::with_capacity(text.len() + 4);
    for ch in text.chars() {
        match ch {
            '\\' => quoted.push_str("\\\\"),
            '"' => quoted.push_str("\\\""),
            '\t' => quoted.push_str("\\t"),
            '\r' => quoted.push_str("\\r"),
            other => quoted.push(other),
        }
    }
    format!(" \"{quoted}\"")
}

/// A `Debug` sink that aborts once the variant name is surely captured,
/// so labeling a node never formats its whole subtree.
struct Prefix<'a> {
    buf: &'a mut String,
    limit: usize,
}

impl std::fmt::Write for Prefix<'_> {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        for ch in s.chars() {
            if self.buf.len() >= self.limit {
                return Err(std::fmt::Error);
            }
            self.buf.push(ch);
        }
        Ok(())
    }
}

/// A kind's variant name: the leading identifier of its Debug form.
fn variant_name(kind: &dyn std::fmt::Debug) -> String {
    let mut buf = String::new();
    let _ = write!(Prefix {
        buf: &mut buf,
        limit: 64
    }, "{kind:?}");
    buf.split(|c: char| c == '(' || c == ' ' || c == '{')
        .next()
        .unwrap_or("")
        .to_string()
}

#[derive(Visitor)]
#[visitor(
    Attribute(enter, exit),
    Decl(enter, exit),
    Func(enter, exit),
    GenericDecl(enter, exit),
    Parameter(enter, exit),
    Stmt(enter, exit),
    Expr(enter, exit),
    Pattern(enter, exit),
    MatchArm(enter, exit),
    Block(enter, exit),
    Body(enter, exit),
    TypeAnnotation(enter, exit),
    RecordField(enter, exit),
    CallArg(enter, exit),
    FuncSignature(enter, exit)
)]
struct DumpVisitor<'a> {
    source: &'a str,
    meta: &'a NodeMetaStorage,
    out: String,
    depth: usize,
}

impl DumpVisitor<'_> {
    fn node(&mut self, label: String, id: NodeID, span: Span) {
        let indent = "  ".repeat(self.depth);
        let location = if span == Span::SYNTHESIZED {
            " @synthesized".to_string()
        } else {
            format!(" @{}..{}", span.start, span.end)
        };
        // Meta token extents only when they widen the node's own span —
        // the formatter's contract for surrounding trivia.
        let extents = match self.meta.get(&id) {
            Some(meta) if meta.start.start != span.start || meta.end.end != span.end => {
                format!(" tokens={}..{}", meta.start.start, meta.end.end)
            }
            _ => String::new(),
        };
        let text = snippet(self.source, span.start, span.end);
        let _ = writeln!(self.out, "{indent}{label}{location}{extents}{text}");
        self.depth += 1;
    }

    fn done(&mut self) {
        self.depth -= 1;
    }

    fn enter_attribute(&mut self, node: &Attribute) {
        self.node("Attribute".into(), node.id, node.span);
    }
    fn exit_attribute(&mut self, _: &Attribute) {
        self.done();
    }

    fn enter_decl(&mut self, node: &Decl) {
        let label = format!("Decl::{}", variant_name(&node.kind));
        self.node(label, node.id, node.span);
    }
    fn exit_decl(&mut self, _: &Decl) {
        self.done();
    }

    fn enter_func(&mut self, node: &Func) {
        self.node("Func".into(), node.id, node.body.span);
    }
    fn exit_func(&mut self, _: &Func) {
        self.done();
    }

    fn enter_generic_decl(&mut self, node: &GenericDecl) {
        self.node("GenericDecl".into(), node.id, node.span);
    }
    fn exit_generic_decl(&mut self, _: &GenericDecl) {
        self.done();
    }

    fn enter_parameter(&mut self, node: &Parameter) {
        self.node("Parameter".into(), node.id, node.span);
    }
    fn exit_parameter(&mut self, _: &Parameter) {
        self.done();
    }

    fn enter_stmt(&mut self, node: &Stmt) {
        let label = format!("Stmt::{}", variant_name(&node.kind));
        self.node(label, node.id, node.span);
    }
    fn exit_stmt(&mut self, _: &Stmt) {
        self.done();
    }

    fn enter_expr(&mut self, node: &Expr) {
        let label = format!("Expr::{}", variant_name(&node.kind));
        self.node(label, node.id, node.span);
    }
    fn exit_expr(&mut self, _: &Expr) {
        self.done();
    }

    fn enter_pattern(&mut self, node: &Pattern) {
        let label = format!("Pattern::{}", variant_name(&node.kind));
        self.node(label, node.id, node.span);
    }
    fn exit_pattern(&mut self, _: &Pattern) {
        self.done();
    }

    fn enter_match_arm(&mut self, node: &MatchArm) {
        self.node("MatchArm".into(), node.id, node.span);
    }
    fn exit_match_arm(&mut self, _: &MatchArm) {
        self.done();
    }

    fn enter_block(&mut self, node: &Block) {
        self.node("Block".into(), node.id, node.span);
    }
    fn exit_block(&mut self, _: &Block) {
        self.done();
    }

    fn enter_body(&mut self, node: &Body) {
        self.node("Body".into(), node.id, node.span);
    }
    fn exit_body(&mut self, _: &Body) {
        self.done();
    }

    fn enter_type_annotation(&mut self, node: &TypeAnnotation) {
        let label = format!("TypeAnnotation::{}", variant_name(&node.kind));
        self.node(label, node.id, node.span);
    }
    fn exit_type_annotation(&mut self, _: &TypeAnnotation) {
        self.done();
    }

    fn enter_record_field(&mut self, node: &RecordField) {
        self.node("RecordField".into(), node.id, node.span);
    }
    fn exit_record_field(&mut self, _: &RecordField) {
        self.done();
    }

    fn enter_call_arg(&mut self, node: &CallArg) {
        self.node("CallArg".into(), node.id, node.span);
    }
    fn exit_call_arg(&mut self, _: &CallArg) {
        self.done();
    }

    fn enter_func_signature(&mut self, node: &FuncSignature) {
        self.node("FuncSignature".into(), node.id, node.span);
    }
    fn exit_func_signature(&mut self, _: &FuncSignature) {
        self.done();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    fn check_corpus_dir(dir: &Path, dumper: fn(&str) -> String) {
        let expected_dir = dir.join("expected");
        let update = std::env::var_os("TALK_UPDATE_PARSER_DUMPS").is_some();
        let mut entries: Vec<_> = std::fs::read_dir(dir)
            .unwrap_or_else(|_| panic!("{} exists", dir.display()))
            .filter_map(|entry| entry.ok())
            .map(|entry| entry.path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "tlk"))
            .collect();
        entries.sort();
        assert!(
            !entries.is_empty(),
            "{} must not be empty",
            dir.display()
        );

        for path in entries {
            let source = std::fs::read_to_string(&path).expect("read corpus source");
            let actual = dumper(&source);
            let name = path.file_stem().expect("file stem").to_string_lossy();
            let expected_path = expected_dir.join(format!("{name}.dump"));
            if update {
                std::fs::create_dir_all(&expected_dir).expect("expected dir");
                std::fs::write(&expected_path, &actual).expect("write dump");
                continue;
            }
            let expected = std::fs::read_to_string(&expected_path).unwrap_or_else(|_| {
                panic!(
                    "missing {}; regenerate with TALK_UPDATE_PARSER_DUMPS=1",
                    expected_path.display()
                )
            });
            assert_eq!(
                actual,
                expected,
                "{} dumped differently; regenerate with TALK_UPDATE_PARSER_DUMPS=1 if intended",
                path.display()
            );
        }
    }

    /// Golden corpus: every `tests/parser/**/*.tlk` must dump exactly
    /// as its `expected/*.dump` sibling — whole files at the root, one
    /// subdirectory per category entry point. Regenerate with
    /// `TALK_UPDATE_PARSER_DUMPS=1 cargo test -p talk parser_dump`.
    #[test]
    fn parser_dump_corpus_matches_expected() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/parser");
        check_corpus_dir(&root, dump);
        check_corpus_dir(&root.join("expr"), dump_expr);
        check_corpus_dir(&root.join("pattern"), dump_pattern);
        check_corpus_dir(&root.join("type"), dump_type);
        check_corpus_dir(&root.join("block"), dump_block_items);
        check_corpus_dir(&root.join("tokentree"), dump_token_trees);
        check_corpus_dir(&root.join("lenient"), dump_lenient);
        check_corpus_dir(&root.join("unicode"), dump);
    }
}
