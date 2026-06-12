use std::path::PathBuf;

use crate::{
    analysis::{Diagnostic, DocumentInput, Workspace, completion::complete_in_workspace},
    lexer::Lexer,
    node_id::FileID,
    parser::Parser,
    parser_error::ParserError,
    token_kind::TokenKind,
};

pub const REPL_DOCUMENT_ID: &str = "<repl>";

#[derive(Clone, Debug)]
pub struct ReplSession {
    persistent_source: String,
    source_path: PathBuf,
}

impl Default for ReplSession {
    fn default() -> Self {
        Self::new()
    }
}

impl ReplSession {
    pub fn new() -> Self {
        let source_path = std::env::current_dir()
            .map(|dir| dir.join("repl.tlk"))
            .unwrap_or_else(|_| PathBuf::from("repl.tlk"));
        Self::with_source_path(source_path)
    }

    pub fn with_source_path(source_path: PathBuf) -> Self {
        Self {
            persistent_source: String::new(),
            source_path,
        }
    }

    pub fn persistent_source(&self) -> &str {
        &self.persistent_source
    }

    pub fn source_path(&self) -> &PathBuf {
        &self.source_path
    }

    pub fn clear(&mut self) {
        self.persistent_source.clear();
    }

    pub fn eval(&mut self, input: &str) -> ReplEvalResult {
        let repl_input = ReplInput::new(input);
        if repl_input.is_empty() {
            return ReplEvalResult::Output {
                stdout: String::new(),
                stderr: String::new(),
                value: None,
            };
        }

        let source = self.combined_source(input);
        if let Some(diagnostics) = self.diagnostics_for_source(&source) {
            return ReplEvalResult::Diagnostics {
                source,
                diagnostics,
                message: None,
            };
        }

        if repl_input.should_persist() {
            self.persist(input);
            return ReplEvalResult::Output {
                stdout: String::new(),
                stderr: String::new(),
                value: None,
            };
        }

        // Evaluate on the λ_G reference evaluator (the slow path; the
        // bytecode VM replaces this in the backend's M2).
        use crate::compiling::driver::{Driver, DriverConfig, Source};
        let driver = Driver::new(
            vec![Source::from(source.as_str())],
            DriverConfig::new("Repl"),
        );
        let typed = match driver.parse() {
            Ok(parsed) => match parsed.resolve_names() {
                Ok(resolved) => resolved.type_check(),
                Err(err) => return ReplEvalResult::Error(format!("{err:?}")),
            },
            Err(err) => return ReplEvalResult::Error(format!("{err:?}")),
        };
        if typed.has_errors() {
            let message = typed
                .diagnostics()
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
                .join("\n");
            return ReplEvalResult::Error(message);
        }
        let mut lowered = typed.lower();
        if !lowered.phase.diagnostics.is_empty() {
            return ReplEvalResult::Error(format!(
                "not yet supported by the backend: {}",
                lowered.phase.diagnostics.join("; ")
            ));
        }
        match lowered.run_vm_with_output() {
            Ok((value, stdout)) => ReplEvalResult::Output {
                stdout,
                stderr: String::new(),
                value: Some(format!("{value:?}")),
            },
            Err(err) => ReplEvalResult::Error(format!("evaluation failed: {err}")),
        }
    }

    pub fn type_of(&self, input: &str) -> ReplEvalResult {
        use crate::compiling::driver::{Driver, DriverConfig, Source};

        let repl_input = ReplInput::new(input);
        if repl_input.is_empty() {
            return ReplEvalResult::Error("/type requires an expression".to_string());
        }

        let source = self.combined_source(input);
        let driver = Driver::new(
            vec![Source::from(source.as_str())],
            DriverConfig::new("Repl"),
        );
        let typed = match driver.parse() {
            Ok(parsed) => match parsed.resolve_names() {
                Ok(resolved) => resolved.type_check(),
                Err(err) => return ReplEvalResult::Error(format!("{err:?}")),
            },
            Err(err) => return ReplEvalResult::Error(format!("{err:?}")),
        };
        if typed.has_errors() {
            let message = typed
                .diagnostics()
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
                .join("\n");
            return ReplEvalResult::Error(message);
        }

        let resolved_names = &typed.phase.resolved_names;
        let _names = crate::name_resolution::symbol::set_symbol_names(
            resolved_names.symbol_names.clone(),
        );

        // A bare identifier shows its (possibly polymorphic) scheme; any
        // other expression shows the type of the final statement.
        let trimmed = input.trim();
        if trimmed.chars().all(|c| c.is_alphanumeric() || c == '_') {
            let scheme = resolved_names
                .symbol_names
                .iter()
                .find(|(sym, name)| {
                    name.as_str() == trimmed && typed.phase.types.schemes.contains_key(sym)
                })
                .map(|(sym, _)| typed.phase.types.schemes[sym].render());
            if let Some(rendered) = scheme {
                return ReplEvalResult::Output {
                    stdout: String::new(),
                    stderr: String::new(),
                    value: Some(rendered),
                };
            }
        }

        let last_expr_ty = typed
            .phase
            .asts
            .values()
            .flat_map(|ast| ast.roots.iter())
            .filter_map(|root| match root {
                crate::node::Node::Stmt(crate::node_kinds::stmt::Stmt {
                    kind: crate::node_kinds::stmt::StmtKind::Expr(expr),
                    ..
                }) => typed.phase.types.node_types.get(&expr.id),
                _ => None,
            })
            .next_back();

        match last_expr_ty {
            Some(ty) => ReplEvalResult::Output {
                stdout: String::new(),
                stderr: String::new(),
                value: Some(ty.render_mono()),
            },
            None => ReplEvalResult::Error("/type requires an expression".to_string()),
        }
    }

    pub fn needs_more_input(&self, input: &str) -> bool {
        needs_more_input(input)
    }

    pub fn complete_source(
        &self,
        line: &str,
        pos: usize,
        original_line_offset: usize,
    ) -> ReplCompletions {
        let pos = pos.min(line.len());
        let start = identifier_start(line, pos);
        let prefix = &line[start..pos];
        let (source, byte_offset) = self.source_for_completion(line, pos);
        let doc_id = REPL_DOCUMENT_ID.to_string();
        let doc = DocumentInput {
            id: doc_id.clone(),
            path: self.source_path.to_string_lossy().into_owned(),
            version: 0,
            text: source,
        };

        let Some(workspace) = Workspace::new(vec![doc]) else {
            return ReplCompletions {
                start: original_line_offset + start,
                items: vec![],
            };
        };

        let byte_offset = u32::try_from(byte_offset).unwrap_or(u32::MAX);
        let mut items: Vec<ReplCompletion> =
            complete_in_workspace(&workspace, &doc_id, byte_offset)
                .into_iter()
                .filter(|item| prefix.is_empty() || item.label.starts_with(prefix))
                .map(|item| ReplCompletion {
                    display: match item.detail {
                        Some(detail) => format!("{:<24} {detail}", item.label),
                        None => item.label.clone(),
                    },
                    replacement: item.label,
                })
                .collect();
        items.sort_by(|a, b| a.replacement.cmp(&b.replacement));
        items.dedup_by(|a, b| a.replacement == b.replacement);

        ReplCompletions {
            start: original_line_offset + start,
            items,
        }
    }

    pub fn complete_input(&self, line: &str, pos: usize) -> ReplCompletions {
        let pos = pos.min(line.len());
        if line.starts_with("/type ") && pos >= "/type ".len() {
            return self.complete_source(
                &line["/type ".len()..],
                pos - "/type ".len(),
                "/type ".len(),
            );
        }

        self.complete_source(line, pos, 0)
    }

    fn source_for_completion(&self, line: &str, pos: usize) -> (String, usize) {
        let mut source = self.persistent_source.clone();
        if !source.is_empty() && !source.ends_with('\n') {
            source.push('\n');
        }
        let offset_base = source.len();
        source.push_str(line);
        (source, offset_base + pos)
    }

    fn combined_source(&self, input: &str) -> String {
        let mut source = self.persistent_source.clone();
        if !source.is_empty() && !source.ends_with('\n') {
            source.push('\n');
        }
        source.push_str(input);
        source
    }

    fn persist(&mut self, input: &str) {
        if !self.persistent_source.is_empty() && !self.persistent_source.ends_with('\n') {
            self.persistent_source.push('\n');
        }
        self.persistent_source.push_str(input);
        if !self.persistent_source.ends_with('\n') {
            self.persistent_source.push('\n');
        }
    }

    fn diagnostics_for_source(&self, source: &str) -> Option<Vec<Diagnostic>> {
        let doc = DocumentInput {
            id: REPL_DOCUMENT_ID.to_string(),
            path: self.source_path.to_string_lossy().into_owned(),
            version: 0,
            text: source.to_string(),
        };
        let workspace = Workspace::new(vec![doc])?;
        let diagnostics = workspace.diagnostics.get(REPL_DOCUMENT_ID)?.clone();
        (!diagnostics.is_empty()).then_some(diagnostics)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReplEvalResult {
    Output {
        stdout: String,
        stderr: String,
        value: Option<String>,
    },
    Diagnostics {
        source: String,
        diagnostics: Vec<Diagnostic>,
        message: Option<String>,
    },
    Error(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReplCompletions {
    pub start: usize,
    pub items: Vec<ReplCompletion>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReplCompletion {
    pub display: String,
    pub replacement: String,
}

pub fn needs_more_input(input: &str) -> bool {
    ReplInput::new(input).needs_more_input()
}

struct ReplInput<'a> {
    source: &'a str,
}

impl<'a> ReplInput<'a> {
    fn new(source: &'a str) -> Self {
        Self { source }
    }

    fn is_empty(&self) -> bool {
        self.source.trim().is_empty()
    }

    fn needs_more_input(&self) -> bool {
        let lexer = Lexer::new(self.source);
        let parser = Parser::new(REPL_DOCUMENT_ID, FileID(0), lexer);
        matches!(parser.parse(), Err(ParserError::UnexpectedEndOfInput(_)))
    }

    fn should_persist(&self) -> bool {
        let mut lexer = Lexer::new(self.source);
        let mut saw_public = false;

        loop {
            let Ok(token) = lexer.next() else {
                return false;
            };

            match token.kind {
                TokenKind::Newline | TokenKind::Semicolon => {}
                TokenKind::Public => saw_public = true,
                TokenKind::Let
                | TokenKind::Func
                | TokenKind::Struct
                | TokenKind::Enum
                | TokenKind::Extend
                | TokenKind::Typealias
                | TokenKind::Effect
                | TokenKind::Import
                | TokenKind::Protocol => return true,
                TokenKind::Static if saw_public => {}
                _ => return false,
            }
        }
    }
}

fn identifier_start(line: &str, pos: usize) -> usize {
    let bytes = line.as_bytes();
    let mut start = pos.min(bytes.len());
    while start > 0 && is_identifier_byte(bytes[start - 1]) {
        start -= 1;
    }
    start
}

fn is_identifier_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

#[cfg(test)]
mod tests {
    use super::*;

    fn session() -> ReplSession {
        ReplSession::with_source_path(PathBuf::from("repl.tlk"))
    }

    #[test]
    fn expression_evaluates() {
        let mut session = session();
        let result = session.eval("1 + 1");
        assert_eq!(
            result,
            ReplEvalResult::Output {
                stdout: String::new(),
                stderr: String::new(),
                value: Some("I64(2)".to_string()),
            }
        );
    }

    #[test]
    fn declaration_persists() {
        let mut session = session();
        let result = session.eval("let x = 2");
        assert!(matches!(result, ReplEvalResult::Output { value: None, .. }));
        assert!(session.persistent_source().contains("let x = 2"));

        // The persisted declaration makes `x` resolve and evaluate.
        let result = session.eval("x + 3");
        assert_eq!(
            result,
            ReplEvalResult::Output {
                stdout: String::new(),
                stderr: String::new(),
                value: Some("I64(5)".to_string()),
            }
        );
    }

    #[test]
    fn bad_input_does_not_persist() {
        let mut session = session();
        let result = session.eval("let x =");
        assert!(matches!(result, ReplEvalResult::Diagnostics { .. }));
        let result = session.eval("x");
        assert!(matches!(result, ReplEvalResult::Diagnostics { .. }));
    }

    #[test]
    fn multiline_function_persists() {
        let mut session = session();
        let result = session.eval("func add_one(x) {\n  x + 1\n}");
        assert!(matches!(result, ReplEvalResult::Output { value: None, .. }));
        assert!(session.persistent_source().contains("add_one"));
    }

    #[test]
    fn type_command_reports_types() {
        let session = session();
        let result = session.type_of("1 + 1");
        assert_eq!(
            result,
            ReplEvalResult::Output {
                stdout: String::new(),
                stderr: String::new(),
                value: Some("Int".to_string()),
            }
        );
    }

    #[test]
    fn type_command_shows_schemes_for_identifiers() {
        let mut session = session();
        let result = session.eval("func identity(x) { x }");
        assert!(matches!(result, ReplEvalResult::Output { value: None, .. }));
        let result = session.type_of("identity");
        assert_eq!(
            result,
            ReplEvalResult::Output {
                stdout: String::new(),
                stderr: String::new(),
                value: Some("<T0>(T0) -> T0".to_string()),
            }
        );
    }

    #[test]
    fn semantic_completion_uses_persisted_declarations() {
        let mut session = session();
        let result = session.eval("let longName = 2");
        assert!(matches!(result, ReplEvalResult::Output { value: None, .. }));

        let completions = session.complete_input("long", 4);
        assert!(
            completions
                .items
                .iter()
                .any(|candidate| candidate.replacement == "longName")
        );
    }
}
