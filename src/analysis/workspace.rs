use rustc_hash::FxHashMap;
use std::path::PathBuf;

use crate::analysis::{Diagnostic, DiagnosticSeverity, DocumentId, DocumentInput, TextRange};
use crate::ast::{AST, NameResolved};
use crate::compiling::driver::{Driver, DriverConfig, Source};
use crate::compiling::module::ModuleId;
use crate::diagnostic::AnyDiagnostic;
use crate::node_id::FileID;
use crate::parser_error::ParserError;
use crate::types::type_session::Types;

#[derive(Clone)]
pub struct Workspace {
    pub versions: FxHashMap<DocumentId, i32>,
    pub file_id_to_document: Vec<DocumentId>,
    pub document_to_file_id: FxHashMap<DocumentId, FileID>,
    pub texts: Vec<String>,
    pub asts: Vec<Option<AST<NameResolved>>>,
    pub resolved_names: crate::name_resolution::name_resolver::ResolvedNames,
    pub types: Option<Types>,
    pub diagnostics: FxHashMap<DocumentId, Vec<Diagnostic>>,
}

impl Workspace {
    pub fn new(mut docs: Vec<DocumentInput>) -> Option<Self> {
        if docs.is_empty() {
            return None;
        }

        docs.sort_by(|a, b| a.id.cmp(&b.id));

        let file_id_to_document: Vec<DocumentId> = docs.iter().map(|doc| doc.id.clone()).collect();
        let file_count = file_id_to_document.len();
        if file_count == 0 {
            return None;
        }

        let document_to_file_id: FxHashMap<DocumentId, FileID> = file_id_to_document
            .iter()
            .enumerate()
            .map(|(i, id)| (id.clone(), FileID(i as u32)))
            .collect();

        let versions: FxHashMap<DocumentId, i32> = docs
            .iter()
            .map(|doc| (doc.id.clone(), doc.version))
            .collect();

        let texts: Vec<String> = docs.iter().map(|doc| doc.text.clone()).collect();

        let sources: Vec<Source> = docs
            .iter()
            .map(|doc| Source::in_memory(PathBuf::from(&doc.path), doc.text.clone()))
            .collect();

        let config = DriverConfig::new("Workspace")
            .lenient_parsing()
            .preserve_comments(true);
        let parsed = Driver::new(sources, config).parse().ok()?;
        let resolved = parsed.resolve_names().ok()?;
        let asts_by_source = resolved.phase.asts.clone();
        let typed = resolved.typecheck().ok()?;
        let Driver { phase, .. } = typed;
        let resolved_names = phase.resolved_names;
        let types = Some(phase.types);
        let diagnostics_any = phase.diagnostics;

        let mut asts: Vec<Option<AST<NameResolved>>> = vec![None; file_id_to_document.len()];
        for ast in asts_by_source.values() {
            let idx = ast.file_id.0 as usize;
            if idx < asts.len() {
                asts[idx] = Some(ast.clone());
            }
        }

        let mut diagnostics: FxHashMap<DocumentId, Vec<Diagnostic>> = FxHashMap::default();
        for diagnostic in diagnostics_any.iter() {
            if let Some((doc_id, diagnostic)) =
                diagnostic_for_any(&file_id_to_document, &texts, &asts, diagnostic)
            {
                diagnostics.entry(doc_id).or_default().push(diagnostic);
            }
        }

        for diagnostics in diagnostics.values_mut() {
            diagnostics.sort_by_key(|d| (d.range.start, d.range.end, d.message.clone()));
        }

        Some(Self {
            versions,
            file_id_to_document,
            document_to_file_id,
            texts,
            asts,
            resolved_names,
            types,
            diagnostics,
        })
    }

    pub fn core() -> Option<Self> {
        let root = std::env::current_dir().ok()?;
        let core_files: [(std::path::PathBuf, &str); 5] = [
            (
                root.join("core/Optional.tlk"),
                include_str!("../../core/Optional.tlk"),
            ),
            (
                root.join("core/Operators.tlk"),
                include_str!("../../core/Operators.tlk"),
            ),
            (
                root.join("core/String.tlk"),
                include_str!("../../core/String.tlk"),
            ),
            (
                root.join("core/Memory.tlk"),
                include_str!("../../core/Memory.tlk"),
            ),
            (
                root.join("core/Array.tlk"),
                include_str!("../../core/Array.tlk"),
            ),
        ];

        let file_id_to_document: Vec<DocumentId> = core_files
            .iter()
            .map(|(path, _)| path.to_string_lossy().into_owned())
            .collect();

        if file_id_to_document.len() != core_files.len() {
            return None;
        }

        let document_to_file_id: FxHashMap<DocumentId, FileID> = file_id_to_document
            .iter()
            .enumerate()
            .map(|(i, id)| (id.clone(), FileID(i as u32)))
            .collect();

        let texts: Vec<String> = core_files
            .iter()
            .map(|(_, text)| (*text).to_string())
            .collect();
        let sources: Vec<Source> = core_files
            .iter()
            .map(|(path, text)| Source::in_memory(path.clone(), *text))
            .collect();

        let mut config = DriverConfig::new("Core").preserve_comments(true);
        config.module_id = ModuleId::Core;

        let driver = Driver::new_bare(sources, config);
        let resolved = driver.parse().ok()?.resolve_names().ok()?;

        let resolved_names = resolved.phase.resolved_names.clone();

        let mut asts: Vec<Option<AST<NameResolved>>> = vec![None; file_id_to_document.len()];
        for ast in resolved.phase.asts.values() {
            let idx = ast.file_id.0 as usize;
            if idx < asts.len() {
                asts[idx] = Some(ast.clone());
            }
        }

        Some(Self {
            versions: FxHashMap::default(),
            file_id_to_document,
            document_to_file_id,
            texts,
            asts,
            resolved_names,
            types: None,
            diagnostics: FxHashMap::default(),
        })
    }

    pub fn document_index(&self, id: &DocumentId) -> Option<usize> {
        self.document_to_file_id.get(id).map(|id| id.0 as usize)
    }

    pub fn text_for(&self, id: &DocumentId) -> Option<&str> {
        let idx = self.document_index(id)?;
        self.texts.get(idx).map(|text| text.as_str())
    }

    pub fn ast_for(&self, id: &DocumentId) -> Option<&AST<NameResolved>> {
        let idx = self.document_index(id)?;
        self.asts.get(idx).and_then(|ast| ast.as_ref())
    }
}

fn parser_error_range(text: &str, err: &ParserError) -> TextRange {
    let eof = text.len() as u32;

    match err {
        ParserError::UnexpectedToken {
            token: Some(token), ..
        } => TextRange::new(token.start, token.end),
        ParserError::InfiniteLoop(Some(token)) | ParserError::ExpectedIdentifier(Some(token)) => {
            TextRange::new(token.start, token.end)
        }
        ParserError::UnexpectedEndOfInput(..) => TextRange::new(eof, eof),
        _ => TextRange::new(0, 0),
    }
}

fn diagnostic_for_any(
    file_id_to_document: &[DocumentId],
    texts: &[String],
    asts: &[Option<AST<NameResolved>>],
    diagnostic: &AnyDiagnostic,
) -> Option<(DocumentId, Diagnostic)> {
    let (id, message, parse_error) = match diagnostic {
        AnyDiagnostic::Parsing(diagnostic) => (
            diagnostic.id,
            diagnostic.kind.to_string(),
            Some(&diagnostic.kind),
        ),
        AnyDiagnostic::NameResolution(diagnostic) => {
            (diagnostic.id, diagnostic.kind.to_string(), None)
        }
        AnyDiagnostic::Typing(diagnostic) => (diagnostic.id, diagnostic.kind.to_string(), None),
    };

    let file_idx = id.0.0 as usize;
    let doc_id = file_id_to_document.get(file_idx)?.clone();

    let range = if let Some(err) = parse_error {
        texts
            .get(file_idx)
            .map(|text| parser_error_range(text, err))
            .unwrap_or_else(|| TextRange::new(0, 0))
    } else {
        match (
            texts.get(file_idx),
            asts.get(file_idx).and_then(|a| a.as_ref()),
        ) {
            (Some(_text), Some(ast)) => match ast.meta.get(&id) {
                Some(meta) => {
                    let (start, end) = meta
                        .identifiers
                        .last()
                        .map(|t| (t.start, t.end))
                        .unwrap_or((meta.start.start, meta.end.end));
                    TextRange::new(start, end)
                }
                None => TextRange::new(0, 0),
            },
            _ => TextRange::new(0, 0),
        }
    };

    Some((
        doc_id,
        Diagnostic {
            range,
            severity: DiagnosticSeverity::Error,
            message,
        },
    ))
}
