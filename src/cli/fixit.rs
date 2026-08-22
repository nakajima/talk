//! `talk fixit` applies the same preferred quick fixes exposed by the LSP's
//! `source.fixAll` action. The compiler, not the CLI, decides which repairs
//! are unambiguous enough to apply automatically.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use async_lsp::lsp_types::{CodeActionKind, CodeActionOrCommand, Position, Range, Url};

use crate::analysis::{DocumentInput, Workspace};
use crate::lsp::document::Document;

pub fn run(paths: &[PathBuf]) -> Result<usize, String> {
    Fixit::new(paths)?.run()
}

struct Fixit {
    paths: Vec<PathBuf>,
    package_root: Option<PathBuf>,
}

impl Fixit {
    fn new(paths: &[PathBuf]) -> Result<Self, String> {
        let package_root = if paths.is_empty() {
            crate::compiling::package::PackageProject::enclosing_root(".")
        } else {
            paths
                .first()
                .and_then(crate::compiling::package::PackageProject::enclosing_root)
        };
        let paths = if paths.is_empty() {
            let Some(root) = &package_root else {
                return Err("talk fixit needs source paths outside a package".to_string());
            };
            crate::cli::package::workspace_source_files(root)
        } else {
            paths.to_vec()
        };
        if paths.is_empty() {
            return Err("talk fixit found no source files".to_string());
        }
        for path in &paths {
            if !path.is_file() {
                return Err(format!(
                    "talk fixit expected a source file: {}",
                    path.display()
                ));
            }
        }
        Ok(Self {
            paths,
            package_root,
        })
    }

    fn run(&self) -> Result<usize, String> {
        let mut total = 0;
        let mut seen = HashSet::new();
        for _ in 0..32 {
            let fingerprint = self.fingerprint()?;
            if !seen.insert(fingerprint) {
                return Err("talk fixit reached a repeating edit state".to_string());
            }
            let applied = self.apply_round()?;
            total += applied;
            if applied == 0 {
                return Ok(total);
            }
        }
        Err("talk fixit did not reach a fixed point after 32 rounds".to_string())
    }

    fn fingerprint(&self) -> Result<String, String> {
        let mut fingerprint = String::new();
        for path in &self.paths {
            fingerprint.push_str(&path.to_string_lossy());
            fingerprint.push('\0');
            fingerprint.push_str(
                &std::fs::read_to_string(path)
                    .map_err(|error| format!("failed to read {}: {error}", path.display()))?,
            );
            fingerprint.push('\0');
        }
        Ok(fingerprint)
    }

    fn workspace(&self) -> Result<Workspace, String> {
        let mut docs = Vec::with_capacity(self.paths.len());
        for path in &self.paths {
            let text = std::fs::read_to_string(path)
                .map_err(|error| format!("failed to read {}: {error}", path.display()))?;
            let path = path.to_string_lossy().into_owned();
            docs.push(DocumentInput {
                id: path.clone(),
                path,
                version: 0,
                text: text.into(),
            });
        }
        let package = match &self.package_root {
            Some(root) => {
                let project = crate::compiling::package::PackageProject::open_at(root, false)
                    .map_err(|error| error.to_string())?;
                Some(
                    project
                        .package_compile_context()
                        .map_err(|error| error.to_string())?,
                )
            }
            None => None,
        };
        Workspace::new_with_package(docs, package)
            .ok_or_else(|| "talk fixit could not build the source workspace".to_string())
    }

    fn apply_round(&self) -> Result<usize, String> {
        let workspace = self.workspace()?;
        let mut applied = 0;
        for path in &self.paths {
            applied += self.apply_document(&workspace, path)?;
        }
        Ok(applied)
    }

    fn apply_document(&self, workspace: &Workspace, path: &Path) -> Result<usize, String> {
        let document_id = path.to_string_lossy().into_owned();
        let Some(text) = workspace.text_for(&document_id) else {
            return Ok(0);
        };
        let absolute = if path.is_absolute() {
            path.to_path_buf()
        } else {
            std::env::current_dir()
                .map_err(|error| error.to_string())?
                .join(path)
        };
        let uri = Url::from_file_path(&absolute)
            .map_err(|_| format!("cannot convert {} to a file URL", absolute.display()))?;
        let actions = crate::lsp::code_actions::compute_code_actions(
            workspace,
            &document_id,
            &uri,
            Range::new(Position::new(0, 0), Position::new(u32::MAX, u32::MAX)),
        );
        let mut edits = Vec::new();
        for action in actions {
            let CodeActionOrCommand::CodeAction(action) = action else {
                continue;
            };
            if action.kind != Some(CodeActionKind::SOURCE_FIX_ALL) {
                continue;
            }
            let Some(changes) = action.edit.and_then(|edit| edit.changes) else {
                continue;
            };
            if let Some(uri_edits) = changes.get(&uri) {
                edits.extend(uri_edits.iter().cloned());
            }
        }
        if edits.is_empty() {
            return Ok(0);
        }

        let document = Document::new(0, text.to_string());
        let mut byte_edits = Vec::with_capacity(edits.len());
        for edit in edits {
            let Some(start) = document.byte_offset(edit.range.start) else {
                return Err(format!("cannot map a fix start in {}", path.display()));
            };
            let Some(end) = document.byte_offset(edit.range.end) else {
                return Err(format!("cannot map a fix end in {}", path.display()));
            };
            byte_edits.push((start, end, edit.new_text));
        }
        byte_edits.sort_by(|left, right| right.0.cmp(&left.0).then(right.1.cmp(&left.1)));

        let mut next = text.to_string();
        let mut boundary = usize::MAX;
        let mut count = 0;
        for (start, end, replacement) in byte_edits {
            if start > end || end > boundary {
                continue;
            }
            next.replace_range(start..end, &replacement);
            boundary = start;
            count += 1;
        }
        std::fs::write(path, next)
            .map_err(|error| format!("failed to write {}: {error}", path.display()))?;
        Ok(count)
    }
}
