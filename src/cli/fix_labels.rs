//! `talk fix-labels` — the ADR 0041 migration tool. Compiles Talk sources,
//! reads the structured `type.argument-label-mismatch` diagnostics, and
//! rewrites call sites to match the declared labels: inserting a missing
//! label, replacing an incorrect one, or removing an unexpected one. Runs
//! to a fixed point, since arity-gated calls can reveal new mismatches
//! once earlier rounds fix their neighbors.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use crate::common::diagnostic::AnyDiagnostic;
use crate::compiling::driver::{CompilationMode, Driver, DriverConfig, Source};
use crate::compiling::module::ModuleId;
use crate::node_id::FileID;
use crate::types::error::{LabelMismatch, TypeError};

/// One byte-level rewrite in a file.
struct Edit {
    start: u32,
    end: u32,
    replacement: String,
}

fn edit_for(mismatch: &LabelMismatch) -> Edit {
    match (&mismatch.expected, &mismatch.found) {
        // Missing label: insert before the ownership marker or value.
        (Some(expected), None) => Edit {
            start: mismatch.insert_at,
            end: mismatch.insert_at,
            replacement: format!("{expected}: "),
        },
        // Incorrect label: replace only the label token.
        (Some(expected), Some(_)) => Edit {
            start: mismatch.label_span.start,
            end: mismatch.label_span.end,
            replacement: expected.clone(),
        },
        // Unexpected label: remove the label, colon, and whitespace up to
        // the ownership marker or value.
        (None, Some(_)) => Edit {
            start: mismatch.label_span.start,
            end: mismatch.insert_at,
            replacement: String::new(),
        },
        (None, None) => unreachable!("a label mismatch names at least one label"),
    }
}

/// Apply one round of fixes. Returns the number of edits applied.
fn apply_round(sources: &[Source], diagnostics: &[AnyDiagnostic]) -> std::io::Result<usize> {
    let mut edits: HashMap<FileID, Vec<Edit>> = HashMap::new();
    for diagnostic in diagnostics {
        let AnyDiagnostic::Types(diagnostic) = diagnostic else {
            continue;
        };
        let TypeError::ArgumentLabelMismatch { mismatches, .. } = &diagnostic.kind else {
            continue;
        };
        for mismatch in mismatches {
            edits
                .entry(mismatch.label_span.file_id)
                .or_default()
                .push(edit_for(mismatch));
        }
    }

    let mut applied = 0;
    for (file_id, mut file_edits) in edits {
        let Some(source) = sources.get(file_id.0 as usize) else {
            continue;
        };
        let path = PathBuf::from(source.path().to_string());
        let mut text = std::fs::read_to_string(&path)?;
        // Bottom-up so earlier offsets stay valid; drop overlaps (they
        // re-resolve next round).
        file_edits.sort_by(|a, b| b.start.cmp(&a.start));
        let mut last_start = u32::MAX;
        for edit in file_edits {
            if edit.end > last_start {
                continue;
            }
            last_start = edit.start;
            text.replace_range(edit.start as usize..edit.end as usize, &edit.replacement);
            applied += 1;
        }
        std::fs::write(&path, text)?;
    }
    Ok(applied)
}

fn label_mismatch_count(diagnostics: &[AnyDiagnostic]) -> usize {
    diagnostics
        .iter()
        .filter(|diagnostic| {
            matches!(
                diagnostic,
                AnyDiagnostic::Types(d) if matches!(d.kind, TypeError::ArgumentLabelMismatch { .. })
            )
        })
        .count()
}

/// Run one program's fix loop to a fixed point. Returns edits applied.
fn run_program(sources: Vec<Source>, config: impl Fn() -> DriverConfig) -> Result<usize, String> {
    let mut total = 0;
    loop {
        let cfg = config();
        let bare = cfg.module_id == ModuleId::Core;
        let driver = if bare {
            Driver::new_bare(sources.clone(), cfg)
        } else {
            Driver::new(sources.clone(), cfg)
        };
        let typed = driver
            .parse()
            .map_err(|err| format!("parse failed: {err:?}"))?
            .resolve_names()
            .map_err(|err| format!("name resolution failed: {err:?}"))?
            .type_check();
        let diagnostics = &typed.phase.diagnostics;
        if label_mismatch_count(diagnostics) == 0 {
            return Ok(total);
        }
        let applied = apply_round(&sources, diagnostics).map_err(|err| err.to_string())?;
        if applied == 0 {
            return Err(format!(
                "{} label mismatches remain but no edits could be applied",
                label_mismatch_count(diagnostics)
            ));
        }
        total += applied;
    }
}

/// Fix the core corpus in `core_dir`; or each file as its own program when
/// `each` is set; or one program from `filenames`. Returns edits applied.
pub fn run(core_dir: Option<&Path>, filenames: &[PathBuf], each: bool) -> Result<usize, String> {
    if let Some(dir) = core_dir {
        let sources: Vec<Source> = crate::compiling::core::CORE_SOURCE_NAMES
            .iter()
            .map(|name| Source::from(dir.join(name)))
            .collect();
        return run_program(sources, || {
            let mut config = DriverConfig::new("Core");
            config.module_id = ModuleId::Core;
            config.mode = CompilationMode::Library;
            config
        });
    }
    if each {
        let mut total = 0;
        for path in filenames {
            match run_program(vec![Source::from(path.clone())], || {
                DriverConfig::new("FixLabels")
            }) {
                Ok(applied) => total += applied,
                Err(err) => eprintln!("{}: {err}", path.display()),
            }
        }
        return Ok(total);
    }
    let sources: Vec<Source> = filenames
        .iter()
        .map(|path| Source::from(path.clone()))
        .collect();
    run_program(sources, || DriverConfig::new("FixLabels"))
}
