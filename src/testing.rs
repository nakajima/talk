use std::{
    error::Error as StdError,
    fmt::{Display, Formatter},
    path::{Path, PathBuf},
};

use indexmap::IndexMap;

use crate::{
    analysis::{Diagnostic, DocumentId},
    ast::{AST, NameResolved},
    compiling::driver::{Driver, DriverConfig, Source},
    diagnostic::AnyDiagnostic,
    vm::interp::Value,
};

const HARNESS_PRELUDE_SOURCE: &str = include_str!("../stdlib/testing_prelude.tlk");
const HARNESS_POSTLUDE_SOURCE: &str = include_str!("../stdlib/testing_postlude.tlk");
const HARNESS_PRELUDE_PATH: &str = "/talk-test-harness/testing_prelude.tlk";
const HARNESS_POSTLUDE_PATH: &str = "/talk-test-harness/testing_postlude.tlk";

#[derive(Debug)]
pub struct Runner {
    roots: Vec<PathBuf>,
}

#[derive(Debug)]
pub enum Outcome {
    NoTests,
    Finished(Summary),
}

#[derive(Debug)]
pub struct Summary {
    pub output: String,
    pub failures: i64,
}

impl Summary {
    pub fn failed(&self) -> bool {
        self.failures > 0
    }
}

#[derive(Clone, Debug)]
pub struct CompileDiagnostic {
    pub document_id: DocumentId,
    pub text: String,
    pub diagnostic: Diagnostic,
}

#[derive(Clone, Debug)]
pub struct CompileDiagnostics {
    pub entries: Vec<CompileDiagnostic>,
}

impl CompileDiagnostics {
    #[cfg(feature = "cli")]
    pub fn render_text(&self, color_mode: crate::cli::diagnostics::ColorMode) -> String {
        let mut output = String::new();
        for entry in &self.entries {
            output.push_str(&crate::cli::diagnostics::render_text(
                &entry.document_id,
                &entry.text,
                &entry.diagnostic,
                color_mode,
            ));
        }
        output
    }
}

#[derive(Debug)]
pub enum TestError {
    Discovery(String),
    Compile(String),
    CompileDiagnostics(CompileDiagnostics),
    Runtime(String),
    UnexpectedReturn(String),
}

impl Display for TestError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Discovery(message)
            | Self::Compile(message)
            | Self::Runtime(message)
            | Self::UnexpectedReturn(message) => f.write_str(message),
            Self::CompileDiagnostics(diagnostics) => {
                if diagnostics.entries.is_empty() {
                    return f.write_str("compilation failed");
                }
                for (index, entry) in diagnostics.entries.iter().enumerate() {
                    if index > 0 {
                        writeln!(f)?;
                    }
                    write!(f, "{}: {}", entry.document_id, entry.diagnostic.message)?;
                }
                Ok(())
            }
        }
    }
}

impl StdError for TestError {}

impl Runner {
    pub fn new(roots: impl IntoIterator<Item = PathBuf>) -> Self {
        Self {
            roots: roots.into_iter().collect(),
        }
    }

    pub fn run(&self) -> Result<Outcome, TestError> {
        let test_sources = self.discover_sources()?;
        if test_sources.is_empty() {
            return Ok(Outcome::NoTests);
        }

        let sources = self.suite_sources(test_sources)?;
        let mut lowered = self.compile_sources(sources)?;
        let (value, output) = lowered.run_vm_with_output().map_err(TestError::Runtime)?;
        let failures = match value {
            Value::I64(failures) => failures,
            other => {
                return Err(TestError::UnexpectedReturn(format!(
                    "test harness returned {other:?}, expected Int"
                )));
            }
        };
        Ok(Outcome::Finished(Summary { output, failures }))
    }

    fn discover_sources(&self) -> Result<Vec<Source>, TestError> {
        let mut files = Vec::new();
        if self.roots.is_empty() {
            Self::collect_dir(Path::new("."), &mut files)?;
        } else {
            for root in &self.roots {
                if root.is_dir() {
                    Self::collect_dir(root, &mut files)?;
                } else if root.is_file() {
                    if !Self::is_test_file(root) {
                        return Err(TestError::Discovery(format!(
                            "{} is not a .test.tlk file",
                            root.display()
                        )));
                    }
                    files.push(root.canonicalize().unwrap_or_else(|_| root.clone()));
                } else {
                    return Err(TestError::Discovery(format!(
                        "{} does not exist",
                        root.display()
                    )));
                }
            }
        }

        files.sort();
        files.dedup();
        Ok(files.into_iter().map(Source::from).collect())
    }

    fn collect_dir(dir: &Path, files: &mut Vec<PathBuf>) -> Result<(), TestError> {
        let entries = std::fs::read_dir(dir).map_err(|err| {
            TestError::Discovery(format!("failed to read {}: {err}", dir.display()))
        })?;
        for entry in entries {
            let entry = entry.map_err(|err| {
                TestError::Discovery(format!("failed to read directory entry: {err}"))
            })?;
            let path = entry.path();
            let file_name = path
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or("");
            if path.is_dir() && !file_name.starts_with(".") {
                if matches!(file_name, ".git" | "target") {
                    continue;
                }
                Self::collect_dir(&path, files)?;
            } else if Self::is_test_file(&path) {
                files.push(path.canonicalize().unwrap_or(path));
            }
        }
        Ok(())
    }

    fn suite_sources(&self, test_sources: Vec<Source>) -> Result<Vec<Source>, TestError> {
        let parsed = Driver::new(test_sources, Self::compile_config())
            .parse()
            .map_err(|err| TestError::Compile(format!("{err:?}")))?;

        let mut sources = Vec::with_capacity(parsed.phase.asts.len() + 2);
        sources.push(Harness::prelude_source());
        sources.extend(parsed.phase.asts.keys().cloned());
        sources.push(Harness::postlude_source());
        Ok(sources)
    }

    fn compile_sources(
        &self,
        sources: Vec<Source>,
    ) -> Result<Driver<crate::compiling::driver::Lowered>, TestError> {
        let driver = Driver::new(sources, Self::compile_config());
        let parsed = driver
            .parse()
            .map_err(|err| TestError::Compile(format!("{err:?}")))?;
        let resolved = parsed
            .resolve_names()
            .map_err(|err| TestError::Compile(format!("{err:?}")))?;
        let asts_by_source = resolved.phase.asts.clone();
        let typed = resolved.type_check();
        if typed.has_errors() {
            let diagnostics = Self::compile_diagnostics(&asts_by_source, typed.diagnostics());
            if diagnostics.entries.is_empty() {
                return Err(TestError::Compile(
                    typed
                        .diagnostics()
                        .iter()
                        .map(|diagnostic| format!("{diagnostic:?}"))
                        .collect::<Vec<_>>()
                        .join("\n"),
                ));
            }
            return Err(TestError::CompileDiagnostics(diagnostics));
        }
        let lowered = typed.lower();
        if !lowered.phase.diagnostics.is_empty() {
            return Err(TestError::Compile(lowered.phase.diagnostics.join("\n")));
        }
        Ok(lowered)
    }

    fn compile_config() -> DriverConfig {
        DriverConfig::new("TalkTests")
            .lenient_parsing()
            .preserve_comments(true)
    }

    fn compile_diagnostics(
        asts_by_source: &IndexMap<Source, AST<NameResolved>>,
        diagnostics: &[AnyDiagnostic],
    ) -> CompileDiagnostics {
        let file_count = asts_by_source
            .values()
            .map(|ast| ast.file_id.0 as usize + 1)
            .max()
            .unwrap_or(0);
        let mut file_id_to_document = vec![String::new(); file_count];
        let mut texts = vec![String::new(); file_count];
        let mut asts = vec![None; file_count];

        for (source, ast) in asts_by_source {
            let index = ast.file_id.0 as usize;
            if index >= file_id_to_document.len() {
                continue;
            }
            file_id_to_document[index] = source.path().into_owned();
            texts[index] = source.read().unwrap_or_default();
            asts[index] = Some(ast.clone());
        }

        let mut entries: Vec<_> = diagnostics
            .iter()
            .filter_map(|diagnostic| {
                let file_index = Self::diagnostic_file_index(diagnostic);
                crate::analysis::workspace::diagnostic_for_any(
                    &file_id_to_document,
                    &texts,
                    &asts,
                    diagnostic,
                )
                .map(|(document_id, diagnostic)| CompileDiagnostic {
                    document_id,
                    text: texts.get(file_index).cloned().unwrap_or_default(),
                    diagnostic,
                })
            })
            .collect();
        entries.sort_by(|left, right| {
            left.document_id
                .cmp(&right.document_id)
                .then(
                    left.diagnostic
                        .range
                        .start
                        .cmp(&right.diagnostic.range.start),
                )
                .then(left.diagnostic.range.end.cmp(&right.diagnostic.range.end))
                .then(left.diagnostic.message.cmp(&right.diagnostic.message))
        });
        CompileDiagnostics { entries }
    }

    fn diagnostic_file_index(diagnostic: &AnyDiagnostic) -> usize {
        match diagnostic {
            AnyDiagnostic::Parsing(diagnostic) => diagnostic.id.0.0 as usize,
            AnyDiagnostic::NameResolution(diagnostic) => diagnostic.id.0.0 as usize,
            AnyDiagnostic::Types(diagnostic) => diagnostic.id.0.0 as usize,
            AnyDiagnostic::Ownership(diagnostic) => diagnostic.id.0.0 as usize,
        }
    }

    fn is_test_file(path: &Path) -> bool {
        path.file_name()
            .and_then(|name| name.to_str())
            .is_some_and(|name| name.ends_with(".test.tlk"))
    }
}

struct Harness;

impl Harness {
    fn prelude_source() -> Source {
        Source::in_memory(PathBuf::from(HARNESS_PRELUDE_PATH), HARNESS_PRELUDE_SOURCE)
    }

    fn postlude_source() -> Source {
        Source::in_memory(
            PathBuf::from(HARNESS_POSTLUDE_PATH),
            HARNESS_POSTLUDE_SOURCE,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn temp_project(name: &str) -> PathBuf {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("time")
            .as_nanos();
        let dir = std::env::temp_dir().join(format!("talk-{name}-{}-{nonce}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("project dir");
        dir
    }

    #[test]
    fn harness_sources_type_check() {
        let typed = Driver::new(
            vec![Harness::prelude_source(), Harness::postlude_source()],
            DriverConfig::new("Harness"),
        )
        .parse()
        .expect("parse")
        .resolve_names()
        .expect("resolve")
        .type_check();
        assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
    }

    #[test]
    fn runner_handles_test_files_below_project_src() {
        let project = temp_project("nested-test-runner");
        let src = project.join("src");
        std::fs::create_dir_all(&src).expect("src dir");
        std::fs::write(
            src.join("testing.tlk"),
            "effect 'failure(String) -> Never\n\
struct TestCase { let name: String let block: () -> Void }\n\
public func test(name: String, block: () -> Void) { () }\n\
public func assert(pass: Bool, msg: String) 'failure {\n\
\tif !pass { 'failure(msg) }\n\
}\n",
        )
        .expect("local testing helper");
        std::fs::write(
            src.join("math.test.tlk"),
            "use testing\n\
test(\"ok\") {\n\tassert(1 + 1 == 2)\n}\n",
        )
        .expect("test file");

        let outcome = Runner::new([project]).run().expect("runner");
        let Outcome::Finished(summary) = outcome else {
            panic!("expected tests to run");
        };
        assert_eq!(summary.failures, 0);
        assert_eq!(summary.output, "\u{1b}[32m.\u{1b}[0m\n1 tests passed.\n");
    }

    #[test]
    fn runner_reports_compile_errors_as_source_diagnostics() {
        let project = temp_project("compile-error-test-runner");
        let test_path = project.join("bad.test.tlk");
        std::fs::write(&test_path, "test \"bad\" {\n\tlet x: Int = \"nope\"\n}\n")
            .expect("test file");

        let err = Runner::new([project]).run().expect_err("compile error");
        let TestError::CompileDiagnostics(diagnostics) = err else {
            panic!("expected source diagnostics");
        };
        assert_eq!(diagnostics.entries.len(), 1, "{diagnostics:?}");
        let entry = &diagnostics.entries[0];
        assert!(
            entry.document_id.ends_with("bad.test.tlk"),
            "{}",
            entry.document_id
        );
        assert!(entry.diagnostic.message.contains("Type mismatch"));
        assert!(entry.text.contains("let x: Int"));
    }

    #[test]
    fn runner_counts_assertion_failures() {
        let project = temp_project("failing-test-runner");
        std::fs::write(
            project.join("math.test.tlk"),
            "test(\"bad\") {\n\tassertMessage(false, \"nope\")\n}\n",
        )
        .expect("test file");

        let outcome = Runner::new([project]).run().expect("runner");
        let Outcome::Finished(summary) = outcome else {
            panic!("expected tests to run");
        };
        assert_eq!(summary.failures, 1);
        assert_eq!(
            summary.output,
            "\u{1b}[31mF\u{1b}[0m\u{1b}[32m.\u{1b}[0m\n\u{1b}[31mbad\u{1b}[0m: nope\n"
        );
    }
}
