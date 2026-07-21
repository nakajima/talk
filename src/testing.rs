use std::{
    error::Error as StdError,
    fmt::{Display, Formatter, Write as _},
    path::{Path, PathBuf},
};

use indexmap::IndexMap;

use crate::{
    analysis::{Diagnostic, DocumentId},
    ast::{AST, NameResolved},
    compiling::driver::{Driver, DriverConfig, Source, Typed, execute_module},
    diagnostic::AnyDiagnostic,
};

const HARNESS_PRELUDE_SOURCE: &str = include_str!("../stdlib/testing_prelude.tlk");
const HARNESS_JSON_PRELUDE_SOURCE: &str = include_str!("../stdlib/testing_json_prelude.tlk");
const HARNESS_POSTLUDE_SOURCE: &str = include_str!("../stdlib/testing_postlude.tlk");
const HARNESS_DIR: &str = "__talk_test_harness";
const JSON_EVENT_PREFIX: &str = "__TALKTEST_EVENT_V1__\t";

#[derive(Debug)]
pub struct Runner {
    roots: Vec<PathBuf>,
    config: Option<DriverConfig>,
    filter: Option<String>,
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

#[derive(Debug)]
pub enum JsonOutcome {
    NoTests,
    Finished(JsonSummary),
}

#[derive(Debug)]
pub struct JsonSummary {
    pub output: String,
    pub failures: i64,
    pub tests: Vec<JsonTest>,
}

#[derive(Debug)]
pub struct JsonTest {
    pub name: String,
    pub status: JsonStatus,
    pub failures: Vec<String>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum JsonStatus {
    Passed,
    Failed,
}

impl JsonOutcome {
    pub fn failed(&self) -> bool {
        match self {
            Self::NoTests => false,
            Self::Finished(summary) => summary.failed(),
        }
    }

    pub fn to_json(&self) -> String {
        match self {
            Self::NoTests => {
                "{\"status\":\"no_tests\",\"failures\":0,\"tests\":[],\"output\":\"\"}".to_string()
            }
            Self::Finished(summary) => summary.to_json(),
        }
    }

    pub fn error_json(kind: &str, message: &str) -> String {
        let mut json = String::new();
        json.push_str("{\"status\":\"error\",\"error\":{\"kind\":\"");
        let _ = write!(&mut json, "{}", JsonEscaped(kind));
        json.push_str("\",\"message\":\"");
        let _ = write!(&mut json, "{}", JsonEscaped(message));
        json.push_str("\"},\"failures\":0,\"tests\":[],\"output\":\"\"}");
        json
    }
}

impl JsonSummary {
    pub fn failed(&self) -> bool {
        self.failures > 0
    }

    fn to_json(&self) -> String {
        let mut json = String::new();
        json.push_str("{\"status\":\"finished\",\"failures\":");
        let _ = write!(&mut json, "{}", self.failures);
        json.push_str(",\"tests\":[");
        for (index, test) in self.tests.iter().enumerate() {
            if index > 0 {
                json.push(',');
            }
            test.push_json(&mut json);
        }
        json.push_str("],\"output\":\"");
        let _ = write!(&mut json, "{}", JsonEscaped(&self.output));
        json.push_str("\"}");
        json
    }
}

impl JsonTest {
    fn push_json(&self, json: &mut String) {
        json.push_str("{\"name\":\"");
        let _ = write!(json, "{}", JsonEscaped(&self.name));
        json.push_str("\",\"status\":\"");
        json.push_str(self.status.as_str());
        json.push_str("\",\"failures\":[");
        for (index, failure) in self.failures.iter().enumerate() {
            if index > 0 {
                json.push(',');
            }
            json.push('"');
            let _ = write!(json, "{}", JsonEscaped(failure));
            json.push('"');
        }
        json.push_str("]}");
    }
}

impl JsonStatus {
    fn as_str(self) -> &'static str {
        match self {
            Self::Passed => "passed",
            Self::Failed => "failed",
        }
    }
}

struct JsonEscaped<'a>(&'a str);

impl Display for JsonEscaped<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for ch in self.0.chars() {
            match ch {
                '"' => f.write_str("\\\"")?,
                '\\' => f.write_str("\\\\")?,
                '\n' => f.write_str("\\n")?,
                '\r' => f.write_str("\\r")?,
                '\t' => f.write_str("\\t")?,
                ch if ch <= '\u{1f}' => write!(f, "\\u{:04x}", ch as u32)?,
                ch => f.write_char(ch)?,
            }
        }
        Ok(())
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

impl TestError {
    pub fn kind(&self) -> &'static str {
        match self {
            Self::Discovery(_) => "discovery",
            Self::Compile(_) | Self::CompileDiagnostics(_) => "compile",
            Self::Runtime(_) => "runtime",
            Self::UnexpectedReturn(_) => "unexpected_return",
        }
    }

    pub fn to_json(&self) -> String {
        JsonOutcome::error_json(self.kind(), &self.to_string())
    }
}

impl StdError for TestError {}

struct JsonEventParser {
    tests: Vec<JsonTest>,
    output: String,
    active: Option<usize>,
}

impl JsonEventParser {
    fn parse(output: &str) -> Result<Self, TestError> {
        let mut parser = Self {
            tests: Vec::new(),
            output: String::new(),
            active: None,
        };
        let mut remaining = output;
        while let Some(prefix_index) = remaining.find(JSON_EVENT_PREFIX) {
            parser.output.push_str(&remaining[..prefix_index]);
            let after_prefix = &remaining[prefix_index + JSON_EVENT_PREFIX.len()..];
            if let Some(newline_index) = after_prefix.find('\n') {
                let event = after_prefix[..newline_index]
                    .strip_suffix('\r')
                    .unwrap_or(&after_prefix[..newline_index]);
                parser.parse_event(event)?;
                remaining = &after_prefix[newline_index + 1..];
            } else {
                let event = after_prefix.strip_suffix('\r').unwrap_or(after_prefix);
                parser.parse_event(event)?;
                remaining = "";
            }
        }
        parser.output.push_str(remaining);
        if parser.active.is_some() {
            return Err(TestError::UnexpectedReturn(
                "test event stream ended during a test".into(),
            ));
        }
        Ok(parser)
    }

    fn into_summary(self, failures: i64) -> JsonSummary {
        JsonSummary {
            output: self.output,
            failures,
            tests: self.tests,
        }
    }

    fn parse_event(&mut self, event: &str) -> Result<(), TestError> {
        let mut parts = event.split('\t');
        let kind = parts.next().unwrap_or_default();
        match kind {
            "start" => {
                let name = Self::decode_hex(Self::next_part(&mut parts, "start name")?)?;
                Self::finish_parts(parts)?;
                if self.active.is_some() {
                    return Err(TestError::UnexpectedReturn(
                        "test event stream started a test before ending the previous test".into(),
                    ));
                }
                self.tests.push(JsonTest {
                    name,
                    status: JsonStatus::Passed,
                    failures: Vec::new(),
                });
                self.active = self.tests.len().checked_sub(1);
                Ok(())
            }
            "failure" => {
                let message = Self::decode_hex(Self::next_part(&mut parts, "failure message")?)?;
                Self::finish_parts(parts)?;
                let active = self.active.ok_or_else(|| {
                    TestError::UnexpectedReturn("test failure event had no active test".into())
                })?;
                let test = self.tests.get_mut(active).ok_or_else(|| {
                    TestError::UnexpectedReturn(
                        "test failure event pointed outside the test list".into(),
                    )
                })?;
                test.status = JsonStatus::Failed;
                test.failures.push(message);
                Ok(())
            }
            "end" => {
                let status = Self::next_part(&mut parts, "end status")?;
                let status = match status {
                    "passed" => JsonStatus::Passed,
                    "failed" => JsonStatus::Failed,
                    other => {
                        return Err(TestError::UnexpectedReturn(format!(
                            "test end event had invalid status {other:?}"
                        )));
                    }
                };
                Self::finish_parts(parts)?;
                let active = self.active.ok_or_else(|| {
                    TestError::UnexpectedReturn("test end event had no active test".into())
                })?;
                let test = self.tests.get_mut(active).ok_or_else(|| {
                    TestError::UnexpectedReturn(
                        "test end event pointed outside the test list".into(),
                    )
                })?;
                if status == JsonStatus::Failed || !test.failures.is_empty() {
                    test.status = JsonStatus::Failed;
                } else {
                    test.status = JsonStatus::Passed;
                }
                self.active = None;
                Ok(())
            }
            other => Err(TestError::UnexpectedReturn(format!(
                "unknown test event kind {other:?}"
            ))),
        }
    }

    fn next_part<'a>(
        parts: &mut impl Iterator<Item = &'a str>,
        field: &str,
    ) -> Result<&'a str, TestError> {
        parts
            .next()
            .ok_or_else(|| TestError::UnexpectedReturn(format!("test event missing {field}")))
    }

    fn finish_parts<'a>(mut parts: impl Iterator<Item = &'a str>) -> Result<(), TestError> {
        if parts.next().is_some() {
            return Err(TestError::UnexpectedReturn(
                "test event had too many fields".into(),
            ));
        }
        Ok(())
    }

    fn decode_hex(value: &str) -> Result<String, TestError> {
        let bytes = value.as_bytes();
        if !bytes.len().is_multiple_of(2) {
            return Err(TestError::UnexpectedReturn(
                "test event had odd-length hex data".into(),
            ));
        }
        let mut decoded = Vec::with_capacity(bytes.len() / 2);
        let mut index = 0;
        while index < bytes.len() {
            let high = Self::hex_value(bytes[index])?;
            let low = Self::hex_value(bytes[index + 1])?;
            decoded.push(high * 16 + low);
            index += 2;
        }
        String::from_utf8(decoded)
            .map_err(|_| TestError::UnexpectedReturn("test event had invalid utf-8 data".into()))
    }

    fn hex_value(byte: u8) -> Result<u8, TestError> {
        match byte {
            b'0'..=b'9' => Ok(byte - b'0'),
            b'a'..=b'f' => Ok(byte - b'a' + 10),
            b'A'..=b'F' => Ok(byte - b'A' + 10),
            _ => Err(TestError::UnexpectedReturn(
                "test event had non-hex data".into(),
            )),
        }
    }
}

impl Runner {
    pub fn new(roots: impl IntoIterator<Item = PathBuf>) -> Self {
        Self {
            roots: roots.into_iter().collect(),
            config: None,
            filter: None,
        }
    }

    pub fn with_config(roots: impl IntoIterator<Item = PathBuf>, config: DriverConfig) -> Self {
        Self {
            roots: roots.into_iter().collect(),
            config: Some(config),
            filter: None,
        }
    }

    pub fn with_filter(mut self, filter: Option<String>) -> Self {
        self.filter = filter;
        self
    }

    pub fn run(&self) -> Result<Outcome, TestError> {
        let test_sources = self.discover_sources()?;
        if test_sources.is_empty() {
            return Ok(Outcome::NoTests);
        }

        let sources = self.suite_sources(test_sources, HarnessMode::Human)?;
        let typed = self.compile_sources(sources)?;
        let (output, failures) = Self::execute(&typed)?;
        Ok(Outcome::Finished(Summary { output, failures }))
    }

    pub fn run_json(&self) -> Result<JsonOutcome, TestError> {
        let test_sources = self.discover_sources()?;
        if test_sources.is_empty() {
            return Ok(JsonOutcome::NoTests);
        }

        let sources = self.suite_sources(test_sources, HarnessMode::Json)?;
        let typed = self.compile_sources(sources)?;
        let (output, failures) = Self::execute(&typed)?;
        let events = JsonEventParser::parse(&output)?;
        Ok(JsonOutcome::Finished(events.into_summary(failures)))
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

    fn suite_sources(
        &self,
        test_sources: Vec<Source>,
        harness_mode: HarnessMode,
    ) -> Result<Vec<Source>, TestError> {
        let driver = match &self.config {
            Some(config) => Driver::new_bare(test_sources, config.clone()),
            None => Driver::new(test_sources, Self::compile_config()),
        };
        let parsed = driver
            .parse()
            .map_err(|err| TestError::Compile(format!("{err:?}")))?;

        let source_root = parsed.config.source_root.clone().unwrap_or_default();
        let mut sources = Vec::with_capacity(parsed.phase.asts.len() + 2);
        sources.push(Harness::prelude_source(
            &source_root,
            harness_mode,
            self.filter.as_deref(),
        ));
        sources.extend(parsed.phase.asts.keys().cloned());
        sources.push(Harness::postlude_source(&source_root));
        Ok(sources)
    }

    /// Run the composed suite through the backend (ADR 0034) with captured
    /// IO; the harness postlude's value is the failure count.
    fn execute(typed: &Driver<Typed>) -> Result<(String, i64), TestError> {
        // Diagnostic: dump the composed suite's middle representation.
        if std::env::var_os("TALK_DUMP_MIR").is_some() {
            match typed.render_mir(None) {
                Ok(rendered) => eprintln!("{rendered}"),
                Err(error) => eprintln!("mir render failed: {error}"),
            }
        }
        let executable = typed.compile_executable(None).map_err(TestError::Compile)?;
        let mut io = talk_runtime::io::CaptureIO::default();
        let value = execute_module(&executable, &mut io).map_err(TestError::Runtime)?;
        let output = String::from_utf8_lossy(&io.out).into_owned();
        let failures = value
            .as_deref()
            .unwrap_or_default()
            .parse::<i64>()
            .map_err(|_| {
                TestError::UnexpectedReturn(format!(
                    "test harness returned {value:?}, expected Int"
                ))
            })?;
        Ok((output, failures))
    }

    fn compile_sources(&self, sources: Vec<Source>) -> Result<Driver<Typed>, TestError> {
        let driver = match &self.config {
            Some(config) => Driver::new_bare(sources, config.clone()),
            None => Driver::new(sources, Self::compile_config()),
        };
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
        Ok(typed)
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
        }
    }

    fn is_test_file(path: &Path) -> bool {
        path.file_name()
            .and_then(|name| name.to_str())
            .is_some_and(|name| name.ends_with(".test.tlk"))
    }
}

#[derive(Clone, Copy)]
enum HarnessMode {
    Human,
    Json,
}

pub(crate) struct Harness;

impl Harness {
    pub(crate) fn human_sources(source_root: &Path) -> [Source; 2] {
        [
            Self::prelude_source(source_root, HarnessMode::Human, None),
            Self::postlude_source(source_root),
        ]
    }

    fn prelude_source(source_root: &Path, mode: HarnessMode, filter: Option<&str>) -> Source {
        let source = match mode {
            HarnessMode::Human => HARNESS_PRELUDE_SOURCE,
            HarnessMode::Json => HARNESS_JSON_PRELUDE_SOURCE,
        };
        let text = match filter {
            Some(filter) => source.replace(
                "let __talktalk_filter_enabled = false\nlet __talktalk_filter_name = \"\"",
                &format!(
                    "let __talktalk_filter_enabled = true\nlet __talktalk_filter_name = \"{}\"",
                    Self::string_literal_contents(filter)
                ),
            ),
            None => source.to_string(),
        };
        Source::in_memory(
            source_root.join(HARNESS_DIR).join("testing_prelude.tlk"),
            text,
        )
    }

    fn string_literal_contents(value: &str) -> String {
        let mut escaped = String::new();
        for ch in value.chars() {
            match ch {
                '"' => escaped.push_str("\\\""),
                '\\' => escaped.push_str("\\\\"),
                '\n' => escaped.push_str("\\n"),
                '\r' => escaped.push_str("\\r"),
                '\t' => escaped.push_str("\\t"),
                ch if ch <= '\u{1f}' => {
                    let _ = write!(&mut escaped, "\\u{{{:x}}}", ch as u32);
                }
                ch => escaped.push(ch),
            }
        }
        escaped
    }

    fn postlude_source(source_root: &Path) -> Source {
        Source::in_memory(
            source_root.join(HARNESS_DIR).join("testing_postlude.tlk"),
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
        for mode in [HarnessMode::Human, HarnessMode::Json] {
            let typed = Driver::new(
                vec![
                    Harness::prelude_source(Path::new("/talk-test-harness"), mode, None),
                    Harness::postlude_source(Path::new("/talk-test-harness")),
                ],
                DriverConfig::new("Harness"),
            )
            .parse()
            .expect("parse")
            .resolve_names()
            .expect("resolve")
            .type_check();
            assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
        }
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
            "test(\"bad\") {\n\tassert_message(false, \"nope\")\n}\n",
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

    #[test]
    fn assertion_macro_reports_the_failed_expression() {
        let project = temp_project("assertion-source-test-runner");
        std::fs::write(
            project.join("math.test.tlk"),
            "test(\"bad\") {\n\t#assert(1 + 1 == 3)\n}\n",
        )
        .expect("test file");

        let outcome = Runner::new([project]).run().expect("runner");
        let Outcome::Finished(summary) = outcome else {
            panic!("expected tests to run");
        };
        assert_eq!(summary.failures, 1);
        assert!(
            summary.output.contains("assertion failed: 1 + 1 == 3"),
            "{}",
            summary.output
        );
    }

    #[test]
    fn runner_filter_runs_only_the_named_test() {
        let project = temp_project("filtered-test-runner");
        std::fs::write(
            project.join("math.test.tlk"),
            "test \"selected\" {\n\tassert(true)\n}\n\n\
test(\"not selected\") {\n\tassert_message(false, \"nope\")\n}\n",
        )
        .expect("test file");

        let outcome = Runner::new([project])
            .with_filter(Some("selected".into()))
            .run()
            .expect("runner");
        let Outcome::Finished(summary) = outcome else {
            panic!("expected tests to run");
        };
        assert_eq!(summary.failures, 0);
        assert_eq!(summary.output, "\u{1b}[32m.\u{1b}[0m\n1 tests passed.\n");
    }

    #[test]
    fn runner_json_reports_tests_and_preserves_user_output() {
        let project = temp_project("json-test-runner");
        std::fs::write(
            project.join("math.test.tlk"),
            "test \"prints\" {\n\tprint_raw(\"hello\")\n\tassert(true)\n}\n\n\
test(\"bad \\\"quote\\\"\") {\n\tprint_raw(\"hello\")\n\tassert_message(false, \"nope\\nline\")\n}\n",
        )
        .expect("test file");

        let outcome = Runner::new([project])
            .with_filter(Some("bad \"quote\"".into()))
            .run_json()
            .expect("runner");
        let JsonOutcome::Finished(summary) = outcome else {
            panic!("expected tests to run");
        };
        assert_eq!(summary.failures, 1);
        assert_eq!(summary.output, "hello");
        assert_eq!(summary.tests.len(), 1);
        assert_eq!(summary.tests[0].name, "bad \"quote\"");
        assert_eq!(summary.tests[0].status, JsonStatus::Failed);
        assert_eq!(summary.tests[0].failures, ["nope\nline"]);
        let json = JsonOutcome::Finished(summary).to_json();
        assert!(json.contains("\"status\":\"finished\""));
        assert!(json.contains("nope\\nline"));
    }
}
