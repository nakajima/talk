use std::hint::black_box;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use talk::analysis::{DocumentInput, Workspace};
use talk::compiling::frontend;
use talk::lsp::semantic_tokens;
use talk::node_id::FileID;

struct Case {
    name: &'static str,
    focus_path: PathBuf,
    focus_text: String,
    documents: Vec<DocumentInput>,
}

impl Case {
    fn load(root: &Path, name: &str) -> Result<Self, String> {
        match name {
            "small" => Self::from_paths(
                "small",
                root.join("benches/editor/fixtures/small.tlk"),
                vec![root.join("benches/editor/fixtures/small.tlk")],
            ),
            "core" => Self::from_paths(
                "core",
                root.join("core/Array.tlk"),
                talk::compiling::core::CORE_SOURCE_NAMES
                    .iter()
                    .map(|name| root.join("core").join(name))
                    .collect(),
            ),
            "syntax" => {
                let directory = root.join("stdlib/syntax");
                let mut paths: Vec<PathBuf> = std::fs::read_dir(&directory)
                    .map_err(|error| format!("failed to read {}: {error}", directory.display()))?
                    .filter_map(|entry| entry.ok().map(|entry| entry.path()))
                    .filter(|path| path.extension().is_some_and(|extension| extension == "tlk"))
                    .collect();
                paths.sort();
                Self::from_paths("syntax", directory.join("Parser.tlk"), paths)
            }
            other => Err(format!(
                "unknown case {other:?}; expected small, core, or syntax"
            )),
        }
    }

    fn from_paths(
        name: &'static str,
        focus_path: PathBuf,
        paths: Vec<PathBuf>,
    ) -> Result<Self, String> {
        let focus_text = std::fs::read_to_string(&focus_path)
            .map_err(|error| format!("failed to read {}: {error}", focus_path.display()))?;
        let documents = paths
            .into_iter()
            .enumerate()
            .map(|(version, path)| {
                let text = std::fs::read_to_string(&path)
                    .map_err(|error| format!("failed to read {}: {error}", path.display()))?;
                let path = path.to_string_lossy().into_owned();
                Ok(DocumentInput {
                    id: path.clone(),
                    path,
                    version: i32::try_from(version).unwrap_or(i32::MAX),
                    text,
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
        Ok(Self {
            name,
            focus_path,
            focus_text,
            documents,
        })
    }

    fn total_bytes(&self) -> usize {
        self.documents
            .iter()
            .map(|document| document.text.len())
            .sum()
    }
}

struct Benchmark {
    warmups: usize,
    iterations: usize,
}

impl Benchmark {
    fn run(&self, case: &Case) {
        self.measure(case, "parse_lenient_focus", || {
            let parsed = frontend::parse_ast_lenient(
                &case.focus_text,
                FileID(0),
                &case.focus_path.to_string_lossy(),
            );
            black_box(&parsed);
        });
        self.measure(case, "semantic_tokens_focus", || {
            let tokens = semantic_tokens::collect(case.focus_text.clone());
            black_box(&tokens);
        });
        self.measure(case, "workspace_rebuild", || {
            let workspace = Workspace::new(case.documents.clone());
            black_box(&workspace);
            assert!(
                workspace.is_some(),
                "workspace benchmark must produce analysis"
            );
        });
    }

    fn measure(&self, case: &Case, operation: &str, mut operation_fn: impl FnMut()) {
        eprintln!("warming {} {operation}", case.name);
        for _ in 0..self.warmups {
            operation_fn();
        }

        let mut samples_us = Vec::with_capacity(self.iterations);
        for iteration in 0..self.iterations {
            eprintln!(
                "measuring {} {operation} {}/{}",
                case.name,
                iteration + 1,
                self.iterations
            );
            let started = Instant::now();
            operation_fn();
            samples_us.push(started.elapsed().as_micros() as u64);
        }

        let mut sorted = samples_us.clone();
        sorted.sort_unstable();
        let median_us = sorted[sorted.len() / 2];
        let p95_index = (sorted.len() * 95).div_ceil(100).saturating_sub(1);
        let p95_us = sorted[p95_index];
        let samples_ms = samples_us
            .iter()
            .map(|sample| format!("{:.3}", *sample as f64 / 1_000.0))
            .collect::<Vec<_>>()
            .join(",");

        println!(
            "{{\"type\":\"result\",\"case\":{:?},\"operation\":{:?},\"focus\":{:?},\"focus_bytes\":{},\"workspace_bytes\":{},\"documents\":{},\"warmups\":{},\"iterations\":{},\"median_ms\":{:.3},\"p95_ms\":{:.3},\"samples_ms\":[{}]}}",
            case.name,
            operation,
            case.focus_path.to_string_lossy(),
            case.focus_text.len(),
            case.total_bytes(),
            case.documents.len(),
            self.warmups,
            self.iterations,
            median_us as f64 / 1_000.0,
            p95_us as f64 / 1_000.0,
            samples_ms
        );
    }
}

struct Arguments {
    warmups: usize,
    iterations: usize,
    cases: Vec<String>,
}

impl Arguments {
    fn parse() -> Result<Option<Self>, String> {
        let mut warmups = 1;
        let mut iterations = 3;
        let mut cases = Vec::new();
        let mut arguments = std::env::args().skip(1);
        while let Some(argument) = arguments.next() {
            match argument.as_str() {
                "--warmups" => {
                    warmups = Self::count("--warmups", arguments.next())?;
                }
                "--iterations" => {
                    iterations = Self::count("--iterations", arguments.next())?;
                    if iterations == 0 {
                        return Err("--iterations must be greater than zero".to_string());
                    }
                }
                "--case" => {
                    cases.push(
                        arguments
                            .next()
                            .ok_or_else(|| "--case requires a name".to_string())?,
                    );
                }
                "--bench" => {}
                "-h" | "--help" => return Ok(None),
                other => return Err(format!("unknown argument: {other}")),
            }
        }
        if cases.is_empty() {
            cases = vec!["small".into(), "core".into(), "syntax".into()];
        }
        Ok(Some(Self {
            warmups,
            iterations,
            cases,
        }))
    }

    fn count(flag: &str, value: Option<String>) -> Result<usize, String> {
        value
            .ok_or_else(|| format!("{flag} requires a count"))?
            .parse()
            .map_err(|_| format!("{flag} requires a non-negative integer"))
    }

    fn usage() {
        eprintln!(
            "Usage: cargo bench --bench editor_latency -- [--case small|core|syntax] [--warmups N] [--iterations N]"
        );
    }
}

fn main() -> ExitCode {
    let arguments = match Arguments::parse() {
        Ok(Some(arguments)) => arguments,
        Ok(None) => {
            Arguments::usage();
            return ExitCode::SUCCESS;
        }
        Err(error) => {
            eprintln!("error: {error}");
            Arguments::usage();
            return ExitCode::from(2);
        }
    };

    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let commit = Command::new("git")
        .args(["rev-parse", "HEAD"])
        .current_dir(root)
        .output()
        .ok()
        .filter(|output| output.status.success())
        .map(|output| String::from_utf8_lossy(&output.stdout).trim().to_string())
        .unwrap_or_else(|| "unknown".to_string());
    let worktree_dirty = Command::new("git")
        .args(["status", "--porcelain"])
        .current_dir(root)
        .output()
        .ok()
        .filter(|output| output.status.success())
        .is_some_and(|output| !output.stdout.is_empty());
    let generated_at = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_secs())
        .unwrap_or_default();
    println!(
        "{{\"type\":\"metadata\",\"format\":1,\"benchmark\":\"editor_frontend_latency\",\"commit\":{:?},\"worktree_dirty\":{},\"generated_at_unix\":{},\"os\":{:?},\"arch\":{:?}}}",
        commit,
        worktree_dirty,
        generated_at,
        std::env::consts::OS,
        std::env::consts::ARCH
    );

    let benchmark = Benchmark {
        warmups: arguments.warmups,
        iterations: arguments.iterations,
    };
    for name in &arguments.cases {
        let case = match Case::load(root, name) {
            Ok(case) => case,
            Err(error) => {
                eprintln!("error: {error}");
                return ExitCode::FAILURE;
            }
        };
        benchmark.run(&case);
    }
    ExitCode::SUCCESS
}
