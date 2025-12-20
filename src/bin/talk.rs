use talk::compiling::driver::DriverConfig;

#[cfg(feature = "cli")]
#[tokio::main(flavor = "current_thread")]
async fn main() {
    use clap::{Args, Parser, Subcommand};

    /// Simple program to greet a person
    #[derive(Parser, Debug)]
    #[command(version, about, long_about = None)]
    struct Cli {
        #[command(subcommand)]
        command: Commands,
    }

    #[derive(Subcommand, Debug)]
    enum Commands {
        // IR { filename: PathBuf },
        Parse { filename: Option<String> },
        Debug { filename: Option<String> },
        Html { filename: Option<String> },
        Check {
            filenames: Vec<String>,
            #[arg(long)]
            json: bool,
        },
        Run { filenames: Vec<String> },
        // Run { filename: PathBuf },
        Lsp(LspArgs),
    }

    #[derive(Debug, Args)]
    struct LspArgs {
        #[arg(long)]
        stdio: bool,
    }

    let cli = Cli::parse();

    // You can check for the existence of subcommands, and if found use their
    // matches just as you would the top level cmd
    match &cli.command {
        Commands::Parse { filename } => {
            use talk::compiling::driver::Driver;

            let (module_name, source) = single_source_for(filename.as_deref());
            let driver = Driver::new(vec![source], DriverConfig::new(module_name));
            let _ = driver.parse().unwrap();
        }
        Commands::Lsp(_) => {
            talk::lsp::server::start().await;
        }
        Commands::Run { filenames } => {
            use talk::{compiling::driver::Driver, ir::interpreter::Interpreter};

            let sources = sources_for_filenames(filenames);
            let driver = Driver::new(sources, DriverConfig::new("talk").executable());
            let module = driver
                .parse()
                .unwrap()
                .resolve_names()
                .unwrap()
                .typecheck()
                .unwrap()
                .lower()
                .unwrap()
                .module("talkin");

            let mut interpreter = Interpreter::new(module.program, Some(module.symbol_names));
            let result = interpreter.run();
            println!("{result:?}");
        }
        Commands::Check { filenames, json } => {
            use talk::analysis::{DocumentInput, Workspace};

            let sources = sources_for_filenames(filenames);
            let mut docs = Vec::with_capacity(sources.len());
            for source in sources {
                let path = source.path().to_string();
                let text = source
                    .read()
                    .unwrap_or_else(|err| panic!("failed to read {path}: {err:?}"));
                docs.push(DocumentInput {
                    id: path.clone(),
                    path,
                    version: 0,
                    text,
                });
            }

            let Some(workspace) = Workspace::new(docs) else {
                return;
            };

            let mut doc_ids: Vec<_> = workspace.diagnostics.keys().cloned().collect();
            doc_ids.sort();

            let mut has_diagnostics = false;
            let mut json_entries = Vec::new();
            for doc_id in doc_ids {
                let text = workspace.text_for(&doc_id).unwrap_or("");
                if let Some(diagnostics) = workspace.diagnostics.get(&doc_id) {
                    for diagnostic in diagnostics {
                        if *json {
                            json_entries.push(json_diagnostic(&doc_id, text, diagnostic));
                        } else {
                            print_diagnostic(&doc_id, text, diagnostic);
                        }
                        has_diagnostics = true;
                    }
                }
            }

            if *json {
                println!(
                    "{{\"diagnostics\":[{}]}}",
                    json_entries.join(",")
                );
            }

            if has_diagnostics {
                std::process::exit(1);
            }
        }
        Commands::Html { filename } => {
            init();
            use talk::highlighter::highlight_html;

            let source = input_text(filename.as_deref());
            let html = highlight_html(&source);
            println!("{html}");
        }
        Commands::Debug { filename } => {
            init();

            use talk::{
                compiling::driver::Driver,
                formatter::{DebugHTMLFormatter, Formatter},
            };

            let (module_name, source) = single_source_for(filename.as_deref());
            let driver = Driver::new(vec![source], DriverConfig::new(module_name));
            let resolved = driver.parse().unwrap().resolve_names().unwrap();
            let meta = resolved.phase.asts[0].meta.clone();

            let formatter = Formatter::new_with_decorators(
                &meta,
                vec![
                    Box::new(DebugHTMLFormatter {}),
                    //Box::new(TypesDecorator {
                    //    types_by_node: typed.phase.types.types_by_node,
                    //}),
                ],
            );

            println!(
                "{}",
                formatter.format(&resolved.phase.asts[0].roots.clone(), 80)
            );
        }
    }
}

#[cfg(feature = "cli")]
const STDIN_NAME: &str = "<stdin>";

#[cfg(feature = "cli")]
fn read_stdin() -> String {
    use std::io::Read;

    let mut buffer = String::new();
    std::io::stdin()
        .read_to_string(&mut buffer)
        .unwrap_or_else(|err| panic!("failed to read stdin: {err}"));
    buffer
}

#[cfg(feature = "cli")]
fn single_source_for(filename: Option<&str>) -> (String, talk::compiling::driver::Source) {
    use std::path::PathBuf;
    use talk::compiling::driver::Source;

    let module_name = match filename {
        Some(name) if name != "-" => name.to_string(),
        _ => STDIN_NAME.to_string(),
    };

    let source = match filename {
        Some(name) if name != "-" => Source::from(PathBuf::from(name)),
        _ => Source::in_memory(PathBuf::from(STDIN_NAME), read_stdin()),
    };

    (module_name, source)
}

#[cfg(feature = "cli")]
fn sources_for_filenames(filenames: &[String]) -> Vec<talk::compiling::driver::Source> {
    use std::path::PathBuf;
    use talk::compiling::driver::Source;

    if filenames.is_empty() {
        return vec![Source::in_memory(PathBuf::from(STDIN_NAME), read_stdin())];
    }

    let mut stdin_text = None;
    let mut sources = Vec::with_capacity(filenames.len());
    for filename in filenames {
        if filename == "-" {
            let text = stdin_text.get_or_insert_with(read_stdin);
            sources.push(Source::in_memory(PathBuf::from(STDIN_NAME), text.clone()));
        } else {
            sources.push(Source::from(PathBuf::from(filename)));
        }
    }

    sources
}

#[cfg(feature = "cli")]
fn input_text(filename: Option<&str>) -> String {
    match filename {
        Some(name) if name != "-" => std::fs::read_to_string(name)
            .unwrap_or_else(|err| panic!("failed to read {name}: {err}")),
        _ => read_stdin(),
    }
}

#[cfg(feature = "cli")]
fn print_diagnostic(
    doc_id: &str,
    text: &str,
    diagnostic: &talk::analysis::Diagnostic,
) {
    let use_color = use_color();
    let (line, col, line_start, line_end) = line_info_for_offset(text, diagnostic.range.start);
    let line_text = text.get(line_start..line_end).unwrap_or("");
    let line_text = line_text.strip_suffix('\r').unwrap_or(line_text);

    let highlight_start =
        clamp_to_char_boundary(text, diagnostic.range.start as usize).clamp(line_start, line_end);
    let highlight_end =
        clamp_to_char_boundary(text, diagnostic.range.end as usize).clamp(highlight_start, line_end);

    let prefix = caret_prefix(&text[line_start..highlight_start]);
    let underline_len = text[highlight_start..highlight_end]
        .chars()
        .count()
        .max(1);
    let underline = "^".repeat(underline_len);

    let severity = severity_label(&diagnostic.severity);
    let severity_style = severity_style(&diagnostic.severity);
    let severity = style(severity, severity_style, use_color);

    let gutter = style("|", "2", use_color);
    let line_no = style(&format!("{line:>4}"), "2", use_color);
    let underline = style(&underline, severity_style, use_color);

    println!("{doc_id}:{line}:{col}: {severity}: {}", diagnostic.message);
    println!("  {gutter}");
    println!("{line_no} {gutter} {line_text}");
    println!("  {gutter} {prefix}{underline}");

    if diagnostic.range.end as usize > line_end {
        println!("  = note: spans multiple lines");
    }

    println!();
}

#[cfg(feature = "cli")]
fn json_diagnostic(
    doc_id: &str,
    text: &str,
    diagnostic: &talk::analysis::Diagnostic,
) -> String {
    let (line, col, line_start, line_end) = line_info_for_offset(text, diagnostic.range.start);
    let line_text = text.get(line_start..line_end).unwrap_or("");
    let line_text = line_text.strip_suffix('\r').unwrap_or(line_text);

    let highlight_start =
        clamp_to_char_boundary(text, diagnostic.range.start as usize).clamp(line_start, line_end);
    let highlight_end =
        clamp_to_char_boundary(text, diagnostic.range.end as usize).clamp(highlight_start, line_end);

    let underline_start = text[line_start..highlight_start].chars().count() as u32 + 1;
    let underline_len = text[highlight_start..highlight_end]
        .chars()
        .count()
        .max(1) as u32;
    let multiline = diagnostic.range.end as usize > line_end;

    format!(
        "{{\"path\":{},\"line\":{},\"column\":{},\"severity\":{},\"message\":{},\"range\":{{\"start\":{},\"end\":{}}},\"line_text\":{},\"underline_start\":{},\"underline_len\":{},\"multiline\":{}}}",
        json_string(doc_id),
        line,
        col,
        json_string(severity_label(&diagnostic.severity)),
        json_string(&diagnostic.message),
        diagnostic.range.start,
        diagnostic.range.end,
        json_string(line_text),
        underline_start,
        underline_len,
        if multiline { "true" } else { "false" }
    )
}

#[cfg(feature = "cli")]
fn line_info_for_offset(text: &str, byte_offset: u32) -> (u32, u32, usize, usize) {
    let offset = clamp_to_char_boundary(text, byte_offset as usize);
    let mut line: u32 = 1;
    let mut last_line_start = 0usize;

    for (idx, ch) in text.char_indices() {
        if idx >= offset {
            break;
        }
        if ch == '\n' {
            line += 1;
            last_line_start = idx + ch.len_utf8();
        }
    }

    let line_end = text[offset..]
        .find('\n')
        .map(|idx| offset + idx)
        .unwrap_or(text.len());
    let col = text[last_line_start..offset].chars().count() as u32 + 1;
    (line, col, last_line_start, line_end)
}

#[cfg(feature = "cli")]
fn caret_prefix(text: &str) -> String {
    let mut prefix = String::new();
    for ch in text.chars() {
        if ch == '\t' {
            prefix.push('\t');
        } else {
            prefix.push(' ');
        }
    }
    prefix
}

#[cfg(feature = "cli")]
fn clamp_to_char_boundary(text: &str, mut idx: usize) -> usize {
    if idx > text.len() {
        idx = text.len();
    }
    while idx > 0 && !text.is_char_boundary(idx) {
        idx -= 1;
    }
    idx
}

#[cfg(feature = "cli")]
fn use_color() -> bool {
    use std::io::IsTerminal;
    std::io::stdout().is_terminal() && std::env::var_os("NO_COLOR").is_none()
}

#[cfg(feature = "cli")]
fn severity_style(severity: &talk::analysis::DiagnosticSeverity) -> &'static str {
    match severity {
        talk::analysis::DiagnosticSeverity::Error => "1;31",
        talk::analysis::DiagnosticSeverity::Warning => "1;33",
        talk::analysis::DiagnosticSeverity::Info => "1;34",
    }
}

#[cfg(feature = "cli")]
fn severity_label(severity: &talk::analysis::DiagnosticSeverity) -> &'static str {
    match severity {
        talk::analysis::DiagnosticSeverity::Error => "error",
        talk::analysis::DiagnosticSeverity::Warning => "warning",
        talk::analysis::DiagnosticSeverity::Info => "info",
    }
}

#[cfg(feature = "cli")]
fn style(text: &str, code: &str, enabled: bool) -> String {
    if enabled {
        format!("\x1b[{code}m{text}\x1b[0m")
    } else {
        text.to_string()
    }
}

#[cfg(feature = "cli")]
fn json_string(value: &str) -> String {
    let mut out = String::from("\"");
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            ch if (ch as u32) < 0x20 => {
                out.push_str(&format!("\\u{:04x}", ch as u32));
            }
            _ => out.push(ch),
        }
    }
    out.push('"');
    out
}

#[cfg(not(feature = "cli"))]
fn main() {
    use core::panic;

    panic!("Compiled without 'cli' feature.")
}

pub fn init() {
    use tracing_subscriber::{EnvFilter, prelude::*, registry};
    let tree = tracing_tree::HierarchicalLayer::new(2).with_filter(EnvFilter::from_default_env()); // ordinary RUST_LOG filtering
    registry().with(tree).init();
}
