use talk::compiling::driver::DriverConfig;

#[cfg(feature = "cli")]
#[cfg(feature = "cli")]
#[tokio::main(flavor = "current_thread")]
async fn main() {
    use clap::{Args, CommandFactory, Parser, Subcommand, ValueHint};
    use clap_complete::{Shell, generate};

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
        Parse {
            #[arg(value_hint = ValueHint::FilePath)]
            filename: Option<String>,
        },
        Format {
            #[arg(value_hint = ValueHint::FilePath)]
            filename: Option<String>,
        },
        Debug {
            #[arg(value_hint = ValueHint::FilePath)]
            filename: Option<String>,
        },
        Html {
            #[arg(value_hint = ValueHint::FilePath)]
            filename: Option<String>,
        },
        Ir {
            #[arg(value_hint = ValueHint::FilePath)]
            filename: Option<String>,
        },

        Check {
            #[arg(value_hint = ValueHint::FilePath)]
            filenames: Vec<String>,
            #[arg(long)]
            json: bool,
        },
        Hover {
            #[arg(value_hint = ValueHint::FilePath)]
            filename: Option<String>,
            #[arg(long, value_name = "N")]
            byte_offset: Option<u32>,
            #[arg(long, value_name = "N")]
            line: Option<u32>,
            #[arg(long, value_name = "N")]
            column: Option<u32>,
            #[arg(long, value_name = "ID")]
            node_id: Option<String>,
        },
        Run {
            #[arg(value_hint = ValueHint::FilePath)]
            filenames: Vec<String>,
        },
        // Run { filename: PathBuf },
        Completions {
            #[arg(value_enum)]
            shell: Shell,
        },
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
        Commands::Completions { shell } => {
            let mut cmd = Cli::command();
            let bin_name = cmd.get_name().to_string();
            generate(*shell, &mut cmd, bin_name, &mut std::io::stdout());
        }
        Commands::Ir { filename } => {
            use talk::compiling::driver::Driver;

            let (module_name, source) = single_source_for(filename.as_deref());
            let driver = Driver::new(vec![source], DriverConfig::new(module_name).executable());
            let lowered = driver
                .parse()
                .unwrap()
                .resolve_names()
                .unwrap()
                .typecheck()
                .unwrap()
                .lower()
                .unwrap();
            println!("{}", lowered.phase.program)
        }
        Commands::Run { filenames } => {
            use talk::{
                compiling::driver::Driver,
                ir::{interpreter::Interpreter, io::StdioIO},
            };

            let sources = sources_for_filenames(filenames);
            let driver = Driver::new(sources, DriverConfig::new("talk").executable());
            let lowered = driver
                .parse()
                .unwrap()
                .resolve_names()
                .unwrap()
                .typecheck()
                .unwrap()
                .lower()
                .unwrap();

            if lowered.has_errors() {
                for diagnostic in lowered.diagnostics() {
                    eprintln!("error: {diagnostic}");
                }
                std::process::exit(1);
            }

            let display_names = lowered.display_symbol_names();
            let module = lowered.module("talkin");

            let mut interpreter = Interpreter::new(module.program, Some(display_names), StdioIO {});
            _ = interpreter.run();
        }
        Commands::Check { filenames, json } => {
            use talk::{
                analysis::{DocumentInput, Workspace},
                cli::diagnostics::{ColorMode, render_json_entry, render_json_output, render_text},
            };

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
                            json_entries.push(render_json_entry(&doc_id, text, diagnostic));
                        } else {
                            print!(
                                "{}",
                                render_text(&doc_id, text, diagnostic, ColorMode::Auto)
                            );
                        }
                        has_diagnostics = true;
                    }
                }
            }

            if *json {
                println!("{}", render_json_output(&json_entries));
            }

            if has_diagnostics {
                std::process::exit(1);
            }
        }
        Commands::Hover {
            filename,
            byte_offset,
            line,
            column,
            node_id,
        } => {
            use talk::analysis::hover::{hover_at, hover_for_node_id};
            use talk::analysis::{DocumentInput, Workspace};
            use talk::common::text::{byte_offset_for_line_column_utf8, clamp_to_char_boundary};
            use talk::node_id::FileID;

            let (_module_name, source) = single_source_for(filename.as_deref());
            let path = source.path().to_string();
            let text = source
                .read()
                .unwrap_or_else(|err| panic!("failed to read {path}: {err:?}"));
            let doc = DocumentInput {
                id: path.clone(),
                path: path.clone(),
                version: 0,
                text: text.clone(),
            };

            let Some(workspace) = Workspace::new(vec![doc]) else {
                println!("{}", hover_error_json("failed to build workspace"));
                std::process::exit(1);
            };

            let query = parse_hover_query(*byte_offset, *line, *column, node_id.clone())
                .unwrap_or_else(|err| {
                    println!("{}", hover_error_json(&err));
                    std::process::exit(1);
                });

            let core = Workspace::core();
            let core = core.as_ref();
            let doc_id = workspace
                .file_id_to_document
                .first()
                .cloned()
                .unwrap_or(path);

            let hover = match query {
                HoverQuery::ByteOffset(offset) => {
                    if offset as usize > text.len() {
                        println!(
                            "{}",
                            hover_error_json("byte offset is past end of document")
                        );
                        std::process::exit(1);
                    }
                    let offset = clamp_to_char_boundary(&text, offset as usize);
                    let offset = u32::try_from(offset).unwrap_or(u32::MAX);
                    hover_at(&workspace, core, &doc_id, offset)
                }
                HoverQuery::LineColumn { line, column } => {
                    let Some(offset) = byte_offset_for_line_column_utf8(&text, line, column) else {
                        println!("{}", hover_error_json("line/column out of range"));
                        std::process::exit(1);
                    };
                    hover_at(&workspace, core, &doc_id, offset)
                }
                HoverQuery::NodeId(node_id) => {
                    if node_id.0 != FileID(0) {
                        println!("{}", hover_error_json("node id file index is out of range"));
                        std::process::exit(1);
                    }
                    hover_for_node_id(&workspace, core, &doc_id, node_id)
                }
            };

            println!("{}", render_hover_json(&doc_id, &text, hover));
        }
        Commands::Html { filename } => {
            init();
            use talk::highlighter::highlight_html;

            let source = input_text(filename.as_deref());
            let html = highlight_html(&source);
            println!("{html}");
        }
        Commands::Format { filename } => {
            use talk::formatter;

            init();
            let source = input_text(filename.as_deref());
            println!("{}", formatter::format_string(&source));
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
enum HoverQuery {
    ByteOffset(u32),
    LineColumn { line: u32, column: u32 },
    NodeId(talk::node_id::NodeID),
}

#[cfg(feature = "cli")]
fn parse_hover_query(
    byte_offset: Option<u32>,
    line: Option<u32>,
    column: Option<u32>,
    node_id: Option<String>,
) -> Result<HoverQuery, String> {
    let mut count = 0;
    if byte_offset.is_some() {
        count += 1;
    }
    if line.is_some() || column.is_some() {
        count += 1;
    }
    if node_id.is_some() {
        count += 1;
    }

    if count == 0 {
        return Err("provide --byte-offset, --line/--column, or --node-id".to_string());
    }
    if count > 1 {
        return Err("provide only one of --byte-offset, --line/--column, or --node-id".to_string());
    }

    if let Some(offset) = byte_offset {
        return Ok(HoverQuery::ByteOffset(offset));
    }

    if line.is_some() || column.is_some() {
        let line = line.ok_or_else(|| "--line requires --column".to_string())?;
        let column = column.ok_or_else(|| "--column requires --line".to_string())?;
        return Ok(HoverQuery::LineColumn { line, column });
    }

    let node_id = node_id.expect("count ensures node id");
    Ok(HoverQuery::NodeId(parse_node_id(&node_id)?))
}

#[cfg(feature = "cli")]
fn parse_node_id(input: &str) -> Result<talk::node_id::NodeID, String> {
    let (file_id, node_id) = match input.split_once(':') {
        Some((file_id, node_id)) => (file_id, node_id),
        None => ("0", input),
    };
    let file_id = file_id
        .parse::<u32>()
        .map_err(|_| "node id file index must be a u32".to_string())?;
    let node_id = node_id
        .parse::<u32>()
        .map_err(|_| "node id must be a u32".to_string())?;
    Ok(talk::node_id::NodeID(
        talk::node_id::FileID(file_id),
        node_id,
    ))
}

#[cfg(feature = "cli")]
fn render_hover_json(doc_id: &str, text: &str, hover: Option<talk::analysis::Hover>) -> String {
    use talk::common::text::line_info_for_offset;

    let mut out = String::new();
    out.push_str("{\"path\":");
    out.push_str(&json_string(doc_id));
    out.push_str(",\"hover\":");

    let Some(hover) = hover else {
        out.push_str("null}");
        return out;
    };

    let talk::analysis::Hover { contents, range } = hover;
    let contents_markdown = format!("```talk\n{contents}\n```");
    out.push_str("{\"contents\":");
    out.push_str(&json_string(&contents));
    out.push_str(",\"contents_markdown\":");
    out.push_str(&json_string(&contents_markdown));

    if let Some(range) = range {
        let (start_line, start_col, _, _) = line_info_for_offset(text, range.start);
        let (end_line, end_col, _, _) = line_info_for_offset(text, range.end);
        out.push_str(",\"range\":{");
        out.push_str("\"start\":{");
        out.push_str(&format!(
            "\"byte\":{},\"line\":{},\"column\":{}",
            range.start, start_line, start_col
        ));
        out.push_str("},\"end\":{");
        out.push_str(&format!(
            "\"byte\":{},\"line\":{},\"column\":{}",
            range.end, end_line, end_col
        ));
        out.push_str("}}");
    } else {
        out.push_str(",\"range\":null");
    }

    out.push_str("}}");
    out
}

#[cfg(feature = "cli")]
fn hover_error_json(message: &str) -> String {
    format!("{{\"error\":{}}}", json_string(message))
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
