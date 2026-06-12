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
        Parse {
            #[arg(value_hint = ValueHint::FilePath)]
            filename: Option<String>,
        },
        /// Print the lowered λ_G program for a file (or stdin).
        Ir {
            #[arg(value_hint = ValueHint::FilePath)]
            filename: Option<String>,
        },
        /// The type of the thing at a position (byte offset, or 1-based
        /// line and column).
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
        Check {
            #[arg(value_hint = ValueHint::FilePath)]
            filenames: Vec<String>,
            #[arg(long)]
            json: bool,
        },
        Run {
            #[arg(value_hint = ValueHint::FilePath)]
            filenames: Vec<String>,
        },
        Repl,
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
        Commands::Ir { filename } => {
            let (module_name, source) = single_source_for(filename.as_deref());
            match talk::compiling::driver::render_ir_from(&module_name, source) {
                Ok(ir) => println!("{ir}"),
                Err(message) => {
                    eprintln!("{message}");
                    std::process::exit(1);
                }
            }
        }
        Commands::Hover {
            filename,
            byte_offset,
            line,
            column,
            node_id,
        } => {
            use talk::analysis::{DocumentInput, Workspace, hover_at};

            let (module_name, text) = match filename.as_deref() {
                Some(name) if name != "-" => match std::fs::read_to_string(name) {
                    Ok(text) => (name.to_string(), text),
                    Err(err) => {
                        eprintln!("error: {err}");
                        std::process::exit(1);
                    }
                },
                _ => (STDIN_NAME.to_string(), read_stdin()),
            };
            let doc_id = module_name.clone();
            let doc = DocumentInput {
                id: doc_id.clone(),
                path: module_name,
                version: 0,
                text: text.clone(),
            };
            let Some(workspace) = Workspace::new(vec![doc]) else {
                eprintln!("error: failed to build workspace");
                std::process::exit(1);
            };
            let hover = match (byte_offset, line, column, node_id) {
                (_, _, _, Some(node_id)) => {
                    let Some(node_id) = talk::analysis::hover::parse_node_id(node_id) else {
                        eprintln!("error: node id must be \"index\" or \"file:index\"");
                        std::process::exit(1);
                    };
                    talk::analysis::hover::hover_for_node_id(&workspace, &doc_id, node_id)
                }
                (Some(offset), None, None, None) => hover_at(&workspace, &doc_id, *offset),
                (None, Some(line), Some(column), None) => {
                    match talk::common::text::byte_offset_for_line_column_utf8(
                        &text, *line, *column,
                    ) {
                        Some(offset) => hover_at(&workspace, &doc_id, offset),
                        None => {
                            eprintln!("error: line/column is past end of document");
                            std::process::exit(1);
                        }
                    }
                }
                _ => {
                    eprintln!(
                        "error: provide --byte-offset, --line and --column, or --node-id"
                    );
                    std::process::exit(1);
                }
            };
            match hover {
                Some(hover) => println!("{}", hover.contents),
                None => {
                    eprintln!("no hover information at that position");
                    std::process::exit(1);
                }
            }
        }
        Commands::Lsp(_) => {
            talk::lsp::server::start().await;
        }
        Commands::Completions { shell } => {
            let mut cmd = Cli::command();
            let bin_name = cmd.get_name().to_string();
            generate(*shell, &mut cmd, bin_name, &mut std::io::stdout());
        }
        Commands::Repl => {
            talk::cli::repl::run();
        }
        Commands::Run { filenames } => {
            use talk::compiling::driver::Driver;

            let module_name = filenames
                .first()
                .cloned()
                .unwrap_or_else(|| STDIN_NAME.to_string());
            let sources = sources_for_filenames(filenames);
            let driver = Driver::new(sources, DriverConfig::new(module_name));
            let parsed = match driver.parse() {
                Ok(parsed) => parsed,
                Err(err) => {
                    eprintln!("error: {err:?}");
                    std::process::exit(1);
                }
            };
            let resolved = match parsed.resolve_names() {
                Ok(resolved) => resolved,
                Err(err) => {
                    eprintln!("error: {err:?}");
                    std::process::exit(1);
                }
            };
            let typed = resolved.type_check();
            if typed.has_errors() {
                for diagnostic in typed.diagnostics() {
                    eprintln!("{diagnostic:?}");
                }
                std::process::exit(1);
            }
            let mut lowered = typed.lower();
            if !lowered.phase.diagnostics.is_empty() {
                for diagnostic in &lowered.phase.diagnostics {
                    eprintln!("{diagnostic}");
                }
                std::process::exit(1);
            }
            match lowered.run_vm() {
                Ok(talk::vm::interp::Value::Void) => {}
                Ok(value) => println!("{value:?}"),
                Err(err) => {
                    eprintln!("{err}");
                    std::process::exit(1);
                }
            }
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
