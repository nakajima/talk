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
        HTML { filename: Option<String> },
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
            use talk::{
                compiling::driver::Driver,
                ir::interpreter::Interpreter,
            };

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
        Commands::HTML { filename } => {
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
fn single_source_for(
    filename: Option<&str>,
) -> (String, talk::compiling::driver::Source) {
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
        Some(name) if name != "-" => {
            std::fs::read_to_string(name)
                .unwrap_or_else(|err| panic!("failed to read {name}: {err}"))
        }
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
