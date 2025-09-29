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
        Parse { filename: String },
        Debug { filename: String },
        // Run { filename: PathBuf },
        // Lsp(LspArgs),
    }

    #[derive(Debug, Args)]
    struct LspArgs {
        #[arg(long)]
        stdio: bool,
    }

    init();

    let cli = Cli::parse();

    // You can check for the existence of subcommands, and if found use their
    // matches just as you would the top level cmd
    match &cli.command {
        Commands::Parse { .. } => {}
        Commands::Debug { filename } => {
            use talk::{
                formatter::{DebugHTMLFormatter, Formatter},
                lexer::Lexer,
                name_resolution::name_resolver::NameResolver,
                parser::Parser,
                types::{
                    type_session::{Raw, TypeSession},
                    types_decorator::TypesDecorator,
                },
            };

            let code = std::fs::read_to_string(filename).unwrap();
            let lexer = Lexer::new(&code);
            let parser = Parser::new(filename, lexer);
            let parsed = parser.parse().unwrap();
            let mut resolved = NameResolver::resolve(parsed);

            let session = TypeSession::<Raw>::drive(&mut resolved);

            let formatter = Formatter::new_with_decorators(
                &resolved.meta,
                vec![
                    Box::new(DebugHTMLFormatter {}),
                    Box::new(TypesDecorator {
                        types_by_node: session.types_by_node,
                    }),
                ],
            );

            println!("{}", formatter.format(&resolved.roots, 80));
        }
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
