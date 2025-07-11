#[cfg(feature = "cli")]
#[tokio::main(flavor = "current_thread")]
async fn main() {
    use std::path::PathBuf;

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
        IR { filename: PathBuf },
        // Parse { filename: String },
        Run { filename: PathBuf },
        Lsp(LspArgs),
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
        // Dump the IR
        #[allow(clippy::print_with_newline)]
        Commands::IR { filename } => {
            use talk::{compiling::driver::Driver, lowering::ir_printer::print};
            let cwd = std::env::current_dir().expect("couldn’t get CWD");
            let mut driver = Driver::with_files(vec![cwd.join(filename).clone()]);
            let lowered = driver.lower();

            for unit in lowered {
                use talk::transforms::monomorphizer::Monomorphizer;

                let monomorphized = Monomorphizer::new(&unit.env).run(unit.module());
                print!("{}\n", print(&monomorphized));
            }
        }

        Commands::Run { filename } => {
            use talk::compiling::driver::Driver;
            let mut driver = Driver::with_files(vec![filename.clone()]);
            let lowered = driver.lower();

            use talk::interpret::interpreter::IRInterpreter;
            use talk::interpret::io::InterpreterStdIO;
            use talk::transforms::monomorphizer::Monomorphizer;

            // let contents = std::fs::read_to_string(filename).expect("Could not read file");
            // let lowered = lower(&contents);
            let mut io = InterpreterStdIO::default();
            for lowered in lowered {
                let monomorphized = Monomorphizer::new(&lowered.env).run(lowered.module());
                let interpreter = IRInterpreter::new(monomorphized, &mut io, &driver.symbol_table);
                interpreter.run().unwrap();
            }
        }
        Commands::Lsp(_args) => talk::lsp::server::start().await,
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
