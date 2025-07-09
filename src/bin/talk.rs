#[cfg(feature = "cli")]
#[tokio::main(flavor = "current_thread")]
async fn main() {
    use std::{fs::File, io::BufWriter, path::PathBuf};

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

    let file = File::create("log.txt").expect("can't create file");

    let _ = tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env()) // respects RUST_LOG
        .without_time()
        .with_target(false)
        .with_writer(move || BufWriter::new(file.try_clone().expect("clone failed")))
        .try_init();

    let cli = Cli::parse();

    // You can check for the existence of subcommands, and if found use their
    // matches just as you would the top level cmd
    match &cli.command {
        // Dump the IR
        #[allow(clippy::print_with_newline)]
        Commands::IR { filename } => {
            use talk::{compiling::driver::Driver, lowering::ir_printer::print};
            let mut driver = Driver::with_files(vec![filename.clone()]);
            let lowered = driver.lower();

            for unit in lowered {
                print!("{}\n", print(&unit.stage.module));
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
                let interpreter = IRInterpreter::new(monomorphized, &mut io);
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
