#[cfg(feature = "cli")]
#[tokio::main(flavor = "current_thread")]
async fn main() {
    use std::{fs::File, path::PathBuf};

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

    let target = Box::new(File::create("log.txt").expect("Can't create file"));
    env_logger::builder()
        .filter(None, log::LevelFilter::Info)
        .target(env_logger::Target::Pipe(target))
        .try_init()
        .unwrap();

    let cli = Cli::parse();

    // You can check for the existence of subcommands, and if found use their
    // matches just as you would the top level cmd
    match &cli.command {
        // Dump the IR
        Commands::IR { filename } => {
            use talk::{compiling::driver::Driver, lowering::ir_printer::print};
            let mut driver = Driver::with_files(vec![filename.clone()]);
            let lowered = driver.lower().unwrap();

            for unit in lowered {
                println!("{}", print(&unit.stage.module));
            }
        }

        Commands::Run { filename } => {
            use talk::compiling::driver::Driver;
            let mut driver = Driver::with_files(vec![filename.clone()]);
            let lowered = driver.lower().unwrap();

            use talk::interpreter::interpreter::IRInterpreter;

            // let contents = std::fs::read_to_string(filename).expect("Could not read file");
            // let lowered = lower(&contents);
            for lowered in lowered {
                let mut interpreter = IRInterpreter::new(lowered.stage.module);
                println!("{:?}", interpreter.run());
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
