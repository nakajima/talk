#[cfg(feature = "cli")]
fn main() {
    use std::path::PathBuf;

    use clap::{Parser, Subcommand};

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
        Parse { filename: String },
        Run { filename: PathBuf },
    }

    env_logger::builder().try_init().unwrap();

    let cli = Cli::parse();

    // You can check for the existence of subcommands, and if found use their
    // matches just as you would the top level cmd
    match &cli.command {
        Commands::IR { filename } => {
            use talk::{compiling::driver::Driver, lowering::ir_printer::print};
            let driver = Driver::with_files(vec![filename.clone()]);
            let lowered = driver.lower().unwrap();

            for unit in lowered {
                println!("{}", print(&unit.stage.module));
            }
        }
        Commands::Parse {
            filename: _filename,
        } => {
            // let contents = std::fs::read_to_string(filename).expect("Could not read file");
            // let parsed = parse(&contents).unwrap();
            // for root in parsed.roots() {
            //     println!("{:#?}", root);
            // }
            todo!()
        }
        Commands::Run { filename } => {
            use talk::compiling::driver::Driver;
            let driver = Driver::with_files(vec![filename.clone()]);
            let lowered = driver.lower().unwrap();

            use talk::lowering::interpreter::IRInterpreter;

            // let contents = std::fs::read_to_string(filename).expect("Could not read file");
            // let lowered = lower(&contents);
            for lowered in lowered {
                let mut interpreter = IRInterpreter::new(lowered.stage.module);
                println!("{:?}", interpreter.run());
            }
        }
    }
}

#[cfg(not(feature = "cli"))]
fn main() {
    use core::panic;

    panic!("Compiled without 'cli' feature.")
}
