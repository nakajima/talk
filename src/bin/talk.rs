#[cfg(feature = "cli")]
fn main() {
    use clap::{Parser, Subcommand};
    use talk::{
        constraint_solver::ConstraintSolver, lowering, name_resolver::NameResolver, parser::parse,
        type_checker::TypeChecker,
    };

    /// Simple program to greet a person
    #[derive(Parser, Debug)]
    #[command(version, about, long_about = None)]
    struct Cli {
        #[command(subcommand)]
        command: Commands,
    }

    #[derive(Subcommand, Debug)]
    enum Commands {
        IR { filename: String },
        Run { filename: String },
    }

    env_logger::builder().try_init().unwrap();

    let cli = Cli::parse();

    // You can check for the existence of subcommands, and if found use their
    // matches just as you would the top level cmd
    match &cli.command {
        Commands::IR { filename } => {
            // Read entire file into a String
            let contents = std::fs::read_to_string(filename).expect("Could not read file");

            let parsed = parse(&contents).unwrap();
            let resolved = NameResolver::new().resolve(parsed);
            let mut inferred = TypeChecker.infer(resolved).unwrap();
            let mut solver = ConstraintSolver::new(&mut inferred);
            solver.solve().unwrap();

            let lowered = lowering::ir::Lowerer::new(inferred).lower().unwrap();

            // Use the pretty printer
            use talk::lowering::ir_printer::pretty_print_ir;
            println!("{}", pretty_print_ir(&lowered.functions()));
        }
        Commands::Run { filename } => {
            println!("WIP: {}", filename);
            // Read entire file into a String
        }
    }
}

#[cfg(not(feature = "cli"))]
fn main() {
    use core::panic;

    panic!("Compiled without 'cli' feature.")
}
