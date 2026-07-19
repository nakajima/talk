use talk::compiling::driver::DriverConfig;

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
        /// Show a parse tree of the input.
        Parse {
            #[arg(value_hint = ValueHint::FilePath)]
            filename: Option<String>,
        },
        /// The Type at a position (byte offset, or 1-based
        /// line/column).
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
        /// Formats the input to stdout
        Format {
            #[arg(value_hint = ValueHint::FilePath)]
            filename: Option<String>,
            #[arg(long)]
            width: Option<usize>,
        },
        /// Syntax highlight the input as HTML
        Html {
            #[arg(value_hint = ValueHint::FilePath)]
            filename: Option<String>,
        },
        /// Type-check the input
        Check {
            #[arg(value_hint = ValueHint::FilePath)]
            filenames: Vec<String>,
            #[arg(long)]
            json: bool,
        },
        /// Compile and execute the input (or the current package's binary
        /// when no filenames are given inside a package).
        Run {
            #[arg(value_hint = ValueHint::FilePath)]
            filenames: Vec<String>,
            /// Execute this zero-parameter public function instead of the
            /// script's top-level statements.
            #[arg(long, value_name = "NAME")]
            entry: Option<String>,
            /// Select the package binary to run.
            #[arg(long, value_name = "NAME")]
            bin: Option<String>,
            /// Use only locally installed package sources.
            #[arg(long)]
            offline: bool,
        },
        /// Discover and execute `.test.tlk` Talk tests.
        Test {
            #[arg(value_hint = ValueHint::FilePath)]
            paths: Vec<String>,
            #[arg(long)]
            json: bool,
            /// Run only the test with this exact name.
            #[arg(long, value_name = "NAME")]
            filter: Option<String>,
        },
        /// Compile the input to a bytecode image.
        Build {
            #[arg(value_hint = ValueHint::FilePath)]
            filenames: Vec<String>,
            /// Where to write the image.
            #[arg(short, long, value_name = "FILE")]
            output: String,
            #[arg(long, value_name = "NAME")]
            entry: Option<String>,
        },
        /// Validate and execute a bytecode image.
        RunImage {
            #[arg(value_hint = ValueHint::FilePath)]
            filename: String,
        },
        /// Render the bytecode compiled from the input.
        Bytecode {
            #[arg(value_hint = ValueHint::FilePath)]
            filenames: Vec<String>,
            #[arg(long, value_name = "NAME")]
            entry: Option<String>,
        },
        /// Render the backend's middle representation for the input.
        Mir {
            #[arg(value_hint = ValueHint::FilePath)]
            filenames: Vec<String>,
            #[arg(long, value_name = "NAME")]
            entry: Option<String>,
        },
        /// Create a new package directory.
        New {
            #[arg(value_hint = ValueHint::DirPath)]
            name: String,
        },
        /// Install package dependencies in the current directory.
        Install {
            #[arg(long)]
            offline: bool,
        },
        /// Refresh the package lockfile in the current directory.
        Update {
            packages: Vec<String>,
            #[arg(long)]
            offline: bool,
        },
        /// Interactive frontend for declarations, type queries, and completion.
        Repl,
        /// Print a dense Talk language reference for LLMs.
        Llm,
        /// Generate shell completions
        Completions {
            #[arg(value_enum)]
            shell: Shell,
        },
        /// Install editor support files.
        Setup {
            #[command(subcommand)]
            target: SetupTarget,
        },
        /// Language? Server. Protocol!
        Lsp(LspArgs),
    }

    #[derive(Subcommand, Debug)]
    enum SetupTarget {
        /// Install plain Neovim runtime support files.
        #[command(name = "nvim")]
        Nvim(NvimSetupArgs),
    }

    #[derive(Debug, Args)]
    struct NvimSetupArgs {
        /// Overwrite existing TalkTalk runtime files if they differ.
        #[arg(long)]
        force: bool,
        /// Install into this runtime root instead of Neovim's data/site dir.
        #[arg(long, value_hint = ValueHint::DirPath)]
        target_dir: Option<std::path::PathBuf>,
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
            match driver.parse() {
                Ok(parsed) => println!("{:#?}", parsed.phase.asts),
                Err(err) => {
                    eprintln!("failed to parse: {err:?}");
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
                    eprintln!("error: provide --byte-offset, --line and --column, or --node-id");
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
        Commands::Setup { target } => {
            let result = match target {
                SetupTarget::Nvim(args) => {
                    NvimRuntimeInstaller::new(args.target_dir.as_deref(), args.force)
                        .and_then(|installer| installer.install())
                }
            };
            if let Err(err) = result {
                eprintln!("error: {err:#}");
                std::process::exit(1);
            }
        }
        Commands::Completions { shell } => {
            let mut cmd = Cli::command();
            let bin_name = cmd.get_name().to_string();
            generate(*shell, &mut cmd, bin_name, &mut std::io::stdout());
        }
        Commands::Repl => {
            talk::cli::repl::run();
        }
        Commands::Llm => {
            println!("{LLM_REFERENCE}");
        }
        Commands::New { name } => {
            let valid_name = matches!(
                std::path::Path::new(name).components().next(),
                Some(std::path::Component::Normal(_))
            ) && std::path::Path::new(name).components().count() == 1;
            if !valid_name {
                eprintln!("error: package name must be one directory name, not a path");
                std::process::exit(1);
            }
            let parent = match std::env::current_dir() {
                Ok(parent) => parent,
                Err(err) => {
                    eprintln!("error: failed to determine the current directory: {err}");
                    std::process::exit(1);
                }
            };
            let root = parent.join(name);
            match talk::compiling::package::PackageProject::create_executable_at(
                &root, name, "0.1.0", "main",
            ) {
                Ok(()) => println!("created package {}", root.display()),
                Err(err) => {
                    eprintln!("error: {err}");
                    std::process::exit(1);
                }
            }
        }
        Commands::Install { offline } => match install_current_package(*offline, false) {
            Ok(_) => println!("installed package dependencies"),
            Err(err) => {
                eprintln!("error: {err}");
                std::process::exit(1);
            }
        },
        Commands::Update { packages, offline } => {
            match update_current_package(*offline, packages) {
                Ok(_) => println!("updated package dependencies"),
                Err(err) => {
                    eprintln!("error: {err}");
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
                let text = match source.read() {
                    Ok(text) => text,
                    Err(err) => {
                        eprintln!("failed to read {path}: {err:?}");
                        std::process::exit(1);
                    }
                };
                docs.push(DocumentInput {
                    id: path.clone(),
                    path,
                    version: 0,
                    text,
                });
            }

            // The ownership pass below re-compiles from the same text:
            // stdin can only be read once, so the sources it uses are
            // rebuilt from what was already read, never re-fetched.
            let compile_sources: Vec<talk::compiling::driver::Source> = docs
                .iter()
                .map(|doc| {
                    talk::compiling::driver::Source::in_memory(
                        std::path::PathBuf::from(&doc.path),
                        doc.text.clone(),
                    )
                })
                .collect();
            let Some(workspace) = Workspace::new(docs) else {
                return;
            };

            let mut doc_ids: Vec<_> = workspace.diagnostics.keys().cloned().collect();
            doc_ids.sort();

            let mut has_errors = false;
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
                        // Warnings print but don't fail the check.
                        has_errors |=
                            diagnostic.severity == talk::analysis::DiagnosticSeverity::Error;
                    }
                }
            }

            // The ownership analysis is the check's second half: what
            // `talk run` rejects at the MIR stage — ownership,
            // exclusivity, the unsafe gate — reports here too (wave F
            // of docs/ownership-rethink-plan.md). Frontend errors gate
            // it: the backend assumes a well-typed program.
            if !has_errors {
                use talk::compiling::driver::{Driver, DriverConfig};
                // Check every declaration, not just the entry's
                // reachable set. Single-threaded at this point.
                unsafe { std::env::set_var("TALK_CHECK_ALL", "1") };
                let driver = Driver::new(compile_sources, DriverConfig::new("Main"));
                if let Ok(parsed) = driver.parse()
                    && let Ok(resolved) = parsed.resolve_names()
                {
                    let typed = resolved.type_check();
                    if !typed.has_errors()
                        && let Err((message, location)) = typed.check_ownership()
                    {
                        has_errors = true;
                        let (path, start, end) = location.unwrap_or((String::new(), 0, 0));
                        let text = workspace
                            .text_for(&path)
                            .map(str::to_string)
                            .or_else(|| std::fs::read_to_string(&path).ok())
                            .unwrap_or_default();
                        let to_utf16 = |byte: u32| {
                            text.get(..byte as usize)
                                .map(|prefix| prefix.encode_utf16().count())
                                .unwrap_or(0) as u32
                        };
                        let diagnostic = talk::analysis::Diagnostic {
                            node_id: None,
                            kind: None,
                            range: talk::analysis::TextRange::new(to_utf16(start), to_utf16(end)),
                            severity: talk::analysis::DiagnosticSeverity::Error,
                            message,
                        };
                        if *json {
                            json_entries.push(render_json_entry(&path, &text, &diagnostic));
                        } else {
                            print!(
                                "{}",
                                render_text(&path, &text, &diagnostic, ColorMode::Auto)
                            );
                        }
                    }
                }
            }

            if *json {
                println!("{}", render_json_output(&json_entries));
            }

            if has_errors {
                std::process::exit(1);
            }
        }
        Commands::Run {
            filenames,
            entry,
            bin,
            offline,
        } => {
            use talk::compiling::driver::{Driver, DriverConfig, execute_module};

            if *offline
                && (filenames.is_empty()
                    && !talk::compiling::package::PackageProject::exists_at(std::path::Path::new(
                        ".",
                    )))
            {
                eprintln!("error: --offline requires package execution");
                std::process::exit(1);
            }
            if filenames.is_empty()
                && talk::compiling::package::PackageProject::exists_at(std::path::Path::new("."))
            {
                let project = match talk::compiling::package::PackageProject::open_at(
                    std::path::PathBuf::from("."),
                    *offline,
                ) {
                    Ok(project) => project,
                    Err(err) => {
                        eprintln!("error: {err}");
                        std::process::exit(1);
                    }
                };
                let executable =
                    match project.compile_binary_entry(bin.as_deref(), entry.as_deref()) {
                        Ok(executable) => executable,
                        Err(err) => {
                            eprintln!("error: {err}");
                            std::process::exit(1);
                        }
                    };
                let mut io = talk_runtime::io::StdioIO;
                match execute_module(&executable, &mut io) {
                    Ok(Some(rendered)) => println!("{rendered}"),
                    Ok(None) => {}
                    Err(message) => {
                        eprintln!("error: {message}");
                        std::process::exit(1);
                    }
                }
                return;
            }

            let sources = sources_for_filenames(filenames);
            let driver = Driver::new(sources, DriverConfig::new("Main"));
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
                    eprintln!("{diagnostic}");
                }
                std::process::exit(1);
            }

            let module = match typed.compile_executable(entry.as_deref()) {
                Ok(module) => module,
                Err(message) => {
                    eprintln!("error: {message}");
                    std::process::exit(1);
                }
            };
            let mut io = talk_runtime::io::StdioIO;
            match execute_module(&module, &mut io) {
                Ok(Some(rendered)) => println!("{rendered}"),
                Ok(None) => {}
                Err(message) => {
                    eprintln!("error: {message}");
                    std::process::exit(1);
                }
            }
        }
        Commands::Test {
            paths,
            json,
            filter,
        } => {
            // A path argument names the project under test: anchor at its
            // enclosing package root (walking up from the first path), so
            // `package::` imports resolve the same from anywhere. With no
            // paths, the current directory is the project as before.
            let project_root = paths
                .first()
                .and_then(talk::compiling::package::PackageProject::enclosing_root)
                .unwrap_or_else(|| std::path::PathBuf::from("."));
            if talk::compiling::package::PackageProject::exists_at(&project_root) {
                let project =
                    match talk::compiling::package::PackageProject::open_at(project_root, false) {
                        Ok(project) => project,
                        Err(err) => {
                            eprintln!("error: {err}");
                            std::process::exit(1);
                        }
                    };
                let package_paths: Vec<std::path::PathBuf> =
                    paths.iter().map(std::path::PathBuf::from).collect();
                if *json {
                    match project.run_tests_json_at_paths(&package_paths, filter.clone()) {
                        Ok(outcome) => {
                            println!("{}", outcome.to_json());
                            if let talk::testing::JsonOutcome::Finished(summary) = outcome
                                && summary.failed()
                            {
                                std::process::exit(1);
                            }
                        }
                        Err(err) => {
                            println!(
                                "{}",
                                talk::testing::JsonOutcome::error_json("package", &err.to_string())
                            );
                            std::process::exit(1);
                        }
                    }
                } else {
                    match project.run_tests_at_paths_with_filter(&package_paths, filter.clone()) {
                        Ok(talk::testing::Outcome::NoTests) => {
                            eprintln!("no .test.tlk files found")
                        }
                        Ok(talk::testing::Outcome::Finished(summary)) => {
                            print!("{}", summary.output);
                            if summary.failed() {
                                eprintln!("{} test assertion(s) failed", summary.failures);
                                std::process::exit(1);
                            }
                        }
                        Err(err) => {
                            eprintln!("error: {err}");
                            std::process::exit(1);
                        }
                    }
                }
                return;
            }
            let runner = talk::testing::Runner::new(paths.iter().map(std::path::PathBuf::from))
                .with_filter(filter.clone());
            if *json {
                match runner.run_json() {
                    Ok(outcome) => {
                        println!("{}", outcome.to_json());
                        if let talk::testing::JsonOutcome::Finished(summary) = outcome
                            && summary.failed()
                        {
                            std::process::exit(1);
                        }
                    }
                    Err(err) => {
                        println!(
                            "{}",
                            talk::testing::JsonOutcome::error_json(err.kind(), &err.to_string())
                        );
                        std::process::exit(1);
                    }
                }
            } else {
                match runner.run() {
                    Ok(talk::testing::Outcome::NoTests) => {
                        eprintln!("no .test.tlk files found")
                    }
                    Ok(talk::testing::Outcome::Finished(summary)) => {
                        print!("{}", summary.output);
                        if summary.failed() {
                            eprintln!("{} test assertion(s) failed", summary.failures);
                            std::process::exit(1);
                        }
                    }
                    Err(talk::testing::TestError::CompileDiagnostics(diagnostics)) => {
                        eprint!(
                            "{}",
                            diagnostics.render_text(talk::cli::diagnostics::ColorMode::Auto)
                        );
                        std::process::exit(1);
                    }
                    Err(err) => {
                        eprintln!("error: {err}");
                        std::process::exit(1);
                    }
                }
            }
        }
        Commands::Build {
            filenames,
            output,
            entry,
        } => {
            let executable = compile_or_exit(filenames, entry.as_deref());
            let bytes = match executable.encode_bytecode() {
                Ok(bytes) => bytes,
                Err(err) => {
                    eprintln!("error: failed to encode bytecode: {err:?}");
                    std::process::exit(1);
                }
            };
            if let Err(err) = std::fs::write(output, bytes) {
                eprintln!("error: failed to write {output}: {err}");
                std::process::exit(1);
            }
        }
        Commands::RunImage { filename } => {
            use talk::compiling::driver::execute_image;
            let bytes = match std::fs::read(filename) {
                Ok(bytes) => bytes,
                Err(err) => {
                    eprintln!("error: failed to read {filename}: {err}");
                    std::process::exit(1);
                }
            };
            let mut io = talk_runtime::io::StdioIO;
            match execute_image(&bytes, &mut io) {
                Ok(Some(rendered)) => println!("{rendered}"),
                Ok(None) => {}
                Err(message) => {
                    eprintln!("error: {message}");
                    std::process::exit(1);
                }
            }
        }
        Commands::Bytecode { filenames, entry } => {
            let executable = compile_or_exit(filenames, entry.as_deref());
            print!("{}", executable.render_bytecode());
        }
        Commands::Mir { filenames, entry } => {
            let typed = check_or_exit(filenames);
            match typed.render_mir(entry.as_deref()) {
                Ok(rendered) => print!("{rendered}"),
                Err(message) => {
                    eprintln!("error: {message}");
                    std::process::exit(1);
                }
            }
        }
        Commands::Html { filename } => {
            init();
            use talk::highlighter::highlight_html;

            let source = input_text(filename.as_deref());
            let html = highlight_html(&source);
            println!("{html}");
        }
        Commands::Format { filename, width } => {
            use talk::formatter;

            init();
            let source = input_text(filename.as_deref());
            print!(
                "{}",
                formatter::format_string_with_width(&source, width.unwrap_or(80))
            );
        }
    }
}

#[cfg(feature = "cli")]
const STDIN_NAME: &str = "<stdin>";

#[cfg(feature = "cli")]
const LLM_REFERENCE: &str = r#"# Talk language reference for LLMs

Talk is a statically typed, Swift-flavored language with local type inference, generics, protocols, algebraic effects, and value-semantics aggregates. This build compiles and executes programs through a register-bytecode backend, with ownership checking (implicit sharing: consumes retain when a value has later uses; exclusivity, linearity, and the intrinsic `'unsafe` effect remain static errors). Files normally use `.tlk`; core library files live in `core/` and are implicitly imported unless a file starts with `// no-core`.

## CLI

    talk run [--entry NAME] files   compile and execute (or the current package's binary; --bin selects one, --offline skips fetches)
    talk test [paths]               discover and run `.test.tlk` tests
    talk build files -o FILE        compile to a bytecode image
    talk run-image FILE             validate and execute a bytecode image
    talk check [--json] files       typecheck, ownership-check, print diagnostics
    talk bytecode / talk mir files  render lowered output
    talk new / install / update     package management
    talk repl                       interactive type queries and completion
    talk format [file]              format source from file or stdin
    talk hover file --line N --column N | --byte-offset N | --node-id ID
    talk html / talk parse          development views
    talk lsp --stdio                language server
    talk setup nvim                 install Neovim runtime support files
    talk completions SHELL          shell completion script
    talk llm                        print this reference

## Lexical and module basics

Comments are `//` line comments. Identifiers are ordinary words; type names are conventionally upper camel case. Statements are separated by newlines; semicolons are accepted but conventionally omitted. Blocks are `{ ... }`. Top-level declarations may be prefixed with `public` to export them. Imports are explicit: `use package::path::{ Foo, bar }`, `use package::path::{ Foo as LocalFoo }`, `use package::path`, or dependency imports such as `use dependency::{ Foo }` / `use dependency`.

## Declarations

    public let name: Type = expr
    func f<T>(x: T, y: Int) -> Result { body }
    struct Point {
        let x: Int
        let y: Int
        init(x: Int, y: Int) { self.x = x; self.y = y; self }
    }
    enum Optional<T> { case some(T) case none }
    protocol P { associated Element func next() -> Element? }
    extend Type: P { typealias Element = Int func next() -> Int? { ... } }
    extend Type { func method() -> R { ... } static func make() -> Type { ... } }
    typealias Name = Type
    effect 'name(payload: Type) -> ReturnType

Function result annotations are optional when inferable, and so are effect payload type annotations (`effect 'oops(error) -> Never`). `init` bodies assign `self.field` and return `self`. Methods have implicit `self`; do not declare a self parameter. Receiver modes: plain `func` reads a shared value, `mut func` may update `self` and writes the receiver back at the call site, `consuming func` takes ownership. Parameters take ownership with the `consume` modifier: `func eat(consume xs: Array<Int>)`. `static func` is called on the type/protocol namespace.

## Expressions and control flow

Literals: integers, floats, strings, `true`, `false`, arrays `[a, b]`, records `{ field: expr, other: expr }`, closures `func(x: Int) -> Int { x + 1 }`. Call arguments are positional (`f(a, b)`) or labeled (`f(x: 1, y: 2)`). Constructors look like calls: `Point(x: 1, y: 2)`, enum cases may be qualified or inferred: `Optional<Int>.some(1)` or `.some(1)`. Field/member access is `value.field` and `value.method(args)`. Generic arguments may be explicit: `id<Int>(1)`. Arguments are always passed plainly — `&x` is not expression syntax; a parameter's `&T`/`&mut T` type alone makes the call site a borrow.

Bindings and mutation: `let x = expr`; assignment is `x = expr` or `self.field = expr`. `let` variables are mutable by assignment in current Talk. Type ascription is `let x: Type = expr`.

Blocks are expressions. `if cond { a } else { b }` is an expression; branches must agree. `if let .some(x) = expr { ... }` matches a single pattern. `loop { ... }` loops forever until `break`; `loop condition { ... }` is while-like. `break`, `continue`, and `return expr` are supported. `for x in iterable { ... }` uses the iterable/iterator protocols.

Pattern matching:

    match expr {
        .caseName(payload) -> result,
        .none -> other,
        0 -> zero,
        _ -> fallback
    }

Patterns can bind enum payloads. GADT-style enum cases may refine the result type, e.g. `case int(Int) -> Expr<Int>`.

Trailing block syntax passes a final closure argument: `f { body }` is `f(func() { body })`.

## Types

Builtin scalar/value types include `Int`, `Float`, `Bool`, `Byte`, `RawPtr`, `Void`/`()`, and `Never`. Core nominal types include `String`, `Substring`, `Array<T>`, and `Optional<T>`; `T?` is syntax for optional. Structural record types are written `{ field: Type }` and match record literals and patterns. Function types are `(A, B) -> R`; effectful functions write effects before the arrow, e.g. `(A) 'io -> R` or `func read() 'io -> Int`. Borrow types use `&T` and exclusive borrows use `&mut T`. Protocol existential types use `any P`; associated type constraints use `any P<Element = Int>` (only protocols whose requirements keep `Self` in receiver position can form existentials — core `Iterator` cannot). Protocol composition uses `&` in where clauses: `where T: A & B`, with multiple predicates chained by `&&`; inline bounds take a single protocol.

Generics are written with angle brackets: `func id<T>(x: T) -> T`. Simple bounds use `T: Protocol`; associated types use `associated Name` in protocols and `typealias Name = Type` in conforming extensions. Protocol requirements can include funcs, mut/consuming funcs, static funcs, associated types, and defaults in extensions.

## Operators and builtins

Common operators are library-backed or builtin-resolved: arithmetic `+ - * /`, comparison `== != < <= > >=`, boolean values, string concatenation via `+`, member calls, and casts/ascriptions using `as` for protocol existentials where supported. `print(x)` prints Showable-ish values; `sleep(ms)` and I/O live in core effects. The core library defines protocols such as `Showable`, `Add`, `Equatable`, `Iterable`, `Iterator`, `From`, `Into`, `Borrowed`, and `Owner`.

Low-level trusted IR escapes use `@_ir(args...) { ... }` and appear mainly in core. Operations include integer/float math, comparisons, `alloc`, `load`, `store`, `gep`, `copy`, and I/O shims. Outside core, `_ir` requires the intrinsic `'unsafe` effect; acknowledge and discharge it with a lexical `@unsafe { ... }` block.

## Effects

Effects are named with a leading tick: `effect 'throws(error: String) -> Never`. Calling an effect is expression syntax: `'throws("bad")`. Effect rows appear on functions before `->`: `func f() 'throws -> ()`. Handlers use `@handle 'effect { payload in body }` for abortive handling; when the effect return type is not `Never`, `continue expr` inside the handler resumes at the perform site with that value.

## Memory and value model

Source-level structs, enums, arrays, strings, records, and function values have value semantics. `&T` and `&mut T` express borrow permissions, `consuming` expresses ownership transfer, and marker protocols like `Owner`/`Borrowed` describe library-level ownership roles. The backend enforces ownership with implicit sharing: a consume of a value with later uses retains automatically, snapshots preserve live views across owner mutation, and only exclusivity violations, linear-value misuse, borrow escapes (returning or globally storing a view of frame-owned data), and ungated `unsafe` constructs are static errors.

## Compiler model

Pipeline: parse -> name resolution/imports -> OutsideIn-style type checking with qualified predicates, protocols, associated types, existentials, and GADT refinements -> TypedProgram -> register MIR with ownership checking and drop elaboration -> register bytecode executed by the runtime VM (the static C runtime and the Wasm embedding host the same VM). Useful inspection commands are `talk check`, `talk hover`, and `talk mir`.
"#;

#[cfg(feature = "cli")]
const NVIM_RUNTIME_RAW_BASE: &str =
    "https://raw.githubusercontent.com/nakajima/talk/main/dev/editors/nvim";

#[cfg(feature = "cli")]
const NVIM_RUNTIME_FILES: &[&str] = &[
    "ftdetect/talktalk.lua",
    "ftplugin/talktalk.lua",
    "indent/talktalk.vim",
    "lua/neotest-talk/init.lua",
    "syntax/talktalk.vim",
];

#[cfg(feature = "cli")]
struct NvimRuntimeInstaller {
    target_root: std::path::PathBuf,
    force: bool,
}

#[cfg(feature = "cli")]
impl NvimRuntimeInstaller {
    fn new(target_dir: Option<&std::path::Path>, force: bool) -> anyhow::Result<Self> {
        let target_root = match target_dir {
            Some(path) => path.to_path_buf(),
            None => Self::default_target_root()?,
        };

        Ok(Self { target_root, force })
    }

    fn install(&self) -> anyhow::Result<()> {
        use anyhow::Context as _;

        println!("Installing TalkTalk Neovim runtime files from github.com/nakajima/talk");
        println!("Target runtime root: {}", self.target_root.display());

        let mut downloads = Vec::with_capacity(NVIM_RUNTIME_FILES.len());
        for relative_path in NVIM_RUNTIME_FILES {
            let contents = Self::download_file(relative_path)?;
            downloads.push((*relative_path, contents));
        }

        for (relative_path, contents) in &downloads {
            let target = self.target_root.join(*relative_path);
            if target.exists() && !self.force {
                let existing = std::fs::read(&target)
                    .with_context(|| format!("failed to read {}", target.display()))?;
                if existing.as_slice() != contents.as_slice() {
                    anyhow::bail!(
                        "{} already exists and differs; rerun with --force to overwrite",
                        target.display()
                    );
                }
            }
        }

        for (relative_path, contents) in downloads {
            let target = self.target_root.join(relative_path);
            if target.exists() && !self.force {
                println!("up to date: {}", target.display());
                continue;
            }

            if let Some(parent) = target.parent() {
                std::fs::create_dir_all(parent)
                    .with_context(|| format!("failed to create {}", parent.display()))?;
            }
            std::fs::write(&target, contents)
                .with_context(|| format!("failed to write {}", target.display()))?;
            println!("installed: {}", target.display());
        }

        Ok(())
    }

    fn default_target_root() -> anyhow::Result<std::path::PathBuf> {
        if let Some(data_dir) = Self::nvim_data_dir() {
            return Ok(data_dir.join("site"));
        }

        Self::fallback_data_site_dir()
    }

    fn nvim_data_dir() -> Option<std::path::PathBuf> {
        let output = std::process::Command::new("nvim")
            .args([
                "--headless",
                "-u",
                "NONE",
                "-i",
                "NONE",
                "--noplugin",
                "+lua io.write(vim.fn.stdpath('data'))",
                "+qa!",
            ])
            .output()
            .ok()?;

        if !output.status.success() {
            return None;
        }

        let stdout = String::from_utf8(output.stdout).ok()?;
        let path = stdout.trim();
        if path.is_empty() {
            None
        } else {
            Some(std::path::PathBuf::from(path))
        }
    }

    fn fallback_data_site_dir() -> anyhow::Result<std::path::PathBuf> {
        let appname = std::env::var_os("NVIM_APPNAME")
            .filter(|value| !value.as_os_str().is_empty())
            .unwrap_or_else(|| "nvim".into());

        let data_home = match std::env::var_os("XDG_DATA_HOME")
            .filter(|value| !value.as_os_str().is_empty())
        {
            Some(path) => std::path::PathBuf::from(path),
            None => {
                let home = std::env::var_os("HOME").ok_or_else(|| {
                    anyhow::anyhow!("could not find Neovim data dir; set HOME or pass --target-dir")
                })?;
                std::path::PathBuf::from(home).join(".local/share")
            }
        };

        Ok(data_home.join(appname).join("site"))
    }

    fn download_file(relative_path: &str) -> anyhow::Result<Vec<u8>> {
        let url = format!("{NVIM_RUNTIME_RAW_BASE}/{relative_path}");
        Downloader::download_url(&url)
    }
}

#[cfg(feature = "cli")]
struct Downloader;

#[cfg(feature = "cli")]
impl Downloader {
    fn download_url(url: &str) -> anyhow::Result<Vec<u8>> {
        let attempts = [
            ("curl", vec!["-fsSL", url]),
            ("wget", vec!["-qO-", url]),
            ("fetch", vec!["-qo", "-", url]),
        ];
        let mut failures = Vec::new();

        for (program, args) in attempts {
            match std::process::Command::new(program).args(args).output() {
                Ok(output) if output.status.success() => return Ok(output.stdout),
                Ok(output) => {
                    let stderr = String::from_utf8_lossy(&output.stderr).trim().to_string();
                    if stderr.is_empty() {
                        failures.push(format!("{program} exited with {}", output.status));
                    } else {
                        failures.push(format!("{program} exited with {}: {stderr}", output.status));
                    }
                }
                Err(err) if err.kind() == std::io::ErrorKind::NotFound => {}
                Err(err) => failures.push(format!("{program}: {err}")),
            }
        }

        if failures.is_empty() {
            anyhow::bail!("could not download {url}; install curl, wget, or fetch");
        }

        anyhow::bail!(
            "could not download {url}; install curl, wget, or fetch; attempts failed: {}",
            failures.join("; ")
        );
    }
}

#[cfg(feature = "cli")]
fn install_current_package(
    offline: bool,
    update: bool,
) -> Result<talk::compiling::package::PackageProject, talk::compiling::package::PackageError> {
    let root =
        std::env::current_dir().map_err(|source| talk::compiling::package::PackageError::Io {
            context: "failed to determine the current directory".into(),
            source,
        })?;
    talk::compiling::package::PackageProject::install_at(root, offline, update)
}

#[cfg(feature = "cli")]
fn update_current_package(
    offline: bool,
    packages: &[String],
) -> Result<talk::compiling::package::PackageProject, talk::compiling::package::PackageError> {
    let root =
        std::env::current_dir().map_err(|source| talk::compiling::package::PackageError::Io {
            context: "failed to determine the current directory".into(),
            source,
        })?;
    talk::compiling::package::PackageProject::update_at(root, offline, packages)
}

#[cfg(feature = "cli")]
fn read_stdin() -> String {
    use std::io::Read;

    let mut buffer = String::new();
    if let Err(err) = std::io::stdin().read_to_string(&mut buffer) {
        eprintln!("failed to read stdin: {err}");
        std::process::exit(1);
    }
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
fn check_or_exit(
    filenames: &[String],
) -> talk::compiling::driver::Driver<talk::compiling::driver::Typed> {
    use talk::compiling::driver::{Driver, DriverConfig};
    let sources = sources_for_filenames(filenames);
    let driver = Driver::new(sources, DriverConfig::new("Main"));
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
            eprintln!("{diagnostic}");
        }
        std::process::exit(1);
    }
    typed
}

#[cfg(feature = "cli")]
fn compile_or_exit(
    filenames: &[String],
    entry: Option<&str>,
) -> talk::compiling::driver::Executable {
    match check_or_exit(filenames).compile_executable(entry) {
        Ok(executable) => executable,
        Err(message) => {
            eprintln!("error: {message}");
            std::process::exit(1);
        }
    }
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
        Some(name) if name != "-" => match std::fs::read_to_string(name) {
            Ok(text) => text,
            Err(err) => {
                eprintln!("failed to read {name}: {err}");
                std::process::exit(1);
            }
        },
        _ => read_stdin(),
    }
}

#[cfg(not(feature = "cli"))]
fn main() {
    eprintln!("talk was compiled without the 'cli' feature");
    std::process::exit(1);
}

pub fn init() {
    use tracing_subscriber::{EnvFilter, prelude::*, registry};
    let tree = tracing_tree::HierarchicalLayer::new(2).with_filter(EnvFilter::from_default_env()); // ordinary RUST_LOG filtering
    registry().with(tree).init();
}
