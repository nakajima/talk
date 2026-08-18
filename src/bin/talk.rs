use talk::compiling::driver::DriverConfig;

#[cfg(feature = "cli")]
#[tokio::main(flavor = "current_thread")]
async fn main() {
    use std::ffi::OsString;

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
        /// Type-check the input. Package files use their enclosing
        /// package context; with no filenames, check the whole workspace.
        Check {
            #[arg(value_hint = ValueHint::FilePath)]
            filenames: Vec<String>,
            #[arg(long)]
            json: bool,
        },
        /// Rewrite call sites to match declared argument labels (ADR 0041).
        FixLabels {
            #[arg(value_hint = ValueHint::FilePath)]
            filenames: Vec<std::path::PathBuf>,
            /// Treat the given directory as the core corpus and fix it.
            #[arg(long, value_name = "DIR")]
            core: Option<std::path::PathBuf>,
            /// Fix each file as its own standalone program.
            #[arg(long)]
            each: bool,
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
            /// Arguments passed to the program after `--`.
            #[arg(last = true, value_name = "ARG")]
            arguments: Vec<String>,
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
            /// Where to write the image, or the executable with --native.
            #[arg(short, long, value_name = "FILE")]
            output: String,
            #[arg(long, value_name = "NAME")]
            entry: Option<String>,
            /// Compile ahead of time to a native executable through C
            /// instead of writing a bytecode image.
            #[arg(long)]
            native: bool,
            /// The C compiler to drive (default: $CC, else `cc`; with
            /// --target, `zig cc`).
            #[arg(long, value_name = "PROGRAM")]
            cc: Option<String>,
            /// Cross-compile for this target triple, which needs `zig`
            /// on PATH (for example aarch64-linux-musl).
            #[arg(long, value_name = "TRIPLE")]
            target: Option<String>,
            /// Extra arguments for the C compiler, after the defaults.
            #[arg(long = "cflag", value_name = "FLAG")]
            cflags: Vec<String>,
            /// Keep the generated C beside the executable.
            #[arg(long)]
            keep_c: bool,
        },
        /// Regenerate the compiled core artifact embedded by WASM builds.
        CoreArtifact {
            /// Verify the checked-in artifact instead of writing it.
            #[arg(long)]
            check: bool,
        },
        /// Regenerates the self-hosted frontend artifact (bootstrap/frontend.tbc)
        Bootstrap {
            /// Directory of .tlk sources (non-recursive); omit for the
            /// frontend profile.
            #[arg(value_hint = ValueHint::DirPath)]
            dir: Option<String>,
            /// Where to write the artifact; the manifest lands beside
            /// it. Required with an explicit source directory.
            #[arg(short, long, value_name = "FILE")]
            output: Option<String>,
            /// Exported function names (repeatable).
            #[arg(long = "export", value_name = "NAME")]
            exports: Vec<String>,
            /// Effects the exports may perform (repeatable; default none).
            #[arg(long = "allow-effect", value_name = "EFFECT")]
            allow_effects: Vec<String>,
            /// Verify the existing artifact and manifest instead of writing.
            #[arg(long)]
            check: bool,
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
        /// Emit C source for the input (the ahead-of-time target).
        C {
            #[arg(value_hint = ValueHint::FilePath)]
            filenames: Vec<String>,
            #[arg(long, value_name = "NAME")]
            entry: Option<String>,
            /// Emit a library instead of a program: no `main`, one
            /// host-callable wrapper per exported function (repeatable).
            #[arg(long = "export", value_name = "NAME")]
            exports: Vec<String>,
            /// Effects the exports may perform (repeatable).
            #[arg(long = "allow-effect", value_name = "EFFECT")]
            allow_effects: Vec<String>,
            /// External symbol prefix for the library (default: talk).
            #[arg(long, value_name = "PREFIX")]
            prefix: Option<String>,
            /// Write the library's generated C header here.
            #[arg(long, value_name = "PATH", value_hint = ValueHint::FilePath)]
            header: Option<String>,
            /// Write the library's export-name-to-symbol manifest here.
            #[arg(long, value_name = "PATH", value_hint = ValueHint::FilePath)]
            manifest: Option<String>,
        },
        /// Render the optimized backend middle representation for the input.
        Mir {
            #[arg(value_hint = ValueHint::FilePath)]
            filenames: Vec<String>,
            #[arg(long, value_name = "NAME")]
            entry: Option<String>,
            /// Render MIR before optimization.
            #[arg(long)]
            no_opt: bool,
            /// Annotate the dump with source spans and binding names
            /// (survives optimization).
            #[arg(long)]
            debug: bool,
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
        /// List the package's locked dependencies: the import each one
        /// provides and the names that import makes available.
        Dependencies {
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
        Repl {
            /// Import the current package library's public surface.
            #[arg(long)]
            package: bool,
        },
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
        #[command(external_subcommand)]
        External(Vec<OsString>),
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
        Commands::External(arguments) => run_external_command(arguments),
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
                text: text.as_str().into(),
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
        Commands::Repl { package } => {
            if let Err(err) = talk::cli::repl::run(*package) {
                eprintln!("error: {err}");
                std::process::exit(1);
            }
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
        Commands::Dependencies { offline } => {
            let root = match std::env::current_dir() {
                Ok(root) => root,
                Err(err) => {
                    eprintln!("error: failed to determine the current directory: {err}");
                    std::process::exit(1);
                }
            };
            match talk::compiling::package::PackageProject::open_at(root, *offline)
                .and_then(|project| project.dependency_report())
            {
                Ok(dependencies) => {
                    if dependencies.is_empty() {
                        println!("no dependencies");
                    }
                    for dependency in dependencies {
                        let kind = if dependency.direct {
                            "direct"
                        } else {
                            "transitive"
                        };
                        println!(
                            "{} {} ({}, {})",
                            dependency.name, dependency.version, dependency.source, kind
                        );
                        println!("  import: use {}", dependency.import_name);
                        if dependency.exports.is_empty() {
                            println!("  exports: (none)");
                        } else {
                            println!("  exports: {}", dependency.exports.join(", "));
                        }
                    }
                }
                Err(err) => {
                    eprintln!("error: {err}");
                    std::process::exit(1);
                }
            }
        }
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

            // Package context comes from the selected file as well as the
            // current directory. Keep explicit stdin dependency-free.
            let package_root = if filenames.is_empty() {
                talk::compiling::package::PackageProject::enclosing_root(".")
            } else if filenames.iter().all(|filename| filename != "-") {
                filenames
                    .first()
                    .and_then(talk::compiling::package::PackageProject::enclosing_root)
            } else {
                None
            };

            let (docs, package) = match package_root {
                Some(root) => {
                    let project =
                        match talk::compiling::package::PackageProject::open_at(&root, false) {
                            Ok(project) => project,
                            Err(err) => {
                                eprintln!("error: {err}");
                                std::process::exit(1);
                            }
                        };
                    let context = match project.package_compile_context() {
                        Ok(context) => context,
                        Err(err) => {
                            eprintln!("error: {err}");
                            std::process::exit(1);
                        }
                    };
                    let sources = if filenames.is_empty() {
                        let paths = talk::cli::package::workspace_source_files(&root);
                        if paths.is_empty() {
                            eprintln!("error: no package sources found under {}", root.display());
                            std::process::exit(1);
                        }
                        paths
                            .into_iter()
                            .map(talk::compiling::driver::Source::from)
                            .collect()
                    } else {
                        sources_for_filenames(filenames)
                    };
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
                            text: text.into(),
                        });
                    }
                    (docs, Some(context))
                }
                None => {
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
                            text: text.into(),
                        });
                    }
                    (docs, None)
                }
            };

            let Some(workspace) = Workspace::new_with_package(docs, package) else {
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

            if *json {
                println!("{}", render_json_output(&json_entries));
            }

            if has_errors {
                std::process::exit(1);
            }
        }
        Commands::FixLabels {
            filenames,
            core,
            each,
        } => match talk::cli::fix_labels::run(core.as_deref(), filenames, *each) {
            Ok(applied) => println!("applied {applied} label fixes"),
            Err(err) => {
                eprintln!("{err}");
                std::process::exit(1);
            }
        },
        Commands::Run {
            filenames,
            entry,
            bin,
            offline,
            arguments,
        } => {
            use talk::compiling::driver::{Driver, DriverConfig};

            let package_root = if filenames.is_empty()
                && talk::compiling::package::PackageProject::exists_at(std::path::Path::new("."))
            {
                Some(std::path::PathBuf::from("."))
            } else if let [path] = filenames.as_slice()
                && talk::compiling::package::PackageProject::exists_at(std::path::Path::new(path))
            {
                Some(std::path::PathBuf::from(path))
            } else {
                None
            };
            if *offline && package_root.is_none() {
                eprintln!("error: --offline requires package execution");
                std::process::exit(1);
            }
            if let Some(package_root) = package_root {
                let project = match talk::compiling::package::PackageProject::open_at(
                    package_root.clone(),
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
                            print_package_error(&err);
                            std::process::exit(1);
                        }
                    };
                let argv0 = filenames
                    .first()
                    .cloned()
                    .unwrap_or_else(|| package_root.to_string_lossy().into_owned());
                let mut program_arguments = Vec::with_capacity(arguments.len() + 1);
                program_arguments.push(argv0);
                program_arguments.extend(arguments.iter().cloned());
                let mut io = talk_vm::io::StdioIO::with_args(program_arguments);
                match executable.run(&mut io) {
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
            let asts_by_source = resolved.phase.asts.clone();
            let typed = resolved.type_check();
            report_diagnostics_or_exit(&asts_by_source, &typed);

            let module = match typed.compile_executable(entry.as_deref()) {
                Ok(module) => module,
                Err(message) => {
                    eprintln!("error: {message}");
                    std::process::exit(1);
                }
            };
            let argv0 = filenames
                .first()
                .cloned()
                .unwrap_or_else(|| STDIN_NAME.to_string());
            let mut program_arguments = Vec::with_capacity(arguments.len() + 1);
            program_arguments.push(argv0);
            program_arguments.extend(arguments.iter().cloned());
            let mut io = talk_vm::io::StdioIO::with_args(program_arguments);
            match module.run(&mut io) {
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
                        Err(talk::compiling::package::PackageError::Test(err)) => {
                            println!("{}", err.to_json());
                            std::process::exit(1);
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
                        Err(talk::compiling::package::PackageError::Test(
                            talk::testing::TestError::CompileDiagnostics(diagnostics),
                        )) => {
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
            native,
            cc,
            target,
            cflags,
            keep_c,
        } => {
            // These only mean anything to the ahead-of-time path; taking
            // them and quietly writing a bytecode image instead would be
            // a silent no-op.
            if !*native && target.is_none() {
                let ignored = [
                    ("--cc", cc.is_some()),
                    ("--cflag", !cflags.is_empty()),
                    ("--keep-c", *keep_c),
                ];
                let given: Vec<&str> = ignored
                    .iter()
                    .filter(|(_, present)| *present)
                    .map(|(flag, _)| *flag)
                    .collect();
                if !given.is_empty() {
                    eprintln!(
                        "error: {} only applies with --native or --target",
                        given.join(", ")
                    );
                    std::process::exit(1);
                }
            }
            if *native || target.is_some() {
                build_native(
                    filenames,
                    output,
                    entry.as_deref(),
                    cc.as_deref(),
                    target.as_deref(),
                    cflags,
                    *keep_c,
                );
                return;
            }
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
        Commands::CoreArtifact { check } => {
            let bytes = talk::compiling::core::artifact_bytes().unwrap_or_else(|error| {
                eprintln!("error: {error}");
                std::process::exit(1);
            });
            let artifact_path = std::path::Path::new(talk::compiling::core::ARTIFACT_PATH);
            let manifest_path = std::path::Path::new(talk::compiling::core::ARTIFACT_MANIFEST_PATH);

            if *check {
                let manifest =
                    talk::compiling::core::artifact_manifest(&bytes).unwrap_or_else(|error| {
                        eprintln!("error: {error}");
                        std::process::exit(1);
                    });
                let current = std::fs::read(artifact_path)
                    .ok()
                    .is_some_and(|existing| existing == bytes)
                    && std::fs::read_to_string(manifest_path)
                        .ok()
                        .is_some_and(|existing| existing == manifest);
                if !current {
                    eprintln!(
                        "error: {} is stale; regenerate with `talk core-artifact`",
                        artifact_path.display()
                    );
                    std::process::exit(1);
                }
                println!("{} is up to date", artifact_path.display());
            } else {
                let manifest =
                    talk::compiling::core::artifact_manifest(&bytes).unwrap_or_else(|error| {
                        eprintln!("error: {error}");
                        std::process::exit(1);
                    });
                if let Some(parent) = artifact_path.parent()
                    && let Err(error) = std::fs::create_dir_all(parent)
                {
                    eprintln!("error: failed to create {}: {error}", parent.display());
                    std::process::exit(1);
                }
                if let Err(error) = std::fs::write(artifact_path, bytes) {
                    eprintln!(
                        "error: failed to write {}: {error}",
                        artifact_path.display()
                    );
                    std::process::exit(1);
                }
                if let Err(error) = std::fs::write(manifest_path, manifest) {
                    eprintln!(
                        "error: failed to write {}: {error}",
                        manifest_path.display()
                    );
                    std::process::exit(1);
                }
                println!("wrote {}", artifact_path.display());
            }
        }
        Commands::Bootstrap {
            dir,
            output,
            exports,
            allow_effects,
            check,
        } => {
            // With no source directory, this is the frontend profile:
            // the export list, allowed effects, and artifact paths all
            // come from one place (ADR 0043).
            let (outcome, output) = if let Some(dir) = dir {
                let Some(output) = output.clone() else {
                    eprintln!("error: --output is required with an explicit source directory");
                    std::process::exit(1);
                };
                let mut files: Vec<std::path::PathBuf> = match std::fs::read_dir(dir) {
                    Ok(entries) => entries
                        .filter_map(|entry| entry.ok())
                        .map(|entry| entry.path())
                        .filter(|path| path.extension().is_some_and(|ext| ext == "tlk"))
                        .collect(),
                    Err(err) => {
                        eprintln!("error: failed to read {dir}: {err}");
                        std::process::exit(1);
                    }
                };
                files.sort();
                if files.is_empty() {
                    eprintln!("error: {dir} contains no .tlk sources");
                    std::process::exit(1);
                }
                let mut sources = Vec::new();
                for path in &files {
                    let name = path
                        .file_name()
                        .map(|name| name.to_string_lossy().into_owned())
                        .unwrap_or_default();
                    match std::fs::read_to_string(path) {
                        Ok(text) => sources.push((name, text)),
                        Err(err) => {
                            eprintln!("error: failed to read {}: {err}", path.display());
                            std::process::exit(1);
                        }
                    }
                }
                match talk::compiling::bootstrap::bootstrap(
                    &sources,
                    exports,
                    allow_effects,
                    None,
                    None,
                ) {
                    Ok(outcome) => (outcome, output),
                    Err(err) => {
                        eprintln!("error: {err}");
                        std::process::exit(1);
                    }
                }
            } else {
                if !exports.is_empty() || !allow_effects.is_empty() || output.is_some() {
                    eprintln!(
                        "error: the frontend profile fixes its own output, exports, and effects; pass a source directory to override them"
                    );
                    std::process::exit(1);
                }
                let root = std::env::current_dir().unwrap_or_else(|err| {
                    eprintln!("error: cannot resolve current directory: {err}");
                    std::process::exit(1);
                });
                match talk::compiling::frontend::regenerate(&root) {
                    Ok(outcome) => (
                        outcome,
                        talk::compiling::frontend::artifact_path(&root)
                            .to_string_lossy()
                            .into_owned(),
                    ),
                    Err(err) => {
                        eprintln!("error: {err}");
                        std::process::exit(1);
                    }
                }
            };
            let manifest_path = std::path::Path::new(&output).with_extension("manifest");
            let abi_path = std::path::Path::new(&output).with_extension("abi");
            let c_path = std::path::Path::new(&output).with_extension("c");
            if *check {
                let abi_current = match &outcome.abi {
                    Some(abi) => std::fs::read_to_string(&abi_path)
                        .ok()
                        .is_some_and(|existing| existing == *abi),
                    None => !abi_path.exists(),
                };
                let c_current = match &outcome.c_source {
                    Some(c_source) => std::fs::read_to_string(&c_path)
                        .ok()
                        .is_some_and(|existing| existing == *c_source),
                    None => !c_path.exists(),
                };
                let current = std::fs::read(&output)
                    .ok()
                    .is_some_and(|existing| existing == outcome.image)
                    && std::fs::read_to_string(&manifest_path)
                        .ok()
                        .is_some_and(|existing| existing == outcome.manifest.to_text())
                    && abi_current
                    && c_current;
                if !current {
                    eprintln!(
                        "error: {output} is stale; regenerate with `talk bootstrap` (without --check)"
                    );
                    std::process::exit(1);
                }
                println!("{output} is up to date");
            } else {
                if let Some(parent) = std::path::Path::new(&output).parent()
                    && !parent.as_os_str().is_empty()
                    && let Err(err) = std::fs::create_dir_all(parent)
                {
                    eprintln!("error: failed to create {}: {err}", parent.display());
                    std::process::exit(1);
                }
                if let Err(err) = std::fs::write(&output, &outcome.image) {
                    eprintln!("error: failed to write {output}: {err}");
                    std::process::exit(1);
                }
                if let Err(err) = std::fs::write(&manifest_path, outcome.manifest.to_text()) {
                    eprintln!("error: failed to write {}: {err}", manifest_path.display());
                    std::process::exit(1);
                }
                if let Some(abi) = &outcome.abi
                    && let Err(err) = std::fs::write(&abi_path, abi)
                {
                    eprintln!("error: failed to write {}: {err}", abi_path.display());
                    std::process::exit(1);
                }
                if let Some(c_source) = &outcome.c_source
                    && let Err(err) = std::fs::write(&c_path, c_source)
                {
                    eprintln!("error: failed to write {}: {err}", c_path.display());
                    std::process::exit(1);
                }
            }
        }
        Commands::RunImage { filename } => {
            let bytes = match std::fs::read(filename) {
                Ok(bytes) => bytes,
                Err(err) => {
                    eprintln!("error: failed to read {filename}: {err}");
                    std::process::exit(1);
                }
            };
            let mut io = talk_vm::io::StdioIO::default();
            match talk_bytecode::run_image(&bytes, &mut io) {
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
        Commands::C {
            filenames,
            entry,
            exports,
            allow_effects,
            prefix,
            header,
            manifest,
        } => {
            if exports.is_empty() && (prefix.is_some() || header.is_some() || manifest.is_some()) {
                eprintln!("error: --prefix, --header, and --manifest require --export");
                std::process::exit(2);
            }
            let typed = check_or_exit(filenames);
            if exports.is_empty() {
                let mir_entry = match entry.as_deref() {
                    Some(name) => talk::compiling::driver::MirEntry::Named(name),
                    None => talk::compiling::driver::MirEntry::Script,
                };
                match typed.compile_mir(mir_entry).and_then(|output| {
                    talk_c::emit(&output.module).map_err(|error| error.to_string())
                }) {
                    Ok(artifact) => print!("{}", artifact.source),
                    Err(message) => {
                        eprintln!("error: {message}");
                        std::process::exit(1);
                    }
                }
            } else {
                let mir_entry = talk::compiling::driver::MirEntry::Exports {
                    names: exports,
                    allowed_effects: allow_effects,
                };
                let artifact = match typed.compile_mir(mir_entry).and_then(|output| {
                    talk_c::emit_library(&output.module, prefix.as_deref().unwrap_or("talk"))
                        .map_err(|error| error.to_string())
                }) {
                    Ok(artifact) => artifact,
                    Err(message) => {
                        eprintln!("error: {message}");
                        std::process::exit(1);
                    }
                };
                for (path, text) in [(&header, &artifact.header), (&manifest, &artifact.manifest)] {
                    if let Some(path) = path
                        && let Err(err) = std::fs::write(path, text)
                    {
                        eprintln!("error: failed to write {path}: {err}");
                        std::process::exit(1);
                    }
                }
                print!("{}", artifact.source);
            }
        }
        Commands::Mir {
            filenames,
            entry,
            no_opt,
            debug,
        } => {
            let typed = check_or_exit(filenames);
            match typed.render_mir(entry.as_deref(), !no_opt, *debug) {
                Ok(rendered) => print!("{rendered}"),
                Err(message) => {
                    eprintln!("error: {message}");
                    std::process::exit(1);
                }
            }
        }
        Commands::Html { filename } => {
            init();
            use talk::compiling::frontend::highlight_html;

            let source = input_text(filename.as_deref());
            let html = highlight_html(&source);
            println!("{html}");
        }
        Commands::Format { filename, width } => {
            init();
            let source = input_text(filename.as_deref());
            print!(
                "{}",
                talk::compiling::frontend::format_string_with_width(&source, width.unwrap_or(80))
            );
        }
    }
}

#[cfg(feature = "cli")]
const STDIN_NAME: &str = "<stdin>";

#[cfg(feature = "cli")]
const LLM_REFERENCE: &str = r#"# Talk language reference for LLMs

Talk is a statically typed, Swift-flavored language with local type inference, generics, protocols, algebraic effects, hygienic macros, and value-semantics aggregates. Normal source files use `.tlk`. Core files under `core/` are implicitly imported unless the first line is `// no-core`.

## CLI

    talk run [--entry NAME] [--bin NAME] [--offline] [files-or-package] [-- args...]
        compile and execute source or a package binary; arguments after `--` are returned by `OS.argc()`
    talk test [--json] [--filter NAME] [paths]
        discover `tests/**/*.test.tlk` and `src/**/*.test.tlk`, or run selected paths
    talk check [--json] [files]
        typecheck and ownership-check; package files use their manifest context, and no files checks targets and tests
    talk build files -o FILE [--entry NAME]
        build a bytecode image; `--native` drives the C backend and compiler (`--cc`, `--target`, `--cflag`, `--keep-c`)
    talk run-image FILE
        validate and execute a bytecode image
    talk bytecode [--entry NAME] files
        render register bytecode
    talk mir [--entry NAME] [--no-opt] [--debug] files
        render optimized or raw MIR, optionally with source annotations
    talk c [--entry NAME] files
        emit C; repeated `--export` plus `--header`/`--manifest` emits a host-callable library
    talk bootstrap [DIR] [-o FILE] [--export NAME] [--allow-effect EFFECT] [--check]
        build or verify a fixed-point service artifact; no DIR targets the self-hosted frontend
    talk fix-labels [--core DIR | --each] files
        rewrite call sites to match declared argument labels
    talk new NAME / talk install / talk update [packages]
        create and resolve packages (`--offline` is available for install/update)
    talk repl
        interactive declarations, type queries, completion, and smart indentation
    talk format [--width N] [file]
        format a file or stdin
    talk parse [file] / talk html [file]
        development parse-tree and highlighted-HTML views
    talk hover [file] --line N --column N | --byte-offset N | --node-id ID
        query the type and callable signature at a source position
    talk lsp --stdio
        run the language server
    talk setup nvim / talk completions SHELL / talk llm
        install Neovim files, generate completions, or print this reference

Use `talk COMMAND --help` for the complete option set. `-` denotes stdin where a command accepts a source file.

## Files, modules, and packages

Comments are `//` line comments. Statements are newline-separated; semicolons are accepted but normally omitted. Blocks use `{ ... }`. Declarations are file-private unless prefixed with `pub`; members may also be public. Local `let` bindings are sequential and may shadow. Function declarations are item-like and can be referenced throughout their block.

Imports select public symbols, aliases, whole modules, or recursive source globs:

    use package::models::{ User, load as load_user }
    use package::models
    use package::models::*
    use self::child::{ value }
    use super::shared::{ Thing }
    use dependency::{ API }

`package::` is rooted at the current package's source root; `self::` and `super::` are relative. A dependency name starts an external-package import. `use path` imports the module's public surface. `use path::*` additionally walks source submodules recursively. A package uses `package.tlk`, `package.lock`, `src/`, and optional `tests/`; `talk run` and `talk check` locate the enclosing package automatically.

Test files use the test prelude, commonly:

    test "name" {
        assert(actual == expected)
    }

## Declarations, labels, and receivers

    pub let answer: Int = 42

    func transform<T>(_ value: T, with count: Int) -> T where T: Copy {
        value
    }

    struct Point {
        pub let x: Int
        pub let y: Int
        init(x: Int, y: Int) { self.x = x; self.y = y; self }
        func magnitude() -> Int { x * x + y * y }
        mut func reset() -> Void { self.x = 0 }
        consuming func take_x() -> Int { self.x }
        static func origin() -> Point { Point(x: 0, y: 0) }
    }

    enum Optional<T> {
        case some(T)
        case none
    }

    protocol IteratorLike {
        associated Element
        mut func next() -> Element?
    }

    extend<T> Box<T>: IteratorLike where T: Copy {
        typealias Element = T
        mut func next() -> T? { ... }
    }

    typealias Pair = (Int, Int)
    effect 'ask<T>(value: T) -> T

Structs get a memberwise initializer when no custom `init` is declared. An initializer assigns `self.field` and returns `self`. Methods have implicit `self`; do not declare a self parameter. Plain methods share the receiver, `mut func` can write it back, `consuming func` takes it, and `static func` is called on the type or protocol namespace. Protocols may inherit protocols, require `init`, methods, static methods, and associated types, and supply default bodies. Extensions may add methods, bind generics with `extend<T> Head<T>`, and declare conformances.

Argument labels are part of a named function or method's callable signature:

    func positional(x) { x }             // call as positional(1)
    func labeled(x:) { x }               // call as labeled(x: 1)
    func typed(x: Int) { x }             // call as typed(x: 1)
    func renamed(with value: Int) { value } // call as renamed(with: 1)
    func bare(_ value: Int) { value }     // call as bare(1)

A bare inferred parameter is positional. A colon opts into a same-name label; typed parameters are labeled unless `_` omits the label. Call arguments never use `&`; the declared parameter mode determines borrowing. Plain parameters are shared borrows by default, `borrow` spells that explicitly, `mut` is exclusive/inout, `consume` transfers ownership to the callee, and `consume mut` is owned and locally mutable. A `mut` call argument names a writable place, for example `bump(value: mut n)`; ordinary and consuming arguments are passed without a marker.

## Expressions, literals, and calls

Literals include integers, floats, strings, characters (`'x'`), `true`, `false`, arrays `[a, b]`, tuples `(a, b)`, unit `()`, and structural records. Records support spread:

    let point = { x: 1, y: 2 }
    let moved = { x: 3, ...point }

Arrays support subscript syntax `items[index]`. Ranges use `lower..upper` (closed) and `lower..<upper` (half-open). Constructors are calls: `Point(x: 1, y: 2)`. Enum cases may be qualified or inferred: `Optional<Int>.some(1)` or `.some(1)`. Labeled enum payloads use the labels in construction and patterns. Member access is `value.field`, tuple access is `value.0`, and methods are `value.method(args)`. Generic arguments may be explicit on functions, types, effects, and case references.

Closures have `func` and block forms:

    func(x: Int) -> Int { x + 1 }
    { x in x + 1 }
    { $0 + 1 }

Trailing-block syntax passes a final closure argument: `items.map { $0 + 1 }`. Blocks are expressions and return their final expression. `let` bindings are mutable by assignment: `let x = 1; x = 2`. Type ascription is `let x: Int = 1`. Assignment also targets fields, tuple projections, and supported subscripts/places.

Common operators include arithmetic `+ - * /`, comparisons `== != < <= > >=`, Boolean `! && ||`, bitwise `& | ^ ~ << >>`, ranges `.. ..<`, postfix propagation `?`, postfix force unwrap `!`, and `as`. Arithmetic and comparison operators resolve through core protocols. String `+` concatenates. Shift amounts are masked to the operand width.

On any two-variant enum, `value?` extracts the first variant or returns the second variant from the enclosing function. `value!` extracts the first variant or evaluates `unreachable`, which performs Core's `'panic` effect. `as` performs supported ascriptions/conversions, including packing protocol existentials.

## Control flow and patterns

`if condition { ... } else { ... }` is an expression when both branches agree in type; statement `if` may omit `else`, and `else if` chains are supported. Conditions may mix Boolean and pattern clauses separated by commas. They run left to right, short-circuit, and expose earlier bindings to later clauses:

    if let .some(user) = lookup(), user.is_valid() {
        use_user(user)
    }

`let pattern = value else { ... }` binds after the statement and runs the `else` block if the pattern misses. `loop { ... }` is infinite and `loop condition { ... }` is while-like. `break`, `continue`, and `return value` are supported. `for x in iterable` uses `Iterable`/`Iterator`; `for x in consume xs` consumes the source, while `for x in mut xs` iterates with writeback.

`match` is exhaustive and is itself an expression:

    match value {
        .some(x) -> x,
        .none -> 0
    }

Patterns include integer, float, Boolean, character, and string literals; bindings and `_`; tuples; enum variants; records; structs; and alternatives with `|`:

    match token {
        "if" | "else" -> 1,
        _ -> 0
    }

    match point {
        Point { x, y: 0, .. } -> x,
        Point { x, y } -> x + y
    }

Record patterns use `{ x, y: pattern, .. }`. Enum cases may have labeled payload patterns. GADT-style cases can refine the enum result, for example `case int(Int) -> Expr<Int>`.

## Types, generics, and protocols

Builtin scalar/value types include `Int`, `Float`, `Bool`, `Byte`, `RawPtr`, `Void`/`()`, and `Never`. Core nominal types include `Character`, `String`, `Substring`, `Array<T>`, `InlineArray<T, N>`, `Optional<T>`, `Result<S, F>`, and range types. `[T]` is `Array<T>`, `[T; N]` is exact-size `InlineArray<T, N>`, and `T?` is optional. Tuples use `(A, B)` and structural records use `{ field: Type }`. Nested/module types use paths such as `graph::Node` and `Array<Int>.Iterator`.

Function types are `(A, B) -> R`. Parameter ownership can appear in them, for example `(mut [Byte], consume String) -> Void`. Effect rows precede the arrow: `(A) 'io -> R`, `(A) '[io, panic] -> R`, or pure `(A) '[] -> R`. A rank-N/quantified function type is `<T, U: Bound>(T, U) -> T`.

Borrow types are `&T`; exclusive borrows are `&mut T`; `*T` is uniquely owned. Protocol existentials are `any P`, with associated bindings written `any P<Element = Int>`. Only object-safe protocols whose requirements keep `Self` in receiver position form existentials. `Self` names the implementing type.

Type generics use angle brackets. Bounds may appear inline or in `where`; associated-type equality and static constraints use `==`, `<`, and `<=`. Separate where predicates use `&&`, and protocol composition within one predicate uses `&`:

    func first<T>(xs: T) -> Int
        where T: Iterable & Copy && T.Element == Int
    { ... }

Static value generics are declared with `static`, are part of type identity, and accept restricted compile-time expressions:

    struct Buffer<Element, static N: Int> { ... }
    func narrow<static N: Int>(x: Int) -> Int where N < 8 { x }
    let bytes: [Byte; 32] = ...
    let matrix: Matrix<N + 1, (M) * 2> = ...

Generic parameters and protocols may have defaults, such as `protocol Eq<RHS = Self>`. Associated types use `associated Name` (optionally with a bound/where clause) and conforming extensions normally provide `typealias Name = Type`.

## Effects

Effects are declarations and calls whose names begin with a tick:

    effect 'ask<T>(value: T) -> T
    let answer = 'ask(value: 42)

A function with no written row infers an open row. A single closed effect is `'io`; a closed list is `'[io, panic]`; `'[]` is explicitly pure; `'[io, ..]` includes `io` while leaving the row open. Generic effect instantiations are tracked independently, and one handler for a label covers every instantiation in its extent.

A handler statement installs a dynamically scoped handler for the subsequent portion of its block and calls made there:

    #handle 'ask { value in
        'continue value
    }
    let answer = 'ask(value: 42)

`'continue expression` resumes at the perform site when the effect has a non-`Never` return. A handler path that does not continue aborts the handled computation. The nearest same-label handler wins. Function values carry latent effect requirements but resolve handlers at invocation time rather than capturing the handler active when the closure was created.

`unreachable` performs Core's public abortive `effect 'panic(message: String) -> Never`. It may be intercepted with `#handle 'panic`; the outer Core host fallback prints an unhandled panic and terminates. Core also uses host effects including `io`, `alloc`, and `async`.

## Hygienic macros

A file-local declarative macro is a balanced token template with `$` parameters:

    macro choose($condition, $yes, $no) {
        if $condition { $yes } else { $no }
    }

    let result = @choose(flag, 1, 2)

Rules may overload by arity. Templates are hygienic: template-written binders and free names use definition-site context, while spliced syntax keeps use-site context. Repeating `$value` repeats evaluation; normal type, effect, ownership, and exhaustiveness checking applies after expansion.

The same `@name(...)` form can expand in expression, root/block item, nominal-member, pattern, and type positions; the invocation position selects the grammar used to parse the expansion. A caller-provided identifier spliced into binder position intentionally exposes a generated declaration. `@assert(condition)` is compiler-provided and preserves the condition's source text in its failure message.

Packages may export deterministic procedural expression macros compiled from `*.macro.tlk` services. Imported procedural macros receive one balanced `(...)`, `[...]`, or `{...}` input tree; for example the bundled `html` stdlib module uses `@html { ... }`. Macro services use typed syntax values and `quote { ... }`, run under fixed budgets, and cannot use inline IR or `#unsafe`.

## Memory, ownership, and declaration grades

Ordinary structs, enums, arrays, strings, tuples, records, and functions have value semantics. Aggregates use reference counting and copy-on-write storage where appropriate. Assignment creates a value snapshot; mutation does not change existing shared views.

Plain parameters and methods borrow by default. `consume` is a callee ownership contract: if a shareable caller value has later uses, the compiler retains it automatically; the final use can move. Returning, capturing, or storing a view generally retains the referent so the escaped value owns its snapshot. A bare borrow return rooted in a frame-owned local is rejected because ownership cannot travel in that `&T` representation.

`struct Name 'linear` and `enum Name 'linear` declare values that must be consumed exactly once on every finite path and cannot be implicitly copied or dropped. `struct Name 'heap`/`enum Name 'heap` use aliased, region-allocated reference semantics; recursive nominal layouts infer the same heap indirection automatically. `*T` is a statically unique value. Marker protocols such as `Copy`, `Clone`, `Borrowed`, `Owner`, and `Deinit` express library ownership roles; payload-free enums are `Copy` automatically.

Static ownership errors are limited to real invariants: overlapping access involving a live `&mut` loan, duplication/drop misuse of linear or unique values, declaration well-formedness (including invalid borrowed fields or parameter modes), unsupported heap placement, definite initialization, and use of unsafe operations outside an unsafe boundary.

Low-level core code uses `#_ir(args...) { ... }`. The trusted IR includes scalar math and comparison, allocation/free, load/store/take, retain/copy/swap, pointer offset, inline-array access, conversions, and host I/O. Outside Core, raw-pointer operations and `_ir` perform the intrinsic `'unsafe` effect; a lexical `#unsafe { ... }` acknowledges and discharges it without installing a runtime handler.

## Core library

Frequently used protocols include `Showable`, `Add`, `Equatable`, `Comparable`, bitwise/shift protocols, `Iterable`, `Iterator`, `From`, `Into`, `Copy`, `Clone`, `Borrowed`, `Owner`, and `Deinit`. `print(value)` renders supported values. Arrays provide copy-on-write mutation and iterator adapters. Strings are UTF-8; `String`/`Substring` iterate extended grapheme-cluster `Character` values, while `.scalars()` and `.utf8()` provide lower-level views. `Result` uses `.ok`/`.error`; `Optional` uses `.some`/`.none`.

## Compiler model

Pipeline: self-hosted parse -> collect and expand macros -> desugar -> resolve modules/names -> OutsideIn-style type checking with qualified predicates, protocols, associated types, existentials, static values, row-polymorphic effects, and GADT refinements -> typed program -> register MIR -> ownership checking and drop elaboration -> optimization/register allocation -> register bytecode.

The default runtime validates and executes bytecode in the register VM. The static C runtime and Wasm embedding host the same VM. The ahead-of-time C backend and external LLVM backend consume the compiler's finalized public MIR; `talk build --native` uses C. Useful inspection surfaces are `talk check`, `talk hover`, `talk bytecode`, and `talk mir --debug`.
"#;

#[cfg(feature = "cli")]
const NVIM_RUNTIME_FILES: &[(&str, &[u8])] = &[
    (
        "ftdetect/talktalk.lua",
        include_bytes!("../../dev/editors/nvim/ftdetect/talktalk.lua"),
    ),
    (
        "ftplugin/talktalk.lua",
        include_bytes!("../../dev/editors/nvim/ftplugin/talktalk.lua"),
    ),
    (
        "indent/talktalk.vim",
        include_bytes!("../../dev/editors/nvim/indent/talktalk.vim"),
    ),
    (
        "lua/neotest-talk/init.lua",
        include_bytes!("../../dev/editors/nvim/lua/neotest-talk/init.lua"),
    ),
    (
        "syntax/talktalk.vim",
        include_bytes!("../../dev/editors/nvim/syntax/talktalk.vim"),
    ),
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

        println!("Installing TalkTalk Neovim runtime files bundled with talk");
        println!("Target runtime root: {}", self.target_root.display());

        for &(relative_path, contents) in NVIM_RUNTIME_FILES {
            let target = self.target_root.join(relative_path);
            if target.exists() && !self.force {
                let existing = std::fs::read(&target)
                    .with_context(|| format!("failed to read {}", target.display()))?;
                if existing.as_slice() != contents {
                    anyhow::bail!(
                        "{} already exists and differs; rerun with --force to overwrite",
                        target.display()
                    );
                }
            }
        }

        for &(relative_path, contents) in NVIM_RUNTIME_FILES {
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

/// Print the compiler's diagnostics in the same annotated form
/// `talk check` renders, exiting on errors. One pipeline for every
/// command that type-checks. Successful-but-noisy programs print
/// nothing here: the corpus contract keeps stderr for failures (and
/// the runtime's own reports), so warnings wait for `talk check`.
#[cfg(feature = "cli")]
fn report_diagnostics_or_exit(
    asts_by_source: &indexmap::IndexMap<
        talk::compiling::driver::Source,
        talk::ast::AST<talk::ast::NameResolved>,
    >,
    typed: &talk::compiling::driver::Driver<talk::compiling::driver::Typed>,
) {
    if !typed.has_errors() {
        return;
    }
    let diagnostics =
        talk::analysis::CompileDiagnostics::from_driver_asts(asts_by_source, typed.diagnostics());
    eprint!(
        "{}",
        diagnostics.render_text(talk::cli::diagnostics::ColorMode::Auto)
    );
    std::process::exit(1);
}

/// Package errors with frontend diagnostics print in the same
/// annotated form; everything else keeps the one-line form.
#[cfg(feature = "cli")]
fn print_package_error(err: &talk::compiling::package::PackageError) {
    if let talk::compiling::package::PackageError::CompileDiagnostics(diagnostics) = err {
        eprint!(
            "{}",
            diagnostics.render_text(talk::cli::diagnostics::ColorMode::Auto)
        );
    } else {
        eprintln!("error: {err}");
    }
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
    let asts_by_source = resolved.phase.asts.clone();
    let typed = resolved.type_check();
    report_diagnostics_or_exit(&asts_by_source, &typed);
    typed
}

/// Create the scratch translation unit, refusing to write through an
/// existing file. `create_new` makes the create-and-open one step, so a
/// name that lost a race -- or was pre-created as a symlink pointing
/// somewhere else -- is an error rather than a file this process
/// truncates. On unix it is created readable only by its owner.
#[cfg(feature = "cli")]
fn scratch_source(source: &str) -> std::io::Result<std::path::PathBuf> {
    use std::io::Write as _;

    let directory = std::env::temp_dir();
    let mut last = None;
    for attempt in 0..32u32 {
        let unique = format!(
            "talk-{}-{}-{attempt}.c",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|elapsed| elapsed.as_nanos())
                .unwrap_or_default()
        );
        let path = directory.join(unique);
        let mut options = std::fs::OpenOptions::new();
        options.write(true).create_new(true);
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt as _;
            options.mode(0o600);
        }
        match options.open(&path) {
            Ok(mut file) => {
                file.write_all(source.as_bytes())?;
                return Ok(path);
            }
            Err(err) if err.kind() == std::io::ErrorKind::AlreadyExists => last = Some(err),
            Err(err) => return Err(err),
        }
    }
    Err(last.unwrap_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::AlreadyExists,
            "could not find an unused scratch name",
        )
    }))
}

/// Which C compiler to drive.
///
/// The default is the host's, because the generated translation unit is
/// ordinary self-contained C and whatever the machine already has will
/// build it. Cross-compiling is the case that needs more than a compiler
/// -- headers and a libc for the target too -- so it goes through `zig
/// cc`, which carries its own.
#[cfg(feature = "cli")]
enum Toolchain {
    Host(String),
    Zig(String),
}

#[cfg(feature = "cli")]
impl Toolchain {
    fn command(&self) -> (&str, Vec<String>) {
        match self {
            Toolchain::Host(program) => (program, vec![]),
            Toolchain::Zig(triple) => ("zig", vec!["cc".into(), "-target".into(), triple.clone()]),
        }
    }
}

#[cfg(feature = "cli")]
fn toolchain(compiler: Option<&str>, target: Option<&str>) -> Result<Toolchain, String> {
    let Some(triple) = target else {
        return Ok(Toolchain::Host(
            compiler
                .map(str::to_string)
                .or_else(|| std::env::var("CC").ok())
                .unwrap_or_else(|| "cc".to_string()),
        ));
    };
    // An explicit --cc wins: someone who has a cross toolchain of their
    // own should not be made to install another one.
    if let Some(compiler) = compiler {
        return Ok(Toolchain::Host(compiler.to_string()));
    }
    let available = std::process::Command::new("zig")
        .arg("version")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .is_ok_and(|status| status.success());
    if !available {
        return Err(format!(
            "error: cross-compiling to `{triple}` needs `zig` on PATH\n\
             note: zig cc carries headers and a libc for every target, which a\n\
             \x20     bare cross compiler does not\n\
             note: install it from https://ziglang.org/download/ (or your package\n\
             \x20     manager), or pass --cc with a cross compiler you already have"
        ));
    }
    Ok(Toolchain::Zig(triple.to_string()))
}

/// Compile ahead of time to a native executable: emit C, then drive a C
/// compiler over it. The generated translation unit is self-contained, so
/// there is nothing to link against and no build system involved.
#[cfg(feature = "cli")]
fn build_native(
    filenames: &[String],
    output: &str,
    entry: Option<&str>,
    compiler: Option<&str>,
    target: Option<&str>,
    extra_flags: &[String],
    keep_c: bool,
) {
    let toolchain = match toolchain(compiler, target) {
        Ok(toolchain) => toolchain,
        Err(message) => {
            eprintln!("{message}");
            std::process::exit(1);
        }
    };
    let mir_entry = match entry {
        Some(name) => talk::compiling::driver::MirEntry::Named(name),
        None => talk::compiling::driver::MirEntry::Script,
    };
    let source = match check_or_exit(filenames)
        .compile_mir(mir_entry)
        .and_then(|output| talk_c::emit(&output.module).map_err(|error| error.to_string()))
    {
        Ok(artifact) => artifact.source,
        Err(message) => {
            eprintln!("error: {message}");
            std::process::exit(1);
        }
    };

    // A uniquely named scratch file, never `<output>.c`: building `foo`
    // must not truncate a `foo.c` that the user owns. `--keep-c` is the
    // one case that writes beside the output, because it was asked for.
    let c_path = if keep_c {
        std::path::Path::new(output).with_extension("c")
    } else {
        match scratch_source(&source) {
            Ok(path) => path,
            Err(err) => {
                eprintln!("error: failed to write the generated C: {err}");
                std::process::exit(1);
            }
        }
    };
    if keep_c && let Err(err) = std::fs::write(&c_path, &source) {
        eprintln!("error: failed to write {}: {err}", c_path.display());
        std::process::exit(1);
    }

    let (program, leading) = toolchain.command();
    let mut command = std::process::Command::new(program);
    command
        .args(leading)
        .args(["-O2", "-std=c11"])
        .arg(&c_path)
        .arg("-o")
        .arg(output)
        .args(extra_flags);
    let status = match command.status() {
        Ok(status) => status,
        Err(err) => {
            eprintln!("error: failed to run `{program}`: {err}");
            eprintln!("note: the generated C is at {}", c_path.display());
            std::process::exit(1);
        }
    };
    if !status.success() {
        eprintln!("error: `{program}` failed to compile the generated C");
        eprintln!("note: the generated C is at {}", c_path.display());
        std::process::exit(1);
    }
    if !keep_c {
        let _ = std::fs::remove_file(&c_path);
    }
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

#[cfg(feature = "cli")]
fn run_external_command(arguments: &[std::ffi::OsString]) -> ! {
    let Some((name, arguments)) = arguments.split_first() else {
        eprintln!("error: missing external command name");
        std::process::exit(1);
    };
    let mut executable = std::ffi::OsString::from("talk-");
    executable.push(name);
    let status = match std::process::Command::new(&executable)
        .args(arguments)
        .status()
    {
        Ok(status) => status,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            eprintln!(
                "error: `{}` is not a talk command; `{}` was not found in PATH",
                name.to_string_lossy(),
                executable.to_string_lossy()
            );
            std::process::exit(1);
        }
        Err(error) => {
            eprintln!(
                "error: failed to run `{}`: {error}",
                executable.to_string_lossy()
            );
            std::process::exit(1);
        }
    };
    std::process::exit(status.code().unwrap_or(1));
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
